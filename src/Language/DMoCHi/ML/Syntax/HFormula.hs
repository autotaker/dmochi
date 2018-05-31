{-# LANGUAGE DeriveGeneric, GeneralizedNewtypeDeriving, RecordWildCards #-}
module Language.DMoCHi.ML.Syntax.HFormula(
  HFormula(..), HFormulaFactory(..)
  , getIdent, getIValue, Context(..), HFormulaT, runHFormulaT, newContext
  , mkBin, mkUni, mkVar, mkLiteral
  , toHFormula, fromHFormula, calcCondition, fromBFormula
) where

import qualified Data.HashTable.IO as H
import           Data.Hashable
import           Text.PrettyPrint.HughesPJClass
import           Data.Type.Equality
import           Control.Monad.Reader
import           Data.IORef
import qualified Z3.Monad as Z3
import qualified Z3.Base as Z3Base

import           Language.DMoCHi.Common.Id
import           Language.DMoCHi.Common.Util
import           Language.DMoCHi.Common.Cache
import           Language.DMoCHi.ML.Syntax.Type
import           Language.DMoCHi.ML.Syntax.Atom hiding(mkBin, mkUni, mkVar, mkLiteral)
import           Language.DMoCHi.ML.Syntax.BFormula
import qualified Language.DMoCHi.ML.SMT as SMT


data HFormula where
    HFormula :: (WellFormed l HFormula arg, Supported l (Labels HFormula)) => 
                !(SLabel l) -> !arg -> Type -> SMT.IValue -> Int -> HFormula

data HFormulaKey where 
    HFormulaKey :: (WellFormed l HFormula arg, Supported l (Labels HFormula)) =>
                    SLabel l -> arg -> HFormulaKey

type instance Key HFormula = HFormulaKey

getIdent :: HFormula -> Int
getIdent (HFormula _ _ _ _ key) = key

getIValue :: HFormula -> SMT.IValue
getIValue (HFormula _ _ _ iv _) = iv

type instance Ident HFormula  = TId
type instance Labels HFormula  = '[ 'Literal, 'Var, 'Unary, 'Binary ]
type instance BinOps HFormula = '[ 'Add, 'Sub, 'Div, 'Mul, 'Eq, 'Lt, 'Lte, 'And, 'Or ]
type instance UniOps HFormula = '[ 'Fst, 'Snd, 'Not, 'Neg ]

instance HasType HFormulaKey where
    getType (HFormulaKey l arg) =
        case (l, arg) of
            (SLiteral, CInt _) -> TInt
            (SLiteral, CBool _) -> TBool
            (SLiteral, CUnit)  -> error "unexpected pattern"
            (SVar, x)    -> getType x
            (SUnary, _)  -> getType arg
            (SBinary, _) -> getType arg

instance HasType HFormula where
    getType (HFormula _ _ ty _ _) = ty

instance Hashable (BinArg HFormula) where
    hashWithSalt salt (BinArg l v1 v2) = 
        salt `hashWithSalt` l 
             `hashWithSalt` getIdent v1 
             `hashWithSalt` getIdent v2

instance Hashable (UniArg HFormula) where
    hashWithSalt salt (UniArg l v) = 
        salt `hashWithSalt` l 
             `hashWithSalt` getIdent v 

instance Hashable HFormulaKey where
    hashWithSalt salt (HFormulaKey l arg) =
        case l of
            SLiteral -> salt `hashWithSalt` (1 :: Int) `hashWithSalt` arg
            SVar     -> salt `hashWithSalt` (2 :: Int) `hashWithSalt` arg
            SBinary  -> salt `hashWithSalt` (3 :: Int) `hashWithSalt` arg
            SUnary   -> salt `hashWithSalt` (4 :: Int) `hashWithSalt` arg

instance Eq HFormulaKey where
    (==) (HFormulaKey l1 arg1) (HFormulaKey l2 arg2) =
        case (l1,l2) of
            (SLiteral, SLiteral) -> arg1 == arg2
            (SLiteral, _) -> False
            (SVar, SVar) -> arg1 == arg2
            (SVar, _) -> False
            (SBinary, SBinary) -> 
                case (arg1, arg2) of
                    (BinArg op1 v1 v2, BinArg op2 v3 v4) -> 
                        case testEquality op1 op2 of
                            Just _ -> v1 == v3 && v2 == v4
                            Nothing -> False
            (SBinary, _) -> False
            (SUnary, SUnary) ->
                case (arg1, arg2) of
                    (UniArg op1 v1, UniArg op2 v2) ->
                        case testEquality op1 op2 of
                            Just _ -> v1 == v2
                            Nothing -> False
            (SUnary, _) -> False

instance Eq HFormula where
    (==) = (==) `on` getIdent  
instance Ord HFormula where
    compare = compare `on` getIdent


data Context = 
    Context {
        ctxHFormulaCache :: Cache HFormula 
      , ctxBFormulaCache :: Cache BFormula
      , ctxCheckSatCache :: HashTable (Int, Int) Bool
      , ctxSMTSolver     :: Z3.Solver
      , ctxSMTContext    :: Z3.Context
      , ctxSMTCount      :: IORef Int
      , ctxSMTCountHit   :: IORef Int
    }

newtype HFormulaT m a = HFormulaT { unHFRomulaT :: ReaderT Context m a }
    deriving (Monad, Applicative, Functor, MonadFix, MonadIO, MonadLogger, MonadReader Context, MonadTrans, MonadId)

runHFormulaT :: HFormulaT m a -> Context -> m a
runHFormulaT (HFormulaT action) ctx = runReaderT action ctx

newContext :: IO Context
newContext = do
    ctxHFormulaCache <- newCache
    ctxBFormulaCache <- newCache
    ctxCheckSatCache <- H.new
    (ctxSMTSolver, ctxSMTContext) <- Z3Base.withConfig $ \cfg -> do
        Z3.setOpts cfg Z3.stdOpts
        ctx <- Z3Base.mkContext cfg
        solver <- Z3Base.mkSolver ctx
        return (solver, ctx)
    ctxSMTCount <- newIORef 0
    ctxSMTCountHit <- newIORef 0
    return $ Context {..}


    

instance MonadIO m => Z3.MonadZ3 (HFormulaT m) where
    getSolver = ctxSMTSolver <$> ask
    getContext = ctxSMTContext <$> ask


class (Z3.MonadZ3 m, BFormulaFactory m) => HFormulaFactory m where
    getHFormulaCache :: m (Cache HFormula)
    checkSat         :: HFormula -> HFormula -> m Bool


instance MonadIO m => HFormulaFactory (HFormulaT m) where
    getHFormulaCache = ctxHFormulaCache <$> ask
    {-# INLINE checkSat #-}
    checkSat p1 p2 = {- measureTime CheckSat $-} do
        ctx <- ask
        let key = (getIdent p1, getIdent p2)
        res <- liftIO $ H.lookup (ctxCheckSatCache ctx) key
        case res of
            Just v -> do
                liftIO $ modifyIORef' (ctxSMTCountHit ctx) succ 
                return v
            Nothing -> do 
                liftIO $ modifyIORef' (ctxSMTCount ctx) succ 

                v <- Z3.local $ do
                    SMT.ASTValue cond <- getIValue <$> mkBin SAnd p1 p2  
                    Z3.assert cond
                    res <- Z3.check
                    case res of
                        Z3.Sat -> return True
                        Z3.Unsat -> return False
                        Z3.Undef -> liftIO $ putStrLn "Undef" >> return True
                liftIO $ H.insert (ctxCheckSatCache ctx) key v
                return v

{-# INLINE genHFormula #-}
genHFormula :: HFormulaFactory m => HFormulaKey -> m SMT.IValue -> m HFormula
genHFormula key@(HFormulaKey l arg) m_iv = do
    cache <- getHFormulaCache
    genEntry cache key $ \i -> do
        iv <- m_iv
        return $ HFormula l arg (getType key) iv i


instance MonadIO m => BFormulaFactory (HFormulaT m) where
    getBFormulaCache = ctxBFormulaCache <$> ask


{-# INLINE mkBin #-}
mkBin :: (HFormulaFactory m, Supported op (BinOps HFormula))  => 
         SBinOp op -> HFormula -> HFormula -> m HFormula
mkBin op v1 v2 = 
    let iv1 = getIValue v1
        iv2 = getIValue v2
        SMT.ASTValue v1' = iv1
        SMT.ASTValue v2' = iv2
        isLinear = case (v1, v2) of
            (HFormula SLiteral (CInt _) _ _ _, _ ) -> True
            (_, HFormula SLiteral (CInt _) _ _ _) -> True
            _ -> False
        key = HFormulaKey SBinary (BinArg op v1 v2)
    in case op of
        SAdd -> genHFormula key (SMT.ASTValue <$> Z3.mkAdd [v1', v2']) 
        SSub -> genHFormula key (SMT.ASTValue <$> Z3.mkSub [v1', v2'])
        SDiv -> genHFormula key (SMT.mkUDiv iv1 iv2)
        SMul -> genHFormula key (SMT.mkUMul isLinear iv1 iv2)
        SEq  -> genHFormula key (SMT.mkEqIValue iv1 iv2)
        SLt  -> genHFormula key (SMT.ASTValue <$> Z3.mkLt v1' v2')
        SLte -> genHFormula key (SMT.ASTValue <$> Z3.mkLe v1' v2')
        SAnd -> case (v1, v2) of
            (HFormula SLiteral (CBool True) _ _ _, _) -> return v2
            (_, HFormula SLiteral (CBool True) _ _ _) -> return v1
            (HFormula SLiteral (CBool False) _ _ _, _) -> return v1
            (_, HFormula SLiteral (CBool False) _ _ _) -> return v2
            _ -> genHFormula key (SMT.ASTValue <$> Z3.mkAnd [v1', v2'])
        SOr  -> case (v1, v2) of
            (HFormula SLiteral (CBool True) _ _ _, _) -> return v1
            (_, HFormula SLiteral (CBool True) _ _ _) -> return v2
            (HFormula SLiteral (CBool False) _ _ _, _) -> return v2
            (_, HFormula SLiteral (CBool False) _ _ _) -> return v1
            _ -> genHFormula key (SMT.ASTValue <$> Z3.mkOr [v1', v2'])

{-# INLINE mkUni #-}
mkUni :: (HFormulaFactory m, Supported op (UniOps HFormula)) => SUniOp op -> HFormula -> m HFormula
mkUni op v1 = 
    let key = HFormulaKey SUnary (UniArg op v1) in
    case op of
        SNeg -> 
            let SMT.ASTValue v1' = getIValue v1 in
            genHFormula key (SMT.ASTValue <$> Z3.mkUnaryMinus v1')
        SNot -> 
            let SMT.ASTValue v1' = getIValue v1 in
            genHFormula key (SMT.ASTValue <$> Z3.mkNot v1')
        SFst -> 
            let SMT.IPair iv_fst _ = getIValue v1 in
            genHFormula key (pure iv_fst)
        SSnd -> 
            let SMT.IPair _ iv_snd = getIValue v1 in
            genHFormula key (pure iv_snd)

{-# INLINE mkLiteral #-}
mkLiteral :: HFormulaFactory m => Lit -> m HFormula
mkLiteral l@(CInt i)  = genHFormula (HFormulaKey SLiteral l) (SMT.ASTValue <$> Z3.mkInteger i)
mkLiteral l@(CBool b) = genHFormula (HFormulaKey SLiteral l) (SMT.ASTValue <$> Z3.mkBool b)
mkLiteral CUnit = error "unexpected pattern"

{-# INLINE mkVar #-}
mkVar :: HFormulaFactory m => TId -> m HFormula
mkVar x@(TId sty name_x) = genHFormula (HFormulaKey SVar x) (SMT.toIValueId sty (show name_x))

{-# INLINE toHFormula #-}
toHFormula :: HFormulaFactory m => Atom -> m HFormula
toHFormula (Atom l arg _) = 
    case (l, arg) of
        (SLiteral, arg) -> mkLiteral arg
        (SVar, arg) -> mkVar arg
        (SBinary, BinArg op v1 v2) -> do
            f1 <- toHFormula v1
            f2 <- toHFormula v2
            mkBin op f1 f2
        (SUnary, UniArg op v1) -> do
            f1 <- toHFormula v1
            mkUni op f1

fromHFormula :: HFormula -> Atom
fromHFormula (HFormula l arg sty _ _) = 
    case (l, arg) of
        (SLiteral, arg) -> Atom l arg sty
        (SVar, arg) -> Atom l arg sty
        (SBinary, BinArg op v1 v2) -> 
            Atom l (BinArg op (fromHFormula v1) (fromHFormula v2)) sty
        (SUnary, UniArg op v1) -> 
            Atom l (UniArg op (fromHFormula v1)) sty


instance Pretty HFormula where
    pPrintPrec plevel prec v = pPrintPrec plevel prec (fromHFormula v)
instance Show HFormula where
    show = render . pPrint 


-- Function: calcCondition fml ps 
-- assumption: fml is a satisfiable formula
-- assertion: phi |- fromBFormula ps ret
{-# INLINE calcCondition #-}
calcCondition :: HFormulaFactory m => HFormula -> [HFormula] -> m BFormula
calcCondition _fml _ps = {- measureTime CalcCondition $ -} do
    phi <- go 1 _fml _ps
    return phi
    where
    go _ _ [] = mkBLeaf True
    go i fml (p:ps) = do
        np <- mkUni SNot p
        b1 <- checkSat fml p
        b2 <- checkSat fml np
        v1 <- if b1 then mkBin SAnd fml p >>= \fml' -> go (i + 1) fml' ps 
                    else mkBLeaf False
        v2 <- if b2 then mkBin SAnd fml np >>= \fml' -> go (i + 1) fml' ps 
                    else mkBLeaf False
        mkBNode i v1 v2

{-# INLINE fromBFormula #-}
fromBFormula :: HFormulaFactory m => [HFormula] -> BFormula -> m HFormula
fromBFormula ps fml = 
    case body fml of
        BLeaf b -> mkLiteral (CBool b)
        BNode i p1 p2 -> do
            v1 <- fromBFormula ps p1
            v2 <- fromBFormula ps p2
            let x = ps !! (i - 1)
            nx <- mkUni SNot x
            v1 <- mkBin SAnd x  v1
            v2 <- mkBin SAnd nx v2
            mkBin SOr v1 v2
