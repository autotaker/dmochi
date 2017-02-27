{-# LANGUAGE LambdaCase, BangPatterns, DeriveGeneric, GeneralizedNewtypeDeriving, MultiParamTypeClasses #-}
module Language.DMoCHi.ML.Saturate where

import           Control.Monad
import           Control.Monad.Reader
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.HashTable.IO as H
import           Data.Hashable
import           Data.IORef
import           Text.Printf
import           Text.PrettyPrint.HughesPJClass
import           Data.Type.Equality
import           Data.Time
import           GHC.Generics (Generic)
import qualified Z3.Monad as Z3
import qualified Z3.Base as Z3Base

import           Language.DMoCHi.Common.Id
import           Language.DMoCHi.Common.Util
import           Language.DMoCHi.ML.Syntax.Type
import           Language.DMoCHi.ML.Syntax.PType hiding(Env)
import           Language.DMoCHi.ML.Syntax.PNormal hiding(mkBin, mkUni, mkVar, mkLiteral)
import qualified Language.DMoCHi.ML.Syntax.PNormal as PNormal
import           Language.DMoCHi.ML.Flow
import qualified Language.DMoCHi.ML.SMT as SMT

data IType = IInt | IBool | IPair IType IType | IFun [([IType], BFormula, ITermType)]
    deriving (Eq,Ord,Show)
data ITermType = IFail | ITerm IType BFormula
    deriving (Eq,Ord,Show)

data BFormula = BAnd BFormula BFormula | BOr BFormula BFormula | BVar Int | BConst Bool
    deriving (Eq,Ord)

data HFormula where
    HFormula :: (WellFormed l HFormula arg, Supported l (Labels HFormula)) => 
                SLabel l -> arg -> Type -> SMT.IValue -> Int -> HFormula

getIdent :: HFormula -> Int
getIdent (HFormula _ _ _ _ key) = key

getIValue :: HFormula -> SMT.IValue
getIValue (HFormula _ _ _ iv _) = iv

type instance Ident HFormula  = TId
type instance Labels HFormula  = '[ 'Literal, 'Var, 'Unary, 'Binary ]
type instance BinOps HFormula = '[ 'Add, 'Sub, 'Eq, 'Lt, 'Lte, 'And, 'Or ]
type instance UniOps HFormula = '[ 'Fst, 'Snd, 'Not, 'Neg ]

type HFormulaTbl = HashTable HFormula HFormula

instance Hashable (BinArg HFormula) where
    hashWithSalt salt (BinArg l v1 v2) = 
        salt `hashWithSalt` l 
             `hashWithSalt` getIdent v1 
             `hashWithSalt` getIdent v2

instance Hashable (UniArg HFormula) where
    hashWithSalt salt (UniArg l v) = 
        salt `hashWithSalt` l 
             `hashWithSalt` getIdent v 

instance Hashable HFormula where
    hashWithSalt salt (HFormula l arg _ _ _) =
        case l of
            SLiteral -> salt `hashWithSalt` (1 :: Int) `hashWithSalt` arg
            SVar     -> salt `hashWithSalt` (2 :: Int) `hashWithSalt` arg
            SBinary  -> salt `hashWithSalt` (3 :: Int) `hashWithSalt` arg
            SUnary   -> salt `hashWithSalt` (4 :: Int) `hashWithSalt` arg

instance Eq HFormula where
    (==) (HFormula l1 arg1 _ _ _) (HFormula l2 arg2 _ _ _) =
        case (l1,l2) of
            (SLiteral, SLiteral) -> arg1 == arg2
            (SLiteral, _) -> False
            (SVar, SVar) -> arg1 == arg2
            (SVar, _) -> False
            (SBinary, SBinary) -> 
                case (arg1, arg2) of
                    (BinArg op1 v1 v2, BinArg op2 v3 v4) -> 
                        case testEquality op1 op2 of
                            Just _ -> v1 === v3 && v2 === v4
                            Nothing -> False
            (SBinary, _) -> False
            (SUnary, SUnary) ->
                case (arg1, arg2) of
                    (UniArg op1 v1, UniArg op2 v2) ->
                        case testEquality op1 op2 of
                            Just _ -> v1 === v2
                            Nothing -> False
            (SUnary, _) -> False

infix 4 ===

(===) :: HFormula -> HFormula -> Bool
(===) = (==) `on` getIdent
            
genHFormula :: (SMT.IValue -> Int -> HFormula) -> R SMT.IValue -> R HFormula
genHFormula generator m_iv = do
    (_, _, v@(HFormula _ _ _ iv key)) <- mfix $ \ ~(ident, iv,_) ->  do
        let key = generator iv ident
        ctx <- ask
        let tbl = ctxHFormulaTbl ctx
        res <- liftIO $ H.lookup tbl key
        case res of
            Just v -> return (getIdent v, getIValue v, v)
            Nothing -> do
                ident' <- liftIO $ readIORef (ctxHFormulaSize ctx)
                liftIO $ writeIORef (ctxHFormulaSize ctx) $! (ident'+1)
                liftIO $ H.insert tbl key key
                iv' <- m_iv
                return (ident', iv',key)
    key `seq` iv `seq` return v

mkBin :: SBinOp op -> HFormula -> HFormula -> R HFormula
mkBin op v1 v2 = 
    let iv1 = getIValue v1
        iv2 = getIValue v2
        SMT.ASTValue v1' = iv1
        SMT.ASTValue v2' = iv2
    in case op of
        SAdd -> genHFormula ( HFormula SBinary (BinArg SAdd v1 v2) TInt) (SMT.ASTValue <$> Z3.mkAdd [v1', v2']) 
        SSub -> genHFormula ( HFormula SBinary (BinArg SSub v1 v2) TInt) (SMT.ASTValue <$> Z3.mkSub [v1', v2'])
        SEq  -> genHFormula ( HFormula SBinary (BinArg SEq v1 v2) TBool) (SMT.mkEqIValue iv1 iv2)
        SLt  -> genHFormula ( HFormula SBinary (BinArg SLt v1 v2) TBool) (SMT.ASTValue <$> Z3.mkLt v1' v2')
        SLte -> genHFormula ( HFormula SBinary (BinArg SLte v1 v2) TBool) (SMT.ASTValue <$> Z3.mkLe v1' v2')
        SGt  -> genHFormula ( HFormula SBinary (BinArg SLt v2 v1) TBool)  (SMT.ASTValue <$> Z3.mkGt v1' v2')
        SGte -> genHFormula ( HFormula SBinary (BinArg SLte v2 v1) TBool) (SMT.ASTValue <$> Z3.mkGe v1' v2')
        SAnd -> genHFormula ( HFormula SBinary (BinArg SAnd v1 v2) TBool) (SMT.ASTValue <$> Z3.mkAnd [v1', v2'])
        SOr  -> genHFormula ( HFormula SBinary (BinArg SOr  v1 v2) TBool) (SMT.ASTValue <$> Z3.mkOr [v1', v2'])

mkUni :: SUniOp op -> HFormula -> R HFormula
mkUni op v1@(HFormula _ _ sty _ _) = 
    case op of
        SNeg -> 
            let SMT.ASTValue v1' = getIValue v1 in
            genHFormula (HFormula SUnary (UniArg SNeg v1) TInt) (SMT.ASTValue <$> Z3.mkUnaryMinus v1')
        SNot -> 
            let SMT.ASTValue v1' = getIValue v1 in
            genHFormula (HFormula SUnary (UniArg SNot v1) TBool) (SMT.ASTValue <$> Z3.mkNot v1')
        SFst -> case sty of
            TPair sty1 _ -> 
                let SMT.IPair iv_fst _ = getIValue v1 in
                genHFormula (HFormula SUnary (UniArg SFst v1) sty1) (pure iv_fst)
            _ -> error "mkUni: Fst"
        SSnd -> case sty of
            TPair _ sty2 -> 
                let SMT.IPair _ iv_snd = getIValue v1 in
                genHFormula (HFormula SUnary (UniArg SSnd v1) sty2) (pure iv_snd)
            _ -> error "mkUni: Snd"

mkLiteral :: Lit -> R HFormula
mkLiteral l@(CInt i)  = genHFormula (HFormula SLiteral l TInt) (SMT.ASTValue <$> Z3.mkInteger i)
mkLiteral l@(CBool b) = genHFormula (HFormula SLiteral l TInt) (SMT.ASTValue <$> Z3.mkBool b)

mkVar :: TId -> R HFormula
mkVar x@(TId sty name_x) = genHFormula (HFormula SVar x sty) (SMT.toIValueId sty (show name_x))

toHFormula :: Formula -> R HFormula
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
fromHFormula :: HFormula -> Formula
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

mkBAnd, mkBOr :: BFormula -> BFormula -> BFormula
mkBAnd (BConst True) b = b
mkBAnd (BConst False) _ = BConst False
mkBAnd b (BConst True) = b
mkBAnd _ (BConst False) = BConst False
mkBAnd b1 b2 = BAnd b1 b2

mkBOr (BConst False) b = b
mkBOr (BConst True) _ = BConst True
mkBOr b (BConst False) = b
mkBOr _ (BConst True) = BConst True
mkBOr b1 b2 = BOr b1 b2

pprintEnv :: Env -> Doc
pprintEnv (penv, ienv) = brackets $ vcat $ punctuate comma (map pprintAssoc (M.keys penv)) 
    where
    pprintAssoc f = 
        let pty = penv M.! f
            ity = ienv M.! f
        in pPrint (name f) <+> text ":" <+> pPrint pty <+> text "|>" <+> pPrint ity

instance Pretty IType where
    pPrintPrec plevel prec ity =
        case ity of
            IInt  -> text "int"
            IBool -> text "bool"
            IPair ity1 ity2 -> maybeParens (prec > 0) d 
                where
                    d1 = pPrintPrec plevel 1 ity1
                    d2 = pPrintPrec plevel 1 ity2
                    d  = d1 <+> text "*" <+> d2
            IFun ty_assoc -> 
                braces $ vcat $ punctuate comma $ 
                    map (\(ty_xs, fml, ty_ret) -> 
                            let d_xs = hsep $ punctuate comma (map (pPrintPrec plevel 0) ty_xs)
                                d_fml = text $ show fml
                                d_ret = pPrintPrec plevel 0 ty_ret
                            in braces (d_xs <+> text "|" <+> d_fml) <+> text "->" <+> d_ret) ty_assoc
instance Pretty ITermType where
    pPrintPrec _ _ IFail = text "fail"
    pPrintPrec plevel _ (ITerm ty fml) = braces $ pPrintPrec plevel 0 ty <+> text "|" <+> text (show fml)

instance Show BFormula where
    showsPrec p (BVar i) = showsPrec p i
    showsPrec _ (BConst True) = showString "true"
    showsPrec _ (BConst False) = showString "false"
    showsPrec p (BAnd b1 b2) = showParen (p > 2) $ showsPrec 2 b1 . showString " && " . showsPrec 2 b2
    showsPrec p (BOr b1 b2)  = showParen (p > 1) $ showsPrec 1 b1 . showString " || " . showsPrec 1 b2

type Env = (PEnv, IEnv)
type PEnv = M.Map TId PType
type IEnv = M.Map TId IType

type HashTable k v = H.BasicHashTable k v

data MeasureKey = CheckSat | CalcCondition | Total
    deriving (Eq, Ord, Show, Generic)

instance Hashable MeasureKey 

data Context = Context { ctxFlowTbl :: HashTable UniqueKey (S.Set ([IType], BFormula))
                       , ctxTypeMap :: TypeMap
                       , ctxFlowMap :: FlowMap
                       , ctxRtnTypeTbl :: HashTable UniqueKey (PType, [HFormula]) 
                       , ctxArgTypeTbl  :: HashTable UniqueKey ([PType], [HFormula]) 
                       , ctxHFormulaTbl :: HFormulaTbl
                       , ctxHFormulaSize :: IORef Int
                       , ctxCheckSatCache :: HashTable (Int, Int) Bool
                       , ctxUpdated :: IORef Bool
                       , ctxSMTCount :: IORef Int
                       , ctxSMTCountHit :: IORef Int
                       , ctxTimer :: HashTable MeasureKey NominalDiffTime
                       , ctxSMTSolver :: Z3.Solver
                       , ctxSMTContext :: Z3.Context }
newtype R a = R { unR :: ReaderT Context IO a }
    deriving (Monad, Applicative, Functor, MonadFix, MonadIO)


instance MonadReader Context R where
    ask = R ask
    local f a = R (local f $ unR a)

instance Z3.MonadZ3 R where
    getSolver = ctxSMTSolver <$> ask
    getContext = ctxSMTContext <$> ask
    

measureTime :: MeasureKey -> R a -> R a
measureTime key action = do
    t_start <- liftIO getCurrentTime
    res <- action
    t_end <- liftIO getCurrentTime
    let dt = diffUTCTime t_end t_start
    ask >>= \ctx -> liftIO $ do
        r <- H.lookup (ctxTimer ctx) key
        case r of
            Nothing -> H.insert (ctxTimer ctx) key $! dt
            Just t  -> H.insert (ctxTimer ctx) key $! dt + t
    return res

calcContextV :: M.Map TId PType -> Value -> PType -> R ()
calcContextV env (Value l arg _ key) pty = 
    case (l, arg) of
        (SLiteral, _) -> return ()
        (SVar, _) -> return ()
        (SUnary, _) -> return ()
        (SBinary, _) -> return ()
        (SPair, (v1, v2)) -> do
            let PPair _ pty1 pty2 = pty
            calcContextV env v1 pty1
            calcContextV env v2 pty2
        (SLambda, (xs, e)) -> do
            let PFun _ (ys, ty_ys, ps) tau = pty
                subst = M.fromList (zip ys xs)
                ty_ys' = map (substPType subst) ty_ys
                ps'    = map (substFormula subst) ps
                tau'   = substTermType subst tau
                env'   = foldr (uncurry M.insert) env $ zip xs ty_ys'
            ctx <- ask
            ps' <- mapM toHFormula ps'
            liftIO $ H.insert (ctxArgTypeTbl ctx) key (ty_ys', ps')
            calcContextE env' e tau'

calcContextE :: M.Map TId PType -> Exp -> TermType -> R ()
calcContextE env (Exp l arg sty key) tau =
    let valueCase :: Value -> R () 
        valueCase v = do
            let (r, rty, ps) = tau
            let subst = M.singleton r v
                rty' = substVPType subst rty
                ps' = map (substVFormula subst) ps
            tbl <- ctxRtnTypeTbl <$> ask 
            ps' <- mapM toHFormula ps'
            calcContextV env v rty'
            liftIO (H.insert tbl key (rty', ps'))
    in case (l, arg) of
        (SLiteral, _) -> valueCase (Value l arg sty key)
        (SVar, _)     -> valueCase (Value l arg sty key)
        (SUnary, _)   -> valueCase (Value l arg sty key)
        (SBinary, _)  -> valueCase (Value l arg sty key)
        (SPair, _)    -> valueCase (Value l arg sty key)
        (SLambda, _)  -> valueCase (Value l arg sty key)
        (SLet, (x, LExp l1 arg1 sty1 key1, e2)) -> 
            let atomCase av = do
                    let ty_x = typeOfAtom env av
                    let env' = M.insert x ty_x env
                    ask >>= \ctx -> liftIO $ H.insert (ctxRtnTypeTbl ctx) key (ty_x, [])
                    calcContextE env' e2 tau
                exprCase e1 = do
                    ctx <- ask
                    let Right tau1@(y, ty_y, ps) = ctxTypeMap ctx M.! key1
                        subst = M.singleton y x
                        ps'   = map (substFormula subst) ps
                        ty_x  = substPType subst ty_y
                        env'  = M.insert x ty_x env
                    ps' <- mapM toHFormula ps'
                    liftIO $ H.insert (ctxRtnTypeTbl ctx) key (ty_x, ps')
                    calcContextE env e1 tau1
                    calcContextE env' e2 tau
            in case (l1, arg1) of
                (SLiteral, _) -> atomCase (Atom l1 arg1 sty1)
                (SVar, _)     -> atomCase (Atom l1 arg1 sty1)
                (SBinary, _)  -> atomCase (Atom l1 arg1 sty1)
                (SUnary, _)   -> atomCase (Atom l1 arg1 sty1)
                (SApp, (f, vs)) -> do
                    let PFun _ argTy retTy = env M.! f
                        (ys, ptys, ps) = argTy
                        subst = M.fromList $ zip ys vs
                        ptys' = map (substVPType subst) ptys
                        ps'   = map (substVFormula subst) ps
                        (r, rty, qs) = retTy
                        subst' = M.insert r (cast (PNormal.mkVar x)) subst
                        qs' = map (substVFormula subst') qs
                        rty' = substVPType subst' rty
                        env' = M.insert x rty' env
                    ctx <- ask
                    ps' <- mapM toHFormula ps'
                    qs' <- mapM toHFormula qs'
                    liftIO (H.insert (ctxArgTypeTbl ctx) key (ptys', ps'))
                    liftIO (H.insert (ctxRtnTypeTbl ctx) key (rty', qs'))
                    zipWithM_ (\v ty_v -> calcContextV env v ty_v) vs ptys'
                    calcContextE env' e2 tau
                (SPair, _)   -> exprCase (Exp l1 arg1 sty1 key1)
                (SLambda, _) -> exprCase (Exp l1 arg1 sty1 key1)
                (SFail, _)   -> exprCase (Exp l1 arg1 sty1 key1)
                (SOmega, _)  -> exprCase (Exp l1 arg1 sty1 key1)
                (SRand, _)   -> do
                    ask >>= \ctx -> liftIO (H.insert (ctxRtnTypeTbl ctx) key (PInt, []))
                    calcContextE (M.insert x PInt env) e2 tau
                (SBranch, _) -> exprCase (Exp l1 arg1 sty1 key1)
        (SAssume, (_, e)) -> calcContextE env e tau
        (SBranch, (e1, e2)) -> calcContextE env e1 tau >> calcContextE env e2 tau
        (SFail, _) -> return ()
        (SOmega, _) -> return ()

pprintContext :: Program -> R Doc
pprintContext prog = do
    d_fs <- forM (functions prog) $ \(f,key,xs,e) -> do
        Just (ty_xs, ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxArgTypeTbl ctx) key
        let d_args = vcat $ zipWith (\x ty_x -> parens $ pPrint (name x) 
                                            <+> colon 
                                            <+> pPrint ty_x) xs ty_xs
            d_ps = hsep $ punctuate comma $ map pPrint ps
        d_body <- pprintE e
        return $ text "let" <+> pPrint (name f) <+> (case ps of [] -> d_args <+> text "="
                                                                _  -> d_args $+$ text "|" <+> d_ps <+> text "=")
                            $+$ (nest 4 d_body <> text ";;")
    d_main <- pprintE (mainTerm prog)
    return $ vcat d_fs $+$ d_main 
    where 
    pprintE :: Exp -> R Doc
    pprintE (Exp l arg sty key) = 
        let valueCase :: Value -> R Doc
            valueCase v = do
                d_v <- pprintV 0 v
                Just (ty_r, ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
                return $ comment (ty_r, ps) $+$ d_v
        in case (l, arg) of
            (SLiteral, _) -> valueCase (Value l arg sty key)
            (SVar, _)     -> valueCase (Value l arg sty key)
            (SUnary, _)   -> valueCase (Value l arg sty key)
            (SBinary, _)  -> valueCase (Value l arg sty key)
            (SPair, _)    -> valueCase (Value l arg sty key)
            (SLambda, _)  -> valueCase (Value l arg sty key)
            (SLet, (x, e1@(LExp l1 arg1 sty1 key1), e2)) ->
                let exprCase d_e1 = do
                        Just (ty_x, ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
                        d_e2 <- pprintE e2
                        let d_ps = hsep $ punctuate comma $ map pPrint ps
                        return $ 
                            text "let" <+> pPrint (name x)
                                       <+> (colon <+> pPrint ty_x <+> (case ps of [] -> empty
                                                                                  _  -> text "|" <+> d_ps) $+$
                                            text "=" <+> d_e1) 
                                       <+> text "in" 
                                       $+$ d_e2
                in case l1 of
                    SLiteral -> exprCase (pPrint e1)
                    SVar     -> exprCase (pPrint e1)
                    SUnary   -> exprCase (pPrint e1)
                    SBinary  -> exprCase (pPrint e1)
                    SPair    -> pprintE (Exp l1 arg1 sty1 key1) >>= exprCase
                    SLambda  -> pprintE (Exp l1 arg1 sty1 key1) >>= exprCase
                    SBranch  -> pprintE (Exp l1 arg1 sty1 key1) >>= exprCase
                    SFail    -> pprintE (Exp l1 arg1 sty1 key1) >>= exprCase
                    SOmega   -> pprintE (Exp l1 arg1 sty1 key1) >>= exprCase
                    SApp     -> do
                        let (f, vs) = arg1
                        Just (ty_vs, ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxArgTypeTbl ctx) key
                        vs' <- mapM (pprintV 0) vs
                        let d_e1 = pPrint (name f) <+> (case ps of [] -> d_vs
                                                                   _  -> d_vs $+$ text "|" <+> d_ps)
                            d_vs = vcat $ zipWith (\d_v ty_v -> parens $ d_v
                                                                     <+> text ":" 
                                                                     <+> pPrint ty_v) vs' ty_vs
                            d_ps = hsep $ punctuate comma $ map pPrint ps
                        exprCase d_e1 
                    SRand    -> exprCase (pPrint e1)
            (SAssume, (cond, e)) -> do
                d_e <- pprintE e
                return $ text "assume" <+> pPrintPrec prettyNormal 9 cond <> text ";" $+$ d_e
            (SBranch, (e1, e2)) -> do
                d_e1 <- pprintE e1
                d_e2 <- pprintE e2
                return $ parens d_e1 <+> text "<>" $+$ parens d_e2
            (SFail, _) -> return $ text "Fail"
            (SOmega, _) -> return $ text "Omega"
    pprintV :: Rational -> Value -> R Doc
    pprintV prec v@(Value l arg _ key) =
        case (l, arg) of
            (SLiteral, _) -> return $ pPrintPrec prettyNormal prec v
            (SVar, _) -> return $  pPrintPrec prettyNormal prec v
            (SBinary, _) -> return $ pPrintPrec prettyNormal prec v
            (SUnary, _) -> return $ pPrintPrec prettyNormal prec v
            (SPair, (v1, v2)) -> do
                d_v1 <- pprintV 0 v1
                d_v2 <- pprintV 0 v2
                return $ parens $ d_v1 <> comma <+> d_v2
            (SLambda, (xs, e)) -> do
                Just (ty_xs, ps) <- do
                    m <- ask >>= \ctx -> liftIO $ H.lookup (ctxArgTypeTbl ctx) key
                    case m of Just v -> return (Just v)
                              Nothing -> error (render (pPrint v))
                d_e <- pprintE e
                let d_args = vcat $ zipWith (\x ty_x -> parens $ pPrint (name x) 
                                                    <+> colon 
                                                    <+> pPrint ty_x) xs ty_xs
                    d_ps = hsep $ punctuate comma $ map pPrint ps
                return $ maybeParens (prec > 0) $ 
                    text "fun" <+> (case ps of 
                                        [] -> d_args <+> text "->"
                                        _  -> d_args $+$ text "|" <+> d_ps <+> text "->") $+$
                        nest 4 d_e

saturate :: TypeMap -> Program -> IO (Bool,[ITermType])
saturate typeMap prog = do
    (smtSolver, smtContext) <- Z3Base.withConfig $ \cfg -> do
        Z3.setOpts cfg Z3.stdOpts
        ctx <- Z3Base.mkContext cfg
        solver <- Z3Base.mkSolver ctx
        return (solver, ctx)
    ctx <- Context <$> H.new
                   <*> pure typeMap
                   <*> flowAnalysis prog
                   <*> H.new
                   <*> H.new
                   <*> H.new
                   <*> newIORef 0
                   <*> H.new
                   <*> newIORef False
                   <*> newIORef 0
                   <*> newIORef 0
                   <*> H.new
                   <*> return smtSolver
                   <*> return smtContext
    let env0 = ( M.fromList [ (f, pty) | (f, key, _, _) <- functions prog, let Left pty = typeMap M.! key ]
               , M.fromList [ (f, IFun []) | (f, _, _, _) <- functions prog] )
        go :: IEnv -> R [ITermType]
        go env = do
            resetUpdate
            env' <- fmap M.fromList $ forM (functions prog) $ \(f, key, xs, e) -> do
                let IFun as' = env M.! f
                IFun as <- mkLiteral (CBool True) >>= \b -> calcTypeFunDef env b (key,xs,e)
                let as'' = merge as as'
                when (as' /= as'') update
                return (f, IFun as'')
            ts <- mkLiteral (CBool True) >>= \b -> calcTypeTerm env' b (mainTerm prog) 
            b <- ask >>= liftIO . readIORef . ctxUpdated
            if b 
              then go env'
              else return ts


    ts <- flip runReaderT ctx $ unR $ measureTime Total $ do
        -- initialize context
        forM_ (functions prog) $ \(f, key, xs, e) -> 
            let pty = fst env0 M.! f in
            calcContextV (fst env0) (mkLambda xs e key) pty
        calcContextE (fst env0) (mainTerm prog) (TId TInt (reserved "main"), PInt, [])

        liftIO $ putStrLn "Abstraction Annotated Program"
        pprintContext prog >>= liftIO . print
        go (snd env0)
        
    let !b = IFail `elem` ts
    readIORef (ctxSMTCount ctx) >>= printf "[Fusion] Number of SMT Call = %d\n"
    readIORef (ctxSMTCountHit ctx) >>= printf "[Fusion] Number of SMT Call Hit = %d\n"
    H.mapM_ (\(k,duration) -> do
        printf "[Fusion] Timer %s: %s\n" (show k) (show duration)) (ctxTimer ctx)
    return (b, ts)

getFlow :: UniqueKey -> R [([IType], BFormula)]
getFlow i = do
    tbl <- ctxFlowTbl <$> ask
    liftIO (H.lookup tbl i) >>= \case
        Just v -> return (S.toList v)
        Nothing -> return []

update :: R ()
update = do
    flag <- ctxUpdated <$> ask
    liftIO $ writeIORef flag True

resetUpdate :: R ()
resetUpdate = do
    flag <- ctxUpdated <$> ask
    liftIO $ writeIORef flag False

addFlow :: UniqueKey -> ([IType], BFormula) -> R ()
addFlow i v = do
    tbl <- ctxFlowTbl <$> ask
    liftIO (H.lookup tbl i) >>= \case
        Just vs | S.member v vs -> return ()
                | otherwise -> liftIO (H.insert tbl i $! (S.insert v vs)) >> update
        Nothing -> liftIO (H.insert tbl i $! (S.singleton v)) >> update

calcTypeFunDef :: IEnv -> HFormula -> (UniqueKey, [TId], Exp) -> R IType
calcTypeFunDef env fml (ident,xs,e) = do
    Just (_, ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxArgTypeTbl ctx) ident
    fs <- getFlow ident
    ity <- fmap (IFun . concat) $ forM fs $ \(thetas, phi) -> do
        let env' = foldr (uncurry M.insert) env (zip xs thetas)
        cond <- fromBFormula ps phi
        fml' <- mkBin SAnd fml cond
        b <- checkSat fml cond
        if b 
          then map ((,,) thetas phi) <$> calcTypeTerm env' fml' e
          else return []
          {-
    liftIO $ print $ text "calcTypeFunDef" $+$ 
            braces (
                --text "env:" <+> pprintEnv env $+$
                text "assumption:" <+> pPrint fml $+$
                text "ident:" <+> pPrint ident  $+$
                text "args:" <+> (brackets $ hsep $ punctuate comma (map pPrint xs)) $+$
                text "result:" <+> pPrint ity
            )
            -}
    return ity

calcTypeValue :: IEnv -> HFormula -> Value -> R IType
calcTypeValue env fml (Value l arg sty key) = 
    let atomCase :: Atom -> R IType
        atomCase v = do
            let ity = calcTypeAtom env v
            return ity
    in case (l,arg) of
        (SLiteral, _) -> atomCase (Atom l arg sty)
        (SVar, _)     -> atomCase (Atom l arg sty)
        (SBinary, _)  -> atomCase (Atom l arg sty)
        (SUnary, _)   -> atomCase (Atom l arg sty)
        (SLambda, (xs,e)) -> calcTypeFunDef env fml (key,xs, e)
        (SPair, (v1, v2)) -> do
            i1 <- calcTypeValue env fml v1
            i2 <- calcTypeValue env fml v2
            return (IPair i1 i2)

calcTypeAtom :: IEnv -> Atom -> IType
calcTypeAtom env (Atom l arg _)   = case (l, arg) of
    (SLiteral, CInt _)  -> IInt
    (SLiteral, CBool _) -> IInt
    (SVar, x) -> env M.! x
    (SBinary, BinArg op _ _) -> case op of
        SAdd -> IInt
        SSub -> IInt
        SEq  -> IBool
        SLt  -> IBool
        SLte -> IBool
        SAnd -> IBool
        SOr  -> IBool
    (SUnary, UniArg op v) -> case op of
        SFst -> (\(IPair i1 _) -> i1) $ calcTypeAtom env v
        SSnd -> (\(IPair _ i2) -> i2) $ calcTypeAtom env v
        SNeg -> IInt
        SNot -> IBool

-- Function: calcCondition fml ps 
-- assumption: fml is a satisfiable formula
-- assertion: phi |- fromBFormula ps ret
calcCondition :: HFormula -> [HFormula] -> R BFormula
calcCondition _fml _ps = measureTime CalcCondition $ do
    phi <- go 1 _fml _ps
    {-
    liftIO $ print $ text "calcCondtion" $+$ 
            braces (
                text "assumption:" <+> pPrint _fml $+$
                text "predicates:" <+> (brackets $ hsep $ punctuate comma (map pPrint _ps)) $+$
                text "result:"     <+> text (show phi)
            )
            -}
    return phi
    where
    go _ _ [] = return $ BConst True
    go i fml (p:ps) = do
        np <- mkUni SNot p
        b1 <- checkSat fml p
        b2 <- checkSat fml np
        v1 <- if b1 then mkBin SAnd fml p >>= \fml' -> go (i + 1) fml' ps 
                    else return $ BConst False
        v2 <- if b2 then mkBin SAnd fml np >>= \fml' -> go (i + 1) fml' ps 
                    else return $ BConst False
        if v1 == v2 then
            return v1
        else 
            return $ mkBOr (mkBAnd (BVar i) v1) (mkBAnd (BVar (-i)) v2)


fromBFormula :: [HFormula] -> BFormula -> R HFormula
fromBFormula ps (BVar i) 
    | i < 0     = mkUni SNot (ps !! ((-i) - 1))
    | otherwise = return $ ps !! (i - 1)
fromBFormula _  (BConst b)   = mkLiteral (CBool b)
fromBFormula ps (BOr p1 p2)  = do
    v1 <- fromBFormula ps p1
    v2 <- fromBFormula ps p2
    mkBin SOr  v1 v2
fromBFormula ps (BAnd p1 p2) = do
    v1 <- fromBFormula ps p1
    v2 <- fromBFormula ps p2
    mkBin SAnd v1 v2

checkSat :: HFormula -> HFormula -> R Bool
checkSat p1 p2 = measureTime CheckSat $ do
    ctx <- ask
    let key = (getIdent p1, getIdent p2)
    res <- liftIO $ H.lookup (ctxCheckSatCache ctx) key
    -- liftIO $ print $ text "checkSat" <+> pPrint key <+> pPrint p1 <+> text "|-" <+> pPrint p2
    case res of
        Just v -> do
            liftIO $ modifyIORef' (ctxSMTCountHit ctx) succ 
            return v
        Nothing -> do 
            liftIO $ modifyIORef' (ctxSMTCount ctx) succ 

            v <- (Z3.local :: R Bool -> R Bool) $ do
                SMT.ASTValue cond <- getIValue <$> mkBin SAnd p1 p2  
                Z3.assert cond
                res <- Z3.check
                case res of
                    Z3.Sat -> return True
                    Z3.Unsat -> return False
                    Z3.Undef -> liftIO $ putStrLn "Undef" >> return True
            liftIO $ H.insert (ctxCheckSatCache ctx) key v
            return v

calcTypeTerm :: IEnv -> HFormula -> Exp -> R [ITermType]
calcTypeTerm env fml (Exp l arg sty key) = 
    let valueCase :: Value -> R [ITermType]
        valueCase v = do
            Just (_, ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
            theta <- calcTypeValue env fml v
            phi   <- calcCondition fml ps
            return [ITerm theta phi]
    in case (l, arg) of
        (SLiteral, _) -> valueCase (Value l arg sty key)
        (SVar, _)     -> valueCase (Value l arg sty key)
        (SUnary, _)   -> valueCase (Value l arg sty key)
        (SBinary, _)  -> valueCase (Value l arg sty key)
        (SPair, _)    -> valueCase (Value l arg sty key)
        (SLambda, _)  -> valueCase (Value l arg sty key)
        (SLet, (x,LExp l1 arg1 sty1 key1,e2)) ->
            let atomCase av = do
                    vx <- mkVar x
                    fml' <- toHFormula av >>= mkBin SEq vx >>= mkBin SAnd fml 
                    let ity_av = calcTypeAtom env av
                        env' = M.insert x ity_av env
                    calcTypeTerm env' fml' e2
                exprCase e1 = do
                    iotas <- calcTypeTerm env fml e1
                    fmap concatMerge $ forM iotas $ \iota_y -> do
                        case iota_y of
                            IFail -> return [IFail]
                            ITerm theta phi -> do
                                Just (_, ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
                                let env' = M.insert x theta env
                                cond <- fromBFormula ps phi
                                fml' <- mkBin SAnd fml cond
                                b <- checkSat fml cond
                                if b
                                  then calcTypeTerm env' fml' e2
                                  else return []
            in case (l1, arg1) of
                (SLiteral, _) -> atomCase (Atom l1 arg1 sty1)
                (SVar, _)     -> atomCase (Atom l1 arg1 sty1)
                (SBinary, _)  -> atomCase (Atom l1 arg1 sty1)
                (SUnary, _)   -> atomCase (Atom l1 arg1 sty1)
                (SApp, (f,vs)) -> do
                    let IFun assoc = env M.! f
                    Just (_, ps) <- ask >>= \ctx -> liftIO (H.lookup (ctxArgTypeTbl ctx) key)
                    phi <- calcCondition fml ps
                    thetas <- mapM (calcTypeValue env fml) vs 
                    flowMap <- ctxFlowMap <$> ask
                    forM_ (flowMap M.! f) $ \ident -> addFlow ident (thetas,phi)

                    fmap concatMerge $ forM assoc $ \(thetas', phi', iota) ->
                        if thetas' == thetas && phi' == phi 
                          then case iota of
                                IFail -> return [IFail]
                                ITerm rtheta rphi -> do
                                    Just (_, qs) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
                                    let env' = M.insert x rtheta env
                                    cond <- fromBFormula qs rphi
                                    fml' <- mkBin SAnd fml cond
                                    b <- checkSat fml cond
                                    if b 
                                      then calcTypeTerm env' fml' e2
                                      else return []
                          else return []
                (SPair, _)   -> exprCase (Exp l1 arg1 sty1 key1)
                (SLambda, _) -> exprCase (Exp l1 arg1 sty1 key1)
                (SBranch, _) -> exprCase (Exp l1 arg1 sty1 key1)
                (SFail, _)   -> exprCase (Exp l1 arg1 sty1 key1)
                (SOmega, _)  -> exprCase (Exp l1 arg1 sty1 key1)
                (SRand, _)   -> calcTypeTerm (M.insert x IInt env) fml e2
        (SAssume, (cond,e)) -> do
            hcond <- toHFormula cond
            b <- checkSat fml hcond
            if b 
              then mkBin SAnd fml hcond >>= \fml' -> calcTypeTerm env fml' e
              else return []
        (SFail,_ ) -> return [IFail]
        (SOmega,_ ) -> return []
        (SBranch, (e1,e2)) -> do
            ts1 <- calcTypeTerm env fml e1
            ts2 <- calcTypeTerm env fml e2
            return $ merge ts1 ts2

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys) = case compare x y of
    EQ -> x : merge xs ys
    LT -> x : merge xs (y:ys)
    GT -> y : merge (x:xs) ys

concatMerge :: Ord a => [[a]] -> [a]
concatMerge [] = []
concatMerge [x] = x
concatMerge (x:y:xs) = concatMerge (merge x y:xs)

