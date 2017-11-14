{-# LANGUAGE FlexibleContexts, BangPatterns, TypeFamilies, DataKinds, KindSignatures, GADTs, MultiParamTypeClasses #-}
module Language.DMoCHi.ML.Syntax.PNormal( Program(..)
                                        , Exp(..), Value(..), Atom(..), LExp(..), Normalized
                                        , DExp
                                        , mkBin, mkUni, mkLiteral, mkVar, mkPair
                                        , mkLambda, mkApp, mkLet, mkLetRec
                                        , mkAssume, mkBranch, mkBranchL
                                        , mkFail, mkOmega, mkRand
                                        , mkFailL, mkOmegaL
                                        , Castable(..)
                                        , normalize, atomOfValue, valueOfLExp, valueOfExp
                                        , freeVariables
                                        , isValue, isAtom
                                        , module Language.DMoCHi.ML.Syntax.Type
                                        , module Language.DMoCHi.ML.Syntax.Base )where
-- import Control.Monad
import Language.DMoCHi.Common.Id
import Language.DMoCHi.Common.Util
-- import qualified Data.Map as M
import qualified Data.Set as S
import GHC.Exts(Constraint)
-- import Data.Char
import Language.DMoCHi.ML.Syntax.Type
import Language.DMoCHi.ML.Syntax.Base
import qualified Language.DMoCHi.ML.Syntax.Typed as Typed
import Control.Monad.Cont
import Control.Monad.Trans.Cont(shiftT,resetT,evalContT)
import Text.PrettyPrint.HughesPJClass


data Program = Program { functions :: [(TId, UniqueKey, [TId], Exp)]
                       , mainTerm  :: Exp }

data Exp where
    Exp :: (Normalized l Exp arg, Supported l (Labels Exp)) => 
            SLabel l -> arg -> Type -> UniqueKey -> Exp

type DExp l = forall arg. Normalized l Exp arg => (SLabel l, arg, Type, UniqueKey)

data Value where
    Value :: (Normalized l Value arg, Supported l (Labels Value)) => 
            SLabel l -> arg -> Type -> UniqueKey -> Value

data Atom where
    Atom :: (Normalized l Atom arg, Supported l (Labels Atom)) => 
            SLabel l -> arg -> Type -> Atom

data LExp where
    LExp :: (Normalized l LExp arg, Supported l (Labels LExp)) => 
                SLabel l -> arg -> Type -> UniqueKey -> LExp

instance HasUniqueKey Exp where
    getUniqueKey (Exp _ _ _ key) = key
instance HasUniqueKey Value where
    getUniqueKey (Value _ _ _ key) = key


instance Eq Atom where
    (==) (Atom l1 arg1 _) (Atom l2 arg2 _) =
        case (l1,l2) of
            (SLiteral, SLiteral) -> arg1 == arg2
            (SLiteral, _) -> False
            (SVar, SVar) -> arg1 == arg2
            (SVar, _) -> False
            (SBinary, SBinary) -> arg1 == arg2
            (SBinary, _) -> False
            (SUnary, SUnary) -> arg1 == arg2
            (SUnary, _) -> False

type family Normalized (l :: Label) (e :: *) (arg :: *) :: Constraint where
    Normalized 'Literal e arg = arg ~ Lit
    Normalized 'Var     e arg = arg ~ Ident e
    Normalized 'Unary   e arg = arg ~ UniArg Atom
    Normalized 'Binary  e arg = arg ~ BinArg Atom
    Normalized 'Pair    e arg = arg ~ (Value, Value)
    Normalized 'Lambda  e arg = arg ~ ([Ident e], Exp)
    Normalized 'App     e arg = arg ~ (Ident e, [Value])
    Normalized 'Let     e arg = arg ~ (Ident e, LExp, Exp)
    Normalized 'LetRec  e arg = arg ~ ([(Ident e, Value)], Exp)
    Normalized 'Assume  e arg = arg ~ (Atom, Exp)
    Normalized 'Branch  e arg = arg ~ (Exp, Exp)
    Normalized 'Fail    e arg = arg ~ ()
    Normalized 'Omega   e arg = arg ~ ()
    Normalized 'Rand    e arg = arg ~ ()
    Normalized l        e arg = 'True ~ 'False

type instance Labels Exp = '[ 'Literal, 'Var, 'Binary, 'Unary, 'Pair, 'Lambda
                            , 'Let, 'LetRec, 'Assume, 'Branch, 'Fail, 'Omega ]
type instance Labels LExp = '[ 'Literal, 'Var, 'Binary, 'Unary, 'Pair, 'Lambda
                             , 'App, 'Branch, 'Rand, 'Fail, 'Omega ]
type instance Labels Value = '[ 'Literal, 'Var, 'Binary, 'Unary, 'Pair, 'Lambda ]
type instance Labels Atom  = '[ 'Literal, 'Var, 'Binary, 'Unary ]
type instance BinOps Atom  = '[ 'Add, 'Sub, 'Div, 'Mul, 'Eq, 'Lt, 'Lte, 'And, 'Or ]
type instance UniOps Atom  = '[ 'Fst, 'Snd, 'Not, 'Neg ]
type instance Ident  Exp = TId
type instance Ident  LExp = TId
type instance Ident  Value = TId
type instance Ident  Atom = TId

mkBin :: SBinOp op -> Atom -> Atom -> Atom
mkBin op v1 v2 = case op of
    SAdd -> Atom SBinary (BinArg SAdd v1 v2) TInt
    SSub -> Atom SBinary (BinArg SSub v1 v2) TInt
    SDiv -> Atom SBinary (BinArg SDiv v1 v2) TInt
    SMul -> Atom SBinary (BinArg SMul v1 v2) TInt
    SEq  -> Atom SBinary (BinArg SEq v1 v2) TBool
    SNEq  -> Atom SUnary (UniArg SNot (Atom SBinary (BinArg SEq v1 v2) TBool)) TBool
    SLt  -> Atom SBinary (BinArg SLt v1 v2) TBool
    SLte -> Atom SBinary (BinArg SLte v1 v2) TBool
    SGt  -> Atom SBinary (BinArg SLt v2 v1) TBool
    SGte -> Atom SBinary (BinArg SLte v2 v1) TBool
    SAnd -> Atom SBinary (BinArg SAnd v1 v2) TBool
    SOr  -> Atom SBinary (BinArg SOr  v1 v2) TBool

mkUni :: SUniOp op -> Atom -> Atom
mkUni op v1@(Atom _ _ sty) = case op of
    SNeg -> Atom SUnary (UniArg SNeg v1) TInt
    SNot -> Atom SUnary (UniArg SNot v1) TBool
    SFst -> case sty of
        TPair sty1 _ -> Atom SUnary (UniArg SFst v1) sty1
        _ -> error "mkUni: Fst"
    SSnd -> case sty of
        TPair _ sty2 -> Atom SUnary (UniArg SSnd v1) sty2
        _ -> error "mkUni: Snd"

mkLiteral :: Lit -> Atom
mkLiteral l@(CInt _) = Atom SLiteral l TInt
mkLiteral l@(CBool _) = Atom SLiteral l TBool
mkLiteral CUnit = error "mkLiteral: unexpected unit literal"

mkVar :: TId -> Atom
mkVar x@(TId sty _) = Atom SVar x sty

mkPair :: Value -> Value -> UniqueKey -> Value
mkPair v1@(Value _ _ sty1 _) v2@(Value _ _ sty2 _) key = Value SPair (v1, v2) (TPair sty1 sty2) key

mkLambda :: [TId] -> Exp -> UniqueKey -> Value
mkLambda xs e@(Exp _ _ sty _) key = 
    Value SLambda (xs, e) (TFun stys sty) key
    where !stys = map getType xs

mkApp :: TId -> [Value] -> UniqueKey -> LExp
mkApp f@(TId (TFun _ r_ty) _) vs key = LExp SApp (f, vs) r_ty key
mkApp _ _ _ = error "mkApp"

mkLet :: TId -> LExp -> Exp -> UniqueKey -> Exp
mkLet f e1 e2@(Exp _ _ sty _) key = Exp SLet (f, e1, e2) sty key

mkLetRec :: [(TId, Value)] -> Exp -> UniqueKey -> Exp
mkLetRec fs e2@(Exp _ _ sty _) key = Exp SLetRec (fs, e2) sty key


mkAssume :: Atom -> Exp -> UniqueKey -> Exp
mkAssume v e@(Exp _ _ sty _) key = Exp SAssume (v, e) sty key

mkBranch :: Exp -> Exp -> UniqueKey -> Exp
mkBranch e1@(Exp _ _ sty _) e2 key = Exp SBranch (e1, e2) sty key

mkBranchL :: Exp -> Exp -> UniqueKey -> LExp
mkBranchL e1@(Exp _ _ sty _) e2 key = LExp SBranch (e1, e2) sty key

mkFail, mkOmega :: Type -> UniqueKey -> Exp
mkFail sty key = Exp SFail () sty key
mkOmega sty key = Exp SOmega () sty key

mkFailL, mkOmegaL :: Type -> UniqueKey -> LExp
mkFailL sty key = LExp SFail () sty key
mkOmegaL sty key = LExp SOmega () sty key

mkRand :: UniqueKey -> LExp
mkRand key = LExp SRand () TInt key

instance HasType Exp where
    getType (Exp _ _ sty _) = sty
instance HasType Value where
    getType (Value _ _ sty _) = sty
instance HasType Atom where
    getType (Atom _ _ sty) = sty
instance HasType LExp where
    getType (LExp _ _ sty _) = sty

class Castable from to where
    type Attr from to
    castWith :: Attr from to -> from -> to
    castWith _ from = cast from
    cast :: from -> to

instance Castable Atom Value where
    type Attr Atom Value = UniqueKey
    cast = castWith reservedKey
    castWith key (Atom l arg sty) = case l of
        SLiteral -> Value l arg sty key
        SVar -> Value l arg sty key
        SBinary -> Value l arg sty key
        SUnary -> Value l arg sty key

instance Castable Value LExp where
    type Attr Value LExp = ()
    cast (Value l arg sty key) = case l of
        SLiteral -> LExp l arg sty key
        SVar     -> LExp l arg sty key
        SBinary  -> LExp l arg sty key
        SUnary   -> LExp l arg sty key
        SPair    -> LExp l arg sty key
        SLambda  -> LExp l arg sty key

instance Castable Value Exp where
    type Attr Value Exp = ()
    cast (Value l arg sty key) = case l of
        SLiteral -> Exp l arg sty key
        SVar -> Exp l arg sty key
        SBinary -> Exp l arg sty key
        SUnary -> Exp l arg sty key
        SLambda -> Exp l arg sty key
        SPair -> Exp l arg sty key

instance Castable Atom Exp where
    type Attr Atom Exp = UniqueKey
    castWith key = cast . (castWith key :: Atom -> Value)
    cast = castWith reservedKey

instance Castable Atom LExp where
    type Attr Atom LExp = UniqueKey
    castWith key = cast . (castWith key :: Atom -> Value)
    cast = castWith reservedKey

instance Castable Atom Typed.Exp where
    type Attr Atom Typed.Exp = UniqueKey
    castWith key = cast . (castWith key :: Atom -> Exp)
    cast = castWith reservedKey

instance Castable Value Typed.Exp where
    type Attr Value Typed.Exp = ()
    cast = cast . (cast :: Value -> Exp)

instance Castable LExp Typed.Exp where
    type Attr LExp Typed.Exp = ()
    cast (LExp l arg sty key) = case (l, arg) of
        (SLiteral,_) -> Typed.Exp l arg sty key
        (SVar, _)    -> Typed.Exp l arg sty key
        (SBinary, BinArg op a b) -> 
            let a', b' :: Typed.Exp
                a' = cast a
                b' = cast b
                arg' = case op of
                    SAdd -> BinArg op a' b'
                    SSub -> BinArg op a' b'
                    SEq  -> BinArg op a' b'
                    SDiv -> BinArg op a' b'
                    SMul -> BinArg op a' b'
                    SLt  -> BinArg op a' b'
                    SLte -> BinArg op a' b'
                    SAnd -> BinArg op a' b'
                    SOr  -> BinArg op a' b'
            in Typed.Exp l arg' sty key
        (SUnary, UniArg op a) ->
            let a' :: Typed.Exp
                a' = cast a
                arg' = case op of
                    SFst -> UniArg op a'
                    SSnd -> UniArg op a'
                    SNeg -> UniArg op a'
                    SNot -> UniArg op a'
            in Typed.Exp l arg' sty key
        (SPair, (e1, e2)) -> Typed.Exp l (cast e1, cast e2) sty key
        (SLambda, (xs, e)) -> Typed.Exp l (xs, cast e) sty key
        (SApp, (f, vs)) -> Typed.Exp l (e_f, map cast vs) sty key
            where e_f = Typed.Exp SVar f (getType f) reservedKey
        (SBranch, (e1, e2)) -> Typed.Exp l (cast e1, cast e2) sty key
        (SRand, ()) -> Typed.Exp l arg sty key
        (SFail, ()) -> Typed.Exp l arg sty key
        (SOmega, ()) -> Typed.Exp l arg sty key

instance Castable Exp Typed.Exp where
    type Attr Exp Typed.Exp = ()
    cast (Exp l arg sty key) = case (l,arg) of
        (SLiteral, _) -> Typed.Exp l arg sty key
        (SVar, _) -> Typed.Exp l arg sty key
        (SBinary, BinArg op a b) -> 
            let a', b' :: Typed.Exp 
                a' = cast a
                b' = cast b
                arg' = case op of
                    SAdd -> BinArg op a' b'
                    SSub -> BinArg op a' b'
                    SDiv -> BinArg op a' b'
                    SMul -> BinArg op a' b'
                    SEq  -> BinArg op a' b'
                    SLt  -> BinArg op a' b'
                    SLte -> BinArg op a' b'
                    SAnd -> BinArg op a' b'
                    SOr  -> BinArg op a' b'
            in Typed.Exp l arg' sty key
        (SUnary, UniArg op a) ->
            let a' :: Typed.Exp
                a' = cast a
                arg' = case op of
                    SFst -> UniArg op a'
                    SSnd -> UniArg op a'
                    SNeg -> UniArg op a'
                    SNot -> UniArg op a'
            in Typed.Exp l arg' sty key
        (SPair, (e1, e2)) -> Typed.Exp l (cast e1, cast e2) sty key
        (SLambda, (xs, e)) -> Typed.Exp l (xs, cast e) sty key
        (SLet, (x, e1, e2)) -> Typed.Exp l (x, cast e1, cast e2) sty key
        (SLetRec, (fs, e2)) -> Typed.Exp l (map (\(f,e1) -> (f, cast e1)) fs, cast e2) sty key
        (SAssume, (cond, e)) -> Typed.Exp l (cast cond, cast e) sty key
        (SBranch, (e1, e2)) -> Typed.Exp l (cast e1, cast e2) sty key
        (SFail, ()) -> Typed.Exp l arg sty key
        (SOmega, ()) -> Typed.Exp l arg sty key

instance Pretty Exp where
    pPrintPrec plevel prec e = pPrintPrec plevel prec (cast e :: Typed.Exp)
instance Pretty Value where
    pPrintPrec plevel prec e = pPrintPrec plevel prec (cast e :: Typed.Exp)
instance Pretty Atom where
    pPrintPrec plevel prec e = pPrintPrec plevel prec (cast e :: Typed.Exp)
instance Pretty LExp where
    pPrintPrec plevel prec e = pPrintPrec plevel prec (cast e :: Typed.Exp)

instance Pretty Program where
    pPrintPrec plevel _ (Program fs t) = 
        text "(* functions *)" $+$ 
        vcat (map (\(f,key,xs,e) -> 
            comment key $+$
            text "let" <+> pPrintPrec plevel 0 f <+> hsep (map (pPrintPrec prettyBind 1) xs) <+> colon <+> pPrint (getType e) <+> equals $+$
            nest 4 (pPrintPrec plevel 0 e <> text ";;")) fs) $+$
        text "(*main*)" $+$
        pPrintPrec plevel 0 t

instance Show Exp where
    show = render . pPrint 
instance Show Value where
    show = render . pPrint 
instance Show Atom where
    show = render . pPrint 
instance Show LExp where
    show = render . pPrint 

normalize :: Typed.Program -> FreshLogging Program
normalize prog = Program <$> mapM (\(f,i,xs,e) -> (,,,) f i xs <$> evalContT (convertE e)) (Typed.functions prog)
                         <*> evalContT (convertE (Typed.mainTerm prog))

convertL :: MonadId m => Typed.Exp -> ContT Exp m LExp
convertL e@(Typed.Exp l arg sty key) = 
    case (l, arg) of
        (SLiteral, _) -> castWith key <$> convertA e
        (SVar, _)     -> castWith key <$> convertA e
        (SUnary, _)   -> castWith key <$> convertA e
        (SBinary, _)  -> castWith key <$> convertA e
        (SPair, _)    -> cast <$> convertV e
        (SLambda, _)  -> cast <$> convertV e
        (SApp, (e, es)) -> do
            f <- convertVar e
            mkApp f <$> mapM convertV es <*> pure key
        (SLet, (x, e1, e2)) -> do
            e1' <- convertL e1
            ContT $ \cont -> do
                e2' <- runContT (convertL e2) cont
                return $ mkLet x e1' e2' key
        (SLetRec, (fs, e2)) -> do
            fs' <- forM fs $ \(f,e1) -> do
                e1' <- convertV e1
                return (f, e1')
            ContT $ \cont -> do
                e2' <- runContT (convertL e2) cont
                return $ mkLetRec fs' e2' key
        (SAssume, (cond, e1)) -> do
            cond' <- convertA cond
            e1' <- convertL e1
            shiftT $ \cont -> lift (mkAssume cond' <$> cont e1' <*> pure key)
        (SBranch, (e1, e2)) -> do
            e1' <- resetT $ convertE e1
            e2' <- resetT $ convertE e2
            return $ mkBranchL e1' e2' key 
        (SIf, (cond, e1, e2)) -> do
            cond' <- convertA cond
            e1' <- resetT $ convertE e1
            e2' <- resetT $ convertE e2
            let ncond' = mkUni SNot cond'
            mkBranchL <$> (mkAssume  cond' e1' <$> freshKey)
                      <*> (mkAssume ncond' e2' <$> freshKey)
                      <*> pure key
        (SFail, ()) -> pure $ mkFailL sty key
        (SOmega, ()) -> pure $ mkOmegaL sty key
        (SRand, ()) -> pure $ mkRand key
            
convertE :: MonadId m => Typed.Exp -> ContT Exp m Exp
convertE e@(Typed.Exp l arg sty key) = 
    case (l, arg) of
        (SLiteral, _) -> castWith key <$> convertA e
        (SVar, _)     -> castWith key <$> convertA e
        (SUnary, _)   -> castWith key <$> convertA e
        (SBinary, _)  -> castWith key <$> convertA e
        (SPair, _)    -> cast <$> convertV e
        (SLambda, _)  -> cast <$> convertV e
        (SApp, (e, es)) -> do
            r <- TId sty <$> identify "r"
            f <- convertVar e
            app <- mkApp f <$> mapM convertV es <*> freshKey
            key' <- freshKey
            return $ mkLet r app (castWith key' $ mkVar r) key
        (SLet, (x, e1, e2)) -> do
            e1' <- convertL e1
            e2' <- resetT $ convertE e2
            return $ mkLet x e1' e2' key
        (SLetRec, (fs, e2)) -> do
            fs' <- forM fs $ \(f,e1) -> do
                e1' <- convertV e1
                return (f, e1')
            e2' <- resetT $ convertE e2
            return $ mkLetRec fs' e2' key
        (SAssume, (e1,e2)) -> do
            e1' <- convertA e1
            e2' <- resetT $ convertE e2
            return $ mkAssume e1' e2'  key
        (SBranch, (e1,e2)) -> do
            e1' <- resetT $ convertE e1
            e2' <- resetT $ convertE e2
            return $ mkBranch e1' e2' key
        (SIf, (cond, e1, e2)) -> do
            cond' <- convertA cond
            e1' <- resetT $ convertE e1
            e2' <- resetT $ convertE e2
            let ncond' = mkUni SNot cond'
            mkBranch <$> (mkAssume  cond' e1' <$> freshKey)
                     <*> (mkAssume ncond' e2' <$> freshKey)
                     <*> pure key
        (SFail, ()) -> pure $ mkFail sty key
        (SOmega, ()) -> pure $ mkOmega sty key
        (SRand, ()) -> do
            r <- TId sty <$> identify "r"
            rand <- mkRand <$> freshKey
            key' <- freshKey
            return $ mkLet r rand (castWith key' $ mkVar r) key

convertVar :: MonadId m => Typed.Exp -> ContT Exp m TId
convertVar e@(Typed.Exp _ _ sty _) = do
    r <- TId sty <$> identify "tmp"
    e' <- convertL e
    shiftT $ \cont -> lift (mkLet r e' <$> cont r <*> freshKey)
    
convertA :: MonadId m => Typed.Exp -> ContT Exp m Atom
convertA e@(Typed.Exp l arg _ _) = 
    case (l,arg) of
        (SLiteral, lit) -> pure (mkLiteral lit)
        (SVar, x) -> pure (mkVar x)
        (SUnary,  UniArg op e1)    -> mkUni op <$> convertA e1
        (SBinary, BinArg op e1 e2) -> mkBin op <$> convertA e1 
                                               <*> convertA e2 
        _ -> mkVar <$> convertVar e
            {-
            e' <- convertL e
            r <- TId sty <$> identify "tmp"
            shiftT $ \cont -> lift (mkLet r e' <$> cont (mkVar r) <*> freshKey)
            -}

convertV :: MonadId m => Typed.Exp -> ContT Exp m Value
convertV e@(Typed.Exp l arg _ key) =
    case (l,arg) of
        (SLiteral, _) -> castWith key <$> convertA e
        (SVar, _) -> castWith key <$> convertA e
        (SUnary, _) -> castWith key <$> convertA e
        (SBinary, _) -> castWith key <$> convertA e
        (SPair, (e1, e2)) -> mkPair <$> convertV e1 <*> convertV e2 <*> pure key
        (SLambda, (x, e1)) -> mkLambda x <$> resetT (convertE e1) <*> pure key
        _ -> do
            kr <- freshKey 
            castWith kr . mkVar <$> convertVar e

{-# INLINE atomOfValue #-}
atomOfValue :: Value -> Maybe Atom
atomOfValue (Value l arg sty _) = case l of
    SLiteral -> Just $ Atom l arg sty
    SVar     -> Just $ Atom l arg sty
    SUnary   -> Just $ Atom l arg sty
    SBinary  -> Just $ Atom l arg sty
    SPair    -> Nothing
    SLambda  -> Nothing

{-# INLINE valueOfLExp #-}
valueOfLExp :: LExp -> Maybe Value
valueOfLExp (LExp l arg sty key) = case l of
    SLiteral -> Just $ Value l arg sty key
    SVar     -> Just $ Value l arg sty key
    SUnary   -> Just $ Value l arg sty key
    SBinary  -> Just $ Value l arg sty key
    SPair    -> Just $ Value l arg sty key
    SLambda  -> Just $ Value l arg sty key
    SApp     -> Nothing
    SRand    -> Nothing
    SBranch  -> Nothing
    SFail    -> Nothing
    SOmega   -> Nothing
    
{-# INLINE valueOfExp #-}
valueOfExp :: Exp -> Maybe Value
valueOfExp (Exp l arg sty key) = case l of
    SLiteral -> Just $ Value l arg sty key
    SVar     -> Just $ Value l arg sty key
    SUnary   -> Just $ Value l arg sty key
    SBinary  -> Just $ Value l arg sty key
    SPair    -> Just $ Value l arg sty key
    SLambda  -> Just $ Value l arg sty key
    SLet     -> Nothing
    SLetRec  -> Nothing
    SAssume  -> Nothing
    SBranch  -> Nothing
    SFail    -> Nothing
    SOmega   -> Nothing

isValue :: SLabel l -> Bool
isValue l = case l of
    SLiteral -> True
    SVar -> True
    SUnary -> True
    SBinary -> True
    SLambda -> True
    SPair -> True
    _ -> False

isAtom :: SLabel l -> Bool
isAtom l = case l of
    SLiteral -> True
    SVar -> True
    SUnary -> True
    SBinary -> True
    _ -> False

freeVariables :: S.Set TId -> Exp -> S.Set TId
freeVariables _scope _e = subE _scope _e S.empty
    where
    subE :: S.Set TId -> Exp -> S.Set TId -> S.Set TId
    subE scope (Exp l arg _ _) acc   = sub (Proxy :: Proxy Exp)   scope l arg acc
    subA :: S.Set TId -> Atom -> S.Set TId -> S.Set TId
    subA scope (Atom l arg _) acc  = sub (Proxy :: Proxy Atom)  scope l arg acc
    subV :: S.Set TId -> Value -> S.Set TId -> S.Set TId
    subV scope (Value l arg _ _) acc = sub (Proxy :: Proxy Value) scope l arg acc
    subL :: S.Set TId -> LExp -> S.Set TId -> S.Set TId
    subL scope (LExp l arg _ _) acc  = sub (Proxy :: Proxy LExp)  scope l arg acc
    sub :: (Normalized l e arg, Ident e ~ TId) => 
           Proxy e -> S.Set TId -> SLabel l -> arg -> S.Set TId -> S.Set TId
    sub _ _ SLiteral _ acc = acc
    sub _ scope SVar     x acc | S.member x scope = acc 
                               | otherwise = S.insert x acc
    sub _ scope SBinary  (BinArg _ v1 v2) acc = subA scope v2 (subA scope v1 acc)
    sub _ scope SUnary   (UniArg _ v1) acc = subA scope v1 acc
    sub _ scope SPair    (v1, v2) acc = subV scope v1 (subV scope v2 acc)
    sub _ scope SAssume  (cond, e) acc = subE scope e (subA scope cond acc)
    sub _ scope SLet     (x, e1, e2) acc = subE (S.insert x scope) e2 (subL scope e1 acc)
    sub _ scope SLetRec  (fs, e2) acc = 
        let scope' = foldr S.insert scope (map fst fs) in
        subE scope' e2 $ foldl (\acc e1 -> subV scope' e1 acc) acc (map snd fs)
    sub _ scope SBranch  (e1, e2) acc = subE scope e1 (subE scope e2 acc)
    sub _ _     SFail    _ acc = acc
    sub _ _     SOmega   _ acc = acc
    sub _ _     SRand    _ acc = acc
    sub _ scope SLambda  (xs, e) acc = subE (foldr S.insert scope xs) e acc
    sub p scope SApp     (f, vs) acc = foldr (subV scope) (sub p scope SVar f acc) vs

