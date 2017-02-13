{-# LANGUAGE FlexibleContexts, BangPatterns, TypeFamilies, DataKinds, KindSignatures, GADTs, MultiParamTypeClasses #-}
module Language.DMoCHi.ML.Syntax.PNormal( Program(..)
                                        , Exp(..), Value(..), Atom(..), LExp(..), Normalized
                                        , mkBin, mkUni, mkLiteral, mkVar, mkPair
                                        , mkLambda, mkApp, mkLet, mkAssume, mkBranch, mkBranchL
                                        , mkFail, mkOmega, mkRand
                                        , mkFailL, mkOmegaL
                                        , Castable(..)
                                        , normalize, atomOfValue, valueOfLExp, valueOfExp
                                        , isValue, isAtom
                                        , module Language.DMoCHi.ML.Syntax.Type
                                        , module Language.DMoCHi.ML.Syntax.Base )where
-- import Control.Monad
import Language.DMoCHi.Common.Id
-- import qualified Data.Map as M
-- import qualified Data.Set as S
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
    Exp :: (Normalized l Exp arg, Elem l (Labels Exp) ~ 'True) => 
            SLabel l -> arg -> Type -> UniqueKey -> Exp

data Value where
    Value :: (Normalized l Value arg, Elem l (Labels Value) ~ 'True) => 
            SLabel l -> arg -> Type -> UniqueKey -> Value

data Atom where
    Atom :: (Normalized l Atom arg, Elem l (Labels Atom) ~ 'True) => 
            SLabel l -> arg -> Type -> Atom

data LExp where
    LExp :: (Normalized l LExp arg, Elem l (Labels LExp) ~ 'True) => 
                SLabel l -> arg -> Type -> UniqueKey -> LExp

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
    Normalized 'Assume  e arg = arg ~ (Atom, Exp)
    Normalized 'Branch  e arg = arg ~ (Exp, Exp)
    Normalized 'Fail    e arg = arg ~ ()
    Normalized 'Omega   e arg = arg ~ ()
    Normalized 'Rand    e arg = arg ~ ()

type instance Labels Exp = '[ 'Literal, 'Var, 'Binary, 'Unary, 'Pair, 'Lambda
                            , 'Let, 'Assume, 'Branch, 'Fail, 'Omega ]
type instance Labels LExp = '[ 'Literal, 'Var, 'Binary, 'Unary, 'Pair, 'Lambda
                             , 'App, 'Branch, 'Rand, 'Fail, 'Omega ]
type instance Labels Value = '[ 'Literal, 'Var, 'Binary, 'Unary, 'Pair, 'Lambda ]
type instance Labels Atom  = '[ 'Literal, 'Var, 'Binary, 'Unary ]
type instance BinOps Atom  = '[ 'Add, 'Sub, 'Eq, 'Lt, 'Lte, 'And, 'Or ]
type instance UniOps Atom  = '[ 'Fst, 'Snd, 'Not, 'Neg ]
type instance Ident  Exp = TId
type instance Ident  LExp = TId
type instance Ident  Value = TId
type instance Ident  Atom = TId

mkBin :: SBinOp op -> Atom -> Atom -> Atom
mkBin op v1 v2 = case op of
    SAdd -> Atom SBinary (BinArg SAdd v1 v2) TInt
    SSub -> Atom SBinary (BinArg SSub v1 v2) TInt
    SEq  -> Atom SBinary (BinArg SEq v1 v2) TBool
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
mkLiteral l@(CBool _) = Atom SLiteral l TInt

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
        (SApp, (f, vs)) -> Typed.Exp l (f, map cast vs) sty key
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

normalize :: Typed.Program -> FreshIO Program
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
        (SApp, (f, es)) -> mkApp f <$> mapM convertV es <*> pure key
        (SLet, (x, e1, e2)) -> do
            e1' <- convertL e1
            ContT $ \cont -> do
                e2' <- runContT (convertL e2) cont
                return $ mkLet x e1' e2' key
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
        (SApp, (f, es)) -> do
            r <- TId sty <$> identify "r"
            app <- mkApp f <$> mapM convertV es <*> freshKey
            key' <- freshKey
            return $ mkLet r app (castWith key' $ mkVar r) key
        (SLet, (x, e1, e2)) -> do
            e1' <- convertL e1
            e2' <- resetT $ convertE e2
            return $ mkLet x e1' e2' key
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

convertA :: MonadId m => Typed.Exp -> ContT Exp m Atom
convertA e@(Typed.Exp l arg sty _) = 
    case (l,arg) of
        (SLiteral, lit) -> pure (mkLiteral lit)
        (SVar, x) -> pure (mkVar x)
        (SUnary,  UniArg op e1)    -> mkUni op <$> convertA e1
        (SBinary, BinArg op e1 e2) -> mkBin op <$> convertA e1 
                                               <*> convertA e2 
        _ -> do
            e' <- convertL e
            r <- TId sty <$> identify "tmp"
            shiftT $ \cont -> lift (mkLet r e' <$> cont (mkVar r) <*> freshKey)

convertV :: MonadId m => Typed.Exp -> ContT Exp m Value
convertV e@(Typed.Exp l arg sty key) =
    case (l,arg) of
        (SLiteral, _) -> castWith key <$> convertA e
        (SVar, _) -> castWith key <$> convertA e
        (SUnary, _) -> castWith key <$> convertA e
        (SBinary, _) -> castWith key <$> convertA e
        (SPair, (e1, e2)) -> mkPair <$> convertV e1 <*> convertV e2 <*> pure key
        (SLambda, (x, e1)) -> mkLambda x <$> resetT (convertE e1) <*> pure key
        _ -> do
            e' <- convertL e
            r <- TId sty <$> identify "tmp"
            kr <- freshKey
            shiftT $ \cont -> lift (mkLet r e' <$> cont (castWith kr (mkVar r)) <*> freshKey)

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
            
{-
data Program = Program { functions :: [(Id,FunDef)] 
                       , mainTerm  :: Exp }

data Exp = Value Value
         | Let Type Id LetValue Exp -- associated type is that of body exp
         | Assume Type AValue Exp
         | Fail Type
         | Branch Type !Int Exp Exp deriving(Eq,Show)

data Value = Atomic AValue | Fun FunDef | Pair Value Value deriving(Eq,Show)

data AValue = Var Id
            | CInt  Integer
            | CBool Bool
            | Op Op deriving(Eq,Show)

data Op = OpAdd AValue AValue
        | OpSub AValue AValue
        | OpEq  AValue AValue
        | OpLt  AValue AValue
        | OpLte AValue AValue
        | OpAnd AValue AValue
        | OpOr  AValue AValue
        | OpFst Type AValue
        | OpSnd Type AValue
        | OpNot AValue  deriving(Eq,Show)

data LetValue = LValue AValue
              | LApp Type !Int Id [Value]
              | LExp !Int Exp 
              | LRand
              deriving(Eq,Show)

data FunDef = FunDef { ident :: !Int,
                       args  :: [Id],
                       body  :: Exp }
                       deriving(Show, Eq)

instance HasType Exp where
    getType (Value v) = getType v
    getType (Let a _ _ _) = a
    getType (Assume a _ _) = a
    getType (Fail a) = a
    getType (Branch a _ _ _) = a

instance HasType LetValue where
    getType (LValue v) = getType v
    getType (LApp ty _ _ _) = ty
    getType (LExp _ e) = getType e
    getType LRand = TInt

instance HasType AValue where
    getType (Var x) = getType x
    getType (CInt _) = TInt
    getType (CBool _) = TBool
    getType (Op op) = getType op
    
instance HasType Value where
    getType (Atomic v) = getType v
    getType (Fun fdef) = getType fdef
    getType (Pair v1 v2) = TPair (getType v1) (getType v2)

instance HasType Op where
    getType (OpAdd _ _) = TInt
    getType (OpSub _ _) = TInt
    getType (OpEq  _ _) = TBool
    getType (OpLt  _ _) = TBool
    getType (OpLte _ _) = TBool
    getType (OpAnd _ _) = TBool
    getType (OpOr  _ _) = TBool
    getType (OpNot _)   = TBool
    getType (OpFst a _)   = a
    getType (OpSnd a _)   = a

instance HasType FunDef where
    getType e = TFun (map getType (args e)) (getType (body e))

size :: Program -> Int
size (Program fs t) = sum [ sizeE (body e) + 1 | (_,e) <- fs ] + sizeE t

sizeE :: Exp -> Int
sizeE (Value v)      = sizeV v
sizeE (Let _ _ lv e)  = 1 + sizeLV lv + sizeE e
sizeE (Assume _ v e) = 1 + sizeAV v + sizeE e
sizeE (Fail _)       = 1
sizeE (Branch _ _ e1 e2) = 1 + sizeE e1 + sizeE e2

sizeAV :: AValue -> Int
sizeAV (Var _) = 1
sizeAV (CInt _) = 1
sizeAV (CBool _) = 1
-- sizeAV (Pair v1 v2) = 1 + sizeV v1 + sizeV v2
sizeAV (Op op) = (case op of
    OpAdd v1 v2 -> bin v1 v2 
    OpSub v1 v2 -> bin v1 v2 
    OpEq  v1 v2 -> bin v1 v2
    OpLt  v1 v2 -> bin v1 v2
    OpLte v1 v2 -> bin v1 v2
    OpAnd v1 v2 -> bin v1 v2
    OpOr  v1 v2 -> bin v1 v2
    OpFst _ v1  -> unary v1
    OpSnd _ v1  -> unary v1
    OpNot v1    -> unary v1) where
        bin v1 v2 = 1 + sizeAV v1 + sizeAV v2
        unary v1 = 1 + sizeAV v1

sizeV (Atomic v) = sizeAV v
sizeV (Fun fdef) = 1 + sizeE (body fdef)
sizeV (Pair v1 v2) = 1 + sizeV v1 + sizeV v2

sizeLV :: LetValue -> Int
sizeLV (LValue v) = sizeAV v
sizeLV (LApp _ _ _ vs) = 1 + sum (map sizeV vs)
sizeLV (LExp _ e) = sizeE e
sizeLV LRand = 1

freeVariables :: S.Set Id -> Exp -> S.Set Id
freeVariables = goE S.empty where
    goE :: S.Set Id -> S.Set Id -> Exp -> S.Set Id
    goE !acc env (Value v) = goV acc env v
    goE !acc env (Let _ x lv e) = goE (goLV acc env lv) (S.insert x env) e
    goE !acc env (Assume _ v e) = goE (goAV acc env v) env e
    goE !acc _ (Fail _) = acc
    goE !acc env (Branch _ _ e1 e2) = goE (goE acc env e1) env e2

    goV :: S.Set Id -> S.Set Id -> Value -> S.Set Id
    goV !acc env (Atomic v) = goAV acc env v
    goV !acc env (Fun fdef) = goE acc (foldr S.insert env (args fdef)) (body fdef)
    goV !acc env (Pair v1 v2) = goV (goV acc env v1) env v2

    goAV :: S.Set Id -> S.Set Id -> AValue -> S.Set Id
    goAV !acc env (Var x) = push acc env x
    goAV !acc _ (CInt _) = acc
    goAV !acc _ (CBool _) = acc
    goAV !acc env (Op (OpAdd v1 v2)) = goAV (goAV acc env v1) env v2
    goAV !acc env (Op (OpSub v1 v2)) = goAV (goAV acc env v1) env v2
    goAV !acc env (Op (OpEq v1 v2)) = goAV (goAV acc env v1) env v2
    goAV !acc env (Op (OpLt v1 v2)) = goAV (goAV acc env v1) env v2
    goAV !acc env (Op (OpLte v1 v2)) = goAV (goAV acc env v1) env v2
    goAV !acc env (Op (OpAnd v1 v2)) = goAV (goAV acc env v1) env v2
    goAV !acc env (Op (OpOr v1 v2)) = goAV (goAV acc env v1) env v2
    goAV !acc env (Op (OpFst _ v)) = goAV acc env v
    goAV !acc env (Op (OpSnd _ v)) = goAV acc env v
    goAV !acc env (Op (OpNot v)) = goAV acc env v
    goLV !acc env (LValue v) = goAV acc env v
    goLV !acc env (LApp _ _ f vs) = 
        foldl (\acc v -> goV acc env v) (push acc env f) vs
    goLV !acc env (LExp _ e) = goE acc env e
    goLV !acc _env LRand = acc
    push acc env x | S.member x env = acc
                   | otherwise = S.insert x acc

alpha :: MonadId m => Value -> m Value
alpha = alphaV M.empty where
    alphaV :: MonadId m => M.Map Id Id -> Value -> m Value
    alphaV env (Atomic av) = pure $ Atomic (renameA env av)
    alphaV env (Fun (FunDef _ xs e)) = do
        l' <- freshInt
        xs' <- mapM alphaId xs
        e' <- alphaE (foldr (uncurry M.insert) env (zip xs xs')) e
        return (Fun (FunDef l' xs' e'))
    alphaV env (Pair v1 v2) = Pair <$> alphaV env v1 <*> alphaV env v2

    alphaE :: MonadId m => M.Map Id Id -> Exp -> m Exp
    alphaE env (Value v) = Value <$> alphaV env v
    alphaE env (Let ty x lv e) = do
        x' <- alphaId x
        Let ty x' <$> alphaLV env lv <*> alphaE (M.insert x x' env) e
    alphaE env (Assume ty av e) = 
        Assume ty (renameA env av) <$> alphaE env e
    alphaE _ (Fail ty) = pure (Fail ty)
    alphaE env (Branch ty _ e1 e2) = do
        l' <- freshInt
        Branch ty l' <$> alphaE env e1 <*> alphaE env e2

    alphaLV :: MonadId m => M.Map Id Id -> LetValue -> m LetValue
    alphaLV env (LValue av) = pure $ LValue (renameA env av)
    alphaLV env (LApp ty _ f vs) = 
        freshInt >>= (\l' -> LApp ty l' (rename env f) <$> (mapM (alphaV env) vs))
    alphaLV env (LExp _ e) = 
        freshInt >>= (\l' -> LExp l' <$> alphaE env e)
    alphaLV _env LRand = pure LRand

    renameA env (Var x) = Var (rename env x)
    renameA _env (CInt i) = CInt i
    renameA _env (CBool b) = CBool b
    renameA env (Op op) = Op $ case op of
        OpAdd v1 v2 -> OpAdd (renameA env v1) (renameA env v2)
        OpSub v1 v2 -> OpSub (renameA env v1) (renameA env v2)
        OpEq v1 v2 -> OpEq (renameA env v1) (renameA env v2)
        OpLt v1 v2 -> OpLt (renameA env v1) (renameA env v2)
        OpLte v1 v2 -> OpLte (renameA env v1) (renameA env v2)
        OpAnd v1 v2 -> OpAnd (renameA env v1) (renameA env v2)
        OpOr v1 v2 -> OpOr (renameA env v1) (renameA env v2)
        OpFst ty v -> OpFst ty (renameA env v)
        OpSnd ty v -> OpSnd ty (renameA env v)
        OpNot v -> OpNot (renameA env v)

    rename env x = case M.lookup x env of
        Just y -> y
        Nothing -> x


alphaId :: MonadId m => Id -> m Id
alphaId x = Id (getType x) <$> freshId (elim $ name x)
    where
    elim x = reverse $ dropWhile (=='_') $ dropWhile isDigit $ reverse x
    

normalize :: MonadId m => Typed.Program -> m Program
normalize prog = do
    let fs = Typed.functions prog
        e0 = Typed.mainTerm prog
    fs' <- forM fs $ \(f,fdef) -> (,) f <$> convertF M.empty fdef
    e0' <- convertE M.empty e0
    return $ Program fs' e0'
    where
    convertE :: MonadId m => M.Map Id Value -> Typed.Exp -> m Exp
    convertE env (Typed.Value v) = Value <$> convertV env v
    convertE env (Typed.Fun fdef) = Value . Fun <$> convertF env fdef
    convertE env (Typed.Let ty x lv e) = case lv of
        Typed.LValue v -> do
            v' <- convertV env v
            case v' of
                Atomic (Var _) -> convertE (M.insert x v' env) e
                Atomic av -> Let ty x (LValue av) <$> convertE env e
                _ -> convertE (M.insert x v' env) e
        Typed.LApp ty' l f vs -> do
            vs' <- mapM (convertV env) vs
            case M.lookup f env of
                Just (Atomic (Var g)) ->
                    Let ty x (LApp ty' l g vs') <$> convertE env e
                Just v -> error $ "Unexpected function value for function call: " ++ show v
                Nothing -> 
                    Let ty x (LApp ty' l f vs') <$> convertE env e
        Typed.LFun fdef -> do
            fdef' <- convertF env fdef
            convertE (M.insert x (Fun fdef') env) e
        Typed.LExp l e1 -> do
            e1' <- convertE env e1
            Let ty x (LExp l e1') <$> convertE env e
        Typed.LRand -> do
            Let ty x LRand <$> convertE env e
    convertE env (Typed.Assume ty v e) = do
        Atomic av <- convertV env v
        Assume ty av <$> convertE env e
    convertE _env (Typed.Fail ty) = pure (Fail ty)
    convertE env (Typed.Branch ty l e1 e2) =
        Branch ty l <$> convertE env e1 <*> convertE env e2
            
    convertF :: MonadId m => M.Map Id Value -> Typed.FunDef -> m FunDef
    convertF env (Typed.FunDef l x e) = FunDef l x <$> convertE env e

    convertV :: MonadId m => M.Map Id Value -> Typed.Value -> m Value
    convertV env (Typed.Var x) = 
        case M.lookup x env of
            Nothing -> pure (Atomic $ Var x)
            Just v  -> alpha v
    convertV _env (Typed.CInt i) = pure (Atomic $ CInt i)
    convertV _env (Typed.CBool b) = pure (Atomic $ CBool b)
    convertV env (Typed.Pair v1 v2) = 
        Pair <$> convertV env v1 <*> convertV env v2
    convertV env (Typed.Op op) = (case op of
        Typed.OpAdd v1 v2 -> bin OpAdd v1 v2
        Typed.OpSub v1 v2 -> bin OpSub v1 v2
        Typed.OpEq v1 v2 -> bin OpEq v1 v2
        Typed.OpLt v1 v2 -> bin OpLt v1 v2
        Typed.OpLte v1 v2 -> bin OpLte v1 v2
        Typed.OpAnd v1 v2 -> bin OpAnd v1 v2
        Typed.OpOr v1 v2 -> bin OpOr v1 v2
        Typed.OpFst ty v -> do
            v' <- convertV env v
            case v' of
                Atomic av -> return $ Atomic $ Op $ OpFst ty av
                Pair v1 _ -> pure v1
                Fun _ -> error "convertV: unexpected Fun"
        Typed.OpSnd ty v -> do
            v' <- convertV env v
            case v' of
                Atomic av -> return $ Atomic $ Op $ OpSnd ty av
                Pair _ v2 -> pure v2
                Fun _ -> error "convertV: unexpected Fun"
        Typed.OpNot v -> do
            Atomic av <- convertV env v
            return $ Atomic $ Op $ OpNot av)
        where 
        bin f v1 v2 = do
            Atomic av1 <- convertV env v1
            Atomic av2 <- convertV env v2
            return $ Atomic $ Op (f av1 av2)

            
            -}

