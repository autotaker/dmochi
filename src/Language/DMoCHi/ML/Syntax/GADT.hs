{-# LANGUAGE GADTs, DataKinds, TypeFamilies, TypeOperators, RankNTypes #-}
module Language.DMoCHi.ML.Syntax.GADT where
import qualified Language.DMoCHi.ML.Syntax.UnTyped as Syntax
import qualified Data.Map  as M
import Control.Applicative

data Type = TInt | TBool | TFun Type Type 
data SType typ where
    SInt :: SType TInt
    SBool :: SType TBool
    SFun  :: SType t1 -> SType t2 -> SType (TFun t1 t2) 

data SList xs where
    SNil :: SList '[]
    SCons :: Value typ -> SList xs -> SList (typ ': xs)

{-
type family App (f :: Type) (xs :: [Type]) :: Type
type instance App f '[] = f
type instance App (TFun ty1 ty2) (ty1 ': ts) = App ty2 ts
-}

data AType where
    AType :: SType typ -> AType

unpack :: AType -> (forall typ. SType typ -> a) -> a
unpack (AType typ) f = f typ

type Env = M.Map String AType


data TyEq (t1 :: Type) (t2 :: Type) where
    Equal :: TyEq t1 t1
    NotEqual :: TyEq t1 t2

tyEq :: SType t1 -> SType t2 -> TyEq t1 t2
tyEq SInt SInt = Equal
tyEq SBool SBool = Equal
tyEq (SFun t1 t2) (SFun t3 t4) = 
    case tyEq t1 t3 of
        Equal -> case tyEq t2 t4 of
            Equal -> Equal
            NotEqual -> NotEqual
        NotEqual -> NotEqual
tyEq _ _ = NotEqual

data Id (typ :: Type) where
    Id :: String -> SType typ -> Id typ

data Value (typ :: Type) where
    Var :: Id typ -> Value typ
    CBool :: Bool -> Value TBool
    CInt  :: Integer -> Value TInt
    Op  :: Op typ -> Value typ

data Op (typ :: Type) where
    OpAdd :: Value TInt -> Value TInt -> Op TInt
    OpSub :: Value TInt -> Value TInt -> Op TInt
    OpNeg :: Value TInt -> Op TInt
    OpEqB :: Value TBool -> Value TBool -> Op TBool
    OpEqI :: Value TInt  -> Value TInt  -> Op TBool
    OpLt  :: Value TInt -> Value TInt -> Op TBool 
    OpGt  :: Value TInt -> Value TInt -> Op TBool
    OpLte :: Value TInt -> Value TInt -> Op TBool
    OpGte :: Value TInt -> Value TInt -> Op TBool
    OpAnd :: Value TBool -> Value TBool -> Op TBool
    OpOr  :: Value TBool -> Value TBool -> Op TBool
    OpNot :: Value TBool -> Op TBool

data Exp typ where 
    Value  :: Value typ -> Exp typ
    Let    :: Id typ' -> LetValue typ' -> Exp typ -> Exp typ
    Assume :: Value TBool -> Exp typ -> Exp typ
    Lambda :: Id typ' -> Exp typ -> Exp (TFun typ' typ)
    Fail   :: Exp typ
    Branch :: Exp typ -> Exp typ -> Exp typ

data App typ where
    AId  :: Id typ -> App typ
    AApp :: App (TFun typ' typ) -> Value typ' -> App typ

data LetValue typ where
    LValue :: Value typ -> LetValue typ
    LApp   :: App typ -> LetValue typ
    LExp   :: PType typ -> Exp typ -> LetValue typ

data PType typ where
    P :: [Predicate typ] -> PType typ
    PFun :: PType typ -> (Value typ -> PType typ') -> PType (TFun typ typ')

type Predicate typ = Value typ -> Value TBool

convertV :: Syntax.Value -> Env -> SType typ -> Maybe (Value typ)
convertV (Syntax.Var s) env ty = 
    unpack (env M.! s) $ \ty' -> case tyEq ty ty' of
        Equal -> return (Var (Id s ty))
        NotEqual -> empty
convertV (Syntax.CInt i) _ SInt   = return (CInt i)
convertV (Syntax.CInt _) _ _ = empty
convertV (Syntax.CBool b) _ SBool = return (CBool b)
convertV (Syntax.CBool _) _ _ = empty
convertV (Syntax.Op op) env ty = fmap Op $ convertOp op env ty

convertOp :: Syntax.Op Syntax.Value -> Env -> SType typ -> Maybe (Op typ)
convertOp (Syntax.OpAdd v1 v2) env SInt = OpAdd <$> convertV v1 env SInt <*> convertV v2 env SInt
convertOp (Syntax.OpSub v1 v2) env SInt = OpSub <$> convertV v1 env SInt <*> convertV v2 env SInt
convertOp (Syntax.OpNeg v1)    env SInt = OpNeg <$> convertV v1 env SInt
convertOp (Syntax.OpEq  v1 v2) env SBool = OpEqI <$> convertV v1 env SInt <*> convertV v2 env SInt
convertOp (Syntax.OpLt  v1 v2) env SBool = OpLt <$> convertV v1 env SInt <*> convertV v2 env SInt
convertOp (Syntax.OpLte v1 v2) env SBool = OpLte <$> convertV v1 env SInt <*> convertV v2 env SInt
convertOp (Syntax.OpGt  v1 v2) env SBool = OpGt <$> convertV v1 env SInt <*> convertV v2 env SInt
convertOp (Syntax.OpGte v1 v2) env SBool = OpGte <$> convertV v1 env SInt <*> convertV v2 env SInt
convertOp (Syntax.OpAnd v1 v2) env SBool = OpAnd <$> convertV v1 env SBool <*> convertV v2 env SBool
convertOp (Syntax.OpOr  v1 v2) env SBool = OpOr <$> convertV v1 env SBool <*> convertV v2 env SBool
convertOp (Syntax.OpNot v1)    env SBool = OpNot <$> convertV v1 env SBool
convertOp _ _ _ = empty

convertE :: Syntax.Exp -> Env -> SType typ -> Maybe (Exp typ)
convertE (Syntax.Value v) env ty = Value <$> convertV v env ty
convertE (Syntax.Let x lv e) env ty = do
    unpack (env M.! x) $ \ty' -> Let (Id x ty') <$> convertLV lv env ty' <*> convertE e env ty
convertE (Syntax.Assume v e) env ty = Assume <$> convertV v env SBool <*> convertE e env ty
convertE (Syntax.Lambda x e) env (SFun ty1 ty2) = 
    unpack (env M.! x) $ \ty' -> case ty' `tyEq` ty1 of
            Equal -> Lambda (Id x ty1) <$> convertE e env ty2
            NotEqual -> empty
convertE (Syntax.Fail)       _ _ = return Fail
convertE (Syntax.Branch e1 e2) env ty = Branch <$> convertE e1 env ty <*> convertE e2 env ty
convertE _ _ _ = empty

convertLV :: Syntax.LetValue -> Env -> SType typ -> Maybe (LetValue typ)
convertLV (Syntax.LValue v) env ty  = LValue <$> convertV v env ty
convertLV (Syntax.LApp x vs) env ty = LApp <$> convertArgs x vs env ty
convertLV (Syntax.LExp ptyp e) env ty = LExp <$> convertP ptyp M.empty ty <*> convertE e env ty

substV :: Id typ -> Value typ -> Value typ' -> Value typ'
substV x v (Var y) = 
    let Id sx ty = x in
    let Id sy ty' = y in
    if sx == sy then
        case tyEq ty ty' of
            Equal -> v
            NotEqual -> error "unexpected type error"
    else (Var y)
substV x v (Op op) = Op $ case op of
    OpAdd v1 v2 -> OpAdd (substV x v v1) (substV x v v2)
    OpSub v1 v2 -> OpSub (substV x v v1) (substV x v v2)
    OpNeg v1 -> OpNeg (substV x v v1)
    OpEqB v1 v2 -> OpEqB (substV x v v1) (substV x v v2)
    OpEqI v1 v2 -> OpEqI (substV x v v1) (substV x v v2)
    OpLt v1 v2 -> OpLt (substV x v v1) (substV x v v2)
    OpGt v1 v2 -> OpGt (substV x v v1) (substV x v v2)
    OpLte v1 v2 -> OpLte (substV x v v1) (substV x v v2)
    OpGte v1 v2 -> OpGte (substV x v v1) (substV x v v2)
    OpAnd v1 v2 -> OpAnd (substV x v v1) (substV x v v2)
    OpOr v1 v2 -> OpOr (substV x v v1) (substV x v v2)
    OpNot v1 -> OpNot (substV x v v1)
substV _ _ t = t

substP :: Id typ -> Value typ -> PType typ' -> PType typ'
substP x v (P ps) = P (map (substV x v.) ps)
substP x v (PFun p f) = PFun (substP x v p) (substP x v.f)
        
convertP :: Syntax.PType -> Env -> SType typ -> Maybe (PType typ)
convertP (Syntax.PInt ps) env SInt =
    P <$> mapM (\(x,v) -> do
        let env' = M.insert x (AType SInt) env
        v' <- convertV v env' SBool
        return $ \vx -> substV (Id x SInt) vx v') ps
convertP (Syntax.PBool ps) env SBool =
    P <$> mapM (\(x,v) -> do
        let env' = M.insert x (AType SBool) env
        v' <- convertV v env' SBool
        return $ \vx -> substV (Id x SBool) vx v') ps
convertP (Syntax.PFun p (x,f)) env (SFun ty ty') = do
    p' <- convertP p env ty
    f' <- convertP f (M.insert x (AType ty) env) ty'
    return $ PFun p' (\vx -> substP (Id x ty) vx f')
convertP _ _ _ = empty

convertArgs :: String -> [Syntax.Value] -> Env -> SType typ -> Maybe (App typ)
convertArgs x _vs env ty0 = unpack (env M.! x) $ \ty' -> go ty0 (AId (Id x ty')) ty' _vs where
    go :: SType typ' -> App typ -> SType typ -> [Syntax.Value] -> Maybe (App typ')
    go ty' acc ty [] = case tyEq ty' ty of
        Equal -> return acc
        NotEqual -> empty
    go ty' acc (SFun ty1 ty2) (v:vs) = do
        acc' <- AApp acc <$> convertV v env ty1
        go ty' acc' ty2 vs
    go _ _ _ _ = empty
