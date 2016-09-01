{-# LANGUAGE FlexibleContexts, BangPatterns #-}
module Language.DMoCHi.ML.Syntax.Typed where
import Text.PrettyPrint
import Control.Monad
--import Control.Applicative
import Control.Monad.State
import Data.Function(on)
import qualified Data.Map as M
import qualified Data.Set as S

data Id = Id { _type :: Type, name :: String } deriving(Show)

instance Eq Id where
    (==) = (==) `on` name

instance Ord Id where
    compare = compare `on` name


type Predicate = (Id,Value)
data Program = Program { functions :: [(Id,FunDef)] 
                       , mainTerm  :: Exp }
data Type = TInt | TBool | TPair Type Type | TFun Type Type deriving(Eq)

data Exp = Value Value
         | Fun   FunDef
         | Let Type Id LetValue Exp -- associated type is that of body exp
         | Assume Type Value Exp
         | Fail Type
         | Branch Type !Int Exp Exp deriving(Eq,Show)

data Value = Var Id
           | CInt  Integer
           | CBool Bool
           | Pair Value Value
           | Op Op deriving(Eq,Show)

data Op = OpAdd Value Value
        | OpSub Value Value
        | OpEq  Value Value
        | OpLt  Value Value
        | OpLte Value Value
        | OpAnd Value Value
        | OpOr  Value Value
        | OpFst Type Value
        | OpSnd Type Value
        | OpNot Value  deriving(Eq,Show)

data LetValue = LValue Value
              | LApp Type !Int Id Value
              | LFun FunDef
              | LExp !Int Exp 
              | LRand
              deriving(Eq,Show)

data FunDef = FunDef { ident :: !Int,
                       arg   :: Id,
                       body  :: Exp }
                       deriving(Show, Eq)

data PType = PInt  [Predicate]
           | PBool [Predicate]
           | PPair Type PType (Id,PType) 
           | PFun  Type PType (Id,PType) deriving(Eq)

data PType' = PInt' | PBool'
            | PFun' Type (Id,PType',[Predicate]) (PType',[Predicate])
            | PPair' Type PType' PType'

class HasType m where
    getType :: m -> Type

instance HasType Id where
    getType = _type

instance HasType Exp where
    getType (Value v) = getType v
    getType (Let a _ _ _) = a
    getType (Assume a _ _) = a
    getType (Fun fdef) = getType fdef
    getType (Fail a) = a
    getType (Branch a _ _ _) = a

instance HasType LetValue where
    getType (LValue v) = getType v
    getType (LApp ty _ _ _) = ty
    getType (LExp _ e) = getType e
    getType (LFun lam) = getType lam
    getType LRand = TInt

instance HasType Value where
    getType (Var x) = getType x
    getType (CInt _) = TInt
    getType (CBool _) = TBool
    getType (Pair v1 v2) = TPair (getType v1) (getType v2)
    getType (Op op) = getType op

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

instance HasType PType where
    getType (PInt _) = TInt
    getType (PBool _) = TBool
    getType (PPair t _ _) = t
    getType (PFun t _ _) = t

instance HasType PType' where
    getType (PInt') = TInt
    getType (PBool') = TBool
    getType (PPair' t _ _) = t
    getType (PFun' t _ _) = t

instance HasType FunDef where
    getType e = TFun (getType (arg e)) (getType (body e))

substV :: Id -> Value -> Value -> Value
substV x v = go where
    go (Var y) | name x == name y = v
    go (Op op) = Op $ case op of
        OpAdd a b -> OpAdd (go a) (go b)
        OpSub a b -> OpSub (go a) (go b)
        OpEq  a b -> OpEq  (go a) (go b)
        OpLt  a b -> OpLt  (go a) (go b)
        OpLte a b -> OpLte (go a) (go b)
        OpAnd a b -> OpAnd (go a) (go b)
        OpOr  a b -> OpOr  (go a) (go b)
        OpNot a   -> OpNot (go a)
        OpFst t a -> OpFst t (go a)
        OpSnd t a -> OpSnd t (go a)
    go (CInt i) = CInt i
    go (CBool b) = CBool b
    go (Pair v1 v2) = Pair (go v1) (go v2)

evalV :: M.Map String Value -> Value -> Value
evalV env = go where
    go (Var y) = env M.! (name y)
    go (Op op) = Op $ case op of
        OpAdd a b -> OpAdd (go a) (go b)
        OpSub a b -> OpSub (go a) (go b)
        OpEq  a b -> OpEq  (go a) (go b)
        OpLt  a b -> OpLt  (go a) (go b)
        OpLte a b -> OpLte (go a) (go b)
        OpAnd a b -> OpAnd (go a) (go b)
        OpOr  a b -> OpOr  (go a) (go b)
        OpNot a   -> OpNot (go a)
        OpFst t a -> OpFst t (go a)
        OpSnd t a -> OpSnd t (go a)
    go (CInt i) = CInt i
    go (CBool b) = CBool b
    go (Pair v1 v2) = Pair (go v1) (go v2)

substPType :: Id -> Value -> PType -> PType
substPType x v = go where
    go (PInt  ps) = PInt (map (\(y,w) -> (y,substV x v w)) ps)
    go (PBool ps) = PBool (map (\(y,w) -> (y,substV x v w)) ps)
    go (PPair ty p1 (y,p2)) = PPair ty (go p1) (y,go p2)
    go (PFun  ty p1 (y,p2)) = PFun ty (go p1) (y,go p2)

fromPType :: PType -> PType'
fromPType (PInt _) = PInt'
fromPType (PBool _) = PBool'
fromPType (PFun ty pty (x,rty)) = PFun' ty (x,pty',ps) (rty',qs)
    where
        pty' = fromPType pty
        rty' = fromPType rty
        ps = case pty of
            PInt ps -> ps
            PBool ps -> ps
            _ -> []
        qs = case rty of
            PInt ps -> ps
            PBool ps -> ps
            _ -> []

toPType :: PType' -> PType
toPType PInt' = PInt []
toPType PBool' = PBool []
toPType (PFun' ty (x,pty,ps) (rty,qs)) = PFun ty pty' (x,rty') 
    where
    pty' = case pty of
        PInt' -> PInt ps
        PBool' -> PBool ps
        _ -> toPType pty
    rty' = case rty of
        PInt' -> PInt qs
        PBool' -> PBool qs
        _ -> toPType rty

size :: Program -> Int
size (Program fs t) = sum [ sizeE (body e) + 1 | (_,e) <- fs ] + sizeE t

sizeE :: Exp -> Int
sizeE (Value v)      = sizeV v
sizeE (Let _ _ lv e)  = 1 + sizeLV lv + sizeE e
sizeE (Fun fdef) = 1 + sizeE (body fdef)
sizeE (Assume _ v e) = 1 + sizeV v + sizeE e
sizeE (Fail _)       = 1
sizeE (Branch _ _ e1 e2) = 1 + sizeE e1 + sizeE e2

sizeV :: Value -> Int
sizeV (Var _) = 1
sizeV (CInt _) = 1
sizeV (CBool _) = 1
sizeV (Pair v1 v2) = 1 + sizeV v1 + sizeV v2
sizeV (Op op) = (case op of
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
        bin v1 v2 = 1 + sizeV v1 + sizeV v2
        unary v1 = 1 + sizeV v1

sizeLV :: LetValue -> Int
sizeLV (LValue v) = sizeV v
sizeLV (LApp _ _ _ v) = foldr (\v y -> 1 + sizeV v + y) 1 [v]
sizeLV (LExp _ e) = sizeE e
sizeLV (LFun e) = sizeE (body e) + 1
sizeLV LRand = 1

pushType :: PType -> State [PType] ()
pushType = modify . (:)

{-
gatherPTypes :: Program -> [PType]
gatherPTypes (Program fs t) = execState doit [] where
    doit = do
        forM_ fs $ \(_,ty,e) -> pushType ty >> gatherTypesE e
        gatherTypesE t

gatherTypesE :: Exp -> State [PType] ()
gatherTypesE (Value _) = return ()
gatherTypesE (Let _ _ lv e) = do
    case lv of 
        LExp ty e' -> pushType ty >> gatherTypesE e'
        _ -> return ()
    gatherTypesE e
gatherTypesE (Assume _ _ e) = gatherTypesE e
gatherTypesE (Lambda _ _ _ e) = gatherTypesE e
gatherTypesE (Fail _) = return ()
gatherTypesE (Branch _ _ e1 e2) = gatherTypesE e1 >> gatherTypesE e2
-}

sizeP :: PType -> Int
sizeP (PInt xs)     = length xs
sizeP (PBool xs)    = length xs
sizeP (PPair _ x1 (_,x2)) = sizeP x1 + sizeP x2
sizeP (PFun  _ x1 (_,x2)) = sizeP x1 + sizeP x2

orderT :: Type -> Int
orderT TInt = 0
orderT TBool = 0
orderT (TPair t1 t2) = max (orderT t1) (orderT t2)
orderT (TFun t1 t2)  = max (orderT t1+1) (orderT t2)

pprintT :: Int -> Type -> Doc
pprintT _ TInt = text "int"
pprintT _ TBool = text "bool"
pprintT assoc (TPair t1 t2) =
    let d1 = pprintT 1 t1
        d2 = pprintT 1 t2
        d  = d1 <+> text "*" <+> d2
    in if assoc <= 0 then d else parens d
pprintT assoc (TFun t1 t2) =
    let d1 = pprintT 1 t1
        d2 = pprintT 0 t2
        d  = d1 <+> text "->" <+> d2
    in if assoc == 0 then d else parens d

instance Show Type where
    show = render . pprintT 0

freeVariables :: S.Set Id -> Exp -> S.Set Id
freeVariables = goE S.empty where
    goE :: S.Set Id -> S.Set Id -> Exp -> S.Set Id
    goE !acc env (Value v) = goV acc env v
    goE !acc env (Fun fdef) = goE acc (S.insert (arg fdef) env) (body fdef)
    goE !acc env (Let _ x lv e) = goE (goLV acc env lv) (S.insert x env) e
    goE !acc env (Assume _ v e) = goE (goV acc env v) env e
    goE !acc _ (Fail _) = acc
    goE !acc env (Branch _ _ e1 e2) = goE (goE acc env e1) env e2
    goV :: S.Set Id -> S.Set Id -> Value -> S.Set Id
    goV !acc env (Var x) = push acc env x
    goV !acc _ (CInt _) = acc
    goV !acc _ (CBool _) = acc
    goV !acc env (Pair v1 v2) = goV (goV acc env v1) env v2
    goV !acc env (Op (OpAdd v1 v2)) = goV (goV acc env v1) env v2
    goV !acc env (Op (OpSub v1 v2)) = goV (goV acc env v1) env v2
    goV !acc env (Op (OpEq v1 v2)) = goV (goV acc env v1) env v2
    goV !acc env (Op (OpLt v1 v2)) = goV (goV acc env v1) env v2
    goV !acc env (Op (OpLte v1 v2)) = goV (goV acc env v1) env v2
    goV !acc env (Op (OpAnd v1 v2)) = goV (goV acc env v1) env v2
    goV !acc env (Op (OpOr v1 v2)) = goV (goV acc env v1) env v2
    goV !acc env (Op (OpFst _ v)) = goV acc env v
    goV !acc env (Op (OpSnd _ v)) = goV acc env v
    goV !acc env (Op (OpNot v)) = goV acc env v
    goLV !acc env (LValue v) = goV acc env v
    goLV !acc env (LApp _ _ f v) = goV (push acc env f) env v
    goLV !acc env (LFun fdef) = goE acc (S.insert (arg fdef) env) (body fdef)
    goLV !acc env (LExp _ e) = goE acc env e
    goLV !acc env LRand = acc
    push acc env x | S.member x env = acc
                   | otherwise = S.insert x acc

