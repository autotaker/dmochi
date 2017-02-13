{-# LANGUAGE FlexibleContexts, BangPatterns, GADTs, TypeFamilies, DataKinds #-}
module Language.DMoCHi.ML.Syntax.Typed {- ( Program(..)
                                      , Exp(..)
                                      , Value(..)
                                      , Op(..)
                                      , LetValue(..)
                                      , FunDef(..)
                                      , substV
                                      , evalV
                                      , size
                                      , sizeE
                                      , sizeV
                                      , sizeLV
                                      , freeVariables
                                      , module Language.DMoCHi.ML.Syntax.Type
                                      ) -} where
-- import qualified Data.Map as M
-- import qualified Data.Set as S
import Language.DMoCHi.Common.Id 
import Language.DMoCHi.ML.Syntax.Type
import Language.DMoCHi.ML.Syntax.Base
import Text.PrettyPrint.HughesPJClass

data Program = Program { functions :: [(TId, UniqueKey, [TId], Exp)] 
                       , mainTerm  :: Exp }

data Exp where
    Exp :: ( WellFormed l Exp arg
           , Supported l (Labels Exp)) => SLabel l -> arg -> Type -> UniqueKey -> Exp

type instance Labels Exp = AllLabels
type instance BinOps Exp = AllBinOps
type instance UniOps Exp = AllUniOps
type instance Ident Exp = TId

instance HasType Exp where
    getType (Exp _ _ sty _) = sty

instance Pretty Exp where
    pPrintPrec plevel prec (Exp op arg sty key) =
        if plevel == prettyNormal
            then doc 
            else comment (key, sty) <+> doc
        where
        doc = genericPPrint pp plevel prec op arg
        pp :: WellFormedPrinter Exp
        pp = WellFormedPrinter { pPrintExp   = pPrintPrec
                               , pPrintIdent = pPrintPrec }

instance Pretty Program where
    pPrintPrec plevel _ (Program fs t) = 
        text "(* functions *)" $+$ 
        vcat (map (\(f,key,xs,e) -> 
            comment key $+$
            text "let" <+> pPrintPrec plevel 0 f <+> hsep (map (pPrintPrec prettyBind 1) xs) <+> colon <+> pPrint (getType e) <+> equals $+$
            nest 4 (pPrintPrec plevel 0 e <> text ";;")) fs) $+$
        text "(*main*)" $+$
        pPrintPrec plevel 0 t
            

{-
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
              | LApp Type !Int Id [Value]
              | LFun FunDef
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

instance HasType FunDef where
    getType e = TFun (map getType (args e)) (getType (body e))

substV :: Id -> Value -> Value -> Value
substV x v = go where
    go (Var y) | name x == name y = v
               | otherwise = Var y
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
sizeLV (LApp _ _ _ vs) = foldr (\v y -> 1 + sizeV v + y) 1 vs
sizeLV (LExp _ e) = sizeE e
sizeLV (LFun e) = sizeE (body e) + 1
sizeLV LRand = 1

freeVariables :: S.Set Id -> Exp -> S.Set Id
freeVariables = goE S.empty where
    goE :: S.Set Id -> S.Set Id -> Exp -> S.Set Id
    goE !acc env (Value v) = goV acc env v
    goE !acc env (Fun fdef) = goE acc (foldr S.insert env (args fdef)) (body fdef)
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
    goLV !acc env (LApp _ _ f vs) = 
        foldl (\acc v -> goV acc env v) (push acc env f) vs
    goLV !acc env (LFun fdef) = goE acc (foldr S.insert env (args fdef)) (body fdef)
    goLV !acc env (LExp _ e) = goE acc env e
    goLV !acc _ LRand = acc
    push acc env x | S.member x env = acc
                   | otherwise = S.insert x acc

-}
