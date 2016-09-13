{-# LANGUAGE FlexibleContexts, BangPatterns #-}
module Language.DMoCHi.ML.Syntax.PNormal( Program(..)
                                        , Exp(..)
                                        , Value(..)
                                        , AValue(..)
                                        , Op(..)
                                        , LetValue(..)
                                        , FunDef(..)
                                        , size
                                        , freeVariables
                                        , normalize
                                        , module Language.DMoCHi.ML.Syntax.Type
                                        ) where
import Control.Monad
import Control.Monad.State
import Language.DMoCHi.Common.Util
import Language.DMoCHi.Common.Id
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Char
import Language.DMoCHi.ML.Syntax.Type
import qualified Language.DMoCHi.ML.Syntax.Typed as Typed

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

{-
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
    -}


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
    goLV !acc env LRand = acc
    push acc env x | S.member x env = acc
                   | otherwise = S.insert x acc

alpha :: MonadId m => Value -> m Value
alpha = alphaV M.empty where
    alphaV :: MonadId m => M.Map Id Id -> Value -> m Value
    alphaV env (Atomic av) = pure $ Atomic (renameA env av)
    alphaV env (Fun (FunDef l xs e)) = do
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
    alphaE env (Branch ty l e1 e2) = do
        l' <- freshInt
        Branch ty l' <$> alphaE env e1 <*> alphaE env e2

    alphaLV :: MonadId m => M.Map Id Id -> LetValue -> m LetValue
    alphaLV env (LValue av) = pure $ LValue (renameA env av)
    alphaLV env (LApp ty l f vs) = 
        freshInt >>= (\l' -> LApp ty l' (rename env f) <$> (mapM (alphaV env) vs))
    alphaLV env (LExp l e) = 
        freshInt >>= (\l' -> LExp l' <$> alphaE env e)
    alphaLV env (LRand) = pure LRand

    renameA env (Var x) = Var (rename env x)
    renameA env (CInt i) = CInt i
    renameA env (CBool b) = CBool b
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
                Atomic (Var y) -> convertE (M.insert x v' env) e
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
    convertE env (Typed.Fail ty) = pure (Fail ty)
    convertE env (Typed.Branch ty l e1 e2) =
        Branch ty l <$> convertE env e1 <*> convertE env e2
            
    convertF :: MonadId m => M.Map Id Value -> Typed.FunDef -> m FunDef
    convertF env (Typed.FunDef l x e) = FunDef l x <$> convertE env e

    convertV :: MonadId m => M.Map Id Value -> Typed.Value -> m Value
    convertV env (Typed.Var x) = 
        case M.lookup x env of
            Nothing -> pure (Atomic $ Var x)
            Just v  -> alpha v
    convertV env (Typed.CInt i) = pure (Atomic $ CInt i)
    convertV env (Typed.CBool b) = pure (Atomic $ CBool b)
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
        Typed.OpSnd ty v -> do
            v' <- convertV env v
            case v' of
                Atomic av -> return $ Atomic $ Op $ OpSnd ty av
                Pair _ v2 -> pure v2
        Typed.OpNot v -> do
            Atomic av <- convertV env v
            return $ Atomic $ Op $ OpNot av)
        where 
        bin f v1 v2 = do
            Atomic av1 <- convertV env v1
            Atomic av2 <- convertV env v2
            return $ Atomic $ Op (f av1 av2)

            

