{-# LANGUAGE FlexibleContexts #-}
module Language.DMoCHi.ML.TypeCheck where
import qualified Data.Map as M
import Control.Applicative
import Control.Monad.Except
import Language.DMoCHi.ML.Syntax.Typed 
import qualified Language.DMoCHi.ML.Syntax.UnTyped as U
import Text.PrettyPrint
import Language.DMoCHi.ML.PrettyPrint.Typed 
import Debug.Trace
import Language.DMoCHi.Common.Id
instance Show TypeError where
    show (UndefinedVariable s) = "UndefinedVariables: "++ s
    show (TypeMisMatch s t1 t2) = "TypeMisMatch: " ++ show t1 ++ " should be " ++ show t2 ++ ". context :" ++ s
    show (TypeMisUse t1 t2)     = "TypeUse: " ++ show t1 ++ " should be in " ++ show t2
    show (OtherError s)         = "OtherError: " ++ s

type Env = M.Map String Type
data TypeError = UndefinedVariable String 
               | TypeMisMatch String Type Type
               | TypeMisUse   Type [Type]
               | OtherError String

fromUnTyped :: (Applicative m,MonadError TypeError m, MonadId m) => U.Program -> m Program
fromUnTyped (U.Program fs t) = do
    fs' <- mapM (\(x,p,e) -> (,,) x <$> convertP p <*> pure e) fs
    let tenv = M.fromList [ (x,ty) | (x,ty,_) <- fs' ]
    fs'' <- forM fs' $ \(x,ty,U.Lambda y e) -> do
        let x' = Id ty x
        fdef <- convertLambda tenv y e ty
        return (x',fdef) 
    Program fs'' <$> convertE tenv TInt t

{-
toUnTyped :: Program -> U.Program
toUnTyped (Program fs t) = U.Program fs' t' where
    fs' = map (\(x,p,e) -> (name x,revP p, revE e)) fs
    t'  = revE t
    -}

shouldBe :: MonadError TypeError m => String -> Type -> Type -> m ()
shouldBe s t1 t2 | t1 == t2 = return ()
                 | otherwise = throwError (TypeMisMatch s t1 t2)

shouldBeValue :: MonadError TypeError m => Value -> Type -> m ()
shouldBeValue v t1 = shouldBe (render $ pprintV 0 v) (getType v) t1

shouldBeIn :: MonadError TypeError m => Type -> [Type] -> m ()
shouldBeIn t1 ts = 
    if t1 `elem` ts then return () else throwError (TypeMisUse t1 ts)

shouldBePair :: MonadError TypeError m => String -> Type -> m (Type,Type)
shouldBePair _ (TPair t1 t2) = return (t1,t2)
shouldBePair s _ = throwError (OtherError $ "expecting pair :" ++ s)

convertP :: (Applicative m,MonadError TypeError m) => U.PType -> m Type
convertP = go M.empty where
    base f env ty ps = 
        f <$> mapM (\(x,p) -> do
            p' <- convertV (M.insert x ty env) p
            shouldBeValue p' TBool
            return (Id ty x,p')) ps
    go env (U.PInt ps) = base (const TInt) env TInt ps
    go env (U.PBool ps) = base (const TBool) env TBool ps
    go env (U.PPair p (x,f)) =  do
        ty1 <- go env p
        ty2 <- go (M.insert x ty1 env) f
        return (TPair ty1 ty2)
    go env (U.PFun p (x,f)) = do
        ty1 <- go env p
        ty2 <- go (M.insert x ty1 env) f
        return (TFun ty1 ty2)

convertE :: (Applicative m,MonadError TypeError m, MonadId m) => Env -> Type -> U.Exp -> m Exp
convertE env ty _e = case _e of
    U.Value v -> do
        v' <- convertV env v
        v' `shouldBeValue` ty
        return $ Value v'
    U.Let x lv e -> do
        (lv',as) <- convertLV env lv
        let ty' = getType lv'
        e' <- Let ty (Id ty' x) lv' <$> convertE (M.insert x ty' env) ty e
        return $ foldr (\(x,vi) acc -> Let ty x vi acc) e' as
    U.Assume v e -> do
        v' <- convertV env v
        shouldBeValue  v' TBool
        Assume ty v' <$> convertE env ty e
    U.Lambda x e -> do
        fdef <- convertLambda env x e ty
        return $ Fun fdef
        {-
        f <- Id ty <$> freshId "f"
        return $ Let ty f (LFun fdef) (Value (Var f))
        -}
                    
    U.Fail -> pure $ Fail ty
    U.Branch e1 e2 -> do
        i <- freshInt
        Branch ty i <$> convertE env ty e1 <*> convertE env ty e2

convertLambda :: (MonadError TypeError m, MonadId m) => Env -> U.Id -> U.Exp -> Type -> m FunDef
convertLambda env arg body (TFun t1 t2) = do
    i <- freshInt
    FunDef i (Id t1 arg) <$> convertE (M.insert arg t1 env) t2 body
convertLambda _ x _ _ = throwError $ OtherError $ "Expecting function:" ++ x


-- f v1 v2 .. vn ==> (yn-1 vn,[(y1,f v1),(y2,y1 v2),...,(yn-1,yn-2,vn-1)])
-- に変換する
convertLV :: (Applicative m,MonadError TypeError m, MonadId m) => Env -> U.LetValue -> m (LetValue,[(Id,LetValue)])
convertLV env lv = case lv of
    U.LValue v -> do
        v' <- convertV env v
        return (LValue v',[])
    U.LRand -> 
        return (LRand,[])
    U.LApp f vs -> do
        vs' <- mapM (convertV env) vs
        case M.lookup f env of
            Just ty -> do
                (ty',xs) <- foldM (\(tf,acc) v -> 
                    case tf of
                        TFun t1 t2 -> do
                            shouldBeValue v  t1
                            x <- Id t2 <$> freshId "tmp"
                            return (t2,x:acc)
                        _ -> throwError $ OtherError $ "Excepting function" ++ show (f,vs)) (ty,[]) vs'
                is <- replicateM (length vs) freshInt
                let ys = reverse (tail xs)
                    f' = Id ty f
                    l = zipWith3 (\x y (i,v) -> (x,LApp (getType x) i y v)) ys (f':ys) (zip is vs')
                    yn = last (f':ys)
                    vn = last vs'
                return $ (LApp ty' (last is) yn vn,l)
            Nothing -> throwError $ UndefinedVariable f
    U.LExp ptyp (U.Lambda x e) -> do
        ty <- convertP ptyp
        fdef <- convertLambda env x e ty
        return (LFun fdef,[])
    U.LExp ptyp e -> do
        ty <- convertP ptyp
        i <- freshInt
        lv <- LExp i <$> convertE env ty e
        return (lv,[])
                

convertV :: (Applicative m,MonadError TypeError m) => Env -> U.Value -> m Value
convertV env v = case v of
    U.Var x -> case M.lookup x env of
        Just ty -> pure $ Var $ Id ty x
        Nothing -> throwError $ UndefinedVariable x
    U.CInt i -> pure $ CInt i
    U.CBool b -> pure $ CBool b
    U.Pair v1 v2 -> Pair <$> convertV env v1 <*> convertV env v2
    U.Op op -> do
        let bin f t v1 v2 = do
                v1' <- convertV env v1
                shouldBeValue v1' t
                v2' <- convertV env v2
                shouldBeValue v2' t
                return $ f v1' v2'
        Op <$> case op of
            U.OpAdd v1 v2 -> bin OpAdd TInt v1 v2
            U.OpSub v1 v2 -> bin OpSub TInt v1 v2
            U.OpNeg v1    -> bin OpSub TInt (U.CInt 0) v1
            U.OpEq  v1 v2 -> do
                v1' <- convertV env v1
                v2' <- convertV env v2
                v1' `shouldBeValue` getType v2'
                -- getType v1' `shouldBeIn` [TInt,TBool]
                return $ OpEq v1' v2'
            U.OpLt  v1 v2 -> bin OpLt TInt v1 v2
            U.OpGt  v1 v2 -> bin OpLt TInt v2 v1
            U.OpLte v1 v2 -> bin OpLte TInt v1 v2
            U.OpGte v1 v2 -> bin OpLte TInt v2 v1
            U.OpAnd v1 v2 -> bin OpAnd TBool v1 v2
            U.OpOr  v1 v2 -> bin OpOr TBool v1 v2
            U.OpNot v1    -> do
                v1' <- convertV env v1
                v1' `shouldBeValue` TBool
                return $ OpNot v1'
            U.OpFst v1    -> do
                v1' <- convertV env v1
                (t1,_) <- shouldBePair ("fst" ++ show v1) $ getType v1'
                return $ OpFst t1 v1'
            U.OpSnd v1    -> do
                v1' <- convertV env v1
                (_,t2) <- shouldBePair ("snd" ++ show v1 ++ "," ++ show env++ show (getType v1')) $ getType v1'
                return $ OpSnd t2 v1'

