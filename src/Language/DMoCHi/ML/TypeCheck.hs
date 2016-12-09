{-# LANGUAGE FlexibleContexts #-}
module Language.DMoCHi.ML.TypeCheck where
import qualified Data.Map as M
import Control.Applicative
import Control.Monad.Except
import Language.DMoCHi.ML.Syntax.Typed 
import qualified Language.DMoCHi.ML.Syntax.UnTyped as U
import Text.PrettyPrint
import Language.DMoCHi.ML.PrettyPrint.Typed 
import qualified Language.DMoCHi.ML.PrettyPrint.UnTyped as U
import Debug.Trace
import Language.DMoCHi.Common.Id
import Language.DMoCHi.ML.DesugarSynonym

instance Show TypeError where
    show (UndefinedVariable s) = "UndefinedVariables: "++ s
    show (TypeMisMatch s t1 t2) = "TypeMisMatch: " ++ show t1 ++ " should be " ++ show t2 ++ ". context :" ++ s
    show (TypeMisMatchList s t1 t2) = "TypeMisMatch: " ++ show t1 ++ " should be " ++ show t2 ++ ". context :" ++ s
    show (TypeMisUse t1 t2)     = "TypeUse: " ++ show t1 ++ " should be in " ++ show t2
    show (Synonym err) = "SynonymError: " ++ show err
    show (OtherError s)         = "OtherError: " ++ s

type Env = M.Map String Type
type SynEnv = M.Map U.SynName U.SynonymDef
data TypeError = UndefinedVariable String 
               | TypeMisMatch String Type Type
               | TypeMisMatchList String [Type] [Type]
               | TypeMisUse   Type [Type]
               | Synonym  SynonymError
               | OtherError String


fromUnTyped :: MonadId m => U.Program -> ExceptT TypeError m Program
fromUnTyped (U.Program fs syns t) = do
    synEnv <- withExceptT Synonym (desugarEnv syns)
    fs' <- mapM (\(x,p,e) -> (,,) x <$> convertP synEnv p <*> pure e) fs
    let tenv = M.fromList [ (x,ty) | (x,ty,_) <- fs' ]
    fs'' <- forM fs' $ \(x,ty,U.Lambda y e) -> do
        let x' = Id ty x
        fdef <- convertLambda synEnv tenv y e ty
        return (x',fdef) 
    Program fs'' <$> convertE synEnv tenv TInt t

{-
toUnTyped :: Program -> U.Program
toUnTyped (Program fs t) = U.Program fs' t' where
    fs' = map (\(x,p,e) -> (name x,revP p, revE e)) fs
    t'  = revE t
    -}

shouldBe :: Monad m => String -> Type -> Type -> ExceptT TypeError m ()
shouldBe s t1 t2 | t1 == t2 = return ()
                 | otherwise = throwError (TypeMisMatch s t1 t2)

shouldBeList :: Monad m => String -> [Type] -> [Type] -> ExceptT TypeError m ()
shouldBeList s ts1 ts2 | ts1 == ts2 = return ()
                       | otherwise = throwError (TypeMisMatchList s ts1 ts2)

shouldBeValue :: Monad m => Value -> Type -> ExceptT TypeError m ()
shouldBeValue v t1 = shouldBe (render $ pprintV 0 v) (getType v) t1

shouldBeIn :: Monad m => Type -> [Type] -> ExceptT TypeError m ()
shouldBeIn t1 ts = 
    if t1 `elem` ts then return () else throwError (TypeMisUse t1 ts)

shouldBePair :: Monad m => String -> Type -> ExceptT TypeError m (Type,Type)
shouldBePair _ (TPair t1 t2) = return (t1,t2)
shouldBePair s _ = throwError (OtherError $ "expecting pair :" ++ s)

convertP :: Monad m => SynEnv -> U.Type -> ExceptT TypeError m Type
convertP synEnv ty =
    withExceptT Synonym (desugarType synEnv ty) >>= 
    fix (\go ty -> case ty of
        U.TInt -> return TInt
        U.TBool -> return TBool
        U.TPair ty1 ty2 -> TPair <$> go ty1 <*> go ty2
        U.TFun tys ty -> TFun <$> mapM go tys <*> go ty
        _ -> throwError $ OtherError $ "convertP: unsupported conversion: " ++ render (U.pprintT 0 ty))

convertE :: MonadId m => SynEnv -> Env -> Type -> U.Exp -> ExceptT TypeError m Exp
convertE synEnv env ty _e = case _e of
    U.Value v -> do
        v' <- convertV env v
        v' `shouldBeValue` ty
        return $ Value v'
    U.Let x lv e -> do
        lv' <- convertLV synEnv env lv
        let ty' = getType lv'
        e' <- Let ty (Id ty' x) lv' <$> convertE synEnv (M.insert x ty' env) ty e
        return e'
    U.Assume v e -> do
        v' <- convertV env v
        shouldBeValue  v' TBool
        Assume ty v' <$> convertE synEnv env ty e
    U.Lambda xs e -> do
        fdef <- convertLambda synEnv env xs e ty
        return $ Fun fdef
    U.Fail -> pure $ Fail ty
    U.Branch e1 e2 -> do
        i <- freshInt
        Branch ty i <$> convertE synEnv env ty e1 <*> convertE synEnv env ty e2

convertLambda :: (MonadId m) => SynEnv -> Env -> [U.Id] -> U.Exp -> Type -> ExceptT TypeError m FunDef
convertLambda synEnv env args body (TFun ts t2) = do
    i <- freshInt
    let env' = foldr (uncurry M.insert) env (zip args ts)
    FunDef i (zipWith Id ts args) <$> convertE synEnv env' t2 body
convertLambda _ _ xs _ _ = throwError $ OtherError $ "Expecting function:" ++ show xs


convertLV :: (MonadId m) => SynEnv -> Env -> U.LetValue -> ExceptT TypeError m (LetValue)
convertLV synEnv env lv = case lv of
    U.LValue v -> do
        v' <- convertV env v
        return $ LValue v'
    U.LRand -> 
        return LRand
    U.LApp f vs -> do
        vs' <- mapM (convertV env) vs
        case M.lookup f env of
            Just ty -> do
                let ts' = map getType vs'
                case ty of
                    TFun ts t2 -> do
                        shouldBeList (show (map (pprintV 0) vs')) ts ts'
                        let f' = Id ty f
                        i <- freshInt
                        return $ LApp t2 i f' vs'
                    _ -> throwError $ OtherError $ "Expecting function" ++ f
            Nothing -> throwError $ UndefinedVariable f
    U.LExp ptyp (U.Lambda x e) -> do
        ty <- convertP synEnv ptyp
        fdef <- convertLambda synEnv env x e ty
        return (LFun fdef)
    U.LExp ptyp e -> do
        ty <- convertP synEnv ptyp
        i <- freshInt
        lv <- LExp i <$> convertE synEnv env ty e
        return lv
                

convertV :: Monad m => Env -> U.Value -> ExceptT TypeError m Value
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

