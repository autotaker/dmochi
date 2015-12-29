{-# LANGUAGE FlexibleContexts #-}
module ML.TypeCheck where
import qualified Data.Map as M
import Control.Applicative
import Control.Monad.Except
import ML.Syntax.Typed 
import qualified ML.Syntax.UnTyped as U
import Text.PrettyPrint
import ML.PrettyPrint.Typed 
import Debug.Trace
import Id
instance Show TypeError where
    show (UndefinedVariable s) = "UndefinedVariables: "++ s
    show (TypeMisMatch s t1 t2)   = "TypeMisMatch: " ++ show t1 ++ " should be " ++ show t2 ++ ". context :" ++ s
    show (TypeMisUse t1 t2)     = "TypeUse: " ++ show t1 ++ " should be in" ++ show t2
    show (OtherError s)         = "OtherError: " ++ s

type Env = M.Map String Type
data TypeError = UndefinedVariable String 
               | TypeMisMatch String Type Type
               | TypeMisUse   Type [Type]
               | OtherError String

fromUnTyped :: (Applicative m,MonadError TypeError m, MonadId m) => U.Program -> m Program
fromUnTyped (U.Program fs t) = do
    fs' <- mapM (\(x,p,e) -> (,,) x <$> convertP p <*> pure e) fs
    let tenv = M.fromList [ (x,getType p) | (x,p,_) <- fs' ]
    fs'' <- mapM (\(x,p,e) -> 
        (,,) (Id (getType p) x) p <$> convertE tenv (getType p) e) fs'
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

convertP :: (Applicative m,MonadError TypeError m) => U.PType -> m PType
convertP = go M.empty where
    base f env ty ps = 
        f <$> mapM (\(x,p) -> do
            p' <- convertV (M.insert x ty env) p
            shouldBeValue p' TBool
            return (Id ty x,p')) ps
    go env (U.PInt ps) = base PInt env TInt ps
    go env (U.PBool ps) = base PBool env TBool ps
    go env (U.PPair p (x,f)) =  do
        p' <- go env p
        let ty = getType p'
        f' <- go (M.insert x ty env) f
        return $ PPair (TPair ty (getType f')) p' (Id ty x,f')
    go env (U.PFun p (x,f)) = do
        p' <- go env p
        let ty = getType p'
        f' <- go (M.insert x ty env) f
        return $ PFun (TFun ty (getType f')) p' (Id ty x,f')

convertE :: (Applicative m,MonadError TypeError m, MonadId m) => Env -> Type -> U.Exp -> m Exp
convertE env ty _e = case _e of
    U.Value v -> do
        v' <- convertV env v
        v' `shouldBeValue` ty
        return $ Value v'
    U.Let x lv e -> do
        lv' <- convertLV env lv
        let ty' = getType lv'
        Let ty (Id ty' x) lv' <$> convertE (M.insert x ty' env) ty e
    U.Assume v e -> do
        v' <- convertV env v
        shouldBeValue  v' TBool
        Assume ty v' <$> convertE env ty e
    U.Lambda x e -> do
        case ty of
            TFun t1 t2 -> do
                i <- freshInt
                Lambda ty i (Id t1 x) <$> convertE (M.insert x t1 env) t2 e
            _ -> throwError $ OtherError "Expecting function"
    U.Fail -> pure $ Fail ty
    U.Branch e1 e2 -> Branch ty <$> convertE env ty e1 <*> convertE env ty e2

convertLV :: (Applicative m,MonadError TypeError m, MonadId m) => Env -> U.LetValue -> m LetValue
convertLV env lv = case lv of
    U.LValue v -> LValue <$> convertV env v
    U.LApp x vs -> do
        vs' <- mapM (convertV env) vs
        case M.lookup x env of
            Just ty -> do
                ty' <- foldM (\tf v -> 
                    case tf of
                        TFun t1 t2 -> t2 <$ shouldBeValue v  t1
                        _ -> throwError $ OtherError $ "Excepting function") ty vs'
                return $ LApp ty' (Id ty x) vs'
            Nothing -> throwError $ UndefinedVariable x
    U.LExp ptyp e -> do
        ptyp' <- convertP ptyp
        LExp ptyp' <$> convertE env (getType ptyp') e
                

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
                getType v1' `shouldBeIn` [TInt,TBool]
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

