{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, Rank2Types, GADTs, TypeOperators, BangPatterns #-}
module Language.DMoCHi.ML.TypeCheck where
import qualified Data.Map as M
import Prelude hiding(mapM)
import Control.Monad.Except
import Control.Monad.RWS.Strict
import qualified Data.DList as DL
-- import Text.PrettyPrint
import Language.DMoCHi.ML.Syntax.Typed 
import Language.DMoCHi.ML.Syntax.Base
import Language.DMoCHi.ML.Syntax.Type
import qualified Language.DMoCHi.ML.Alpha as U
import qualified Language.DMoCHi.ML.Syntax.UnTyped as U(SynName, SynonymDef(..), Type(..), Lit(..))
import qualified Language.DMoCHi.Common.Id as Id
import Language.DMoCHi.Common.Id(MonadId(..), UniqueKey, FreshIO)
import Language.DMoCHi.ML.DesugarSynonym
--import Debug.Trace

instance Show TypeError where
    show (UndefinedVariable s)      = "UndefinedVariables: "++ s
    show (TypeMisMatch p t1 t2)     = "TypeMisMatch: " ++ show t1 ++ " should be " ++ show t2 ++ ". context :" ++ show p
    show (ArityMisMatch p t1 t2)    = "ArityMismatch: " ++ show t1 ++ " should be  " ++ show t2 ++ ". context :" ++ show p
    show (Synonym err)  = "SynonymError: " ++ show err
    show (Infer err)  = "InferError: " ++ show err
    show (OtherError s) = "OtherError: " ++ s

type Env = M.Map (Id.Id String) Type
type Annot = M.Map UniqueKey Type
type SynEnv = M.Map U.SynName U.SynonymDef
data TypeError = UndefinedVariable String  
               | TypeMisMatch (UniqueKey,Env) Type Type
               | ArityMisMatch (UniqueKey,Env) Int Int
               | Synonym  SynonymError
               | Infer  InferError
               | OtherError String

fromUnTyped :: U.Program -> ExceptT TypeError FreshIO Program
fromUnTyped prog = do
    annot <- withExceptT Infer (infer prog)
    let env = M.fromList [ (f, annot M.! key) | (f, _, U.Exp _ _ key) <- U.functions prog ]
    fs' <- forM (U.functions prog) $ \(f, _, e) -> do
        Exp l arg sty key <- convertE annot env e
        case (l, arg) of
            (SLambda, (xs, e)) -> return (TId sty f, key, xs, e)
            _ -> throwError $ OtherError "RHS of definition should be a function"
    e0 <- convertE annot env (U.mainTerm prog)
    return $ Program { functions = fs', mainTerm = e0 }

type TSubst = M.Map String U.Type 
type InferM m = RWST (M.Map U.SynName U.SynonymDef) (DL.DList (UniqueKey, U.Type)) TSubst (ExceptT InferError m)

data InferError = RecursiveType
                | SynError SynonymError
                | CannotUnify
                deriving Show

updateSubst :: MonadState TSubst m => String -> U.Type -> m ()
updateSubst key value = do
    theta <- get 
    put $! M.insert key value theta

subst :: (MonadState TSubst m) => U.Type -> m U.Type
subst U.TInt = pure U.TInt
subst U.TBool = pure U.TBool
subst (U.TPair ty1 ty2) = U.TPair <$> subst ty1 <*> subst ty2
subst (U.TFun ts ty) = U.TFun <$> mapM subst ts <*> subst ty
subst (U.TSyn ts synName) = U.TSyn <$> mapM subst ts <*> pure synName
subst (U.TVar x) = do
    theta <- get
    case M.lookup x theta of
        Just ty -> do
            ty' <- subst ty
            updateSubst x ty'
            return ty'
        Nothing -> return (U.TVar x)

unify :: (MonadError InferError m, 
          MonadReader (M.Map String U.SynonymDef) m,
          MonadState TSubst m) => U.Type -> U.Type -> m ()
unify U.TInt U.TInt = return ()
unify U.TBool U.TBool = return ()
unify (U.TPair ty1 ty2) (U.TPair ty3 ty4) = unify ty1 ty3 >> unify ty2 ty4
unify (U.TFun tys1 ty1) (U.TFun tys2 ty2) = zipWithM_ unify tys1 tys2 >> unify ty1 ty2
unify (U.TSyn ts name) ty = do
    synEnv <- ask
    let synDef = synEnv M.! name
        n = length $ U.typVars synDef
        m = length ts
    when (n /= m) $ throwError (SynError $ ArgLengthDiffer n m)
    ty' <- case runExcept (substType (M.fromList $ zip (U.typVars synDef) ts) (U.synDef synDef)) of
        Left err -> throwError $ SynError err
        Right ty' -> return ty'
    unify ty' ty
unify ty1 ty2@(U.TSyn _ _) = unify ty2 ty1
unify (U.TVar x) ty2 = do
    theta <- get
    case M.lookup x theta of
        Just ty1' -> unify ty1' ty2
        Nothing   -> do
            ty2' <- subst ty2
            case ty2' of
                U.TVar y | x == y -> return ()
                _ | x `elemType` ty2' -> throwError RecursiveType
                  | otherwise -> updateSubst x ty2'
unify ty1 ty2@(U.TVar _) = unify ty2 ty1
unify U.TInt _ = throwError CannotUnify 
unify U.TBool _ = throwError CannotUnify
unify (U.TPair _ _) _ = throwError CannotUnify
unify (U.TFun _ _) _ = throwError CannotUnify
    
elemType :: String -> U.Type -> Bool
elemType _ U.TInt = False
elemType _ U.TBool = False
elemType x (U.TPair ty1 ty2) = elemType x ty1 || elemType x ty2
elemType x (U.TFun tys ty) = any (elemType x) (ty:tys)
elemType x (U.TVar y) = x == y
elemType x (U.TSyn tys _) = any (elemType x) tys

infer :: (MonadId m, MonadIO m) => U.Program -> ExceptT InferError m (M.Map UniqueKey Type)
infer prog = do
    let synEnv = M.fromList [ (U.synName syn, syn) | syn <- U.synonyms prog ]
    (res,_,_) <- runRWST (do
        ((), annot) <- listen $ do
                env <- fmap M.fromList $ mapM (\(f,ty',_) -> do
                            ty <- U.TVar <$> Id.freshId "t"
                            unify ty ty'
                            return (f, ty)) (U.functions prog)
                forM_ (U.functions prog) $ \(f,_,e) -> inferE env e >>= unify (env M.! f)
                ty <- inferE env (U.mainTerm prog)
                unify ty U.TInt
        let annotEnv = M.fromList (DL.toList annot)
        forM_ (U.typeAnn prog) $ \(key, ty) -> unify ty (annotEnv M.! key)
        fmap M.fromList $ mapM (\(key,ty) -> do
            ty' <- subst ty
            case runExcept (convertType synEnv ty') of
                Left err -> throwError $ SynError err
                Right v -> return (key,v)) (DL.toList annot)) synEnv M.empty
    return res
             

inferE :: (MonadId m, MonadIO m) => M.Map (Id.Id String) U.Type -> U.Exp -> InferM m U.Type
inferE env (U.Exp l arg key) = do
    tvar <- U.TVar <$> Id.freshId "ty"
    tell (DL.singleton (key, tvar))
    ty <- case (l, arg) of
        (SLiteral, U.CInt _) -> pure U.TInt
        (SLiteral, U.CBool _) -> pure U.TBool
        (SVar, x) -> return $! env M.! x
        (SBinary, BinArg op e1 e2) -> do
            ty1 <- inferE env e1
            ty2 <- inferE env e2
            let f :: (MonadId m, MonadIO m) => U.Type -> InferM m ()
                f ty = unify ty1 ty >> unify ty2 ty
            case op of
                SAdd -> f U.TInt >> pure U.TInt
                SSub -> f U.TInt >> pure U.TInt
                SEq  -> f U.TInt >> pure U.TBool
                SLt  -> f U.TInt >> pure U.TBool
                SGt  -> f U.TInt >> pure U.TBool
                SLte -> f U.TInt >> pure U.TBool
                SGte -> f U.TInt >> pure U.TBool
                SAnd -> f U.TBool >> pure U.TBool
                SOr  -> f U.TBool >> pure U.TBool
        (SUnary, UniArg op e1) -> do
            ty1 <- inferE env e1
            case op of
                SFst -> do
                    ty_pair <- U.TPair <$> pure tvar <*> (U.TVar <$> Id.freshId "ty")
                    tvar <$ unify ty1 ty_pair
                SSnd -> do
                    ty_pair <- U.TPair <$> (U.TVar <$> Id.freshId "ty") <*> pure tvar
                    tvar <$ unify ty1 ty_pair
                SNeg -> U.TInt <$ unify ty1 U.TInt
                SNot -> U.TBool <$ unify ty1 U.TBool
        (SPair, (e1, e2)) -> U.TPair <$> inferE env e1 
                                     <*> inferE env e2
        (SLambda, (xs,e)) -> do
            tys <- mapM (\_ -> U.TVar <$> Id.freshId "t") xs
            let env' = foldr (uncurry M.insert) env (zip xs tys)
            U.TFun tys <$> inferE env' e
        (SApp, (f, es)) -> do
            tys <- mapM (inferE env) es
            let ty_f = U.TFun tys tvar
            tvar <$ unify (env M.! f) ty_f
        (SLet, (x, e1, e2)) -> do
            ty_x <- inferE env e1
            let env' = M.insert x ty_x env
            inferE env' e2
        (SAssume, (cond, e)) -> do
            ty <- inferE env cond
            unify ty U.TBool
            inferE env e
        (SIf, (cond, e1, e2)) -> do
            ty <- inferE env cond
            unify ty U.TBool
            ty1 <- inferE env e1
            ty2 <- inferE env e2
            ty1 <$ unify ty1 ty2
        (SBranch, (e1,e2)) -> do
            ty1 <- inferE env e1
            ty2 <- inferE env e2
            ty1 <$ unify ty1 ty2
        (SFail, _) -> pure tvar
        (SOmega, _) -> pure tvar
        (SRand, _) -> pure U.TInt
    ty <$ unify tvar ty

shouldBe :: (UniqueKey, Env) -> Type -> Type-> ExceptT TypeError FreshIO ()
shouldBe s t1 t2 =
    unless (t1 == t2) $ throwError (TypeMisMatch s t1 t2)

convertType :: forall m . Monad m => SynEnv -> U.Type -> ExceptT SynonymError m Type
convertType synEnv ty = do
    ty <- desugarType synEnv ty
    go ty 
        where
        go :: U.Type -> ExceptT SynonymError m Type
        go ty = case ty of
            U.TInt -> return TInt
            U.TBool -> return TBool
            U.TPair ty1 ty2 -> go ty1 >>= \sty1 -> go ty2 >>= \sty2 -> return (TPair sty1 sty2)
            U.TFun tys ty -> do
                stys <- mapM go tys
                go ty >>=  \sty -> return (TFun stys sty)
            U.TSyn _ _ -> error "convertType: undesugared synonym"
            U.TVar _x -> return TInt

convertE :: Annot -> Env -> U.Exp -> ExceptT TypeError FreshIO Exp
convertE annot env (U.Exp l arg key) = 
    let !sty = annot M.! key in
    case (l,arg) of
        (SLiteral, U.CInt _)  -> do
            shouldBe (key,env) sty TInt
            return $ Exp l arg sty key
        (SLiteral, U.CBool _) -> do
            shouldBe (key,env) sty TBool
            return $ Exp l arg sty key
        (SVar, x) -> do
            let !sty' = env M.! x
            shouldBe (key,env) sty sty'
            return $ Exp l (TId sty' x) sty key
        (SBinary, BinArg op e1 e2) ->  do
            e1'@(Exp _ _ sty1 key1) <- convertE annot env e1
            e2'@(Exp _ _ sty2 key2) <- convertE annot env e2
            typeOfBinOp env op sty1 key1 sty2 key2 (\sty' -> do
                shouldBe (key,env) sty sty'
                return $ Exp l (BinArg op e1' e2') sty key)
        (SUnary, UniArg op e1) ->  do
            e1'@(Exp _ _ sty1 key1) <- convertE annot env e1
            typeOfUniOp env op sty1 key1 (\sty' -> do
                shouldBe (key,env) sty sty'
                return $ Exp l (UniArg op e1') sty key)
        (SPair, (e1, e2)) -> do
            e1'@(Exp _ _ sty1 _) <- convertE annot env e1
            e2'@(Exp _ _ sty2 _) <- convertE annot env e2
            shouldBe (key,env) sty (TPair sty1 sty2)
            return $ Exp l (e1', e2') sty key
        (SLambda, (xs, e1)) -> do
            case sty of
                TFun ty_args sty1' -> do
                    let n = length ty_args
                        m = length xs
                    when (length ty_args /= length xs) $ 
                        throwError $ ArityMisMatch (key,env) n m
                    let env' = foldr (uncurry M.insert) env $ zip xs ty_args
                        ys = zipWith (\x ty -> TId ty x) xs ty_args
                    e1'@(Exp _ _ sty1 key1) <- convertE annot env' e1
                    shouldBe (key1,env) sty1 sty1'
                    return $ Exp l (ys, e1') sty key
                _ -> throwError $ OtherError $ "This function expected to have type " ++ show sty
        (SApp, (f, es)) -> do
            case env M.! f of
                sty_f@(TFun tys sty') -> do
                    es' <- mapM (convertE annot env) es
                    let g :: Exp -> Type -> ExceptT TypeError FreshIO ()
                        g (Exp _ _ sty_i key_i) sty_i' = 
                            void $ shouldBe (key_i,env) sty_i sty_i'
                    zipWithM_ g es' tys
                    let n = length es
                        m = length tys
                    when (n /= m) $ throwError $ ArityMisMatch (key,env) n m
                    shouldBe (key,env) sty sty'
                    return $ Exp l (TId sty_f f, es') sty key
                sty_f -> throwError $ OtherError $ "App" ++ show sty_f
        (SLet, (x, e1, e2)) -> do
            e1'@(Exp _ _ sty1 _) <- convertE annot env e1
            let env' = M.insert x sty1 env
            e2'@(Exp _ _ sty2 _) <- convertE annot env' e2
            shouldBe (key,env) sty sty2
            return $ Exp l (TId sty1 x, e1', e2') sty key
        (SAssume, (e1, e2)) -> do
            e1'@(Exp _ _ sty1 key1) <- convertE annot env e1
            shouldBe (key1,env) sty1 TBool
            e2'@(Exp _ _ sty2 _) <- convertE annot env e2
            shouldBe (key,env) sty sty2
            return $ Exp l (e1', e2') sty key
        (SIf, (e1, e2, e3)) -> do
            e1'@(Exp _ _ sty1 key1) <- convertE annot env e1
            shouldBe (key1,env) sty1 TBool
            e2'@(Exp _ _ sty2 _) <- convertE annot env e2
            shouldBe (key,env) sty sty2
            e3'@(Exp _ _ sty3 _) <- convertE annot env e3
            shouldBe (key,env) sty sty3
            return $ Exp l (e1', e2', e3') sty key
        (SBranch, (e2, e3)) -> do
            e2'@(Exp _ _ sty2 _) <- convertE annot env e2
            shouldBe (key,env) sty sty2
            e3'@(Exp _ _ sty3 _) <- convertE annot env e3
            shouldBe (key,env) sty sty3
            return $ Exp l (e2', e3') sty key
        (SFail, ()) -> return $ Exp l () sty key
        (SOmega, ()) -> return $ Exp l () sty key
        (SRand, ()) -> shouldBe (key,env) sty TInt >> return (Exp l () sty key)
                
typeOfUniOp :: Env -> SUniOp op -> Type -> UniqueKey -> (Type -> ExceptT TypeError FreshIO b) -> ExceptT TypeError FreshIO b
typeOfUniOp _ SFst sty1 _key1 k = do
    case sty1 of
        TPair sty' _ -> k sty'
        _ -> throwError $ OtherError $ "Expected a pair type but found " ++ show sty1
typeOfUniOp _ SSnd sty1 _key1 k = do
    case sty1 of
        TPair _ sty' -> k sty'
        _ -> throwError $ OtherError $ "Expected a pair type but found " ++ show sty1
typeOfUniOp env SNot sty1 key1 k = do
    shouldBe (key1,env) sty1 TBool
    k TBool
typeOfUniOp env SNeg sty1 key1 k = do
    shouldBe (key1,env) sty1 TInt
    k TInt
        
typeOfBinOp :: Env -> SBinOp op -> Type -> UniqueKey -> Type -> UniqueKey -> 
               (Type -> ExceptT TypeError FreshIO b) -> ExceptT TypeError FreshIO b 
typeOfBinOp env op sty1 key1 sty2 key2 k = (case op of
    SAdd -> intOp TInt
    SSub -> intOp TInt
    SEq -> intOp TBool
    SLt -> intOp TBool
    SGt -> intOp TBool
    SLte -> intOp TBool
    SGte -> intOp TBool
    SAnd -> boolOp
    SOr  -> boolOp
    ) where intOp sty = do
                shouldBe (key1,env) sty1 TInt
                shouldBe (key2,env) sty2 TInt
                k sty
            boolOp = do
                shouldBe (key1,env) sty1 TBool
                shouldBe (key2,env) sty2 TBool
                k TBool
    
