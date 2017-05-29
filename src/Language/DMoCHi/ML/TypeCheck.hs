{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, Rank2Types, GADTs, TypeOperators, BangPatterns #-}
module Language.DMoCHi.ML.TypeCheck where
import qualified Data.Map as M
import Prelude hiding(mapM)
import Control.Monad.Except
import Control.Monad.RWS.Strict
import qualified Data.DList as DL
import Data.IORef
-- import Text.PrettyPrint
import Language.DMoCHi.ML.Syntax.Typed 
import Language.DMoCHi.ML.Syntax.Base
import Language.DMoCHi.ML.Syntax.Type
--import Text.PrettyPrint.HughesPJClass
import qualified Language.DMoCHi.ML.Alpha as U
import qualified Language.DMoCHi.ML.Syntax.UnTyped as U(AnnotVar(..),SynName, SynonymDef(..), Type(..), TypeScheme(..), Lit(..), toTypeScheme, matchTypeScheme, matchType)
import qualified Language.DMoCHi.Common.Id as Id
import Language.DMoCHi.Common.Id(MonadId(..), UniqueKey, FreshIO, getUniqueKey)
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
type SynEnv = M.Map U.SynName U.SynonymDef

type UExp = U.Exp (Maybe U.Type)
data TypeError = UndefinedVariable String  
               | TypeMisMatch (UniqueKey,Env) Type Type
               | ArityMisMatch (UniqueKey,Env) Int Int
               | Synonym  SynonymError
               | Infer  InferError
               | OtherError String
               deriving(Eq)

fromUnTyped :: U.Program (Maybe U.Type) -> ExceptT TypeError FreshIO Program
fromUnTyped _prog = do
    prog <- withExceptT Infer (infer _prog)
    let synEnv = M.fromList [ (U.synName syn, syn) | syn <- U.synonyms prog ]
    env <- fmap M.fromList $ forM (U.functions prog) $ \(f, tyS, _) -> do
        case convertType synEnv (U.typeBody tyS) of
            Right sty -> pure (varName f, sty)
            Left err -> throwError (Synonym err)
    fs' <- forM (U.functions prog) $ \(f, _, e) -> do
        Exp l arg sty key <- convertE synEnv env e
        case (l, arg) of
            (SLambda, (xs, e)) -> return (TId sty (U.varName f), key, xs, e)
            _ -> throwError $ OtherError "RHS of definition should be a function"
    e0 <- convertE synEnv env (U.mainTerm prog)
    return $ Program { functions = fs', mainTerm = e0 }

type TSubst = M.Map String U.Type 
type InferM m = RWST (M.Map U.SynName U.SynonymDef) (DL.DList (UniqueKey, U.Type)) TSubst (ExceptT InferError m)

data InferError = RecursiveType
                | SynError SynonymError
                | SchemeError U.TypeScheme U.TypeScheme
                | CannotUnify
                deriving (Show,Eq)

updateSubst :: MonadState TSubst m => String -> U.Type -> m ()
updateSubst key value = do
    theta <- get 
    put $! M.insert key value theta

subst :: (MonadState TSubst m) => U.Type -> m U.Type
subst U.TInt = pure U.TInt
subst U.TBool = pure U.TBool
subst U.TUnit = pure U.TUnit
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
unify U.TUnit U.TUnit = return ()
unify (U.TPair ty1 ty2) (U.TPair ty3 ty4) = unify ty1 ty3 >> unify ty2 ty4
unify (U.TFun tys1 ty1) (U.TFun tys2 ty2) = 
    let n1 = length tys1 
        n2 = length tys2
    in
    if n1 == n2 
    then zipWithM_ unify tys1 tys2 >> unify ty1 ty2
    else if n1 < n2 then do
        zipWithM_ unify tys1 tys2
        unify ty1 (U.TFun (drop n1 tys2) ty2)
    else do
        zipWithM_ unify tys1 tys2
        unify (U.TFun (drop n2 tys1) ty1) ty2
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
unify U.TInt _  = pure ()
unify U.TBool _ = pure ()
unify U.TUnit _ = pure ()
unify (U.TPair _ _) _ = pure ()
unify (U.TFun _ _) _ = pure ()
    
elemType :: String -> U.Type -> Bool
elemType _ U.TInt = False
elemType _ U.TBool = False
elemType _ U.TUnit = False
elemType x (U.TPair ty1 ty2) = elemType x ty1 || elemType x ty2
elemType x (U.TFun tys ty) = any (elemType x) (ty:tys)
elemType x (U.TVar y) = x == y
elemType x (U.TSyn tys _) = any (elemType x) tys

concretize :: MonadId m => U.TypeScheme -> m ([String], U.Type)
concretize (U.TypeScheme [] ty) = pure ([],ty)
concretize (U.TypeScheme args ty) = do
    names <- mapM Id.freshId args
    let rho = M.fromList $ zip args (map U.TVar names)
    return (names, substWith rho ty)

substWith :: M.Map String U.Type -> U.Type -> U.Type
substWith rho = go
    where
    go U.TInt  = U.TInt
    go U.TBool = U.TBool
    go U.TUnit = U.TUnit
    go (U.TVar x) = case M.lookup x rho of
        Just v -> v
        Nothing -> U.TVar x
    go (U.TPair ty1 ty2) = U.TPair (go ty1) (go ty2)
    go (U.TFun ts ty) = U.TFun (map go ts) (go ty)
    go (U.TSyn ts synName) = U.TSyn (map go ts) synName

concretize' :: MonadId m => U.TypeScheme -> m U.Type
concretize' = fmap snd . concretize

copyPoly :: forall m. (MonadId m, MonadIO m) => U.Program U.Type -> ExceptT InferError m (U.Program U.Type)
copyPoly prog = do
    copyEnvRef <- liftIO $ newIORef M.empty
    copyAssocRef <- liftIO $ newIORef []
    let bindInfo = M.fromList [ (U.varName f, (tyS, e)) | (f, tyS, e) <- U.functions prog ]
    let renamePoly :: [Id.Id String] -> U.Var U.Type -> [U.Type] -> ExceptT InferError m (U.Var U.Type)
        renamePoly stack x tys = do
            copyEnv <- liftIO $ readIORef copyEnvRef
            case M.lookup (U.varName x,tys) copyEnv of
                Just x' -> pure x'
                Nothing | elem (U.varName x) stack -> throwError RecursiveType
                        | otherwise -> do
                        let (tyS, e) = bindInfo M.! (U.varName x)
                            stack' = U.varName x : stack
                        x' <- U.refresh x 
                        liftIO $ writeIORef copyEnvRef (M.insert (U.varName x,tys) x' copyEnv)
                        e' <- go (stack', M.fromList (zip (U.typeArgs tyS) tys)) e
                        liftIO $ modifyIORef copyAssocRef ((x',e'):)
                        return x'
        go :: ([Id.Id String], M.Map String U.Type) -> U.Exp U.Type -> ExceptT InferError m (U.Exp U.Type)
        go !st@(stack,rho) (U.Exp l arg (_ty,_key)) = do
            key' <- freshKey
            let ty = substWith rho _ty
            case (l, arg) of
                (SLiteral, _) -> pure (U.Exp l arg (ty, key'))
                (SVar, x) -> case M.lookup (U.varName x) bindInfo of
                    Nothing -> pure (U.Exp SVar (x{ U.varType = ty}) (ty,key'))
                    Just (tyS, _) -> do
                        case U.matchType (U.typeBody tyS) ty of
                            Just match -> do
                                let tys = map (match M.!) (U.typeArgs tyS)
                                x' <- renamePoly stack (x{ U.varType = ty }) tys
                                pure (U.Exp SVar x' (ty,key'))
                            Nothing -> throwError CannotUnify
                (SBinary, BinArg op e1 e2) -> do
                    e1' <- go st e1
                    e2' <- go st e2
                    pure $ U.Exp l (BinArg op e1' e2') (ty,key')
                (SUnary, UniArg op e1) -> do
                    e1' <- go st e1
                    pure $ U.Exp l (UniArg op e1') (ty,key')
                (SPair, (e1, e2)) -> do
                    e1' <- go st e1
                    e2' <- go st e2
                    pure $ U.Exp l (e1', e2') (ty,key')
                (SLambda, (xs, e)) -> do
                    e' <- go st e
                    let ys = map (fmap (substWith rho)) xs
                    pure $ U.Exp l (ys, e') (ty, key')
                (SApp, (e, es)) -> do
                    e' <- go st e
                    es' <- mapM (go st) es
                    pure $ U.Exp l (e', es') (ty, key')
                (SLet, (x, e1, e2)) -> do
                    e1' <- go st e1
                    e2' <- go st e2
                    let y = fmap (substWith rho) x
                    pure $ U.Exp l (y, e1', e2') (ty, key')
                (SLetRec, (fs, e)) -> do
                    fs' <- mapM (\(f, ef) -> (fmap (substWith rho) f,) <$> go st ef) fs
                    e' <- go st e
                    pure $ U.Exp l (fs', e') (ty, key')
                (SAssume, (cond, e)) -> do
                    cond' <- go st cond
                    e' <- go st e
                    pure $ U.Exp l (cond', e') (ty, key')
                (SIf, (cond, e1, e2)) -> do
                    cond' <- go st cond
                    e1' <- go st e1
                    e2' <- go st e2
                    pure $ U.Exp l (cond', e1', e2') (ty, key')
                (SBranch, (e1, e2)) -> do
                    e1' <- go st e1
                    e2' <- go st e2
                    pure $ U.Exp l (e1', e2') (ty, key')
                (SFail,  _) -> pure (U.Exp l arg (ty, key'))
                (SOmega, _) -> pure (U.Exp l arg (ty, key'))
                (SRand,  _) -> pure (U.Exp l arg (ty, key'))
    e0 <- go ([], M.empty) (U.mainTerm prog)
    fs <- liftIO $ readIORef copyAssocRef
    let prog' = prog { U.functions = map (\(f, e) -> (f, U.TypeScheme [] (varType f), e)) fs
                     , U.mainTerm = e0 }
    return prog'

annotType :: U.Exp U.Type -> U.Type
annotType (U.Exp _ _ (ty,_)) = ty

infer :: (MonadId m, MonadIO m) => U.Program (Maybe U.Type)-> ExceptT InferError m (U.Program U.Type)
infer prog = do
    let synEnv = M.fromList [ (U.synName syn, syn) | syn <- U.synonyms prog ]
    (prog,_,_) <- runRWST (do
        let env = M.fromList [ (U.varName f, tyS) | (f, tyS, _) <- U.functions prog ]
        fs <- forM (U.functions prog) $ \(f,tyS,e) -> do
            e' <- inferE env e
            let ty2 = U.typeBody tyS
            unify (annotType e') ty2
            ty2' <- subst ty2
            e' <- traverse subst e'
            let tyS' = U.toTypeScheme ty2'
            case U.matchTypeScheme tyS tyS' of
                Nothing -> throwError (SchemeError tyS tyS')
                Just xs -> return (fmap (const ty2') f, tyS'{ U.typeArgs = xs } , e')
        e0 <- inferE env (U.mainTerm prog)
        unify (annotType e0) U.TUnit
        e0' <- traverse subst e0
        return $ U.Program fs (U.synonyms prog) e0') synEnv M.empty
    copyPoly prog


inferE :: (MonadId m, MonadIO m) => M.Map (Id.Id String) U.TypeScheme -> UExp -> InferM m (U.Exp U.Type)
inferE env (U.Exp l arg (_,key)) = do
    tvar <- U.TVar <$> Id.freshId "ty"
    tell (DL.singleton (key, tvar))
    let insertTy (x,ty) env = M.insert x (U.TypeScheme [] ty) env
    e <- case (l, arg) of
        (SLiteral, U.CInt _)  -> pure $ U.Exp l arg (U.TInt,  key)
        (SLiteral, U.CBool _) -> pure $ U.Exp l arg (U.TBool, key)
        (SLiteral, U.CUnit)   -> pure $ U.Exp l arg (U.TUnit, key)
        (SVar, x) -> concretize' (env M.! U.varName x) >>= \ty ->
                     pure $ U.Exp l (fmap (const ty) x) (ty, key)
        (SBinary, BinArg op e1 e2) -> do
            e1' <- inferE env e1
            e2' <- inferE env e2
            let f :: (MonadId m, MonadIO m) => U.Type -> InferM m ()
                f ty = unify (annotType e1') ty >> unify (annotType e2') ty
            ty <- case op of
                SAdd -> f U.TInt >> pure U.TInt
                SSub -> f U.TInt >> pure U.TInt
                SDiv -> f U.TInt >> pure U.TInt
                SMul -> f U.TInt >> pure U.TInt
                SEq  -> f U.TInt >> pure U.TBool
                SNEq -> f U.TInt >> pure U.TBool
                SLt  -> f U.TInt >> pure U.TBool
                SGt  -> f U.TInt >> pure U.TBool
                SLte -> f U.TInt >> pure U.TBool
                SGte -> f U.TInt >> pure U.TBool
                SAnd -> f U.TBool >> pure U.TBool
                SOr  -> f U.TBool >> pure U.TBool
            pure $ U.Exp l (BinArg op e1' e2') (ty, key)
        (SUnary, UniArg op e1) -> do
            e1' <- inferE env e1
            let ty1 = annotType e1'
            ty <- case op of
                SFst -> do
                    ty_pair <- U.TPair <$> pure tvar <*> (U.TVar <$> Id.freshId "ty")
                    tvar <$ unify ty1 ty_pair
                SSnd -> do
                    ty_pair <- U.TPair <$> (U.TVar <$> Id.freshId "ty") <*> pure tvar
                    tvar <$ unify ty1 ty_pair
                SNeg -> U.TInt <$ unify ty1 U.TInt
                SNot -> U.TBool <$ unify ty1 U.TBool
            pure $ U.Exp l (UniArg op e1') (ty, key)
        (SPair, (e1, e2)) -> do
            e1' <- inferE env e1
            e2' <- inferE env e2
            pure $ U.Exp l (e1',e2') (U.TPair (annotType e1') (annotType e2'), key)
        (SLambda, (xs,e)) -> do
            ys <- mapM (traverse (\_ -> U.TVar <$> Id.freshId "t")) xs
            let tys = map varType ys
            let env' = foldr insertTy env (zip (map U.varName xs) tys)
            e' <- inferE env' e
            pure $ U.Exp l (ys, e') (U.TFun tys (annotType e'), key)
        (SApp, (e, es)) -> do
            e' <- inferE env e
            es' <- mapM (inferE env) es
            let ty_f = U.TFun (map annotType es') tvar
            unify (annotType e') ty_f
            pure $ U.Exp l (e', es') (ty_f, key)
        (SLet, (x, e1, e2)) -> do
            e1' <- inferE env e1
            let y = fmap (const (annotType e1')) x
                env' = insertTy (U.varName x, annotType e1') env
            e2' <- inferE env' e2
            pure $ U.Exp l (y, e1', e2') (annotType e2', key)
        (SLetRec, (fs, e)) -> do
            as <- forM fs $ \(f, U.Exp _ _ _) -> do
                tvar_f <- U.TVar <$> Id.freshId "ty"
                --tell (DL.singleton (key_f, tvar_f))
                return (U.varName f, tvar_f)
            let env' = foldr insertTy env as
            fs' <- forM fs $ \(f, e1) -> do
                e1'   <- inferE env' e1
                let ty_f = annotType e1'
                ty_f'  <- concretize' $ env' M.! (U.varName f) 
                unify ty_f ty_f'
                return (fmap (const ty_f) f, e1')
            e' <- inferE env' e
            pure $ U.Exp l (fs', e') (annotType e', key)
        (SAssume, (cond, e)) -> do
            cond' <- inferE env cond
            unify (annotType cond') U.TBool
            e' <- inferE env e
            pure $ U.Exp l (cond', e') (annotType e', key)
        (SIf, (cond, e1, e2)) -> do
            cond' <- inferE env cond
            unify (annotType cond') U.TBool
            e1' <- inferE env e1
            e2' <- inferE env e2
            unify (annotType e1') (annotType e2') 
            pure $ U.Exp l (cond', e1', e2') (annotType e1', key)
        (SBranch, (e1,e2)) -> do
            e1' <- inferE env e1
            e2' <- inferE env e2
            unify (annotType e1') (annotType e2') 
            pure $ U.Exp l (e1', e2') (annotType e1', key)
        (SFail, _) -> pure $ U.Exp l arg (tvar, key)
        (SOmega, _) -> pure $ U.Exp l arg (tvar, key)
        (SRand, _) -> pure $ U.Exp l arg (U.TInt, key)
    e <$ unify tvar (annotType e) 

-- shouldBe :: (UniqueKey, Env) -> Type -> Type-> ExceptT TypeError FreshIO ()
shouldBe s t1 t2 =
    unless (t1 == t2) $ throwError (TypeMisMatch s t1 t2)

convertType :: SynEnv -> U.Type -> Either SynonymError Type
convertType synEnv ty = runExcept $ fmap go (desugarType synEnv ty)
    where
        go ty = case ty of
            U.TInt  -> TInt
            U.TBool -> TBool
            U.TUnit -> TInt 
            U.TPair ty1 ty2 -> TPair (go ty1) (go ty2)
            U.TFun tys ty -> TFun (map go tys) (go ty)
            U.TSyn _ _ -> error "convertType: undesugared synonym"
            U.TVar _x -> TInt

convertE :: SynEnv -> Env -> U.Exp U.Type -> ExceptT TypeError FreshIO Exp
convertE synEnv env (U.Exp l arg (ty,key)) = do
    let mty = convertType synEnv ty
    sty <- case mty of
        Left err -> throwError (Synonym err)
        Right sty -> pure sty
    case (l,arg) of
        (SLiteral, U.CInt _)  -> do
            shouldBe (key,env) sty TInt
            return $ Exp l arg sty key
        (SLiteral, U.CBool _) -> do
            shouldBe (key,env) sty TBool
            return $ Exp l arg sty key
        (SLiteral, U.CUnit) -> do
            shouldBe (key, env) sty TInt
            return $ Exp l (U.CInt 0) sty key
        (SVar, x) -> do
            let !sty' = env M.! (U.varName x)
            shouldBe (key,env) sty sty'
            return $ Exp l (TId sty' (U.varName x)) sty key
        (SBinary, BinArg op e1 e2) ->  do
            e1' <- convertE synEnv env e1
            e2' <- convertE synEnv env e2
            typeOfBinOp env op 
                        (getType e1') (getUniqueKey e1') 
                        (getType e2') (getUniqueKey e2') $ \sty' -> do
                shouldBe (key,env) sty sty'
                return $ Exp l (BinArg op e1' e2') sty key
        (SUnary, UniArg op e1) ->  do
            e1' <- convertE synEnv env e1
            typeOfUniOp env op 
                        (getType e1') (getUniqueKey e1') $ \sty' -> do
                shouldBe (key,env) sty sty'
                return $ Exp l (UniArg op e1') sty key
        (SPair, (e1, e2)) -> do
            e1' <- convertE synEnv env e1
            e2' <- convertE synEnv env e2
            shouldBe (key,env) sty (TPair (getType e1') (getType e2'))
            return $ Exp l (e1', e2') sty key
        (SLambda, (xs, e1)) -> do
            case sty of
                TFun ty_args sty1' -> do
                    let n = length ty_args
                        m = length xs
                    when (length ty_args /= length xs) $ 
                        throwError $ ArityMisMatch (key,env) n m
                    let env' = foldr (uncurry M.insert) env $ zip (map U.varName xs) ty_args
                        ys = zipWith (\x ty -> TId ty (U.varName x)) xs ty_args
                    e1' <- convertE synEnv env' e1
                    shouldBe (getUniqueKey e1',env) (getType e1') sty1'
                    return $ Exp l (ys, e1') sty key
                _ -> throwError $ OtherError $ "This function expected to have type " ++ show sty
        (SApp, (e, es)) -> do
            e' <- convertE synEnv env e
            case getType e' of
                TFun tys sty' -> do
                    es' <- mapM (convertE synEnv env) es
                    let g :: Exp -> Type -> ExceptT TypeError FreshIO ()
                        g e_i sty_i' = 
                            void $ shouldBe (getUniqueKey e_i,env) (getType e_i) sty_i'
                    zipWithM_ g es' tys
                    let n = length es
                        m = length tys
                    when (n /= m) $ throwError $ ArityMisMatch (key,env) n m
                    shouldBe (key,env) sty sty'
                    return $ Exp l (e', es') sty key
                sty_f -> throwError $ OtherError $ "App" ++ show sty_f
        (SLet, (x, e1, e2)) -> do
            e1' <- convertE synEnv env e1
            let env' = M.insert (U.varName x) (getType e1') env
            e2' <- convertE synEnv env' e2
            shouldBe (key,env) sty (getType e2')
            return $ Exp l (TId (getType e1') (U.varName x), e1', e2') sty key
        (SLetRec, (fs, e)) -> do
            env' <- fmap (foldr (uncurry M.insert) env) $ forM fs $ \(f, _) ->
                case convertType synEnv (varType f) of
                    Left err -> throwError (Synonym err)
                    Right sty -> return (U.varName f, sty)
            fs' <- forM fs $ \(f, e1) -> do
                e1' <- convertE synEnv env' e1
                return (TId (getType e1') (U.varName f), e1')
            e' <- convertE synEnv env' e
            shouldBe (key, env) sty (getType e')
            return $ Exp l (fs', e') sty key
        (SAssume, (e1, e2)) -> do
            e1' <- convertE synEnv env e1
            shouldBe (getUniqueKey e1',env) (getType e1') TBool
            e2' <- convertE synEnv env e2
            shouldBe (key,env) sty (getType e2')
            return $ Exp l (e1', e2') sty key
        (SIf, (e1, e2, e3)) -> do
            e1' <- convertE synEnv env e1
            shouldBe (getUniqueKey e1',env) (getType e1') TBool
            e2' <- convertE synEnv env e2
            shouldBe (key,env) sty (getType e2')
            e3' <- convertE synEnv env e3
            shouldBe (key,env) sty (getType e3')
            return $ Exp l (e1', e2', e3') sty key
        (SBranch, (e2, e3)) -> do
            e2' <- convertE synEnv env e2
            shouldBe (key,env) sty (getType e2')
            e3' <- convertE synEnv env e3
            shouldBe (key,env) sty (getType e3')
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
    SMul -> intOp TInt
    SDiv -> intOp TInt
    SEq  -> intOp TBool
    SNEq -> intOp TBool
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
    
