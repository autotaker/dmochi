{-# LANGUAGE FlexibleContexts #-}
module Language.DMoCHi.ML.Preprocess.TypeInfer(infer,InferError) where
import qualified Data.Map as M
--import           Prelude hiding(mapM)
import           Control.Monad.Except
import           Control.Monad.State.Strict
import           Language.DMoCHi.ML.Syntax.Base
--import Text.PrettyPrint.HughesPJClass
import           Language.DMoCHi.ML.Syntax.Alpha
import           Language.DMoCHi.ML.Syntax.UnTyped(AnnotVar(..),SynName, SynonymDef(..), Type(..), TypeScheme(..), Lit(..), toTypeScheme, matchTypeScheme)
import qualified Language.DMoCHi.Common.Id as Id
import           Language.DMoCHi.Common.Id(MonadId(..))
import           Language.DMoCHi.Common.Util
import           Language.DMoCHi.ML.Preprocess.DesugarSynonym
-- import Debug.Trace

type UExp = Exp (Maybe Type)

type TSubst = M.Map String Type
type SynEnv = M.Map SynName SynonymDef
type InferM m = StateT TSubst (ExceptT InferError m)

data InferError = RecursiveType
                | SynError SynonymError
                | SchemeError TypeScheme TypeScheme
                | CannotUnify
                deriving (Show,Eq)

updateSubst :: MonadState TSubst m => String -> Type -> m ()
updateSubst key value = state $ \theta -> 
    let !theta' = M.insert key value theta in
    ((), theta')

subst :: (MonadState TSubst m) => Type -> m Type
subst TInt = pure TInt
subst TBool = pure TBool
subst TUnit = pure TUnit
subst (TPair ty1 ty2) = TPair <$> subst ty1 <*> subst ty2
subst (TFun ts ty) = TFun <$> mapM subst ts <*> subst ty
subst (TSyn ts synName) = TSyn <$> mapM subst ts <*> pure synName
subst (TVar x) = do
    theta <- get
    case M.lookup x theta of
        Just ty -> do
            ty' <- subst ty
            updateSubst x ty'
            return ty'
        Nothing -> return (TVar x)

unify :: Monad m => SynEnv -> Type -> Type -> InferM m ()
unify env a b = go a b
    where
    go TInt TInt = return ()
    go TBool TBool = return ()
    go TUnit TUnit = return ()
    go (TPair ty1 ty2) (TPair ty3 ty4) = go ty1 ty3 >> go ty2 ty4
    go (TFun [] ty1) ty2 = go ty1 ty2 
    go ty1 (TFun [] ty2) = go ty1 ty2
    go (TFun (ty:tys1) ty1) (TFun (ty':tys2) ty2) = 
        go ty ty' >> go (TFun tys1 ty1) (TFun tys2 ty2)
    go (TSyn ts name) ty = do
        let def = env M.! name
            n = length $ typVars def
            m = length ts
        when (n /= m) $ throwError (SynError $ ArgLengthDiffer n m)
        ty' <- case runExcept (substType (M.fromList $ zip (typVars def) ts) (synDef def)) of
            Left err -> throwError $ SynError err
            Right ty' -> return ty'
        go ty' ty
    go ty1 ty2@(TSyn _ _) = go ty2 ty1
    go (TVar x) ty2 = do
        theta <- get
        case M.lookup x theta of
            Just ty1' -> go ty1' ty2
            Nothing   -> do
                ty2' <- subst ty2
                case ty2' of
                    TVar y | x == y -> return ()
                    _ | x `elemType` ty2' -> throwError RecursiveType
                      | otherwise -> updateSubst x ty2'
    go ty1 ty2@(TVar _) = go ty2 ty1
    go TInt _  = pure ()
    go TBool _ = pure ()
    go TUnit _ = pure ()
    go (TPair _ _) _ = pure ()
    go (TFun _ _) _ = pure ()
    
elemType :: String -> Type -> Bool
elemType _ TInt = False
elemType _ TBool = False
elemType _ TUnit = False
elemType x (TPair ty1 ty2) = elemType x ty1 || elemType x ty2
elemType x (TFun tys ty) = any (elemType x) (ty:tys)
elemType x (TVar y) = x == y
elemType x (TSyn tys _) = any (elemType x) tys

concretize :: MonadId m => TypeScheme -> m ([String], Type)
concretize (TypeScheme [] ty) = pure ([],ty)
concretize (TypeScheme args ty) = do
    names <- mapM Id.freshId args
    let rho = M.fromList $ zip args (map TVar names)
    return (names, substWith rho ty)

substWith :: M.Map String Type -> Type -> Type
substWith rho = go
    where
    go TInt  = TInt
    go TBool = TBool
    go TUnit = TUnit
    go (TVar x) = case M.lookup x rho of
        Just v -> v
        Nothing -> TVar x
    go (TPair ty1 ty2) = TPair (go ty1) (go ty2)
    go (TFun ts ty) = TFun (map go ts) (go ty)
    go (TSyn ts synName) = TSyn (map go ts) synName

concretize' :: MonadId m => TypeScheme -> m Type
concretize' = fmap snd . concretize

annotType :: Exp Type -> Type
annotType (Exp _ _ (ty,_)) = ty

freshType :: MonadId m => InferM m Type
freshType = TVar <$> Id.freshId "ty"

infer :: Program (Maybe Type)-> ExceptT InferError (FreshIO c) (Program Type)
infer prog = evalStateT doit M.empty
    where
    synEnv = M.fromList [ (synName syn, syn) | syn <- synonyms prog ]
    doit = do
        let env = M.fromList [ (varName f, tyS) | (f, tyS, _) <- functions prog ]
        fs <- forM (functions prog) $ \(f,tyS,e) -> do
            e' <- inferE synEnv env e
            ty2 <- concretize' tyS
            unify synEnv (annotType e') ty2
            ty2' <- subst ty2
            e' <- traverse subst e'
            let tyS' = toTypeScheme ty2'
            case matchTypeScheme tyS tyS' of
                Nothing -> throwError (SchemeError tyS tyS')
                Just xs -> return (fmap (const ty2') f, tyS'{ typeArgs = xs } , e')
        e0 <- inferE synEnv env (mainTerm prog)
        unify synEnv (annotType e0) TUnit
        e0' <- traverse subst e0
        return $ Program fs (synonyms prog) e0'


inferE :: (MonadId m, MonadIO m) => SynEnv -> M.Map (Id.Id String) TypeScheme -> UExp -> InferM m (Exp Type)
inferE synEnv env (Exp l arg (_,key)) = do
    tvar <- freshType
    let insertTy (x,ty) env = M.insert x (TypeScheme [] ty) env
    e <- case (l, arg) of
        (SLiteral, CInt _)  -> pure $ Exp l arg (TInt,  key)
        (SLiteral, CBool _) -> pure $ Exp l arg (TBool, key)
        (SLiteral, CUnit)   -> pure $ Exp l arg (TUnit, key)
        (SVar, x) -> concretize' (env M.! varName x) >>= \ty ->
                     pure $ Exp l (fmap (const ty) x) (ty, key)
        (SBinary, BinArg op e1 e2) -> do
            e1' <- inferE synEnv env e1
            e2' <- inferE synEnv env e2
            let f :: (MonadId m, MonadIO m) => Type -> InferM m ()
                f ty = unify synEnv (annotType e1') ty >> 
                       unify synEnv (annotType e2') ty
            ty <- case op of
                SAdd -> f TInt >> pure TInt
                SSub -> f TInt >> pure TInt
                SDiv -> f TInt >> pure TInt
                SMul -> f TInt >> pure TInt
                SEq  -> f TInt >> pure TBool
                SNEq -> f TInt >> pure TBool
                SLt  -> f TInt >> pure TBool
                SGt  -> f TInt >> pure TBool
                SLte -> f TInt >> pure TBool
                SGte -> f TInt >> pure TBool
                SAnd -> f TBool >> pure TBool
                SOr  -> f TBool >> pure TBool
            pure $ Exp l (BinArg op e1' e2') (ty, key)
        (SUnary, UniArg op e1) -> do
            e1' <- inferE synEnv env e1
            let ty1 = annotType e1'
            ty <- case op of
                SFst -> do
                    ty_pair <- TPair <$> pure tvar <*> freshType
                    tvar <$ unify synEnv ty1 ty_pair
                SSnd -> do
                    ty_pair <- TPair <$> freshType <*> pure tvar
                    tvar <$ unify synEnv ty1 ty_pair
                SNeg -> TInt <$ unify synEnv ty1 TInt
                SNot -> TBool <$ unify synEnv ty1 TBool
            pure $ Exp l (UniArg op e1') (ty, key)
        (SPair, (e1, e2)) -> do
            e1' <- inferE synEnv env e1
            e2' <- inferE synEnv env e2
            pure $ Exp l (e1',e2') (TPair (annotType e1') (annotType e2'), key)
        (SLambda, (xs,e)) -> do
            ys <- mapM (traverse (\_ -> freshType)) xs
            let tys = map varType ys
            let env' = foldr insertTy env (zip (map varName xs) tys)
            e' <- inferE synEnv env' e
            pure $ Exp l (ys, e') (TFun tys (annotType e'), key)
        (SApp, (e, es)) -> do
            e' <- inferE synEnv env e
            es' <- mapM (inferE synEnv env) es
            let ty_f = TFun (map annotType es') tvar
            unify synEnv (annotType e') ty_f
            pure $ Exp l (e', es') (tvar, key)
        (SLet, (x, e1, e2)) -> do
            e1' <- inferE synEnv env e1
            let y = fmap (const (annotType e1')) x
                env' = insertTy (varName x, annotType e1') env
            e2' <- inferE synEnv env' e2
            pure $ Exp l (y, e1', e2') (annotType e2', key)
        (SLetRec, (fs, e)) -> do
            as <- forM fs $ \(f, Exp _ _ _) -> do
                tvar_f <- freshType
                --tell (DL.singleton (key_f, tvar_f))
                return (varName f, tvar_f)
            let env' = foldr insertTy env as
            fs' <- forM fs $ \(f, e1) -> do
                e1'   <- inferE synEnv env' e1
                let ty_f = annotType e1'
                ty_f'  <- concretize' $ env' M.! (varName f) 
                unify synEnv ty_f ty_f'
                return (fmap (const ty_f) f, e1')
            e' <- inferE synEnv env' e
            pure $ Exp l (fs', e') (annotType e', key)
        (SAssume, (cond, e)) -> do
            cond' <- inferE synEnv env cond
            unify synEnv (annotType cond') TBool
            e' <- inferE synEnv env e
            pure $ Exp l (cond', e') (annotType e', key)
        (SIf, (cond, e1, e2)) -> do
            cond' <- inferE synEnv env cond
            unify synEnv (annotType cond') TBool
            e1' <- inferE synEnv env e1
            e2' <- inferE synEnv env e2
            unify synEnv (annotType e1') (annotType e2') 
            pure $ Exp l (cond', e1', e2') (annotType e1', key)
        (SBranch, (e1,e2)) -> do
            e1' <- inferE synEnv env e1
            e2' <- inferE synEnv env e2
            unify synEnv (annotType e1') (annotType e2') 
            pure $ Exp l (e1', e2') (annotType e1', key)
        (SFail, _) -> pure $ Exp l arg (tvar, key)
        (SOmega, _) -> pure $ Exp l arg (tvar, key)
        (SRand, _) -> pure $ Exp l arg (TInt, key)
    e <$ unify synEnv tvar (annotType e) 
