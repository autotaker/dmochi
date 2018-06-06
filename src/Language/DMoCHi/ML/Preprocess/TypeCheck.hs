module Language.DMoCHi.ML.Preprocess.TypeCheck where
import qualified Data.Map as M
import Prelude hiding(mapM)
import Control.Monad.Except
import Data.IORef
-- import Text.PrettyPrint
import Language.DMoCHi.ML.Syntax.Typed 
import Language.DMoCHi.ML.Syntax.Base
import Language.DMoCHi.ML.Syntax.Type
import qualified Language.DMoCHi.ML.Syntax.Alpha as U
import qualified Language.DMoCHi.ML.Syntax.UnTyped as U(AnnotVar(..),SynName, SynonymDef(..), Type(..), TypeScheme(..), Lit(..), matchType)
import qualified Language.DMoCHi.Common.Id as Id
import Language.DMoCHi.ML.Preprocess.TypeInfer
import Language.DMoCHi.Common.Id(MonadId(..), UniqueKey)
import Language.DMoCHi.ML.Preprocess.DesugarSynonym
import Language.DMoCHi.Common.Util

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

fromUnTyped :: U.Program (Maybe U.Type) -> ExceptT TypeError (FreshIO c) Program
fromUnTyped _prog = do
    prog <- withExceptT Infer (infer _prog)
    prog <- copyPoly prog
    let synEnv = M.fromList [ (U.synName syn, syn) | syn <- U.synonyms prog ]
    env <- fmap M.fromList $ forM (U.functions prog) $ \(f, tyS, _) -> 
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

copyPoly :: forall m. (MonadId m, MonadIO m) => U.Program U.Type -> ExceptT TypeError m (U.Program U.Type)
copyPoly prog = do
    copyEnvRef <- liftIO $ newIORef M.empty
    copyAssocRef <- liftIO $ newIORef []
    let bindInfo = M.fromList [ (U.varName f, (tyS, e)) | (f, tyS, e) <- U.functions prog ]
    let renamePoly :: [Id.Id String] -> U.Var U.Type -> [U.Type] -> ExceptT TypeError m (U.Var U.Type)
        renamePoly stack x tys = do
            copyEnv <- liftIO $ readIORef copyEnvRef
            case M.lookup (U.varName x,tys) copyEnv of
                Just x' -> pure x'
                Nothing | elem (U.varName x) stack -> throwError (OtherError "polymorphic recursion is not supported")
                        | otherwise -> do
                        let (tyS, e) = bindInfo M.! (U.varName x)
                            stack' = U.varName x : stack
                        x' <- U.refresh x 
                        liftIO $ writeIORef copyEnvRef (M.insert (U.varName x,tys) x' copyEnv)
                        e' <- go (stack', M.fromList (zip (U.typeArgs tyS) tys)) e
                        liftIO $ modifyIORef copyAssocRef ((x',e'):)
                        return x'
        go :: ([Id.Id String], M.Map String U.Type) -> U.Exp U.Type -> ExceptT TypeError m (U.Exp U.Type)
        go st@(stack,rho) (U.Exp l arg (_ty,_key)) = do
            key' <- freshKey
            let ty = substWith rho _ty
            case (l, arg) of
                (SLiteral, _) -> pure (U.Exp l arg (ty, key'))
                (SVar, x) -> case M.lookup (U.varName x) bindInfo of
                    Nothing -> pure (U.Exp SVar (x{ U.varType = ty}) (ty,key'))
                    Just (tyS, _) -> 
                        case U.matchType (U.typeBody tyS) ty of
                            Just match -> do
                                let tys = map (match M.!) (U.typeArgs tyS)
                                x' <- renamePoly stack (x{ U.varType = ty }) tys
                                pure (U.Exp SVar x' (ty,key'))
                            Nothing -> error $ "cannot match: " ++ show x
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

-- shouldBe :: (UniqueKey, Env) -> Type -> Type-> ExceptT TypeError FreshIO ()
-- throw error if the input types are not equivalent
shouldBe s expected actual =
    unless (expected `equiv` actual) $ throwError (TypeMisMatch s expected actual)

-- type equivalence: equality as curried types
equiv :: Type -> Type -> Bool
equiv TInt TInt = True
equiv TBool TBool = True
equiv (TPair t1 t2) (TPair t3 t4) = equiv t1 t3 && equiv t2 t4
equiv (TFun [] ty1) ty2 = equiv ty1 ty2
equiv ty1 (TFun [] ty2) = equiv ty1 ty2
equiv (TFun (ty:tys1) ty1) (TFun (ty':tys2) ty2) = 
    equiv ty ty' && equiv (TFun tys1 ty1) (TFun tys2 ty2)
equiv TInt _ = False
equiv TBool _ = False
equiv (TFun _ _) _ = False
equiv (TPair _ _) _ = False

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

cast :: MonadId m => Exp -> Type -> m Exp
cast e ty | getType e == ty = return e
cast e ty = do
    let castV v ty | ty_v == ty = return v
                   | otherwise = 
            case (ty_v, ty) of
                (TPair _ _, TPair ty3 ty4) -> do
                    v1 <- mkUni SFst v <$> Id.freshKey
                    v2 <- mkUni SSnd v <$> Id.freshKey
                    v1' <- castV v1 ty3
                    v2' <- castV v2 ty4
                    mkPair v1' v2' <$> Id.freshKey
                (TFun _ _, TFun tys2 ty2) -> do
                    xs <- mapM (\ty -> TId ty <$> Id.identify "arg") tys2
                    -- dig e ty xs : ty2
                    --   e : ty
                    let dig e _ [] = cast e ty2
                        dig e (TFun tys1 _) xs | length xs < length tys1 = do --partially applied
                            vs1 <- zipWithM (\x ty -> do
                                    v_x <- mkVar x <$> Id.freshKey
                                    castV v_x ty) xs tys1
                            ys <- mapM (\ty -> TId ty <$> Id.identify "arg") (drop (length xs) tys1)
                            vs2 <- mapM (\y -> mkVar y <$> Id.freshKey) ys
                            e_app <- mkApp e (vs1 ++ vs2) <$> Id.freshKey 
                            e_lam <- mkLambda ys e_app <$> Id.freshKey
                            castV e_lam ty2
                        dig e (TFun tys1 ty1) xs = do
                            vs1 <- zipWithM (\x ty -> do
                                    v_x <- mkVar x  <$> Id.freshKey
                                    castV v_x ty) xs tys1
                            e_app <- mkApp e vs1 <$> Id.freshKey
                            dig e_app ty1 (drop (length tys1) xs)
                        dig _ _ _ = error "unexpected pattern"
                    e_body <- dig v ty_v xs
                    mkLambda xs e_body <$> Id.freshKey
                (TPair _ _, _) -> error "unexpected pattern"
                (TInt, _) -> error "unexpected pattern"
                (TBool, _) -> error "unexpected pattern"
                (TFun _ _, _) -> error "unexpected pattern"
         where ty_v = getType v
    let ty_e = getType e
    x <- TId ty_e <$> Id.identify "tmp"
    e' <- (mkVar x <$> Id.freshKey) >>= \v -> castV v ty
    mkLet x e e' <$> Id.freshKey

convertE :: forall c. SynEnv -> Env -> U.Exp U.Type -> ExceptT TypeError (FreshIO c) Exp
convertE synEnv env (U.Exp l arg (ty,key)) = do
    let conv :: U.Type -> ExceptT TypeError (FreshIO c) Type
        conv ty = case convertType synEnv ty of
            Left err -> throwError (Synonym err)
            Right sty -> pure sty
    case (l, arg) of
        (SLiteral, U.CInt _)  -> return $ mkLiteral arg key
        (SLiteral, U.CBool _) -> return $ mkLiteral arg key
        (SLiteral, U.CUnit) -> return $ mkLiteral (U.CInt 0) key
        (SVar, x) -> do
            let sty = env M.! (U.varName x)
            return $ mkVar (TId sty (U.varName x)) key
        (SBinary, BinArg op e1 e2) ->  do
            e1' <- convertE synEnv env e1
            e2' <- convertE synEnv env e2
            return $ mkBin op e1' e2' key
        (SUnary, UniArg op e1) ->  do
            e1' <- convertE synEnv env e1
            return $ mkUni op e1' key
        (SPair, (e1, e2)) -> do
            e1' <- convertE synEnv env e1
            e2' <- convertE synEnv env e2
            return $ mkPair e1' e2' key
        (SLambda, (xs, e1)) -> do
            ty_xs <- mapM (conv . varType) xs
            let env' = foldr (uncurry M.insert) env $ zip (map U.varName xs) ty_xs
                ys = zipWith (\x ty -> TId ty (U.varName x)) xs ty_xs
            e1' <- convertE synEnv env' e1
            return $ mkLambda ys e1' key
        (SApp, (e, es)) -> do
            e' <- convertE synEnv env e
            es' <- mapM (convertE synEnv env) es
            let go _ f [] = return f
                go (TFun ty_vs ty_r) f args 
                    | length args >= length ty_vs = do
                        -- Suppose go ([ty_1 .. ty_m] -> ty_r) e_f (arg_1 .. arg_n)
                        -- Return Term: go ty_r (e_f (cast arg_1 ty_1) .. (cast arg_m ty_m)) (arg_{m+1} .. arg_n)
                        let (args1,args2) = splitAt (length ty_vs) args
                        args1' <- zipWithM cast args1 ty_vs
                        f' <- mkApp f args1' <$> Id.freshKey
                        go ty_r f' args2
                    | otherwise = do -- partial application: generate closure
                        -- Suppose: go ([ty_1 .. ty_m] -> ty_r) e_f (arg_1 .. arg_n)
                        -- Return Term:
                        -- let f = e_f in
                        -- let y_1 = cast arg_1 ty_1 in
                        -- ...
                        -- let y_n = cast arg_n ty_n in
                        -- fun y_{n+1} .. y_m -> f y_1 .. y_m
                        let (ty_vs1, ty_vs2) = splitAt (length args) ty_vs
                        f' <- TId (getType f) <$> Id.identify "fun"
                        ys1 <- mapM (\ty -> TId ty <$> Id.identify "arg") ty_vs1
                        ys2 <- mapM (\ty -> TId ty <$> Id.identify "arg") ty_vs2
                        args' <- zipWithM cast args ty_vs1
                        vs <- mapM (\y -> Exp SVar y (getType y) <$> Id.freshKey) (ys1 ++ ys2)
                        f'' <- mkVar f' <$> Id.freshKey
                        e_app <- mkApp f'' vs <$> Id.freshKey 
                        e_lam <- mkLambda ys2 e_app  <$> Id.freshKey
                        keys <- replicateM (length args + 1) Id.freshKey
                        return $ foldr (\(y, e_y, key) e -> mkLet y e_y e key) e_lam (zip3 (f':ys1) (f:args') keys)
                go _ _ _ = error "convertE: App: unexpected pattern"
            go (getType e') e' es'
        (SLet, (x, e1, e2)) -> do
            e1' <- convertE synEnv env e1
            let env' = M.insert (U.varName x) (getType e1') env
            e2' <- convertE synEnv env' e2
            return $ mkLet (TId (getType e1') (U.varName x)) e1' e2' key
        (SLetRec, (fs, e)) -> do
            env' <- fmap (foldr (uncurry M.insert) env) $ forM fs $ \(f, e_f) ->
                case convertType synEnv (annotType e_f) of
                    Left err -> throwError (Synonym err)
                    Right sty -> return (U.varName f, sty)
            fs' <- forM fs $ \(f, e1) -> do
                (Exp SLambda (xs, e_body) _ key) <- convertE synEnv env' e1 
                let ty_f@(TFun _ ty_r) = env' M.! U.varName f
                e_body <- cast e_body ty_r
                return (TId ty_f (U.varName f), mkLambda xs e_body key)
            e' <- convertE synEnv env' e
            return $ mkLetRec fs' e' key
        (SAssume, (e1, e2)) -> do
            e1' <- convertE synEnv env e1
            e2' <- convertE synEnv env e2
            return $ mkAssume e1' e2' key
        (SIf, (e1, e2, e3)) -> do
            e1' <- convertE synEnv env e1
            e2' <- convertE synEnv env e2
            e3' <- convertE synEnv env e3
            e3' <- cast e3' (getType e2')
            return $ mkIf e1' e2' e3' key
        (SBranch, (e2, e3)) -> do
            e2' <- convertE synEnv env e2
            e3' <- convertE synEnv env e3
            e3' <- cast e3' (getType e2')
            return $ mkBranch e2' e3' key
        (SFail, ())  -> conv ty >>= \sty -> return $ mkFail sty key
        (SOmega, ()) -> conv ty >>= \sty -> return $ mkOmega sty key
        (SRand, ())  -> return $ mkRand key
                
