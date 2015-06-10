module ML.Convert where
import ML.Syntax.Typed
import qualified Boolean.Syntax.Typed as B
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad
import Control.Applicative
import Data.SBV hiding(name)
import Debug.Trace
import Text.Printf
import Text.PrettyPrint(render)
import ML.PrettyPrint.Typed
import Control.Exception
import Id
import Control.Monad.IO.Class
import Data.Maybe(isJust)

type Constraints = [Value]
type Env = M.Map String (Either PType Value)

{-
substPType :: Id -> Value -> PType -> PType
substPType x v ty = trace s ty' where
    ty' = ML.Syntax.Typed.substPType x v ty 
    s = printf "substPType(%s,%s,%s) = %s" sx sv sty sty'
    sx = name x
    sv = render $ pprintV 0 v
    sty = render $ pprintP 0 ty
    sty' = render $ pprintP 0 ty'
    -}

infixl 9 !
(!) :: (Show key,Ord key) => M.Map key v -> key -> v
(!) m key | M.member key m = m M.! key
          | otherwise = error $ printf "given key(%s) is not an element in the map" $ show key

convert :: (MonadIO m, MonadId m,Applicative m) => Program -> m B.Program
convert p = do
    let env = M.fromList [ (name x,Left ty) | (x,ty,_) <- functions p ]
    ds <- forM (functions p) $ \(x,ty,e) -> do
        liftIO $ printf "Abstracting function %s\n" $ name x
        t <- convertE [] env ty e
        return (B.Symbol (B.getSort t) (name x),t)
    t <- convertE [] env (PInt []) (mainTerm p)
    return $ B.Program ds t

getPType :: Env -> Value -> (B.Term, PType)
getPType env (Var y) = 
    let Left pty = env ! (name y) in (B.V (B.Symbol (toSort pty) (name y)),pty)
getPType env (Op (OpFst _ v)) =
    let (t,PPair _ p1 _) = getPType env v in 
    (B.f_proj 0 2 t, p1)
getPType env (Op (OpSnd _ v)) =
    let (t,PPair _ p1 (x0,p2)) = getPType env v
        p2' = substPType x0 (Op (OpFst (getType p1) v)) p2 in
    (B.f_proj 1 2 t, p2')
getPType _ _ = error $ "failed to infer type"

toSort :: PType -> B.Sort
toSort (PInt ps) = B.Tuple (map (const B.Bool) ps)
toSort (PBool ps) = B.Tuple (map (const B.Bool) ps)
toSort (PPair _ ty_f (_,ty_s)) = B.Tuple [toSort ty_f,toSort ty_s]
toSort (PFun  _ ty_x (_,ty_r)) = toSort ty_x B.:-> toSort ty_r

convertE :: (MonadIO m, MonadId m,Applicative m) =>  Constraints -> Env -> PType -> Exp -> m B.Term
convertE cts env sigma _e = case _e of
    Value v -> convertV cts env sigma v
    Let _ x (LValue v) e -> 
        case getType x of
            TInt -> convertE (addC cts $ Op (Var x `OpEq` v)) (addE env (name x) (PInt [])) sigma e
            TBool -> convertE (addC cts $ Op (Var x `OpEq` v)) (addE env (name x) (PBool [])) sigma e
            _ -> do
                let (t,pty) = getPType env v 
                let s = render $ pprintP 0 pty
                let x' = B.Symbol (toSort pty) (name x)
                liftIO $ putStrLn $ name x ++ " PType = " ++ s
                B.f_let x' t <$> convertE cts (addE env (name x) pty) sigma e
    Let _ x (LApp _ f vs) e -> do
        let Left ty_f = env ! name f
        let (ty_vs,ty_r) = substPTypes ty_f vs
        es <- zipWithM (convertE cts env) ty_vs (map Value vs)
        let x' = B.Symbol (toSort ty_r) (name x)
        let f' = B.Symbol (toSort ty_f) (name f)
        B.f_let x' (foldl B.f_app (B.V f') es) <$> convertE cts (addE env (name x) ty_r) sigma e
    Let _ x (LExp ty_v ev) e -> 
        let x' = B.Symbol (toSort ty_v) (name x) in
        B.f_let x' <$> convertE cts env ty_v ev <*> convertE cts (addE env (name x) ty_v) sigma e
    Assume _ v e ->
        B.f_assume <$> convertP cts env v <*> convertE (addC cts v) env sigma e
    Lambda _ x e -> 
        let PFun _ ty_x (y,ty_r) = sigma in
        let x' = B.Symbol (toSort ty_x) (name x) in
        B.Lam x' <$> convertE cts (addE env (name x) ty_x) (substPType y (Var x) ty_r) e
    Fail _ -> return $ B.Fail (B.Symbol (toSort sigma) "")
    Branch _ e1 e2 -> B.f_branch <$> convertE cts env sigma e1 <*> convertE cts env sigma e2

convertV :: (MonadIO m, MonadId m,Applicative m) => Constraints -> Env -> PType -> Value -> m B.Term
convertV cts env (PInt ps) v = do
    pnames <- replicateM (length ps) (freshId "int")
    let pnames' = map (B.Symbol B.Bool) pnames
    let bs = map (\(x,w) -> substV x v w) ps
    let envs = scanl (uncurry . addE') env $ zip pnames bs
    es <- zipWithM (\env_i b_i -> convertP cts env_i b_i) envs bs
    return $ foldr (uncurry B.f_let) (B.T (map B.V pnames')) $ zip pnames' es
convertV cts env (PBool ps) v = do
    pnames <- replicateM (length ps) (freshId "bool")
    let pnames' = map (B.Symbol B.Bool) pnames
    let bs = map (\(x,w) -> substV x v w) ps
    let envs = scanl (uncurry . addE') env $ zip pnames bs
    es <- zipWithM (\env_i b_i -> convertP cts env_i b_i) envs bs
    return $ foldr (uncurry B.f_let) (B.T (map B.V pnames')) $ zip pnames' es
convertV cts env t1@(PPair _ ty_f (x0,ty_s)) v = do
    liftIO $ putStrLn $ render $ pprintP 0 t1
    liftIO $ putStrLn $ render $ pprintV 0 v
    let (vf,vs) = case v of
            Pair v1 v2 -> (v1,v2)
            Var (Id (TPair t1 t2) _) -> (Op $ OpFst t1 v,Op $ OpSnd t2 v)
            _ -> error $ "expecting a pair or a variable but found : " ++ (render $ pprintV 0 v) ++ show (getType v)
    x <- freshId "x"
    let x' = B.Symbol (toSort ty_f) x
    B.f_let x' <$> convertV cts env ty_f vf <*> do
        let env1 = addE env x ty_f
        let vx = Var $ Id (getType x0) x
        let cts1 = foldl addC (eqs (getType x0) vx vf) cts
            eqs TInt          v1 v2 = pure $ Op $ OpEq v1 v2
            eqs TBool         v1 v2 = pure $ Op $ OpEq v1 v2
            eqs (TPair t1 t2) v1 v2 = 
                let v1f = Op $ OpFst t1 v1 in
                let v1s = Op $ OpSnd t2 v1 in
                let (v2f,v2s) = case v2 of
                        Pair v2f v2s -> (v2f,v2s)
                        _ -> let v2f = Op $ OpFst t1 v2 in
                             let v2s = Op $ OpSnd t2 v2 in
                             (v2f,v2s) in
                eqs t1 v1f v2f <|> eqs t2 v1s v2s
            eqs (TFun _ _) v1 v2 = empty
        y <- freshId "y"
        let y' = B.Symbol (toSort ty_s) y
        B.f_let y' <$> convertV cts env1 (substPType x0 vf ty_s) vs <*> do
            return $ B.T [B.V x',B.V y']
convertV cts env t1@(PFun ty ty_x (x0,ty_r)) v = do
    let (vf,t2@(PFun _ ty_x' (x0',ty_r'))) = getPType env v
    if t1 == t2 then
        return $ vf
    else do
        x <- freshId "x"
        let x' = B.Symbol (toSort ty_x) x
        B.Lam x' <$> do
            y <- freshId "y"
            let y' = B.Symbol (toSort ty_x') y
            let env1 = addE env x ty_x
            let vx = Var $ Id (getType x0) x
            B.f_let y' <$> convertV cts env1 ty_x' vx <*> do
                z <- freshId "z"
                let z' = B.Symbol (toSort ty_r') z
                let vz = Var $ Id (getType ty_r) z
                let env2 = addE (addE env1 y ty_x') z (substPType x0' vx ty_r')
                B.f_let z' (B.f_app vf (B.V y')) <$> convertV cts env2 (substPType x0 vx ty_r) vz

convertP :: MonadIO m => Constraints -> Env -> Value -> m B.Term
convertP cts env b = liftIO $ do
    et <- liftIO $ model (addC cts b) env
    ef <- liftIO $ model (addC cts (Op (OpNot b))) env
    if et == B.C False then
        return $ B.f_assume ef (B.C False)
    else if ef == B.C False then
        return $ B.f_assume et (B.C True)
    else
        return $ B.f_assume et (B.C True) `B.f_branch` B.f_assume ef (B.C False)

printConstraints :: Constraints -> IO ()
printConstraints cts = do
    putStrLn "---Constraints---"
    forM_ cts $ putStrLn . render . pprintV 0

printPredicates :: [(Value,B.Term)] -> IO ()
printPredicates ps = do
    putStrLn "---Predicates---"
    forM_ ps $ \(v,term) -> putStrLn $ show term ++ " : " ++ (render $ pprintV 0 v)


gatherVariables :: Env -> [ (String,Type) ]
gatherVariables env = do
    (x,e) <- M.assocs env
    let go var TInt = pure (var,TInt)
        go var TBool = pure (var,TBool)
        go var (TPair t1 t2) = go (var ++ ".fst") t1 
                           <|> go (var ++ ".snd") t2
        go _ _ = empty
    case e of
        Left pty -> go x (getType pty)
        Right _ -> empty


model :: Constraints -> Env -> IO B.Term
model cts env = handle ((\e -> model cts env) :: SomeException -> IO B.Term) $ do
    let ps = filter (not.trivial.fst) $ predicates env
    let vs = gatherVariables env
    let bs = [ b | (b,TBool) <- vs ]
    let xs = [ x | (x,TInt)  <- vs ]
    fool <- isVacuous $ do
        boolTbl <- fmap M.fromList $ forM bs $ \b -> (,) b <$> forall b
        intTbl  <- fmap M.fromList $ forM xs $ \x -> (,) x <$> forall x
        constrain $ bAnd (map (toSBV boolTbl intTbl) cts)
        return (true :: SBool)
    let problem :: Value -> Symbolic SBool
        problem p = do
            -- constrain
            boolTbl <- fmap M.fromList $ forM bs $ \b -> (,) b <$> forall b
            intTbl  <- fmap M.fromList $ forM xs $ \x -> (,) x <$> forall x
            -- eval
            return $ bAnd (map (toSBV boolTbl intTbl) cts) ==> toSBV boolTbl intTbl p
    printConstraints cts
    printPredicates ps
    if fool then do
        putStrLn "constraints are vacuous"
        return (B.C False)
    else do
        let contain memo key = any (flip S.member memo) $ subset key
            subset = foldr (\x acc -> acc <|> (x:) <$> acc) (pure [])
        let step (acc,memo) ((p1,t1,key1):mp2) = if contain memo key1 then return (acc,memo) else  do
                ThmResult _res <- prove $ problem p1
                case _res of
                    Unsatisfiable _ -> do
                        putStrLn $ "found: " ++ (render $ pprintV 0 p1)
                        return (B.f_and acc t1,S.insert key1 memo)
                    _ -> case mp2 of 
                        [] -> return (acc,memo)
                        (p2,t2,key2):_ -> do
                            ThmResult _res <- prove $ problem p2
                            case _res of 
                                Unsatisfiable _ -> do
                                    putStrLn $ "found:" ++ (render $ pprintV 0 p2)
                                    return (B.f_and acc t2,S.insert key2 memo)
                                _ -> return (acc,memo)
        let ps' = [ [(p,t,[i]), (Op $ OpNot p, B.f_not t,[-i])] | ((p,t),i) <- zip ps [0..] ] ++ 
                  [ [(Op $ OpNot $ Op $ OpAnd p q, B.f_not $ B.f_and t s,[-i,-j])]
                    | ((p,t),i) <- zip ps [0..], 
                      ((q,s),j) <- zip ps [0..], 
                      i < (j :: Int) ]   ++
                  [ [(Op $ OpNot $ Op $ OpAnd (Op $ OpAnd p q) r, B.f_not $ B.f_and t (B.f_and s u),[-i,-j,-k])]
                    | ((p,t),i) <- zip ps [0..], 
                      ((q,s),j) <- zip ps [0..], 
                      ((r,u),k) <- zip ps [0..],
                      i < (j :: Int) &&  j < k ]
        fst <$>foldM step (B.C True,S.empty) ps'
        
toSBV :: M.Map String SBool -> M.Map String SInteger -> Value -> SBool
toSBV boolTbl intTbl = goBool where
    goBool (Var   x) = boolTbl ! name x
    goBool (CInt  _) = undefined
    goBool (CBool b) = if b then true else false
    goBool (Op op) = goBoolOp op
    goBool (Pair _ _) = undefined
    goInt (Var x) = intTbl ! name x
    goInt (CInt i) = fromIntegral i
    goInt (CBool _) = undefined
    goInt (Pair _ _) = undefined
    goInt (Op op) = goIntOp op
    goBoolOp (OpEq v1 v2) 
        | getType v1 == TInt = goInt v1 .== goInt v2
        | getType v1 == TBool = goBool v1 .== goBool v2
        | otherwise = undefined
    goBoolOp (OpLt v1 v2) = goInt v1 .< goInt v2
    goBoolOp (OpLte v1 v2) = goInt v1 .<= goInt v2
    goBoolOp (OpAnd v1 v2) = goBool v1 &&& goBool v2
    goBoolOp (OpOr  v1 v2) = goBool v1 ||| goBool v2
    goBoolOp (OpNot  v1) = bnot $ goBool v1 
    goBoolOp op@(OpFst _ _) = goBool (evalPair $ Op op)
    goBoolOp op@(OpSnd _ _) = goBool (evalPair $ Op op)
    goBoolOp _ = undefined
    goIntOp (OpAdd v1 v2) = goInt v1 + goInt v2
    goIntOp (OpSub v1 v2) = goInt v1 - goInt v2
    goIntOp op@(OpFst _ _) = goInt (evalPair $ Op op)
    goIntOp op@(OpSnd _ _) = goInt (evalPair $ Op op)
    goIntOp _ = undefined

evalPair :: Value -> Value
evalPair (Op (OpFst ty v)) = 
    case evalPair v of
        Var x -> Var $ Id ty (name x++".fst")
        Pair f _ -> f
        _ -> error "evalPair"
evalPair (Op (OpSnd ty v)) =
    case evalPair v of
        Var x -> Var $ Id ty (name x++".snd")
        Pair _ s -> s
        _ -> error "evalPair"
evalPair (Pair p1 p2) = Pair (evalPair p1) (evalPair p2)
evalPair v = v
            
predicates :: Env -> [(Value,B.Term)]
predicates env = (do
    (x,e) <- M.assocs env
    case e of 
        Right p -> pure (p,B.V (B.Symbol B.Bool x))
        Left ty -> 
            let x' = B.Symbol (toSort ty) x in
            go (Var $ Id (getType ty) x) (B.V x') ty) where
    f t bt xs = do
        let n = length xs
        (i,(y,pv)) <- zip [0..] xs
        let pv' = substV y t pv
        pure (pv', B.f_proj i n bt)
    go t bt (PInt xs) = f t bt xs 
    go t bt (PBool xs) = f t bt xs
    go t bt (PPair _ p1 (x0,p2)) = 
        let bfst = B.f_proj 0 2 bt
            bsnd = B.f_proj 1 2 bt
            tfst = Op $ OpFst (getType p1) t
            tsnd = Op $ OpSnd (getType p2) t in
        go tfst bfst p1 <|> go tsnd bsnd (substPType x0 tfst p2)
    go _ _ (PFun _ _ _) = empty

trivial :: Value -> Bool
trivial t = isJust (eval t) where
    eval :: Value -> Maybe (Either Bool Integer)
    eval (CInt i) = return $ Right i
    eval (CBool b) = return $ Left b
    eval (Op op) = case op of
        OpAdd e1 e2 -> Right <$> intOp (+) e1 e2
        OpSub e1 e2 -> Right <$> intOp (-) e1 e2
        OpEq  e1 e2 -> case getType e1 of
            TInt -> Left <$> intOp (==) e1 e2
            TBool -> Left <$> boolOp (==) e1 e2
            _ -> Nothing
        OpLt  e1 e2 -> Left <$> intOp (<) e1 e2
        OpLte e1 e2 -> Left <$> intOp (<=) e1 e2
        OpAnd e1 e2 -> Left <$> boolOp (&&) e1 e2
        OpOr  e1 e2 -> Left <$> boolOp (||) e1 e2
        OpFst _ _ -> Nothing
        OpSnd _ _ -> Nothing
        OpNot e -> Left . not <$> (eval e >>= toBool)
    eval _ = Nothing
    toInt (Right i) = return i
    toInt _ = Nothing
    toBool (Left b) = return b
    toBool _ = Nothing
    intOp op e1 e2 = op <$> (eval e1 >>= toInt) <*> (eval e2 >>= toInt)
    boolOp op e1 e2 = op <$> (eval e1 >>= toBool) <*> (eval e2 >>= toBool)



substPTypes :: PType -> [Value] -> ([PType],PType)
substPTypes ty [] = ([],ty)
substPTypes (PFun _ ty1 (x,ty2)) (v:vs) = (ty1:tys,ty) where
    (tys,ty) = substPTypes (substPType x v ty2) vs
substPTypes ty l = error $ "Type_mismatch" ++ (render $ pprintP 0 ty) ++ (show$ map (render.pprintV 9) l)

addC :: Constraints -> Value -> Constraints
addC = flip (:)

addE :: Env -> String -> PType -> Env
addE env x ty = M.insert x (Left ty) env

addE' :: Env -> String -> Value -> Env
addE' env x ty = M.insert x (Right ty) env
