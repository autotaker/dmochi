module ML.Convert where
import ML.Syntax.Typed
import qualified Boolean.Syntax as B
import qualified Data.Map as M
import Control.Monad
import Control.Applicative
import Data.SBV hiding(name)
import System.IO.Unsafe
import Data.IORef
import Debug.Trace
import Text.Printf
import Text.PrettyPrint(render)
import ML.PrettyPrint.Typed
import Control.Exception

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

-- syntax sugars
assume :: B.Term -> B.Term -> B.Term
assume (B.C True) e = e
assume (B.C False) _ = B.Omega ""
assume p e = B.If p e (B.Omega "")
nondet :: B.Term -> B.Term -> B.Term
nondet e1 (B.Omega _) = e1
nondet (B.Omega _) e2 = e2
nondet (B.C True) (B.C False) = B.TF
nondet e1 e2 = B.If B.TF e1 e2

fAnd :: B.Term -> B.Term -> B.Term
fAnd (B.C True) t = t
fAnd t1 t2 = B.App (B.V "and") (B.T [t1,t2])

fOr  :: B.Term -> B.Term -> B.Term
fOr t1 t2 = B.App (B.V "or") (B.T [t1,t2])

fNot  :: B.Term -> B.Term
fNot t1 = B.App (B.V "not") t1

tAnd :: B.Term
tAnd = 
    let x = B.V "x" in
    let fx = B.Proj (B.ProjN 0) (B.ProjD 2) x in
    let sx = B.Proj (B.ProjN 1) (B.ProjD 2) x in
    B.Lam "x" (B.If fx sx (B.C False))

tOr :: B.Term
tOr =
    let x = B.V "x" in
    let fx = B.Proj (B.ProjN 0) (B.ProjD 2) x in
    let sx = B.Proj (B.ProjN 1) (B.ProjD 2) x in
    B.Lam "x" (B.If fx (B.C True) sx)

tNot :: B.Term
tNot =
    let x = B.V "x" in
    B.Lam "x" (B.If x (B.C False) (B.C True))

infixl 9 !
(!) :: (Show key,Ord key) => M.Map key v -> key -> v
(!) m key | M.member key m = m M.! key
          | otherwise = error $ printf "given key(%s) is not an element in the map" $ show key

convert :: Program -> IO B.Program
convert p = do
    let env = M.fromList [ (name x,Left ty) | (x,ty,_) <- functions p ]
    ds <- forM (functions p) $ \(x,ty,e) -> do
        printf "Abstracting function %s\n" $ name x
        (,) (name x) <$> convertE [] env ty e
    let ps = [("and",tAnd),("or",tOr),("not",tNot)]
    t <- convertE [] env (PInt []) (mainTerm p)
    return $ B.Program (ps++ds) t

getPType :: Env -> Value -> (B.Term, PType)
getPType env (Var y) = 
    let Left pty = env ! (name y) in (B.V (name y),pty)
getPType env (Op (OpFst _ v)) =
    let (t,PPair _ p1 _) = getPType env v in 
    (B.Proj (B.ProjN 0) (B.ProjD 2) t, p1)
getPType env (Op (OpSnd _ v)) =
    let (t,PPair _ p1 (x0,p2)) = getPType env v
        p2' = substPType x0 (Op (OpFst (getType p1) v)) p2 in
    (B.Proj (B.ProjN 1) (B.ProjD 2) t, p2')
getPType _ _ = error "failed to infer type"

convertE :: Constraints -> Env -> PType -> Exp -> IO B.Term
convertE cts env sigma _e = case _e of
    Value v -> convertV cts env sigma v
    Let _ x (LValue v) e -> 
        case getType x of
            TInt -> convertE (addC cts $ Op (Var x `OpEq` v)) (addE env (name x) (PInt [])) sigma e
            TBool -> convertE (addC cts $ Op (Var x `OpEq` v)) (addE env (name x) (PBool [])) sigma e
            _ -> do
                let (t,pty) = getPType env v 
                let s = render $ pprintP 0 pty
                print $ "PType = " ++ s
                B.Let (name x) t <$> convertE cts (addE env (name x) pty) sigma e
    Let _ x (LApp _ f vs) e -> do
        let Left ty_f = env ! name f
        let (ty_vs,ty_r) = substPTypes ty_f vs
        es <- zipWithM (convertE cts env) ty_vs (map Value vs)
        B.Let (name x) (foldl B.App (B.V (name f)) es) <$> convertE cts (addE env (name x) ty_r) sigma e
    Let _ x (LExp ty_v ev) e -> 
        B.Let (name x) <$> convertE cts env ty_v ev <*> convertE cts (addE env (name x) ty_v) sigma e
    Assume _ v e ->
        assume <$> convertP cts env v <*> convertE (addC cts v) env sigma e
    Lambda _ x e -> 
        let PFun _ ty_x (y,ty_r) = sigma in
        B.Lam (name x) <$> convertE cts (addE env (name x) ty_x) (substPType y (Var x) ty_r) e
    Fail _ -> return $ B.Fail ""
    Branch _ e1 e2 -> nondet <$> convertE cts env sigma e1 <*> convertE cts env sigma e2

convertV :: Constraints -> Env -> PType -> Value -> IO B.Term
convertV cts env (PInt ps) v = do
    pnames <- replicateM (length ps) freshId
    let bs = map (\(x,w) -> substV x v w) ps
    let envs = scanl (uncurry . addE') env $ zip pnames bs
    es <- zipWithM (\env_i b_i -> convertP cts env_i b_i) envs bs
    return $ foldr (uncurry B.Let) (B.T (map B.V pnames)) $ zip pnames es
convertV cts env (PBool ps) v = do
    pnames <- replicateM (length ps) freshId
    let bs = map (\(x,w) -> substV x v w) ps
    let envs = scanl (uncurry . addE') env $ zip pnames bs
    es <- zipWithM (\env_i b_i -> convertP cts env_i b_i) envs bs
    return $ foldr (uncurry B.Let) (B.T (map B.V pnames)) $ zip pnames es
convertV cts env t1@(PPair _ ty_f (x0,ty_s)) v = do
    putStrLn $ render $ pprintP 0 t1
    putStrLn $ render $ pprintV 0 v
    let (vf,vs) = case v of
            Pair v1 v2 -> (v1,v2)
            Var (Id (TPair t1 t2) _) -> (Op $ OpFst t1 v,Op $ OpSnd t2 v)
            _ -> error $ "expecting a pair or a variable but found : " ++ (render $ pprintV 0 v) ++ show (getType v)
    x <- freshId
    B.Let x <$> convertV cts env ty_f vf <*> do
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
        y <- freshId
        B.Let y <$> convertV cts env1 (substPType x0 vf ty_s) vs <*> do
            return $ B.T [B.V x,B.V y]
convertV cts env t1@(PFun ty ty_x (x0,ty_r)) v = do
    let (vf,t2@(PFun _ ty_x' (x0',ty_r'))) = getPType env v
    if t1 == t2 then
        return $ vf
    else do
        putStrLn $ render $ pprintP 0 t1
        putStrLn $ render $ pprintP 0 t2
        putStrLn $ render $ pprintV 0 v
        x <- freshId
        print ("x",x)
        B.Lam x <$> do
            y <- freshId
            print ("y",y)
            let env1 = addE env x ty_x
            let vx = Var $ Id (getType x0) x
            B.Let y <$> convertV cts env1 ty_x' vx <*> do
                z <- freshId
                print ("z",z)
                let vz = Var $ Id (getType ty_r) z
                let env2 = addE (addE env1 y ty_x') z (substPType x0' vx ty_r')
                B.Let z (B.App vf (B.V y)) <$> convertV cts env2 (substPType x0 vx ty_r) vz

globalIdRef :: IORef Int
globalIdRef = unsafePerformIO (newIORef 0)

freshId :: IO String
freshId = do
    i <- readIORef globalIdRef
    writeIORef globalIdRef (i+1)
    return $ "fresh_" ++ show i

convertP :: Constraints -> Env -> Value -> IO B.Term
convertP cts env b = do
    et <- model (addC cts b) env
    ef <- model (addC cts (Op (OpNot b))) env
    if et == B.C False then
        return $ assume ef (B.C False)
    else if ef == B.C False then
        return $ assume et (B.C True)
    else
        return $ assume et (B.C True) `nondet` assume ef (B.C False)

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
    let ps = predicates env
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
        let step acc ((p1,t1):mp2) = do
            ThmResult _res <- prove $ problem p1
            case _res of
                Unsatisfiable _ -> do
                    putStrLn $ "found: " ++ (render $ pprintV 0 p1)
                    return (fAnd acc t1)
                _ -> case mp2 of 
                    [] -> return acc
                    (p2,t2):_ -> do
                        ThmResult _res <- prove $ problem p2
                        case _res of 
                            Unsatisfiable _ -> do
                                putStrLn $ "found:" ++ (render $ pprintV 0 p2)
                                return (fAnd acc t2)
                            _ -> return acc
        let ps' = [ [(p,t), (Op $ OpNot p, fNot t)] | (p,t) <- ps ] ++ 
                  [ [(Op $ OpNot $ Op $ OpAnd p q, fNot $ fAnd t s)]
                    | ((p,t),i) <- zip ps [0..], 
                      ((q,s),j) <- zip ps [0..], 
                      i < (j :: Int) ] ++
                  [ [(Op $ OpNot $ Op $ OpAnd (Op $ OpAnd p q) r, fNot $ fAnd t (fAnd s u))]
                    | ((p,t),i) <- zip ps [0..], 
                      ((q,s),j) <- zip ps [0..], 
                      ((r,u),k) <- zip ps [0..],
                      i < (j :: Int) &&  j < k ]
        foldM step (B.C True) ps'
        
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
        Right p -> pure (p,B.V x)
        Left ty -> go (Var $ Id (getType ty) x) (B.V x) ty) where
    f t bt xs = do
        let n = B.ProjD $ length xs
        (i,(y,pv)) <- zip [0..] xs
        let pv' = substV y t pv
        pure (pv', B.Proj (B.ProjN i) n bt)
    go t bt (PInt xs) = f t bt xs 
    go t bt (PBool xs) = f t bt xs
    go t bt (PPair _ p1 (x0,p2)) = 
        let bfst = B.Proj (B.ProjN 0) (B.ProjD 2) bt
            bsnd = B.Proj (B.ProjN 1) (B.ProjD 2) bt
            tfst = Op $ OpFst (getType p1) t
            tsnd = Op $ OpSnd (getType p2) t in
        go tfst bfst p1 <|> go tsnd bsnd (substPType x0 tfst p2)
    go _ _ (PFun _ _ _) = empty

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
