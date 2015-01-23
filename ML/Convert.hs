module ML.Convert where
import ML.Syntax
import qualified Boolean.Syntax as B
import qualified Data.Map as M
import Control.Monad
import Control.Applicative
import Data.SBV
import System.IO.Unsafe
import Data.IORef
import Debug.Trace
import Text.Printf

type Constraints = [Value]
type Env = M.Map Id (Either PType Value)

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
    let env = M.fromList [ (x,Left ty) | (x,ty,_) <- functions p ]
    ds <- forM (functions p) $ \(x,ty,e) -> (,) x <$> convertE [] env ty e
    let ps = [("and",tAnd),("or",tOr),("not",tNot)]
    t <- convertE [] env (PInt []) (mainTerm p)
    return $ B.Program (ps++ds) t

convertE :: Constraints -> Env -> PType -> Exp -> IO B.Term
convertE cts env sigma _e = case _e of
    Value v -> convertV cts env sigma v
    Let x (LValue v) e -> 
        convertE (addC cts $ Op (Var x `OpEq` v)) (addE env x (PInt [])) sigma e
    Let x (LApp f vs) e -> do
        let Left ty_f = env ! f
        let (ty_vs,ty_r) = substPType ty_f vs
        es <- zipWithM (convertE cts env) ty_vs (map Value vs)
        B.Let x (foldl B.App (B.V f) es) <$> convertE cts (addE env x ty_r) sigma e
    Let x (LExp ty_v ev) e -> 
        B.Let x <$> convertE cts env ty_v ev <*> convertE cts (addE env x ty_v) sigma e
    Assume v e ->
        assume <$> convertP cts env v <*> convertE (addC cts v) env sigma e
    Lambda x e -> 
        let PFun ty_x ty_r = sigma in
        B.Lam x <$> convertE cts (addE env x ty_x) (ty_r (Var x)) e
    Fail -> return $ B.Fail ""
    Branch e1 e2 -> nondet <$> convertE cts env sigma e1 <*> convertE cts env sigma e2

convertV :: Constraints -> Env -> PType -> Value -> IO B.Term
convertV cts env (PInt ps) v = do
    pnames <- replicateM (length ps) freshId
    let bs = map ($v) ps
    let envs = scanl (uncurry . addE') env $ zip pnames bs
    es <- zipWithM (\env_i b_i -> convertP cts env_i b_i) envs bs
    return $ foldr (uncurry B.Let) (B.T (map B.V pnames)) $ zip pnames es
convertV cts env (PBool ps) v = do
    pnames <- replicateM (length ps) freshId
    let bs = map ($v) ps
    let envs = scanl (uncurry . addE') env $ zip pnames bs
    es <- zipWithM (\env_i b_i -> convertP cts env_i b_i) envs bs
    return $ foldr (uncurry B.Let) (B.T (map B.V pnames)) $ zip pnames es
convertV cts env (PFun ty_x ty_r) v = do
    let Var f = v
    let Left (PFun ty_x' ty_r') = env ! f
    x <- freshId
    B.Lam x <$> do
        y <- freshId
        let env1 = addE env x ty_x
        B.Let y <$> convertV cts env1 ty_x' (Var x) <*> do
            z <- freshId
            let env2 = addE (addE env1 y ty_x') z (ty_r' (Var x))
            B.Let z (B.App (B.V f) (B.V y)) <$> convertV cts env2 (ty_r (Var x)) (Var z)

globalIdRef :: IORef Int
globalIdRef = unsafePerformIO (newIORef 0)

freshId :: IO Id
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
    forM_ cts print

printPredicates :: [(Value,B.Term)] -> IO ()
printPredicates ps = do
    putStrLn "---Predicates---"
    forM_ ps $ \(v,term) -> putStrLn $ show term ++ " : " ++ show v

model :: Constraints -> Env -> IO B.Term
model cts env = do
    let ps = predicates env
    let bs = [ b | (b,Left (PBool _)) <- M.assocs env ]
    let xs = [ x | (x,Left (PInt _))  <- M.assocs env ]
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
        let step acc (p,t) = do
            ThmResult _res <- prove $ problem p
            case _res of
                Unsatisfiable _ -> return (fAnd acc t)
                _ -> do
                    ThmResult _res <- prove $ problem $ Op $ OpNot p
                    case _res of 
                        Unsatisfiable _ -> return (fAnd acc (fNot t))
                        _ -> return acc
        foldM step (B.C True) ps
        
toSBV :: M.Map Id SBool -> M.Map Id SInteger -> Value -> SBool
toSBV boolTbl intTbl = goBool where
    goBool (Var   x) = boolTbl ! x
    goBool (CInt  _) = undefined
    goBool (CBool b) = if b then true else false
    goBool (Op op) = goBoolOp op
    goInt (Var x) = intTbl ! x
    goInt (CInt i) = fromIntegral i
    goInt (CBool _) = undefined
    goInt (Op op) = goIntOp op
    goBoolOp (OpEq v1 v2) = goInt v1 .== goInt v2
    goBoolOp (OpLt v1 v2) = goInt v1 .< goInt v2
    goBoolOp (OpLte v1 v2) = goInt v1 .<= goInt v2
    goBoolOp (OpGt v1 v2) = goInt v1 .> goInt v2
    goBoolOp (OpGte v1 v2) = goInt v1 .>= goInt v2
    goBoolOp (OpAnd v1 v2) = goBool v1 &&& goBool v2
    goBoolOp (OpOr  v1 v2) = goBool v1 ||| goBool v2
    goBoolOp (OpNot  v1) = bnot $ goBool v1 
    goBoolOp _ = undefined
    goIntOp (OpAdd v1 v2) = goInt v1 + goInt v2
    goIntOp (OpSub v1 v2) = goInt v1 - goInt v2
    goIntOp (OpNeg v1) = - goInt v1
    goIntOp _ = undefined

predicates :: Env -> [(Value,B.Term)]
predicates env = do
    (x,ty) <- M.assocs env
    let f xs = do
        let n = B.ProjD $ length xs
        (i,p) <- zip [0..] xs
        pure (p (Var x), B.Proj (B.ProjN i) n (B.V x))
    case ty of
        Right p -> pure (p,B.V x)
        Left (PInt xs) -> f xs
        Left (PBool xs) -> f xs
        _ -> empty

substPType :: PType -> [Value] -> ([PType],PType)
substPType ty [] = ([],ty)
substPType (PFun ty1 ty2) (v:vs) = (ty1:tys,ty) where
    (tys,ty) = substPType (ty2 v) vs
substPType _ _ = error "Type_missmatch"

addC :: Constraints -> Value -> Constraints
addC = flip (:)

addE :: Env -> Id -> PType -> Env
addE env x ty = M.insert x (Left ty) env

addE' :: Env -> Id -> Value -> Env
addE' env x ty = M.insert x (Right ty) env
