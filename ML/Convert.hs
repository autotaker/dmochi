module ML.Convert where
import ML.Syntax
import qualified Boolean.Syntax as B
import qualified Data.Map as M
import Control.Monad
import Control.Applicative
import Data.SBV
import Data.Maybe(fromJust)
import System.IO.Unsafe
import Data.IORef
import Text.Printf

type Constraints = [Value]
type Env = M.Map Id (Either PType Value)

-- syntax sugars
assume :: B.Term -> B.Term -> B.Term
assume p e = B.If p e (B.Omega "")
nondet :: B.Term -> B.Term -> B.Term
nondet e1 e2 = B.If B.TF e1 e2

fAnd :: B.Term -> B.Term -> B.Term
fAnd t1 t2 = B.App (B.V "and") (B.T [t1,t2])

fOr  :: B.Term -> B.Term -> B.Term
fOr t1 t2 = B.App (B.V "or") (B.T [t1,t2])

fNot  :: B.Term -> B.Term
fNot t1 = B.App (B.V "not") t1

convertE :: Constraints -> Env -> PType -> Exp -> IO B.Term
convertE cts env sigma _e = case _e of
    Value v -> convertV cts env sigma v
    Let x (LValue v) e -> 
        convertE (addC cts $ Op (Var x `OpEq` v)) (addE env x (PInt [])) sigma e
    Let x (LApp f vs) e -> do
        let Left ty_f = env M.! f
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
    let Left (PFun ty_x' ty_r') = env M.! f
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
    let n = length ps
    let bs = [ b | (b,Left (PBool _)) <- M.assocs env ]
    let xs = [ x | (x,Left (PInt _))  <- M.assocs env ]
    fool <- isVacuous $ do
        boolTbl <- fmap M.fromList $ forM bs $ \b -> (,) b <$> forall b
        intTbl  <- fmap M.fromList $ forM xs $ \x -> (,) x <$> forall x
        constrain $ bAnd (map (toSBV boolTbl intTbl) cts)
        return (true :: SBool)
    let problem :: Symbolic SBool
        problem = do
            -- construct model
            a <- exists "a" :: Symbolic SInt16
            b <- exists "b" :: Symbolic SInt16
            forM_ [a,b] $ \x -> constrain $ (fromIntegral (-n)) .<= x &&& x .< fromIntegral n
            -- constrain
            boolTbl <- fmap M.fromList $ forM bs $ \b -> (,) b <$> forall b
            intTbl  <- fmap M.fromList $ forM xs $ \x -> (,) x <$> forall x

            -- eval
            let er = map (toSBV boolTbl intTbl . fst) ps
            let f x j = (x .== fromIntegral j ==> er !! j) &&& 
                        (x .== fromIntegral (-j-1) ==> bnot (er !! j)) 
            let ea = bAnd $ [ f a j | j <- [0..n-1] ] 
                eb = bAnd $ [ f b j | j <- [0..n-1] ]
            return $ bAnd (map (toSBV boolTbl intTbl) cts) ==> (ea &&& eb)
    printConstraints cts
    printPredicates ps
    if fool then do
        putStrLn "constraints are vacuous"
        return (B.C False)
    else do
        res <- sat problem
        print res
        if modelExists res then do
            let g v = map (fromJust .flip getModelValue res) v
            let [a,b] = map fromIntegral $ (g ["a","b"] :: [Int16])
            let f x | x >= 0 = ps !! x 
                    | otherwise = let (p,t) = ps !! (-x-1) in (Op (OpNot p),fNot t)
            let [ea,eb] = map f [a,b]
            if a == b then do
                printf "%s\n" (show $ fst ea)
                return $ (snd ea)
            else if a == -b-1 then do
                printf "%s\n" (show $ CBool False)
                return $ B.C False
            else do
                printf "AND (%s) (%s)\n" (show $ fst ea) (show $ fst eb)
                return $ fAnd (snd ea) (snd eb)
        else
            return (B.C True)
        
toSBV :: M.Map Id SBool -> M.Map Id SInteger -> Value -> SBool
toSBV boolTbl intTbl = goBool where
    goBool (Var x) = boolTbl M.! x
    goBool (CInt _) = undefined
    goBool (CBool b) = if b then true else false
    goBool (Op op) = goBoolOp op
    goInt (Var x) = intTbl M.! x
    goInt (CInt i) = fromIntegral i
    goInt (CBool _) = undefined
    goInt (Op op) = goIntOp op
    goBoolOp (OpEq v1 v2) = goInt v1 .== goInt v2
    goBoolOp (OpLt v1 v2) = goInt v1 .< goInt v2
    goBoolOp (OpGt v1 v2) = goInt v1 .> goInt v2
    goBoolOp (OpAnd v1 v2) = goBool v1 &&& goBool v2
    goBoolOp (OpOr  v1 v2) = goBool v1 &&& goBool v2
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
