{-# LANGUAGE TupleSections #-}
module Type where
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Applicative
import Syntax
import Flow(ReducedFlowGraph,Id)
import Control.Arrow
import Control.Monad
import Util
import Data.Array
import Data.Array.ST
import Data.Maybe
import Data.List(intersperse)
import Debug.Trace

data VType = T | F | VFun [([VType],TType)] deriving(Eq,Ord)
data TType = TPrim VType | TFail deriving(Eq,Ord)

instance Show TType where
    show (TPrim ty) = show ty
    show TFail = "Fail"

instance Show VType where
    show T = "T"
    show F = "F"
    show (VFun l) = case l of
        [] -> "Top"
        _ -> concat $ intersperse "," $ map (\(tys,ty) -> "("++show tys ++ " -> " ++ show ty++")") l

data Context = Context { flowEnv :: M.Map [Symbol] [[VType]]
                       , symEnv  :: M.Map Symbol VType } deriving(Eq,Show)

printContext :: Context -> IO ()
printContext (Context flow sym) = do
    putStrLn "--- Flow ---"
    forM_ (M.assocs flow) $ \(fs,tys) -> do
        putStrLn $ "<" ++ concat (intersperse ", " fs) ++ ">"
        forM_ tys $ \tup -> do
            forM_ (zip fs tup) $ \(x,ty) -> do
                putStrLn $ "\t"++x ++ " : " ++ show ty
            putStrLn "***"
        putStrLn ""
    putStrLn "--- Env ---"
    forM_ (M.assocs sym) $ \(x,VFun l) -> do
        putStrLn $ x ++ ":"
        forM_ l $ \(tys,ty) -> putStrLn $ "\t" ++ show tys ++ " -> " ++ show ty
        putStrLn ""


initContext :: Program -> ReducedFlowGraph -> Context
initContext (Program defs _) (_,mapSym,_) = 
    Context (fmap (const []) mapSym) (M.fromList (map (second (const (VFun []))) defs))

saturate :: Program -> ReducedFlowGraph -> [Context]
saturate p flow = iterate (saturateSub (definitions p) flow) (initContext p flow)

saturateSub :: [Def] -> ReducedFlowGraph -> Context -> Context
saturateSub defs flow ctx = Context { flowEnv=env1, symEnv=env2 } where
    env1 = saturateFlow flow (symEnv ctx)
    env2 = saturateSym env1 (symEnv ctx) defs

saturateFlow :: ReducedFlowGraph -> M.Map Symbol VType -> M.Map [Symbol] [[VType]]
saturateFlow (edgeTbl,symMap,leafTbl) env = fmap (tbl!) symMap  where
    terms :: [[Term]]
    terms = catMaybes $ elems leafTbl
    fvarMap :: M.Map [Term] [[Symbol]]
    fvarMap = M.fromList $ map (\ts -> 
              (ts,nub [location M.! x | x <- nub $ ts >>= freeVariables, M.member x location])) terms
    bvarMap :: M.Map [Term] [[Symbol]]
    bvarMap = M.fromList $ map (\ts -> (ts,nub $ ts >>= boundVariables)) terms
    location :: M.Map Symbol [Symbol]
    location = M.fromList $ [ (x,xs) | xs <- M.keys symMap, x <- xs ]
    bb = bounds edgeTbl
    depTbl :: Array Id [Id]
    depTbl = accumArray (flip (:)) [] bb $ 
             [ (t,s) | (s,ts) <- assocs edgeTbl, t <- ts ] ++ 
             [ (symMap M.! xs,s) | (s,Just ts) <- assocs leafTbl, xs <- nub $ (fvarMap M.! ts) ++ (bvarMap M.! ts)]
    tbl :: Array Id [[VType]]
    tbl = runSTArray $ do
        arr <- newArray (bounds leafTbl) []
        let go s | S.null s = return ()
                 | otherwise  = do
                let (v,vs) = S.deleteFindMin s
                ty <- readArray arr v
                ty' <- case leafTbl ! v of
                    Nothing -> do
                        tys <- forM (edgeTbl  ! v) $ readArray arr
                        return $ nub $ concat $ ty:tys
                    Just ts -> do
                        let fvars = fvarMap M.! ts
                            bvars = bvarMap M.! ts
                        tys <- forM fvars $ \fs ->
                            map (zip fs) <$> (readArray arr $ symMap M.! fs)
                        m <- M.fromList <$> forM bvars (\xs -> (xs,) <$> readArray arr (symMap M.! xs))
                        let cands = concat <$> sequence tys
                        let res = nub $ do
                            l <- cands
                            let env' = updateEnv env l
                                f t = saturateTerm m env' t >>= \tty -> case tty of
                                    TPrim ty -> return ty
                                    _ -> empty
                            mapM f ts
                        return res
                if ty' /= ty 
                then writeArray arr v ty' >> go (foldr S.insert vs (depTbl ! v))
                else go vs
        go $ S.fromList $ map fst $ filter (isJust . snd) $ assocs leafTbl
        return arr

updateEnv :: M.Map Symbol VType -> [(Symbol,VType)] -> M.Map Symbol VType
updateEnv = foldl (\acc (x,ty) -> M.insert x ty acc)
    
saturateSym :: M.Map [Symbol] [[VType]] -> M.Map Symbol VType -> [Def] -> M.Map Symbol VType
saturateSym flowEnv symEnv defs = 
    M.fromList $ [ (x,ty) | (x,t) <- defs, let [TPrim ty] = saturateTerm flowEnv symEnv t ]

saturateTerm :: M.Map [Symbol] [[VType]] -> M.Map Symbol VType -> Term -> [TType]
saturateTerm flowEnv = go where
    f env xs tys = foldl (\acc (x,ty) -> M.insert x ty acc) env $ zip xs tys
    go _ (C True) = pure $ TPrim T
    go _ (C False) = pure $ TPrim F
    go env (V x) = pure $ TPrim (env M.! x)
    go _ (Fail _) = pure $ TFail
    go _ (Omega _) = empty
    go env (Lam xs t) = pure $ TPrim (VFun [(tys,ty) | tys <- flowEnv M.! xs, ty <- go (f env xs tys) t ])
    go env (App t ts) = 
        let ty1 = go env t
            ty2s = map (go env) ts
            check = foldr (\l acc -> not (null l) && (TFail `elem` l || acc)) False
        in
        nub $ (pure TFail <* guard (check $ ty1:ty2s)) <|> 
        (do (ty2s',ty) <- [ v | TPrim (VFun l) <- ty1, v <- l]
            forM_ (zip ty2s' ty2s) $ \(ty',ty2) -> guard (any (contain ty') [ ty | TPrim ty <- ty2])
            return ty)
    go env (t1 :+: t2) = go env t1 <|> go env t2
    go env (If t1 t2 t3) =
        let ty1 = go env t1 in
        (pure TFail <* guard (TFail `elem` ty1)) <|>
        (go env t2  <* guard (TPrim T `elem` ty1)) <|>
        (go env t3  <* guard (TPrim F `elem` ty1))

contain :: VType -> VType -> Bool
contain T T = True
contain F F = True
contain (VFun l1) (VFun l2) = all (\x -> any (x==) l2) l1
contain T F = False
contain F T = False
contain t1 t2 = error $ "inconsistent types: " ++ show t1 ++ " " ++ show t2
