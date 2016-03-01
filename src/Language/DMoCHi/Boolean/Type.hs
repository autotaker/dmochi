{-# LANGUAGE TupleSections, FlexibleContexts #-}
module Language.DMoCHi.Boolean.Type where
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Applicative
import Language.DMoCHi.Boolean.Syntax
import Language.DMoCHi.Boolean.Flow(FlowGraph,Id)
import Control.Arrow(second)
import Control.Monad
import Language.DMoCHi.Boolean.Util
import Data.Array
import Data.Array.ST
import Data.Maybe
import Data.List(intersperse)
import Data.List((\\))

data VType = VT | VF | VTup [VType] |VFun [(VType,TType)] deriving(Eq,Ord)
data TType = TPrim VType | TFail deriving(Eq,Ord)

instance Show TType where
    show (TPrim ty) = show ty
    show TFail = "Fail"

instance Show VType where
    show VT = "T"
    show VF = "F"
    show (VTup l) = show l
    show (VFun l) = case l of
        [] -> "Top"
        _ -> concat $ intersperse "^" $ map (\(ty1,ty2) -> "("++show ty1 ++ " -> " ++ show ty2++")") l

data Context = Context { flowEnv :: M.Map Symbol [VType]
                       , symEnv  :: M.Map Symbol  VType } deriving(Eq,Show)

printContext :: Context -> IO ()
printContext (Context flow sym) = do
    putStrLn "--- Flow ---"
    forM_ (M.assocs flow) $ \(f,tys) -> do
        putStrLn $ f ++ ":"
        forM_ tys $ \ty -> putStrLn $ "\t" ++ show ty
        putStrLn ""
    putStrLn "--- Env ---"
    forM_ (M.assocs sym) $ \(x,VFun l) -> do
        putStrLn $ x ++ ":"
        forM_ l $ \(tys,ty) -> putStrLn $ "\t" ++ show tys ++ " -> " ++ show ty
        putStrLn ""

initContext :: Program -> FlowGraph -> Context
initContext (Program defs _) (_,mapSym,_) = 
    Context (fmap (const []) mapSym) (M.fromList (map (second (const (VFun []))) defs))

saturate :: Program -> FlowGraph -> [Context]
saturate p flow = iterate (saturateSub (definitions p) flow) (initContext p flow)

saturateSub :: [Def] -> FlowGraph -> Context -> Context
saturateSub defs flow ctx = Context { flowEnv=env1, symEnv=env2 } where
    env1 = saturateFlow flow (symEnv ctx)
    env2 = saturateSym env1 (symEnv ctx) defs

saturateFlow :: FlowGraph -> M.Map Symbol VType -> M.Map Symbol [VType]
saturateFlow (edgeTbl,symMap,leafTbl) env = fmap (tbl!) symMap  where
    terms :: [(Id,Term ())]
    terms = [ (i,t)     | (i,Just t) <- assocs leafTbl ]
    fvarMap = M.fromList $ map (\(i,t) -> (i,freeVariables t \\ (M.keys env))) terms
    bvarMap = M.fromList $ map (\(i,t) -> (i,boundVariables t)) terms
    bb = bounds edgeTbl
    depTbl :: Array Id [Id]
    depTbl = accumArray (flip (:)) [] bb $ 
             [ (t,s) | (s,ts) <- assocs edgeTbl, t <- ts ] ++ 
             [ (symMap M.! x,s) | (s,Just _) <- assocs leafTbl, x <- nub $ (fvarMap M.! s) ++ (bvarMap M.! s)]
    tbl :: Array Id [VType]
    tbl = runSTArray $ do
        arr <- newArray (bounds leafTbl) []
        let go s | S.null s = return ()
                 | otherwise  = do
                let (v,vs) = S.deleteFindMin s
                ty <- readArray arr v
                ty' <- case leafTbl ! v of
                    Nothing -> do
                        tys <- forM (edgeTbl  ! v) $ readArray arr
                        let res = nub $ concat $ ty : tys
                        return res
                    Just (V _ _) -> do
                        tys <- forM (edgeTbl  ! v) $ readArray arr
                        let res = nub $ concat $ ty : tys
                        return res
                    Just t -> do
                        let fvars = fvarMap M.! v
                            bvars = bvarMap M.! v
                        tys <- forM fvars $ \f -> readArray arr $ symMap M.! f
                        m <- M.fromList <$> forM bvars (\xs -> (xs,) <$> readArray arr (symMap M.! xs))
                        let cands = sequence tys
                        let res = nub $ do
                            l <- cands
                            let env' = updateEnv env (zip fvars l)
                                f _t = saturateTerm m env' _t >>= \tty -> case tty of
                                    TPrim _ty -> return _ty
                                    _ -> empty
                            f t
                        return res
                if ty' /= ty 
                then writeArray arr v ty' >> (go (foldr S.insert vs (depTbl ! v)))
                else go vs
        go $ S.fromList $ map fst $ filter (isJust . snd) $ assocs leafTbl
        return arr

updateEnv :: M.Map Symbol VType -> [(Symbol,VType)] -> M.Map Symbol VType
updateEnv = foldl (\acc (x,ty) -> M.insert x ty acc)
    
saturateSym :: M.Map Symbol [VType] -> M.Map Symbol VType -> [Def] -> M.Map Symbol VType
saturateSym _flowEnv _symEnv defs = 
    M.fromList $ [ (x,ty) | (x,t) <- defs, let [TPrim ty] = saturateTerm _flowEnv _symEnv t ]

saturateTerm :: M.Map Symbol [VType] -> M.Map Symbol VType -> Term () -> [TType]
saturateTerm _flowEnv = go where
    go _ (C _ True) = pure $ TPrim VT
    go _ (C _ False) = pure $ TPrim VF
    go env (V _ x) = pure $ TPrim (env M.! x)
    go _ (Fail _ _) = pure $ TFail
    go _ (TF _)    = pure (TPrim VT) <|> pure (TPrim VF)
    go _ (Omega _ _) = empty
    go env (Lam _ x t) = pure $ TPrim (VFun [(tyx,ty) | tyx <- _flowEnv M.! x, ty <- go (M.insert x tyx env) t ])
    go env (App _ t1 t2) = 
        let ty1 = go env t1
            ty2 = go env t2 in
        nub $ (pure TFail <* guard (TFail `elem` ty1)) <|> 
              (pure TFail <* guard (not (null ty1) && (TFail `elem` ty2))) <|>
              (do (ty2',ty) <- [ v | TPrim (VFun l) <- ty1, v <- l]
                  guard (any (contain ty2') [ _ty | TPrim _ty <- ty2])
                  return ty)
    go env (If _ t1 t2 t3) =
        let ty1 = go env t1 in
        nub $ (pure TFail <* guard (TFail `elem` ty1)) <|>
              (go env t2  <* guard (TPrim VT `elem` ty1)) <|>
              (go env t3  <* guard (TPrim VF `elem` ty1))
    go env (T _ ts) = 
        let check = foldr (\tyi acc -> (TFail `elem` tyi) || (not (null tyi) && acc)) False
            tys = map (go env) ts 
            tys' = map (\l -> [ ty | TPrim ty <- l]) tys
        in (pure TFail <* guard (check tys)) <|> (TPrim . VTup <$> sequence tys')
    go env (Let _ x t1 t2) =
        let ty1  = go env t1
            ty1' = [ tyx | TPrim tyx <- ty1 ]
        in nub $ (pure TFail <* guard (TFail `elem` ty1)) <|>
                 msum (map (\tyx -> go (M.insert x tyx env) t2) ty1')
    go env (Proj _ n _ t) = 
        let tys = go env t in 
        nub $ map (\ty -> case ty of
            TFail -> TFail
            TPrim (VTup ts) -> TPrim (ts !! projN n)
            TPrim _ -> undefined) tys
           
contain :: VType -> VType -> Bool
contain VT VT = True
contain VF VF = True
contain (VFun l1) (VFun l2) = all (\x -> any (x==) l2) l1
contain VT VF = False
contain VF VT = False
contain (VTup t1) (VTup t2) = all (uncurry contain) $ zip t1 t2
contain t1 t2 = error $ "inconsistent types: " ++ show t1 ++ " " ++ show t2
