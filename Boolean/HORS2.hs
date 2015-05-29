module Boolean.HORS2 where
import Boolean.Syntax.Typed 
import Boolean.SelectiveCPS(selectiveCPS,elimTupleP,CPSTerm(..))
import Boolean.HORS(HORS(..),ATerm(..),M)
import Control.Monad.State
import Control.Arrow
import Control.Applicative
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Char
import Id

toHORS :: (MonadId m,Applicative m) => Program -> m HORS
toHORS p = do
    (ds,t0) <- selectiveCPS p >>= elimTupleP
    let l = ["br","end","fail","true","false","if","and","or","not"]
    let trs = [ [("q",["q","q"])] -- br
              , [("q",[])]        -- end
              , [("q",[])]        -- fail
              , [("q",[])]        -- true
              , [("q",[])]        -- false
              , [("q",["q","q","q"])] -- if
              , [("q",["q","q"])] -- and
              , [("q",["q","q"])] -- or
              , [("q",["q"])] -- not
              ]
    ts <- mapM freshId l
    let tenv = M.fromList $ zipWith (\x y -> (x,Var y)) l ts
    (sym,rs) <- flip runStateT [] $ do
        forM_ ds $ \(f,t) -> do
            let (xs,tb) = decompose t
            let f' = capitalize $ name f
            tb' <- lambdaLifting tenv (S.fromList xs) tb 
            registerRule f' xs tb'
        t0' <- lambdaLifting tenv S.empty t0
        sym <- freshId "Main"
        registerRule sym [] t0'
        return sym
    return $ HORS rs (zip ts trs) sym

capitalize :: String -> String
capitalize (x:xs) = toUpper x : xs
capitalize _ = error "capitalizing an empty string"

decompose :: CPSTerm -> ([String],CPSTerm)
decompose (CPSLam [x] t) = first (name x:) $ decompose t
decompose t = ([],t)

lambdaLifting :: (Monad m,Applicative m,MonadId m) => M.Map String ATerm -> S.Set String -> CPSTerm -> M m ATerm
lambdaLifting tenv xs _t = case _t of
    CPSVar x -> pure $ Var $ if S.member (name x) xs then (name x) else capitalize (name x)
    CPSApp _ t1 t2 -> liftA2 (:@) (lambdaLifting tenv xs t1) (lambdaLifting tenv xs t2)
    CPSLam [_] _ -> do
        let (ys,t') = decompose _t
        let zs = freeVariables _t
        let ns = S.toList $ S.intersection xs zs
        let arity (_ :-> s) = 1 + arity s
            arity _ = 0
        let a = arity (getSort t')
        f <- freshId "Fun"
        xs <- replicateM a (freshId "v")
        t'' <- lambdaLifting tenv (S.fromList $ ns ++ ys) t'
        registerRule f (ns ++ ys++xs) (foldl (:@) t'' (map Var xs))
        return $ foldl (:@) (Var f) $ map Var ns
    CPSTrue -> return $ tenv M.! "true"
    CPSFalse -> return $ tenv M.! "false"
    CPSBranch t1 t2 -> liftA2 (\x y -> (tenv M.! "br") :@ x :@ y) 
                              (lambdaLifting tenv xs t1)
                              (lambdaLifting tenv xs t2)
    CPSIf b t1 t2 -> (\x y z -> (tenv M.! "if") :@ x :@ y :@ z)
                    <$> (lambdaLifting tenv xs b)
                    <*> (lambdaLifting tenv xs t1)
                    <*> (lambdaLifting tenv xs t2)
    CPSAnd t1 t2 -> liftA2 (\x y -> (tenv M.! "and") :@ x :@ y) 
                           (lambdaLifting tenv xs t1)
                           (lambdaLifting tenv xs t2)
    CPSOr  t1 t2 -> liftA2 (\x y -> (tenv M.! "or") :@ x :@ y) 
                           (lambdaLifting tenv xs t1)
                           (lambdaLifting tenv xs t2)
    CPSNot t1 -> (\x -> (tenv M.! "not") :@ x ) <$> (lambdaLifting tenv xs t1)
    CPSFail -> return $ tenv M.! "fail"
    CPSOmega -> return $ tenv M.! "end"
    _ -> error "unexpected CPSTuple for lambdaLifting"

registerRule :: Monad m => String -> [String] -> ATerm -> M m ()
registerRule f xs t = modify ((f,xs,t):)

freeVariables :: CPSTerm -> S.Set String
freeVariables _t = execState (go S.empty _t) S.empty where
    go env (CPSVar x) = unless (S.member (name x) env) $ modify (S.insert (name x))
    go env (CPSLam [x] t) = go (S.insert (name x) env) t
    go env (CPSApp _ t1 t2) = go env t1 >> go env t2
    go env (CPSBranch t1 t2) = go env t1 >> go env t2
    go env (CPSIf t1 t2 t3) = go env t1 >> go env t2 >> go env t3
    go env (CPSAnd t1 t2) = go env t1 >> go env t2
    go env (CPSOr t1 t2) = go env t1 >> go env t2
    go env (CPSNot t) = go env t
    go _ CPSTrue = return ()
    go _ CPSFalse = return ()
    go _ CPSOmega = return ()
    go _ CPSFail = return ()
    go _ _ = error "unexpected pattern for freeVariables"
