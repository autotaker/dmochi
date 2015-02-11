module Boolean.HORS where
import Boolean.Syntax hiding(freeVariables)
import Boolean.CPS(cps,STerm(..))
import Control.Monad.State
import Control.Arrow
import Control.Applicative
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Char
import Id

data HORS = HORS { rules     :: [Rule]
                 , terminals :: [(String,[(String,[String])])]
                 , startSym  :: String }

type Rule = (String,[String],ATerm)

data ATerm = Var String | ATerm :@ ATerm

type M m a = StateT [Rule] m a

toHORS :: (MonadId m,Applicative m) => Program -> m HORS
toHORS p = do
    (ds,t0) <- cps p
    let l = ["br","end","fail","true","false"]
    let trs = [ [("q0",["q0","q0"]),("q1",["q1","q1"])] -- br
              , [("q0",[]),("q1",[])]                   -- end
              , [("q1",[])]                             -- fail
              , [("q0",["q0","q1"]),("q1",["q1","q1"])] -- true
              , [("q0",["q1","q0"]),("q1",["q1","q1"])] -- false
              ]
    ts <- mapM freshId l
    let tenv = M.fromList $ zipWith (\x y -> (x,Var y)) l ts
    (sym,rs) <- flip runStateT [] $ do
        forM_ ds $ \(f,t) -> do
            let (xs,tb) = decompose t
            let f' = capitalize f
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

decompose :: STerm -> ([String],STerm)
decompose (SLam x t) = first (x:) $ decompose t
decompose t = ([],t)

lambdaLifting :: (Monad m,Applicative m,MonadId m) => M.Map String ATerm -> S.Set String -> STerm -> M m ATerm
lambdaLifting tenv xs _t = case _t of
    SV x -> pure $ Var $ if S.member x xs then x else capitalize x
    SApp t1 t2 -> liftA2 (:@) (lambdaLifting tenv xs t1) (lambdaLifting tenv xs t2)
    SLam _ _ -> do
        let (ys,t') = decompose _t
        let zs = freeVariables _t
        let ns = S.toList $ S.intersection xs zs
        f <- freshId "Fun"
        t'' <- lambdaLifting tenv (S.fromList $ ns ++ ys) t'
        registerRule f (ns ++ ys) t''
        return $ foldl (:@) (Var f) $ map Var ns
    STrue -> return $ tenv M.! "true"
    SFalse -> return $ tenv M.! "false"
    SBranch -> return $ tenv M.! "br"
    SFail -> return $ tenv M.! "fail"
    SOmega -> return $ tenv M.! "end"

registerRule :: Monad m => String -> [String] -> ATerm -> M m ()
registerRule f xs t = modify ((f,xs,t):)

freeVariables :: STerm -> S.Set String
freeVariables _t = execState (go S.empty _t) S.empty where
    go env (SV x) = unless (S.member x env) $ modify (S.insert x)
    go env (SLam x t) = go (S.insert x env) t
    go env (SApp t1 t2) = go env t1 >> go env t2
    go _ _ = return ()
