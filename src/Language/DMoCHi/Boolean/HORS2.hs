{-# LANGUAGE FlexibleContexts #-}
module Language.DMoCHi.Boolean.HORS2 where

import Language.DMoCHi.Boolean.Syntax.Typed 
import Language.DMoCHi.Boolean.SelectiveCPS(selectiveCPS,elimTupleP,CPSTerm(..),elimBoolP)
import Language.DMoCHi.Boolean.HORS(HORS(..),ATerm(..),M,Automaton(..))
import Control.Monad.State
import Control.Arrow
import Control.Applicative
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Char
import Language.DMoCHi.Common.Id

toHORS :: (MonadId m, Applicative m) => Program -> m HORS
toHORS p = do
    (ds,t0) <- selectiveCPS p >>= elimTupleP
    let ranks = [("br",2),("end",0),("fail",0),("btrue",0),("bfalse",0),
                 ("if",3),("and",2),("or",2),("not",1) ]
    let qs = ["q","qt","qf"]
    let l = map fst ranks
    let trs "q" "br" = [[(1,"q"),(2,"q")]]
        trs "q" "end" = [[]]
        trs "qt" "btrue" = [[]]
        trs "qf" "bfalse" = [[]]
        trs "q" "if" = [ [(1,"qt"),(2,"q")]
                       , [(1,"qf"),(3,"q")]
                       , [(2,"q"),(3,"q")] ]
        trs "qt" "and" = [ [(1,"qt"),(2,"qt")] ]
        trs "qf" "and" = [ [(1,"qf")], [(2,"qf")]]
        trs "qt" "or"  = [ [(1,"qt")], [(2,"qt")]]
        trs "qf" "or"  = [ [(1,"qf"), (2,"qf") ]]
        trs "qt" "not" = [ [(1,"qf")]]
        trs "qf" "not" = [ [(1,"qt")]]
        trs _ _ = []
    let tenv = M.fromList $ map (\x -> (x,Var x)) l
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
    return $ HORS rs (Automaton ranks qs (Right trs)) sym

toHORSChurch :: (MonadId m,Applicative m) => Program -> m HORS
toHORSChurch p = do
    (ds,t0) <- selectiveCPS p >>= elimTupleP >>= elimBoolP
    let ranks = [("br",2),("end",0),("fail",0)]
    let qs = ["q"]
    let l = map fst ranks
    let trs "q" "br" = Just ["q","q"]
        trs "q" "end" = Just []
        trs _ _ = Nothing
    let tenv = M.fromList $ map (\x -> (x,Var x)) l
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
    return $ HORS rs (Automaton ranks qs (Left trs)) sym

capitalize :: String -> String
capitalize (x:xs) = toUpper x : xs
capitalize _ = error "capitalizing an empty string"

decompose :: CPSTerm -> ([String],CPSTerm)
decompose (CPSLam x t) = first (name x:) $ decompose t
decompose t = ([],t)

lambdaLifting :: (Monad m,Applicative m,MonadId m) => M.Map String ATerm -> S.Set String -> CPSTerm -> M m ATerm
lambdaLifting tenv xs _t = case _t of
    CPSVar x -> pure $ Var $ if S.member (name x) xs then (name x) else capitalize (name x)
    CPSApp _ t1 t2 -> liftA2 (:@) (lambdaLifting tenv xs t1) (lambdaLifting tenv xs t2)
    CPSLam _ _ -> do
        let (ys,t') = decompose _t
        let zs = freeVariables _t
        let ns = S.toList $ S.intersection xs zs
        let arity (_ :-> s) = 1 + arity s
            arity _ = 0
        let a = arity (getSort t')
        f <- freshId "Fun"
        vs <- replicateM a (freshId "v")
        t'' <- lambdaLifting tenv (S.fromList $ ns ++ ys) t'
        registerRule f (ns ++ ys++vs) (foldl (:@) t'' (map Var vs))
        return $ foldl (:@) (Var f) $ map Var ns
    CPSTrue -> return $ tenv M.! "btrue"
    CPSFalse -> return $ tenv M.! "bfalse"
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
    go env (CPSLam x t) = go (S.insert (name x) env) t
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
