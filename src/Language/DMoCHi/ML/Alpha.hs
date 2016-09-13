{-# LANGUAGE FlexibleContexts #-}
module Language.DMoCHi.ML.Alpha(alpha,AlphaError) where
import Language.DMoCHi.ML.Syntax.UnTyped
import Language.DMoCHi.Common.Id
import Control.Monad.Except
import Control.Monad.Reader
import qualified Data.Map as M
import Control.Applicative
import Data.List(sort,group)

data AlphaError = UndefinedVariable String
                | MultipleDefinition [String]

instance Show AlphaError where
    show (UndefinedVariable s) = "UndefinedVariable: "++s
    show (MultipleDefinition fs) = "MultipleDefinition: "++show fs

type M m a = ReaderT (M.Map String String) m a

alpha :: (MonadError AlphaError m,MonadId m,Applicative m) => Program -> m Program
alpha (Program fs t0) = do
    env <- M.fromList <$> mapM (\(x,_,_) -> (,) x <$> freshId x) fs
    when (M.size env /= length fs) $ do
        let fs' = map head $ filter ((>1).length) $ group $ sort $ map (\(x,_,_) -> x) fs
        throwError $ MultipleDefinition fs'
    flip runReaderT env $ do
        fs' <- forM fs $ \(x,p,e) -> (,,) <$> rename x <*> pure p <*> renameE e
        t0' <- renameE t0
        return $ Program fs' t0'

rename :: MonadError AlphaError m => String -> M m String
rename x = do
    env <- ask
    let m = M.lookup x env
    case m of
        Nothing -> throwError $ UndefinedVariable x
        Just x' -> return x'

{-
renameP :: (MonadError AlphaError m,MonadId m, Applicative m) => PType -> M m PType
renameP (PInt ps)  = PInt  <$> mapM (\(x,v) -> register x (renameV v)) ps
renameP (PBool ps) = PBool <$> mapM (\(x,v) -> register x (renameV v)) ps
renameP (PPair p1 (x,p2)) = PPair <$> renameP p1 <*> register x (renameP p2)
renameP (PFun  p1 (x,p2)) = PFun  <$> renameP p1 <*> register x (renameP p2)
-}


renameE :: (MonadError AlphaError m,MonadId m, Applicative m) => Exp -> M m Exp
renameE (Value v) = fmap Value $ renameV v
renameE (Let x lv e) = do
    lv' <- case lv of
        LValue v -> LValue <$> renameV v
        LApp f vs -> LApp <$> rename f <*> mapM renameV vs
        LExp p ev -> LExp <$> pure p <*> renameE ev
        LRand -> pure LRand
    (x',e') <- register x (renameE e)
    return $ Let x' lv' e'
renameE (Assume v e) = liftA2 Assume (renameV v) (renameE e)
renameE (Lambda xs e) = uncurry Lambda <$> register' xs (renameE e)
renameE Fail = pure Fail
renameE (Branch e1 e2) = liftA2 Branch (renameE e1) (renameE e2)


renameV :: (MonadError AlphaError m,Applicative m) => Value -> M m Value
renameV (Var x) = Var <$> rename x
renameV (CInt i) = return $ CInt i
renameV (CBool b) = return $ CBool b
renameV (Pair v1 v2) = liftA2 Pair (renameV v1) (renameV v2)
renameV (Op op) = Op <$> case op of
    OpAdd v1 v2 -> liftA2 OpAdd (renameV v1) (renameV v2)
    OpSub v1 v2 -> liftA2 OpSub (renameV v1) (renameV v2)
    OpNeg v1 -> fmap OpNeg (renameV v1)
    OpEq v1 v2 -> liftA2 OpEq (renameV v1) (renameV v2)
    OpLt v1 v2 -> liftA2 OpLt (renameV v1) (renameV v2)
    OpGt v1 v2 -> liftA2 OpGt (renameV v1) (renameV v2)
    OpLte v1 v2 -> liftA2 OpLte (renameV v1) (renameV v2)
    OpGte v1 v2 -> liftA2 OpGte (renameV v1) (renameV v2)
    OpAnd v1 v2 -> liftA2 OpAnd (renameV v1) (renameV v2)
    OpOr  v1 v2 -> liftA2 OpOr  (renameV v1) (renameV v2)
    OpFst v1 -> fmap OpFst (renameV v1)
    OpSnd v1 -> fmap OpSnd (renameV v1)
    OpNot v1 -> fmap OpNot (renameV v1)

register :: (MonadError AlphaError m,MonadId m) => String -> M m a -> M m (String,a)
register x m = do
    x' <- freshId x
    v  <- local (M.insert x x') m
    return (x',v)

register' :: (MonadError AlphaError m,MonadId m) => [String] -> M m a -> M m ([String],a)
register' xs m = do
    xs' <- mapM freshId xs
    v  <- local (\env -> foldr (uncurry M.insert) env (zip xs xs')) m
    return (xs',v)
