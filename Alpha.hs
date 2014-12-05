module Alpha(Err,alphaConversion) where
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import Control.Applicative
import Text.Printf
import qualified Data.Map as M
import qualified Data.Set as S
import Syntax
import Util

alphaConversion :: Program -> Either Err (Program,[Symbol])
alphaConversion p = runExcept $ do
    (p',memo) <- runStateT (convert p) S.empty
    return (p',S.toList memo)

convert :: Program -> StateT (S.Set String) (Except Err) Program
convert p = do
    let defs = definitions p
        syms = map fst defs
        env = M.fromList [ (s,s) | s <- syms ]
    defs' <- forM defs $ \(f,t) -> do
        b <- S.member f <$> get
        assert (not b) $ printf "Multiple declarations of %s" f
        modify (S.insert f)
        t' <- runReaderT (convertTerm f t) env
        return (f,t')
    Program defs' <$> runReaderT (convertTerm "@" $ mainTerm p) env

type AMonad a = ReaderT (M.Map String String) (StateT (S.Set String) (Except Err)) a

convertTerm :: String -> Term -> AMonad Term
convertTerm label _t = case _t of
    C _ -> pure _t
    V x -> V <$> rename x
    T ts -> T <$> mapM (convertTerm label) ts
    TF  -> pure TF
    Proj i j t -> Proj i j <$> convertTerm label t
    Let x t1 t2 -> do
        x' <- genName label x
        liftA2 (Let x') (convertTerm label t1) (local (M.insert x x') $ convertTerm label t2)
    Lam x t -> do
        x' <- genName label x
        Lam x' <$> (local (M.insert x x') $ convertTerm (label++"$f") t)
    App t1 t2 -> liftA2 App (convertTerm label t1) (convertTerm label t2)
--    t1 :+: t2 -> liftA2 (:+:) (convertTerm label t1) (convertTerm label t2)
    If t1 t2 t3 -> liftA3 If (convertTerm label t1)
                             (convertTerm label t2)
                             (convertTerm label t3)
    Fail _ -> Fail <$> genName label "Fail"
    Omega _ -> Omega <$> genName label "Omega"

rename :: Symbol -> AMonad Symbol
rename x = do
    env <- ask
    case M.lookup x env of
        Nothing -> throwError $ printf "Undefined variable: %s" x
        Just x' -> return x'

genName :: String -> Symbol -> AMonad Symbol
genName label x = do
    s <- get
    let n = S.size s
        x' = printf "%s_%d@%s" x n label
    put $ S.insert x' s
    return x'
