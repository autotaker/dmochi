module Alpha where
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import Control.Applicative
import Text.Printf
import qualified Data.Map as M
import qualified Data.Set as S
import Syntax
import Data.List(foldl')

type Err = String

alphaConversion :: Program -> Either Err (Program,[Symbol])
alphaConversion p = runExcept $ do
    (p',memo) <- runStateT (convert p) S.empty
    return (p',S.toList memo)

assert :: (MonadError e m) => Bool -> e -> m ()
assert b e = unless b $ throwError e
    
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
    V x -> V <$> rename x
    Lam xs t -> do
        assert (allDifferent xs) $ 
            printf "Conflicting labels %s at %s" (show xs) label
        xs' <- forM xs (genName label)
        let f e = foldl' (\acc (x,x') -> M.insert x x' acc) e $ zip xs xs'
        local f $ convertTerm (label++"$f") t
    App t ts -> liftA2 App (convertTerm label t)
                           (mapM (convertTerm label) ts)
    t1 :+: t2 -> liftA2 (:+:) (convertTerm label t1) (convertTerm label t2)
    If t1 t2 t3 -> liftA3 If (convertTerm label t1)
                             (convertTerm label t2)
                             (convertTerm label t3)
    t -> pure t

allDifferent :: (Ord a) => [a] -> Bool
allDifferent xs = length xs == S.size (S.fromList xs)

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
