module Boolean.Alpha(Err,alphaConversion) where
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import Control.Applicative
import Text.Printf
import qualified Data.Map as M
import Boolean.Syntax
import Boolean.Util

alphaConversion :: Program -> Either Err (Program,[(Symbol,Term ())])
alphaConversion p = runExcept $ do
    (p',memo) <- runStateT (convert p) (M.fromList [("true",C () True),("false",C () False),("*",TF ())])
    return (p',M.toList memo)

type Acc = M.Map String (Term ())
convert :: Program -> StateT Acc (Except Err) Program
convert p = do
    let defs = definitions p
        syms = map fst defs
        env = M.fromList [ (s,s) | s <- syms ]
    defs' <- forM defs $ \(f,t) -> do
        b <- M.member f <$> get
        assert (not b) $ printf "Multiple declarations of %s" f
        modify (M.insert f (V () f))
        t' <- runReaderT (convertTerm f t) env
        return (f,t')
    Program defs' <$> runReaderT (convertTerm "@" $ mainTerm p) env

type AMonad a = ReaderT (M.Map String String) (StateT Acc (Except Err)) a

convertTerm :: String -> Term () -> AMonad (Term ())
convertTerm label _t = case _t of
    C _ _ -> pure _t
    V _ x -> V () <$> rename x
    T _ ts -> T () <$> mapM (convertTerm label) ts
    TF _ -> pure (TF ())
    Proj _ i j t -> Proj () i j <$> convertTerm label t
    Let _ x t1 t2 -> do
        x' <- mfix (genName label x . V ())
        liftA2 (Let () x') (convertTerm label t1) (local (M.insert x x') $ convertTerm label t2)
    Lam _ x t -> do
        x' <- mfix (genName label x . V ())
        Lam () x' <$> (local (M.insert x x') $ convertTerm (label++"$f") t)
    App _ t1 t2 -> liftA2 (App ()) (convertTerm label t1) (convertTerm label t2)
--    t1 :+: t2 -> liftA2 (:+:) (convertTerm label t1) (convertTerm label t2)
    If _ t1 t2 t3 -> liftA3 (If ()) (convertTerm label t1)
                                    (convertTerm label t2)
                                    (convertTerm label t3)
    Fail _ _ -> Fail () <$> mfix (genName label "Fail".Fail ())
    Omega _ _ -> Omega () <$> mfix (genName label "Omega".Omega ())

rename :: Symbol -> AMonad Symbol
rename x = do
    env <- ask
    case M.lookup x env of
        Nothing -> throwError $ printf "Undefined variable: %s" x
        Just x' -> return x'

genName :: String -> Symbol -> Term () -> AMonad Symbol
genName label x t = do
    s <- get
    let n = M.size s
        x' = printf "%s_%d@%s" x n label
    put $ M.insert x' t s
    return x'
