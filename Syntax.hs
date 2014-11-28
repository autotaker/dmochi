module Syntax where
import qualified Data.Sequence as Q
import qualified Data.Set as S
import Data.Foldable(toList)
import Control.Monad.Writer
import Control.Monad.Reader
import Util
import Data.Hashable
import Data.List(intersperse)

data Program = Program { definitions :: [Def]
                       , mainTerm    :: Term } deriving(Show)

type Def = (Symbol,Term)
type Symbol = String
data Term = C Bool | V Symbol | T [Term]
          | Lam Symbol Term
          | Let Symbol Term Term
          | Proj Int Term
          | App Term Term
          | Term :+: Term 
          | If Term Term Term 
          | Fail Symbol | Omega Symbol deriving(Ord,Eq)

instance Show Term where
    show (C True) = "true"
    show (C False) = "false"
    show (V x) = x
    show (T xs) = "<"++concat (intersperse "," (map show xs)) ++ ">"
    show (Lam x t) = "λ " ++ x ++ " . "++show t
    show (Let x t1 t2) = unwords ["let",x,"=",show t1,"in",show t2]
    show (Proj i t) = "#"++show i++ " " ++ "(" ++ show t ++ ")"
    show (App t1 t2) = "("++show t1++") "++ show t2
    show (t1 :+: t2) = unwords ["("++show t1++")","<>",show t2]
    show (If t1 t2 t3) = unwords ["if",show t1,"then",show t2,"else",show t3]
    show (Fail s) = "Fail(" ++ s ++ ")"
    show (Omega s) = "Omega("++ s ++ ")"


symbols :: Program -> [Symbol]
symbols (Program defs t0) = nub $ toList $ execWriter doit where
    push = tell . Q.singleton
    doit = mapM_ (\(f,t) -> push f >> go t) defs >> go t0
    go (C _) = return ()
    go (V x) = push x
    go (T ts) = mapM_ go ts
    go (Fail x) = push x
    go (Omega x) = push x
    go (Lam x t) = push x >> go t
    go (Let x t1 t2) = push x >> go t1 >> go t2
    go (Proj _ t) = go t
    go (App t1 t2) = go t1 >> go t2
    go (t1 :+: t2) = go t1 >> go t2
    go (If t1 t2 t3) = go t1 >> go t2 >> go t3

freeVariables :: Term -> [Symbol]
freeVariables = nub . toList . execWriter . flip runReaderT S.empty . go where
    push = tell . Q.singleton
    go (V x) = fmap (S.member x) ask >>= \b -> unless b $ push x
    go (T ts) = mapM_ go ts
    go (Proj _ t) = go t
    go (Lam x t) = local (S.insert x) $ go t
    go (Let x t1 t2) = go t1 >> local (S.insert x) (go t2)
    go (App t1 t2) = go t1 >> go t2
    go (t1 :+: t2) = go t1 >> go t2
    go (If t1 t2 t3) = go t1 >> go t2 >> go t3
    go _ = return ()

boundVariables :: Term -> [Symbol]
boundVariables = nub . toList . execWriter . go where
    push = tell . Q.singleton
    go (Lam x t) = push x >> go t
    go (Let x t1 t2) = push x >> go t1 >> go t2
    go (Proj _ t) = go t
    go (App t1 t2) = go t1 >> go t2
    go (T ts) = mapM_ go ts
    go (t1 :+: t2) = go t1 >> go t2
    go (If t1 t2 t3) = go t1 >> go t2 >> go t3
    go _ = return ()
    

instance Hashable Term where
    hashWithSalt s (C b) = s `hashWithSalt` (0::Int) `hashWithSalt` b
    hashWithSalt s (V x) = s `hashWithSalt` (1::Int) `hashWithSalt` x
    hashWithSalt s (Fail x) = s `hashWithSalt` (2::Int) `hashWithSalt` x
    hashWithSalt s (Omega x) = s `hashWithSalt` (3::Int) `hashWithSalt` x
    hashWithSalt _ _ = undefined
