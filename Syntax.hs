module Syntax where
import qualified Data.Sequence as Q
import Data.Foldable(toList)
import Control.Monad.Writer
import Util
import Data.Hashable

data Program = Program { definitions :: [Def]
                       , mainTerm    :: Term } deriving(Show)

type Def = (Symbol,Term)
type Symbol = String
data Term = C Bool | V Symbol
          | Lam [Symbol] Term
          | App Term [Term]
          | Term :+: Term 
          | If Term Term Term 
          | Fail Symbol | Omega Symbol deriving(Show,Eq)

symbols :: Program -> [Symbol]
symbols (Program defs t0) = nub $ toList $ execWriter doit where
    push = tell . Q.singleton
    doit = mapM_ (\(f,t) -> push f >> go t) defs >> go t0
    go (C _) = return ()
    go (V x) = push x
    go (Fail x) = push x
    go (Omega x) = push x
    go (Lam xs t) = mapM_ push xs >> go t
    go (App t ts) = go t >> mapM_ go ts
    go (t1 :+: t2) = go t1 >> go t2
    go (If t1 t2 t3) = go t1 >> go t2 >> go t3

instance Hashable Term where
    hashWithSalt s (C b) = s `hashWithSalt` (0::Int) `hashWithSalt` b
    hashWithSalt s (V x) = s `hashWithSalt` (1::Int) `hashWithSalt` x
    hashWithSalt s (Fail x) = s `hashWithSalt` (2::Int) `hashWithSalt` x
    hashWithSalt s (Omega x) = s `hashWithSalt` (3::Int) `hashWithSalt` x
    hashWithSalt _ _ = undefined
