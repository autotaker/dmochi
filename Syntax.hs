module Syntax where
data Program = Program { definitions :: [Def]
                       , mainTerm    :: Term } deriving(Show)

type Def = (Symbol,Term)
type Symbol = String
data Term = C Bool | V Symbol
          | Lam [Symbol] Term
          | App Term [Term]
          | Term :+: Term 
          | If Term Term Term 
          | Fail | Omega deriving(Show)

