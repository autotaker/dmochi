module Language.DMoCHi.ML.HornClause where
import Data.List(intersperse)

newtype HCCS = HCCS { clauses :: [Clause] }

data Clause = Clause { cHead :: Head , cBody :: Body }

data Head = Bot | PVar String [Term] deriving(Show)
type Body = [Term]

data Term = Bool Bool
          | Int Integer
          | Var String
          | Pred String [Term]
          | Add Term Term
          | Sub Term Term
          | Eq  Term Term
          | NEq Term Term
          | Gt  Term Term
          | Lt  Term Term
          | Lte Term Term
          | Gte Term Term
--          | Pair Term Term
          | Not Term
          | And Term Term
          | Iff Term Term
          | Or  Term Term

instance Show HCCS where
    show (HCCS cs) = unlines $ map show cs

instance Show Clause where
    show (Clause Bot body) = 
        "?- " ++ (concat $ intersperse ", " (map show body)) ++ "."
    show (Clause (PVar p ts) body) = 
        show (Pred p ts) ++ " :- " ++ (concat $ intersperse "," (map show body)) ++ "."

instance Show Term where
    showsPrec _ (Bool True) = showString "top"
    showsPrec _ (Bool False) = showString "bot"
    showsPrec _ (Int i) = shows i
    showsPrec _ (Var x) = showString x
    -- showsPrec _ (Pair t1 t2) = showParen True $ shows t1 . showChar ',' . showChar ' ' . shows t2
    showsPrec _ (Pred p []) = showString $ p ++"(dummy)"
    showsPrec _ (Pred p ps) = 
        showString p . showChar '(' .
        (foldr1 (\a b -> a . showChar ',' . showChar ' ' . b) (map shows ps)) .
        showChar ')'
    showsPrec d (Add t1 t2) = showParen (d >= 5) $ 
        (showsPrec 5 t1) . showString " + " . (showsPrec 5 t2)
    showsPrec d (Sub t1 t2) = showParen (d >= 5) $ 
        (showsPrec 5 t1) . showString " - " . (showsPrec 5 t2)
    showsPrec d (Eq t1 t2) = showParen (d >= 4) $ 
        (showsPrec 4 t1) . showString " = " . (showsPrec 4 t2)
    showsPrec d (NEq t1 t2) = showParen (d >= 4) $
        (showsPrec 4 t1) . showString " \\= " . (showsPrec 4 t2)
    showsPrec d (Gt t1 t2) = showParen (d >= 4) $
        (showsPrec 4 t1) . showString " > " . (showsPrec 4 t2)
    showsPrec d (Lt t1 t2) = showParen (d >= 4) $
        (showsPrec 4 t1) . showString " < " . (showsPrec 4 t2)
    showsPrec d (Lte t1 t2) = showParen (d >= 4) $
        (showsPrec 4 t1) . showString " <= " . (showsPrec 4 t2)
    showsPrec d (Gte t1 t2) = showParen (d >= 4) $
        (showsPrec 4 t1) . showString " >= " . (showsPrec 4 t2)
    showsPrec d (And t1 t2) = showParen (d >= 3) $
        (showsPrec 3 t1) . showString " /\\ " . (showsPrec 4 t2)
    showsPrec d (Or  t1 t2) = showParen (d >= 3) $
        (showsPrec 3 t1) . showString " \\/ " . (showsPrec 4 t2)
    showsPrec d (Iff t1 t2) = showParen (d >= 3) $
        (showsPrec 3 t1) . showString " <=> " . (showsPrec 4 t2)
    showsPrec d (Not t1) = showChar '!' . (showsPrec 6 t1)


