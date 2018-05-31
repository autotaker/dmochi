module Language.DMoCHi.ML.HornClause.Syntax where

import Data.List(intersperse)
import Language.DMoCHi.ML.Syntax.Type
import Text.PrettyPrint.HughesPJ
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State.Strict

newtype HCCS = HCCS { clauses :: [Clause] }
instance Monoid HCCS where
  mappend (HCCS a) (HCCS b) = HCCS (a ++ b)
data Clause = Clause { cHead :: Head , cBody :: Body }

data Head = Bot | PVar String [Term] deriving(Show)
type Body = [Term]

data Term = Bool Bool
          | Int Integer
          | Var TId
          | Pred String [Term]
          | Add Term Term
          | Sub Term Term
          | Mul Term Term
          | Div Term Term
          | Eq  Term Term
          | NEq Term Term
          | Gt  Term Term
          | Lt  Term Term
          | Lte Term Term
          | Gte Term Term
          | Not Term
          | And Term Term
          | Or  Term Term

instance HasType Term where
    getType (Bool _) = TBool
    getType (Int _) = TInt
    getType (Var x) = getType x
    getType (Pred _ _) = TBool
    getType (Add _ _) = TInt
    getType (Sub _ _) = TInt
    getType (Mul _ _) = TInt
    getType (Div _ _) = TInt
    getType (Eq _ _) = TBool
    getType (NEq _ _) = TBool
    getType (Gt _ _) = TBool
    getType (Lt _ _) = TBool
    getType (Gte _ _) = TBool
    getType (Lte _ _) = TBool
    getType (Not _) = TBool
    getType (And _ _) = TBool
    getType (Or _ _) = TBool

freeVariables :: Clause -> [TId]
freeVariables clause = S.toList $ execState doit S.empty
    where
    doit = do
        forM_ (cBody clause) term
        case cHead clause of
            Bot -> return ()
            PVar _ ts -> mapM_ term ts
    push k = modify' (S.insert k)
    term = \case
        Bool _ -> return ()
        Int _ -> return ()
        Var x -> push x
        Pred _ ts -> mapM_ term ts
        Add t1 t2 -> term t1 >> term t2
        Sub t1 t2 -> term t1 >> term t2
        Mul t1 t2 -> term t1 >> term t2
        Div t1 t2 -> term t1 >> term t2
        Eq  t1 t2 -> term t1 >> term t2
        NEq t1 t2 -> term t1 >> term t2
        Gt  t1 t2 -> term t1 >> term t2
        Lt  t1 t2 -> term t1 >> term t2
        Gte t1 t2 -> term t1 >> term t2
        Lte t1 t2 -> term t1 >> term t2
        Not t1    -> term t1
        Or  t1 t2 -> term t1 >> term t2
        And t1 t2 -> term t1 >> term t2

renamePVar :: (String -> String) -> HCCS -> HCCS
renamePVar rename (HCCS hccs) = HCCS $
  map (\clause -> Clause { cHead = renameHead (cHead clause)
                         , cBody = renameBody (cBody clause)}) hccs
  where
  renameHead Bot = Bot
  renameHead (PVar s ts) = PVar (rename s) (map renameTerm ts)
  renameBody = map renameTerm
  renameTerm = \case
    Bool b -> Bool b
    Int i -> Int i
    Var x -> Var x
    Pred s ts -> Pred (rename s) (map renameTerm ts)
    Add t1 t2 -> Add (renameTerm t1) (renameTerm t2)
    Sub t1 t2 -> Sub (renameTerm t1) (renameTerm t2)
    Mul t1 t2 -> Mul (renameTerm t1) (renameTerm t2)
    Div t1 t2 -> Div (renameTerm t1) (renameTerm t2)
    Eq t1 t2 -> Eq (renameTerm t1) (renameTerm t2)
    NEq t1 t2 -> NEq (renameTerm t1) (renameTerm t2)
    Gt t1 t2 -> Gt (renameTerm t1) (renameTerm t2)
    Lt t1 t2 -> Lt (renameTerm t1) (renameTerm t2)
    Gte t1 t2 -> Gte (renameTerm t1) (renameTerm t2)
    Lte t1 t2 -> Lte (renameTerm t1) (renameTerm t2)
    Not t1 -> Not (renameTerm t1)
    And t1 t2 -> And (renameTerm t1) (renameTerm t2)
    Or t1 t2 -> Or (renameTerm t1) (renameTerm t2)

predicates :: HCCS -> [(String, [Type])]
predicates (HCCS hccs) = M.toList $ execState doit M.empty
    where
    doit :: State (M.Map String [Type]) ()
    doit = forM_ hccs $ \clause -> do
        forM_ (cBody clause) $ \case
            Pred s ts -> push s (map getType ts)
            _ -> return () 
        case cHead clause of
            Bot -> return ()
            PVar s ts -> push s (map getType ts)
    push k v = modify' (M.insert k v)

renderSMTLib2 :: HCCS -> String
renderSMTLib2 hccs = render doit ++ "\n"
    where
    doit = header $+$ vcat (map renderClause (clauses hccs)) $+$ footer
    header = setLogic $+$ declareFuncs
        where
        setLogic = parens $ text "set-logic" <+> text "HORN"
        declareFuncs = vcat $ map declareFunc (predicates hccs)
        declareFunc (pred, argTypes) = 
            parens $ text "declare-fun" 
                 <+> quote pred 
                 <+> parens (hsep $ map renderType argTypes)
                 <+> text "Bool"
    renderType TInt = text "Int"
    renderType TBool = text "Bool"
    renderType t = error $ "renderSMTLib2: unsupported type :" ++ show t
    quote s = text ("|" ++ s  ++ "|")
    renderClause clause = 
        parens $ text "assert" 
             <+> (parens $ text "forall" 
                       <+> parens (hsep (map renderTId vars)) 
                       <+> (parens $ text "=>" <+> body <+> head))
        where
        vars = freeVariables clause
        head = case cHead clause of
            Bot -> text "false"
            PVar s ts -> renderTerm (Pred s ts)
        body = case cBody clause of
            [] -> text "true"
            ts -> parens $ hsep $ text "and" : map renderTerm ts
    renderTId x = parens $ (quote $ show $ name x) <+> (renderType $ getType x)
    renderTerm = \case
        Bool True -> text "true"
        Bool False -> text "false"
        Int i | i >= 0 -> integer i
              | otherwise -> parens $ text "-" <+> integer (abs i)
        Var x -> quote $ show $ name x
        Pred s ts -> parens $ hsep (quote s : map renderTerm ts)
        Add t1 t2 -> parens $ text "+" <+> renderTerm t1 <+> renderTerm t2
        Sub t1 t2 -> parens $ text "-" <+> renderTerm t1 <+> renderTerm t2
        Mul t1 t2 -> parens $ text "*" <+> renderTerm t1 <+> renderTerm t2
        Div t1 t2 -> parens $ text "/" <+> renderTerm t1 <+> renderTerm t2
        Eq  t1 t2 -> parens $ text "=" <+> renderTerm t1 <+> renderTerm t2
        NEq t1 t2 -> parens $ text "!=" <+> renderTerm t1 <+> renderTerm t2
        Gt  t1 t2 -> parens $ text ">" <+> renderTerm t1 <+> renderTerm t2
        Lt  t1 t2 -> parens $ text "<" <+> renderTerm t1 <+> renderTerm t2
        Gte t1 t2 -> parens $ text ">=" <+> renderTerm t1 <+> renderTerm t2
        Lte t1 t2 -> parens $ text "<=" <+> renderTerm t1 <+> renderTerm t2
        Not t1    -> parens $ text "not" <+> renderTerm t1
        And t1 t2 -> parens $ text "and" <+> renderTerm t1 <+> renderTerm t2
        Or  t1 t2 -> parens $ text "or" <+> renderTerm t1 <+> renderTerm t2
    footer = checkSat $+$ getModel 
        where
        checkSat = parens $ text "check-sat"
        getModel = parens $ text "get-model"

instance Show HCCS where
    show (HCCS cs) = unlines $ map show cs

instance Show Clause where
    show (Clause Bot body) = 
        "?- " ++ (concat $ intersperse ", " (map show body)) ++ "."
    show (Clause (PVar _ []) _) = ""
    show (Clause (PVar p ts) []) = show (Pred p ts) ++ "."
    show (Clause (PVar p ts) body) = 
        show (Pred p ts) ++ " :- " ++ (concat $ intersperse "," (map show body)) ++ "."

instance Show Term where
    showsPrec _ (Bool True) = showString "true"
    showsPrec _ (Bool False) = showString "false"
    showsPrec _ (Int i) = shows i
    showsPrec d (Var x) | d >= 1 = showString (show $ name x)
                        | otherwise = showParen True (showString (show $ name x) . showChar ':' . showsPrec 0 (getType x))
    -- showsPrec _ (Var x) = showString (name x)
    -- showsPrec _ (Pair t1 t2) = showParen True $ shows t1 . showChar ',' . showChar ' ' . shows t2
    showsPrec _ (Pred _ []) = showString "top"
    showsPrec _ (Pred p ps) = 
        showString p . showChar '(' .
        (foldr1 (\a b -> a . showChar ',' . showChar ' ' . b) (map shows ps)) .
        showChar ')'
    showsPrec d (Mul t1 t2) = showParen (d >= 6) $ 
        (showsPrec 6 t1) . showString " * " . (showsPrec 6 t2)
    showsPrec d (Div t1 t2) = showParen (d >= 6) $ 
        (showsPrec 6 t1) . showString " / " . (showsPrec 6 t2)
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
    showsPrec _ (Not t1) = showChar '!' . (showsPrec 6 t1)


