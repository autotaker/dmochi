module Language.DMoCHi.Boolean.PrettyPrint.Typed where

import Text.PrettyPrint
import Language.DMoCHi.Boolean.Syntax.Typed

parenPrec :: Int -> Int -> Doc -> Doc
parenPrec pterm pcur doc 
    | pcur <= pterm = doc
    | otherwise = parens doc

pprintSym :: Symbol -> Doc
pprintSym x = text (name x) <+> colon <+> pprintSort (getSort x)

pprintSort :: Sort -> Doc
pprintSort = go 0 where
    go _ X = text "X"
    go _ Bool = text "Bool"
    go _ (Tuple ss) = brackets $ hsep $ punctuate comma $ map (go 0) ss
    go p (s1 :-> s2) = 
        parenPrec 0 p $ 
            go 1 s1 <+> text "->" <+> go 0 s2

pprintProgram :: Program -> Doc
pprintProgram (Program ds t0) = vcat ds' $+$ t0' where
    ds' = map (\(x,t) -> 
                text "let" <+> pprintSym x <+> text "=" $+$ 
                      indent (pprintTerm 0 t) <> text ";;") ds
    t0' = pprintTerm 0 t0

{-
 - Syntax 
 - T9 := Bool | Symbol | Fail | (n T8{n}) | (T0)
 - T8 := T9 | T8 . (idx/size)
 - T7 := T8 | T7 T8 | not T8
 - T5 := T6 | T5 && T6
 - T4 := T5 | T4 || T5
 - T3 := T4 | T3 <> T4
 - T0 := T3 
 -    | let x : ty = T0 in T0
 -    | assume b; T0
 -    | fun x : ty -> T0
 -}

prec :: Term -> Int
prec (C _)          = 6
prec (V _)          = 6
prec (T _)          = 6
prec (Fail _)       = 6
prec (Proj _ _ _ _) = 5
prec (App _ _ _)    = 4
prec (Not _)        = 4
prec (And _ _)      = 3
prec (Or  _ _)      = 2
prec (Branch _ _ _ _) = 1
prec (Let _ _ _ _)  = 0
prec (Lam _ _)      = 0
prec (Assume _ _ _) = 0

indent :: Doc -> Doc
indent t = nest 4 t

pprintTerm :: Int -> Term -> Doc
pprintTerm p _t = parenPrec (prec _t) p $ case _t of
    C True  -> text "true"
    C False -> text "false"
    V x     -> text $ name x
    T ts    -> 
        parens $ hsep $ int (length ts) : map (pprintTerm 5) ts
    App _ t1 t2 -> 
        let d1 = pprintTerm (prec _t) t1
            d2 = pprintTerm (prec _t+1) t2 in 
        d1 <+> d2
    Proj _ idx size t -> 
        let proj = parens $ int idx <> text "/" <> int size in
        pprintTerm (prec _t) t <> text "." <> proj 
    Lam x t -> 
        text "fun" <+> parens (pprintSym x) <+> text "->"  $+$
        indent (pprintTerm 0 t)
    Let _ x tx t ->
        text "let" <+> pprintSym x <+> text "=" $+$
            indent (pprintTerm 0 tx <+> text "in") $+$ 
        pprintTerm 0 t
    Assume _ b t -> 
        text "assume" <+> pprintTerm 0 b <> semi $+$ 
        pprintTerm 0 t
    Branch _ b t1 t2 ->
        pprintTerm (prec _t) t1 <+> 
        text (if b  then "<+>" else "<>") $$
        pprintTerm (prec _t+1) t2
    And t1 t2 ->
        pprintTerm (prec _t) t1 <+>
        text "&&" <+>
        pprintTerm (prec _t+1) t2
    Or t1 t2 ->
        pprintTerm (prec _t) t1 <+>
        text "||" <+>
        pprintTerm (prec _t+1) t2
    Not t1 ->
        text "not" <+> pprintTerm (prec _t+1) t1
    Fail x -> text "fail" <> parens (pprintSort (getSort x))
