module Language.DMoCHi.Boolean.PrettyPrint.SelectiveCPS where

import Text.PrettyPrint
import Language.DMoCHi.Boolean.SelectiveCPS hiding(name,Symbol)
import Language.DMoCHi.Boolean.Syntax.Typed(Sort(..), HasSort(..), Symbol(..))

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

pprintProgram :: CPSProgram -> Doc
pprintProgram (ds,t0) = vcat ds' $+$ t0' where
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


prec :: CPSTerm -> Int
prec CPSTrue        = 6
prec CPSFalse       = 6
prec (CPSVar _)     = 6
prec (CPSTuple _)   = 6
prec (CPSProj _ _ _ _) = 5
prec CPSFail        = 6
prec CPSOmega       = 6
prec (CPSApp _ _ _)   = 4
prec (CPSNot _)     = 4
prec (CPSAnd _ _)   = 3
prec (CPSOr  _ _)   = 2
prec (CPSBranch _ _)= 1
prec (CPSLam _ _)   = 0
prec (CPSIf _ _ _)  = 0

indent :: Doc -> Doc
indent t = nest 4 t

pprintTerm :: Int -> CPSTerm -> Doc
pprintTerm p _t = parenPrec (prec _t) p $ case _t of
    CPSTrue  -> text "true"
    CPSFalse -> text "false"
    CPSVar x -> text $ name x
    CPSTuple ts    -> 
        parens $ hsep $ int (length ts) : map (pprintTerm 5) ts
    CPSProj _ idx size t ->
        let proj = parens $ int idx <> text "/" <> int size in
        pprintTerm (prec _t) t <> text "." <> proj 
    CPSApp _ t1 t2 -> 
        let d1 = pprintTerm (prec _t) t1
            d2 = pprintTerm (prec _t+1) t2 in 
        d1 <+> d2
    CPSLam x t -> 
        text "fun" <+> (parens $ pprintSym $ x) <+> text "->"  $+$
        indent (pprintTerm 0 t)
    CPSIf b t1 t2 -> 
        text "if" <+> pprintTerm 0 b <+> text "then" $+$ 
        indent (pprintTerm 0 t1) $+$
        text "else" $+$
        indent (pprintTerm 0 t2)
    CPSBranch t1 t2 ->
        pprintTerm (prec _t) t1 <+> 
        text "<>" $$
        pprintTerm (prec _t+1) t2
    CPSAnd t1 t2 ->
        pprintTerm (prec _t) t1 <+>
        text "&&" <+>
        pprintTerm (prec _t+1) t2
    CPSOr t1 t2 ->
        pprintTerm (prec _t) t1 <+>
        text "||" <+>
        pprintTerm (prec _t+1) t2
    CPSNot t1 ->
        text "not" <+> pprintTerm (prec _t+1) t1
    CPSFail -> text "fail"
    CPSOmega -> text "omega"

