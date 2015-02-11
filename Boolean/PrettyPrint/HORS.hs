module Boolean.PrettyPrint.HORS(pprintTerm,pprintRule,pprintHORS,printHORS) where

import Text.PrettyPrint
import Boolean.HORS

pprintTerm :: Int -> ATerm -> Doc
pprintTerm _ (Var s) = text s
pprintTerm p (t1 :@ t2) = 
    let d = pprintTerm 0 t1 <+> pprintTerm 1 t2 in
    if p == 0 then d else parens d

pprintRule :: Rule -> Doc
pprintRule (f,xs,t) = text f <+> hsep (map text xs) <+> text "->" <+> pprintTerm 0 t <+> text "."

pprintT :: (String,[(String,[String])]) -> Doc
pprintT (a,ts) = vcat $ map (\(q,qs) -> 
    text q <+> text a <+> text "->" <+> hsep (map text qs) <> text ".") ts

pprintHORS :: HORS -> Doc
pprintHORS hors = 
    text "%BEGING" $+$
    vcat (map pprintRule $ rules hors) $+$
    text "%ENDG" $+$
    text "%BEGINA" $+$
    vcat (map pprintT $ terminals hors) $+$
    text "%ENDA"

printHORS :: HORS -> IO ()
printHORS = putStrLn . render . pprintHORS


