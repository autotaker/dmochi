module Boolean.PrettyPrint.HORS(pprintTerm,pprintRule,pprintHORS,printHORS,SyntaxParam(..)) where

import Text.PrettyPrint
import Boolean.HORS

data SyntaxParam = Horsat | Preface | HorsatZDD

pprintTerm :: Int -> ATerm -> Doc
pprintTerm _ (Var s) = text s
pprintTerm p (t1 :@ t2) = 
    let d = pprintTerm 0 t1 <+> pprintTerm 1 t2 in
    if p == 0 then d else parens d

pprintRule :: Rule -> Doc
pprintRule (f,xs,t) = text f <+> hsep (map text xs) <+> text "->" <+> pprintTerm 0 t <+> text "."

printAutomaton :: SyntaxParam -> Automaton -> Doc
printAutomaton Horsat = printHorsat
printAutomaton Preface = printPreface
printAutomaton HorsatZDD = printHorsatZDD

printTTA :: [(Terminal,Int)] -> [AState] -> TTARule -> Doc
printTTA ts qs tta =
    text "%BEGINA" $+$
    vcat (do
        (t,_) <- ts
        q <- qs
        case tta q t of
            Just cl -> return $ pprintTrans q t (hsep (map text cl))
            Nothing -> []) $+$
    text "%ENDA"

reduce :: a -> (a -> a -> a) -> [a] -> a
reduce a _ [] = a
reduce _ op l = foldl1 op l

printHorsat, printPreface, printHorsatZDD :: Automaton -> Doc
printHorsat (Automaton ts qs trs) = case trs of
        Left tta -> printTTA ts qs tta
        Right ata ->
            text "%BEGINR" $+$
            vcat (map (\(t,r) -> text t <+> text "->" <+> int r <> text ".") ts) $+$
            text "%ENDR" $+$
            text "%BEGINATA" $+$
            vcat (do
                (t,_) <- ts
                q <- qs
                let build = reduce (text "false") (\a b -> a <+> text "\\/" <+> b) . map build1
                    build1 = reduce (text "true") (\a b -> a <+> text "/\\" <+> b) . map build2 
                    build2 (i,qi) = parens (int i <> comma <+> text qi)
                return $ pprintTrans q t (build (ata q t))) $+$ 
            text "%ENDATA"

printPreface (Automaton ts qs trs) = case trs of
    Left tta -> printTTA ts qs tta
    Right ata ->
        text "%BEGINA" $+$
        vcat (do
            (t,_) <- ts
            q <- qs
            cl <- ata q t
            let d = hsep (map (\(i,qi) -> parens (int i <> comma <+> text qi)) cl)
            return $ pprintTrans q t d)
            $+$ 
        text "%ENDA"
                    
printHorsatZDD = undefined


pprintTrans :: AState -> Terminal -> Doc -> Doc
pprintTrans q a d =
    text q <+> text a <+> text "->" <+> d <> text "." --hsep (map text qs) <> text "."

pprintHORS :: SyntaxParam -> HORS -> Doc
pprintHORS param hors = 
    text "%BEGING" $+$
    vcat (map pprintRule $ rules hors) $+$
    text "%ENDG" $+$
    printAutomaton param (automaton hors)

printHORS :: SyntaxParam -> HORS -> IO ()
printHORS param = putStrLn . render . pprintHORS param


