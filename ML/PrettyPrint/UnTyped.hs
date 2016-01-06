module ML.PrettyPrint.UnTyped(pprintE
                             ,pprintV
                             ,pprintP
                             ,pprintProgram
                             ,printProgram) where
import Text.PrettyPrint
import ML.Syntax.UnTyped

pprintE :: Exp -> Doc
pprintE (Value v) = pprintV 0 v
pprintE (Let x lv e) = 
    case lv of
        LValue v  -> 
            text "let" <+> text x <+> equals <+> pprintV 0 v <+> text "in" $+$ 
            pprintE e
        LApp f vs ->
            text "let" <+> text x <+> equals <+> 
                text f <+> hsep (map (pprintV 9) vs) <+> text "in" $+$
            pprintE e
        LExp ptyp ev ->
            text "let" <+> text x <+> colon <+> pprintP 0 ptyp <+> equals $+$
            nest 4 (pprintE ev) <+> text "in" $+$
            pprintE e
        LRand ->
            text "let" <+> text x <+> equals <+> text "*" <+> text "in" $+$ 
            pprintE e

pprintE (Assume v e) = 
    text "assume" <+> pprintV 0 v <> semi $+$
    pprintE e
pprintE (Lambda x e) =
    text "fun" <+> text x <+> text "->" $+$ 
    nest 4 (pprintE e)
pprintE (Fail) = text "Fail"
pprintE (Branch e1 e2) =
    parens (pprintE e1) $+$ text "<>" $+$ parens (pprintE e2)

pprintV :: Int -> Value -> Doc
pprintV _ (Var x) = text x
pprintV _ (CInt x) = integer x
pprintV _ (CBool b) = text $ if b then "true" else "false" 
pprintV _ (Pair v1 v2) = parens (pprintV 0 v1 <+> comma <+> pprintV 0 v2)
pprintV assoc (Op op) | assoc <= assoc' =  op' 
                      | otherwise = parens op' where
    assoc' = priority op
    f = pprintV assoc'
    g = pprintV (assoc'+1)
    op' = case op of
        OpAdd v1 v2 -> f v1 <+> text "+" <+> g v2
        OpSub v1 v2 -> f v1 <+> text "-" <+> g v2
        OpNeg v1 -> text "-" <> f v1
        OpFst v1 -> f v1 <> text ".fst"
        OpSnd v1 -> f v1 <> text ".snd"
        OpEq v1 v2 -> g v1 <+> text "=" <+> g v2 
        OpLt v1 v2 -> g v1 <+> text "<" <+> g v2
        OpGt v1 v2 -> g v1 <+> text ">" <+> g v2
        OpLte v1 v2 -> g v1 <+> text "<=" <+> g v2
        OpGte v1 v2 -> g v1 <+> text ">=" <+> g v2
        OpAnd v1 v2 -> f v1 <+> text "&&" <+> g v2
        OpOr  v1 v2 -> f v1 <+> text "||" <+> g v2
        OpNot v1    -> text "not" <+> (g v1)
    

pprintPSub :: String -> [Predicate] -> Doc
pprintPSub tname ps = 
    let f (x,v) = text x <> text "." <> pprintV 0 v in
    text tname <> (brackets $ hsep $ punctuate semi $ map f ps)
        
pprintP :: Int -> PType -> Doc
pprintP _ (PInt ps) = pprintPSub "int" ps
pprintP _ (PBool ps) = pprintPSub "bool" ps
pprintP assoc (PPair ty_f (x,ty_s)) = 
    let df = pprintP 1 ty_f in
    let ds = pprintP 1 ty_s in
    let d = text x <+> colon <+> df <+> text "*" <+> ds in
    if assoc == 0 then d else parens d

pprintP assoc (PFun p (x,f)) = 
    let dp = pprintP 1 p in
    let df = pprintP 0 f in
    let d = text x <+> colon <+> dp <+> text "->" <+> df in
    if assoc == 0 then d else parens d

pprintProgram :: Program -> Doc
pprintProgram (Program fs t) =
    let d = vcat $ map (\(f,ty,e) -> 
            text "let" <+> text f <+> colon <+> pprintP 0 ty <+> equals $+$
            nest 4 (pprintE e <> text ";;")) fs in
    text "(* functions *)" $+$ 
    d $+$ 
    text "(*main*)" $+$
    pprintE t

printProgram :: Program -> IO ()
printProgram = putStrLn . render . pprintProgram

priority :: Op -> Int
priority (OpAdd _ _) = 6
priority (OpSub _ _) = 6
priority (OpNeg _)   = 8
priority (OpEq _ _)  = 4
priority (OpLt _ _)  = 4
priority (OpGt _ _)  = 4
priority (OpLte _ _) = 4
priority (OpGte _ _) = 4
priority (OpAnd _ _) = 3
priority (OpOr _ _)  = 2
priority (OpNot _)   = 8
priority (OpFst _)   = 9
priority (OpSnd _)   = 9
