module ML.PrettyPrint.Typed(pprintE
                           ,pprintT
                           ,pprintV
                           ,pprintP
                           ,pprintProgram
                           ,printProgram) where
import Text.PrettyPrint
import ML.Syntax.Typed

pprintE :: Exp -> Doc
pprintE (Value v) = pprintV 0 v
pprintE (Let _ x' lv e) = 
    let x = name x' in
    case lv of
        LValue v  -> 
            text "let" <+> text x <+> colon <+> pprintT 0 (getType v) 
                       <+> equals 
                       <+> pprintV 0 v <+> text "in" $+$ 
            pprintE e
        LApp ty i f v ->
            text "let" <+> text x <+> colon <+> pprintT 0 ty
                       <+> equals <+> text ("(*" ++ show i ++ "*)") <+>
                text (name f) <+> hsep (map (pprintV 9) [v]) <+> text "in" $+$
            pprintE e
        LExp ptyp ev ->
            text "let" <+> text x <+> colon <+> pprintP 0 ptyp <+> equals $+$
            nest 4 (pprintE ev) <+> text "in" $+$
            pprintE e
pprintE (Assume _ v e) = 
    text "assume" <+> pprintV 0 v <> semi $+$
    pprintE e
pprintE (Lambda _ i x e) =
    text "fun" <+> text ("(*" ++ show i ++ "*)") <+> text (name x) <+> text "->" $+$ 
    nest 4 (pprintE e)
pprintE (Fail _) = text "Fail"
pprintE (Branch _ i e1 e2) =
    parens (pprintE e1) $+$ text "<>" <+> text ("(*" ++ show i ++ "*)") $+$ parens (pprintE e2)

pprintV :: Int -> Value -> Doc
pprintV _ (Var x) = text (name x)
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
        OpEq v1 v2 -> g v1 <+> text "=" <+> g v2 
        OpLt v1 v2 -> g v1 <+> text "<" <+> g v2
        OpLte v1 v2 -> g v1 <+> text "<=" <+> g v2
        OpAnd v1 v2 -> f v1 <+> text "&&" <+> g v2
        OpOr  v1 v2 -> f v1 <+> text "||" <+> g v2
        OpNot v1    -> text "not" <+> (g v1)
        OpFst _ v1 -> f v1 <> text ".fst"
        OpSnd _ v1 -> f v1 <> text ".snd"
    

pprintPSub :: String -> [Predicate] -> Doc
pprintPSub tname ps = 
    let f (x,v) = text (name x) <> text "." <> pprintV 0 v in
    text tname <> (brackets $ hsep $ punctuate semi $ map f ps)
        
pprintP :: Int -> PType -> Doc
pprintP _ (PInt ps) = pprintPSub "int" ps
pprintP _ (PBool ps) = pprintPSub "bool" ps
pprintP assoc (PPair _ p (x,f)) = 
    let dp = pprintP 1 p in
    let df = pprintP 1 f in
    let d = text (name x) <+> colon <+> dp <+> text "*" <+> df in
    if assoc == 0 then d else parens d
pprintP assoc (PFun _ p (x,f)) = 
    let dp = pprintP 1 p in
    let df = pprintP 0 f in
    let d = text (name x) <+> colon <+> dp <+> text "->" <+> df in
    if assoc == 0 then d else parens d

pprintProgram :: Program -> Doc
pprintProgram (Program fs t) =
    let d = vcat $ map (\(f,ty,e) -> 
            text "let" <+> text (name f) <+> colon <+> pprintP 0 ty <+> equals $+$
            nest 4 (pprintE e <> text ";;")) fs in
    text "(* functions *)" $+$ 
    d $+$ 
    text "(* main *)" $+$
    pprintE t

printProgram :: Program -> IO ()
printProgram = putStrLn . render . pprintProgram

priority :: Op -> Int
priority (OpAdd _ _) = 6
priority (OpSub _ _) = 6
priority (OpEq _ _)  = 4
priority (OpLt _ _)  = 4
priority (OpLte _ _) = 4
priority (OpAnd _ _) = 3
priority (OpOr _ _)  = 2
priority (OpNot _)   = 8
priority (OpFst _ _)   = 9
priority (OpSnd _ _)   = 9
