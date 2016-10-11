module Language.DMoCHi.ML.PrettyPrint.PNormal(pprintE
                           ,pprintT
                           ,pprintV
                           ,pprintA
                           ,pprintF
                           ,pprintProgram
                           ,printProgram) where
import Text.PrettyPrint
import Language.DMoCHi.ML.Syntax.PNormal

pprintApp :: Id -> [Value] -> Doc
pprintApp f [] = text (name f) <+> parens empty
pprintApp f vs = text (name f) <+> hsep (map (pprintV 9) vs)

pprintE :: Exp -> Doc
pprintE (Value v) = pprintV 0 v
pprintE (Let _ x' lv e) = 
    let x = name x' in
    case lv of
        LValue v  -> 
            text "let" <+> text x <+> colon <+> pprintT 0 (getType v) 
                       <+> equals 
                       <+> pprintA 0 v <+> text "in" $+$ 
            pprintE e
        LApp ty i f vs ->
            text "let" <+> text x <+> colon <+> pprintT 0 ty
                       <+> equals <+> text ("(*" ++ show i ++ "*)") <+>
                pprintApp f vs <+> text "in" $+$
            pprintE e
        LExp i ev ->
            text "let" <+> text x <+> colon <+> pprintT 0 (getType ev) 
                       <+> text ("(*" ++ show i ++ "*)") <+> equals $+$
            nest 4 (pprintE ev) <+> text "in" $+$
            pprintE e
        LRand -> 
            text "let" <+> text x <+> colon <+> pprintT 0 TInt
                       <+> equals <+> text "*" <+> text "in" $+$
            pprintE e
pprintE (Assume _ v e) = 
    text "assume" <+> pprintA 0 v <> semi $+$
    pprintE e
pprintE (Fail _) = text "Fail"
pprintE (Branch _ i e1 e2) =
    parens (pprintE e1) $+$ text "<>" <+> text ("(*" ++ show i ++ "*)") $+$ parens (pprintE e2)
-- pprintE (Fun fdef) = pprintF fdef

pprintF :: FunDef -> Doc
pprintF (FunDef i xs e) = 
    text "fun" <+> text ("(*" ++ show i ++ "*)") <+> hsep (map (text.name) xs) <+> text "->" $+$ 
    nest 4 (pprintE e)

pprintV :: Int -> Value -> Doc
pprintV assoc (Atomic v) = pprintA assoc v
pprintV _ (Pair v1 v2) = parens (pprintV 0 v1 <+> comma <+> pprintV 0 v2)
pprintV assoc (Fun fdef) | assoc > 0 = parens $ pprintF fdef
                         | otherwise = pprintF fdef


pprintA :: Int -> AValue -> Doc
pprintA _ (Var x) = text (name x)
pprintA _ (CInt x) = integer x
pprintA _ (CBool b) = text $ if b then "true" else "false" 
-- pprintA _ (Pair v1 v2) = parens (pprintA 0 v1 <+> comma <+> pprintA 0 v2)
pprintA assoc (Op op) | assoc <= assoc' =  op' 
                      | otherwise = parens op' where
    assoc' = priority op
    f = pprintA assoc'
    g = pprintA (assoc'+1)
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
    

        

pprintProgram :: Program -> Doc
pprintProgram (Program fs t) =
    text "(* functions *)" $+$ 
    (vcat $ map (\(f,fdef) -> 
        text "let" <+> text (name f) <+> equals $+$
        nest 4 (pprintF fdef <> text ";;")) fs) $+$ 
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
