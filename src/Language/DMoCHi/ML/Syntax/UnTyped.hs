{-# LANGUAGE GADTs, TypeFamilies, LambdaCase #-}
module Language.DMoCHi.ML.Syntax.UnTyped( Exp(..), Id, AnnotVar(..)
                                        , Type(..), SynName 
                                        , SynonymDef(..), Program(..), unusedVar
                                        , mkLiteral, mkVar, mkUnary, mkBinary
                                        , mkPair, mkLambda, mkApp, mkLet, mkLetRec
                                        , mkAssume, mkIf
                                        , mkBranch,  mkFail, mkOmega, mkRand
                                        , module Language.DMoCHi.ML.Syntax.Base ) where
import Language.DMoCHi.ML.Syntax.Base
import Language.DMoCHi.Common.Id
import Text.PrettyPrint.HughesPJClass

data Exp where
    Exp :: (WellFormed l Exp arg, Supported l (Labels Exp)) => !(SLabel l) -> arg -> Maybe Type -> Exp

data AnnotVar a = V { varName :: a 
                  , varType :: Maybe Type }
                  deriving(Eq,Show)
type Var = AnnotVar String

type instance Ident Exp  = Var
type instance Labels Exp = AllLabels
type instance BinOps Exp = AllBinOps
type instance UniOps Exp = AllUniOps

type SynName = String

data Program = Program { functions :: [(Var,Type,Exp)] 
                       , synonyms :: [SynonymDef]
                       , mainTerm  :: Exp }

data SynonymDef = SynonymDef { synName :: SynName
                             , typVars :: [String]
                             , synDef :: Type }

data Type = TInt | TBool | TPair Type Type | TUnit
          | TFun [Type] Type | TSyn [Type] SynName
          | TVar String
          deriving(Eq,Show)

{-
instance HasUniqueKey Exp where
    getUniqueKey (Exp _ _ key) = key
    -}


unusedVar :: Var
unusedVar = V "" Nothing

mkLiteral :: Lit -> Exp
mkLiteral lit = Exp SLiteral lit Nothing

mkVar :: Var -> Exp
mkVar x = Exp SVar x Nothing

mkUnary :: (Supported op (UniOps Exp)) => SUniOp op -> Exp -> Exp
mkUnary op e = Exp SUnary (UniArg op e) Nothing

mkBinary :: (Supported op (BinOps Exp)) => SBinOp op -> Exp -> Exp -> Exp
mkBinary op e1 e2 = Exp SBinary (BinArg op e1 e2) Nothing

mkPair :: Exp -> Exp -> Exp
mkPair e1 e2 = Exp SPair (e1,e2) Nothing

mkLambda :: [Var] -> Exp -> Exp
mkLambda xs e = Exp SLambda (xs, e) Nothing

mkApp :: Exp -> [Exp] -> Exp
mkApp e es = Exp SApp (e, es) Nothing

mkLet :: Var -> Exp -> Exp -> Exp
mkLet x e1 e2 = Exp SLet (x, e1, e2) Nothing

mkLetRec :: [(Var, Exp)] -> Exp -> Exp
mkLetRec xs e = Exp SLetRec (xs, e) Nothing

mkAssume :: Exp -> Exp -> Exp
mkAssume cond e = Exp SAssume (cond, e) Nothing

mkIf :: Exp -> Exp -> Exp -> Exp
mkIf e1 e2 e3 = Exp SIf (e1,e2,e3) Nothing

mkBranch :: Exp -> Exp -> Exp
mkBranch e1 e2 = Exp SBranch (e1, e2) Nothing

mkFail, mkOmega, mkRand :: Exp
mkFail  = Exp SFail () Nothing
mkOmega = Exp SOmega () Nothing
mkRand = Exp SRand () Nothing

instance Pretty Type where
    pPrintPrec plevel prec = \case
        TInt -> text "int"
        TBool -> text "bool"
        TUnit -> text "unit"
        TVar x -> text ('\'':x)
        TPair t1 t2 -> maybeParens (prec >= 1) (d1 <+> text "*" <+> d2)
            where
            d1 = pPrintPrec plevel 1 t1
            d2 = pPrintPrec plevel 1 t2
        TFun ts t -> maybeParens (prec >= 1) (d1 <+> text "->" <+> d2)
            where
            d1 = brackets $ hsep $ punctuate comma (map (pPrintPrec plevel 0) ts)
            d2 = pPrintPrec plevel 0 t
        TSyn [] syn -> text syn
        TSyn tys syn -> darg <+> text syn
            where
            darg = case tys of
                [ty] -> pPrintPrec plevel 1 ty
                _ -> parens $ hsep $ punctuate comma (map (pPrintPrec plevel 0) tys)

instance Pretty a => Pretty (AnnotVar a) where
    pPrintPrec plevel prec (V x Nothing) = pPrintPrec plevel prec x
    pPrintPrec plevel _ (V x (Just ty)) = 
        parens $ pPrintPrec plevel 0 x <+> text ":" <+> pPrintPrec plevel 0 ty

instance Pretty Exp where
    pPrintPrec plevel prec (Exp l arg key) = 
        if plevel == prettyNormal then doc else comment key <+> doc
            where
            pp :: WellFormedPrinter Exp
            pp = WellFormedPrinter {
                   pPrintExp = pPrintPrec,
                   pPrintIdent = pPrintPrec
                 }
            doc = genericPPrint pp plevel prec l arg


instance Pretty Program where
    pPrintPrec plevel _ (Program fs syns t) = 
        text "(* functions *)" $+$ 
        vcat (map (\(f,ty,e) -> 
            text "let" <+> text (varName f) <+> colon <+> pPrintPrec plevel 0 ty <+> equals $+$
            nest 4 (pPrintPrec plevel 0 e <> text ";;")) fs) $+$
        text "(* synonyms *)" $+$
        vcat (map (\syn -> 
            let dargs = case typVars syn of
                    [] -> empty
                    [x] -> text ('\'':x)
                    xs  -> parens $ hsep $ punctuate comma (map (text . ('\'':)) xs)
            in
            text "type" <+> dargs <+> text (synName syn) <+> equals 
                        <+> pPrintPrec plevel 0 (synDef syn) <> text ";;") syns) $+$
                        {-
        (if plevel == prettyNormal
         then empty
         else text "(* annotations *)" $+$
              vcat (map (\(key, ty) -> pPrint key <+> colon <+> pPrintPrec plevel 0 ty) annot)) $+$ -}
        text "(*main*)" $+$
        pPrintPrec plevel 0 t
