{-# LANGUAGE GADTs, TypeFamilies, LambdaCase #-}
module Language.DMoCHi.ML.Syntax.UnTyped( Exp(..), Id
                                        , Type(..), SynName 
                                        , SynonymDef(..), Program(..)
                                        , getKey
                                        , mkLiteral, mkVar, mkUnary, mkBinary
                                        , mkUnary', mkBinary'
                                        , mkPair, mkLambda, mkApp, mkLet, mkAssume, mkIf
                                        , mkBranch, mkBranch', mkFail, mkOmega, mkRand
                                        , module Language.DMoCHi.ML.Syntax.Base ) where
import Language.DMoCHi.ML.Syntax.Base
import Language.DMoCHi.Common.Id
import Text.PrettyPrint.HughesPJClass

data Exp where
    Exp :: (WellFormed l Exp arg, Supported l (Labels Exp)) => SLabel l -> arg -> UniqueKey -> Exp

type instance Ident Exp = String
type instance Labels Exp = AllLabels
type instance BinOps Exp = AllBinOps
type instance UniOps Exp = AllUniOps


type SynName = String

data Program = Program { functions :: [(String,Type,Exp)] 
                       , synonyms :: [SynonymDef]
                       , typeAnn :: [(UniqueKey, Type)]
                       , mainTerm  :: Exp }

data SynonymDef = SynonymDef { synName :: SynName
                             , typVars :: [String]
                             , synDef :: Type }

data Type = TInt | TBool | TPair Type Type 
          | TFun [Type] Type | TSyn [Type] SynName
          | TVar String
          deriving(Eq,Show)

getKey :: Exp -> UniqueKey
getKey (Exp _ _ key) = key

{-# INLINE mkLiteral #-}
mkLiteral :: MonadId m => Lit -> m Exp
mkLiteral lit = Exp SLiteral lit <$> freshKey

{-# INLINE mkVar #-}
mkVar :: MonadId m => String -> m Exp
mkVar lit = Exp SVar lit <$> freshKey

{-# INLINE mkUnary #-}
mkUnary :: (MonadId m, Supported op (UniOps Exp)) => SUniOp op -> Exp -> m Exp
mkUnary op e = Exp SUnary (UniArg op e) <$> freshKey
{-# INLINE mkUnary' #-}
mkUnary' :: (MonadId m, Supported op (UniOps Exp)) => SUniOp op -> m (Exp -> Exp)
mkUnary' op = do
    key <- freshKey
    return (\e -> Exp SUnary (UniArg op e) key)

{-# INLINE mkBinary #-}
mkBinary :: (MonadId m,Supported op (BinOps Exp)) => SBinOp op -> Exp -> Exp -> m Exp
mkBinary op e1 e2 = Exp SBinary (BinArg op e1 e2) <$> freshKey

{-# INLINE mkBinary' #-}
mkBinary' :: (MonadId m, Supported op (BinOps Exp)) => SBinOp op -> m (Exp -> Exp -> Exp)
mkBinary' op = do
    key <- freshKey
    return (\e1 e2 -> Exp SBinary (BinArg op e1 e2) key)

{-# INLINE mkPair #-}
mkPair :: MonadId m => Exp -> Exp -> m Exp
mkPair e1 e2 = Exp SPair (e1,e2) <$> freshKey

{-# INLINE mkLambda #-}
mkLambda :: MonadId m => [String] -> Exp -> m Exp
mkLambda xs e = Exp SLambda (xs, e) <$> freshKey

{-# INLINE mkApp #-}
mkApp :: MonadId m => String -> [Exp] -> m Exp
mkApp f es = Exp SApp (f, es) <$> freshKey

{-# INLINE mkLet #-}
mkLet :: MonadId m => String -> Exp -> Exp -> m Exp
mkLet x e1 e2 = Exp SLet (x, e1, e2) <$> freshKey

{-# INLINE mkAssume #-}
mkAssume :: MonadId m => Exp -> Exp -> m Exp
mkAssume cond e = Exp SAssume (cond, e) <$> freshKey

{-# INLINE mkIf #-}
mkIf :: MonadId m => Exp -> Exp -> Exp -> m Exp
mkIf e1 e2 e3 = Exp SIf (e1,e2,e3) <$> freshKey

{-# INLINE mkBranch #-}
mkBranch :: MonadId m => Exp -> Exp -> m Exp
mkBranch e1 e2 = Exp SBranch (e1, e2) <$> freshKey
{-# INLINE mkBranch' #-}
mkBranch' :: MonadId m => m (Exp -> Exp -> Exp)
mkBranch' = do
    key <- freshKey
    return (\e1 e2 -> Exp SBranch (e1,e2) key)

{-# INLINE mkFail #-} 
{-# INLINE mkOmega #-}
{-# INLINE mkRand #-}
mkFail, mkOmega, mkRand :: MonadId m => m Exp
mkFail  = Exp SFail () <$> freshKey
mkOmega = Exp SOmega () <$> freshKey
mkRand = Exp SRand () <$> freshKey

instance Pretty Type where
    pPrintPrec plevel prec = \case
        TInt -> text "int"
        TBool -> text "bool"
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


instance Pretty Exp where
    pPrintPrec plevel prec (Exp l arg key) = 
        if plevel == prettyNormal then doc else comment key <+> doc
            where
            pp :: WellFormedPrinter Exp
            pp = WellFormedPrinter {
                   pPrintExp = pPrintPrec,
                   pPrintIdent = \_ _ -> text
                 }
            doc = genericPPrint pp plevel prec l arg


instance Pretty Program where
    pPrintPrec plevel _ (Program fs syns annot t) = 
        text "(* functions *)" $+$ 
        vcat (map (\(f,ty,e) -> 
            text "let" <+> text f <+> colon <+> pPrintPrec plevel 0 ty <+> equals $+$
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
        (if plevel == prettyNormal
         then empty
         else text "(* annotations *)" $+$
              vcat (map (\(key, ty) -> pPrint key <+> colon <+> pPrintPrec plevel 0 ty) annot)) $+$
        text "(*main*)" $+$
        pPrintPrec plevel 0 t
        


{-
data Exp = Value Value 
         | Let Id LetValue Exp 
         | Assume Value Exp
         | Lambda [Id] Exp
         | Fail
         | Branch Exp Exp deriving(Show)

data Value = Var Id
           | CInt Integer
           | CBool Bool
           | Pair Value Value
           | App Id [Value]
           | Op Op deriving(Show)

data Op = OpAdd Value Value
        | OpSub Value Value
        | OpNeg Value
        | OpEq  Value Value
        | OpLt  Value Value
        | OpGt  Value Value
        | OpLte Value Value
        | OpGte Value Value
        | OpAnd Value Value
        | OpOr  Value Value
        | OpFst Value
        | OpSnd Value
        | OpNot Value deriving(Show)

data LetValue = LValue Value
              | LApp Id [Value]
              | LExp Type Exp
              | LRand
              deriving(Show)
-}


