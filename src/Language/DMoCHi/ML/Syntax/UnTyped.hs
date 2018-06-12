{-# LANGUAGE GADTs, TypeFamilies, LambdaCase #-}
module Language.DMoCHi.ML.Syntax.UnTyped( Exp(..), Id, AnnotVar(..), AType(..)
                                        , Type(..), TypeScheme(..), SynName, annot, annotVar, toTypeScheme
                                        , SynonymDef(..), Program(..), unusedVar, matchTypeScheme, matchType
                                        , arity
                                        , mkLiteral, mkVar, mkUnary, mkBinary
                                        , mkPair, mkLambda, mkApp, mkLet, mkLetRec
                                        , mkAssume, mkIf, mkMark
                                        , mkBranch,  mkFail, mkOmega, mkRand
                                        , module Language.DMoCHi.ML.Syntax.Base ) where
import Language.DMoCHi.ML.Syntax.Base
import Language.DMoCHi.Common.Id
import Text.PrettyPrint.HughesPJClass
import Control.Monad
import qualified Data.Set as S
import qualified Data.Map as M

data Exp where
    Exp :: (WellFormed l Exp arg, Supported l (Labels Exp)) => !(SLabel l) -> arg -> Maybe Type -> Exp

type Var = AnnotVar String (Maybe Type)

type instance Ident Exp  = Var
type instance Labels Exp = AllLabels
type instance BinOps Exp = AllBinOps
type instance UniOps Exp = AllUniOps

type SynName = String

data Program = Program { functions :: [(Var,TypeScheme,Exp)] 
                       , synonyms :: [SynonymDef]
                       , specs     :: [(String, AType)]
                       , mainTerm  :: Exp }

data SynonymDef = SynonymDef { synName :: SynName
                             , typVars :: [String]
                             , synDef :: Type }

data AType = ABase String Type [Exp] | AFun AType AType


data Type = TInt | TBool | TPair Type Type | TUnit
          | TFun [Type] Type | TSyn [Type] SynName
          | TVar String
          deriving(Eq,Ord,Show)
data TypeScheme = 
    TypeScheme { typeArgs :: [String] 
               , typeBody :: Type }
               deriving(Eq,Show)

toTypeScheme :: Type -> TypeScheme
toTypeScheme ty = TypeScheme fvs ty
    where
    fvs = S.toList $ go S.empty ty
    go acc TInt = acc
    go acc TBool = acc
    go acc TUnit = acc
    go acc (TPair ty1 ty2) = go (go acc ty1) ty2
    go acc (TFun tys ty) = foldl go (go acc ty) tys
    go acc (TSyn tys _) = foldl go acc tys
    go acc (TVar x) = S.insert x acc

-- matchType:
--  input: ty1 ty2 (probably ty1 :> ty2)
--  output: rho s.t. subst rho ty1 == ty2 if exists
matchType :: Type -> Type -> Maybe (M.Map String Type)
matchType = go M.empty
    where
    go !acc TInt TInt = pure acc
    go !acc TBool TBool = pure acc
    go !acc TUnit TUnit = pure acc
    go !acc (TPair ty1 ty2) (TPair ty3 ty4) = do
        acc' <- go acc ty1 ty3
        go acc' ty2 ty4
    go !acc (TFun [] ty1) (TFun [] ty2) = go acc ty1 ty2
    go !acc (TFun [] ty1) ty2 = go acc ty1 ty2
    go !acc ty1 (TFun [] ty2) = go acc ty1 ty2
    go !acc (TFun (ty1:tys1) ty2) (TFun (ty3:tys3) ty4) = do
        acc' <- go acc ty1 ty3
        go acc' (TFun tys1 ty2) (TFun tys3 ty4)
    go !acc (TSyn tys1 _) (TSyn tys2 _) = 
        if length tys1 /= length tys2
        then Nothing
        else foldM (\acc (ty1, ty2) -> go acc ty1 ty2) acc (zip tys1 tys2)
    go !acc (TVar x) ty2 = case M.lookup x acc of
        Just ty1 | ty1 == ty2 -> pure acc
        Nothing -> pure $ M.insert x ty2 acc
        _ -> Nothing
    go _ TInt _ = Nothing
    go _ TBool _ = Nothing
    go _ TUnit _ = Nothing
    go _ (TPair _ _) _ = Nothing
    go _ (TFun _ _) _ = Nothing
    go _ (TSyn _ _) _ = Nothing

matchTypeScheme :: TypeScheme -> TypeScheme -> Maybe [String]
matchTypeScheme (TypeScheme fvs1 ty1) (TypeScheme _ ty2) = doit
    where
    doit = do
        acc <- go M.empty ty1 ty2
        pure $ map (acc M.!) fvs1
    go !acc TInt TInt = pure acc
    go !acc TBool TBool = pure acc
    go !acc TUnit TUnit = pure acc
    go !acc (TPair ty1 ty2) (TPair ty3 ty4) = do
        acc' <- go acc ty1 ty3
        go acc' ty2 ty4
    go !acc (TFun [] ty1) (TFun [] ty2) = go acc ty1 ty2
    go !acc (TFun [] ty1) ty2 = go acc ty1 ty2
    go !acc ty1 (TFun [] ty2) = go acc ty1 ty2
    go !acc (TFun (ty1:tys1) ty2) (TFun (ty3:tys3) ty4) = do
        acc' <- go acc ty1 ty3
        go acc' (TFun tys1 ty2) (TFun tys3 ty4)
    go !acc (TSyn tys1 _) (TSyn tys2 _) = 
        if length tys1 /= length tys2
        then Nothing
        else foldM (\acc (ty1, ty2) -> go acc ty1 ty2) acc (zip tys1 tys2)
    go !acc (TVar x) (TVar y) = case M.lookup x acc of
        Just z | y == z -> pure acc
        Nothing -> pure $ M.insert x y acc
        _ -> Nothing
    go _ TInt _ = Nothing
    go _ TBool _ = Nothing
    go _ TUnit _ = Nothing
    go _ (TPair _ _) _ = Nothing
    go _ (TFun _ _) _ = Nothing
    go _ (TSyn _ _) _ = Nothing
    go _ (TVar _) _ = Nothing


{-
instance HasUniqueKey Exp where
    getUniqueKey (Exp _ _ key) = key
    -}

arity :: Exp -> Int
arity (Exp SLambda (xs, _) _) = length xs
arity _ = 0

annot :: Exp -> Type -> Exp
annot (Exp l arg _) ty = Exp l arg (Just ty)

annotVar :: Var -> Type -> Var
annotVar (V x _) ty = V x (Just ty)

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

mkMark :: Var -> Exp -> Exp
mkMark x e = Exp SMark (x, e) Nothing

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

instance Pretty AType where
  pPrintPrec plevel prec = \case
    ABase x ty [] -> maybeParens (prec >= 1) $ text x <> text ":" <> pPrint ty
    ABase x ty preds -> maybeParens (prec >= 1) $
      text x <> text ":" <> pPrint ty <> brackets dpreds
      where dpreds = hsep $ punctuate semi $ map (pPrintPrec plevel 0) preds
    AFun ty1 ty2 -> maybeParens (prec >= 1) $
      pPrintPrec plevel 1 ty1 <+> text "->" <+> pPrintPrec plevel 0 ty2


instance Pretty TypeScheme where
    pPrintPrec plevel prec (TypeScheme [] ty) = pPrintPrec plevel prec ty
    pPrintPrec plevel prec (TypeScheme xs ty) = 
        maybeParens (prec >= 1) $ 
            text "forall" <+> hsep (map (text.('\'':)) xs) <> text 
                      "." <+> pPrintPrec plevel 0 ty

instance Show a => Pretty (AnnotVar a (Maybe Type)) where
    pPrintPrec _ _ (V x Nothing) = text (show x)
    pPrintPrec plevel _ (V x (Just ty)) = 
        parens $ text (show x) <+> text ":" <+> pPrintPrec plevel 0 ty

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
instance Show Exp where
  show = render . pPrint
instance Show Program where
  show = render . pPrint

instance Show AType where
  show = render. pPrint

instance Pretty Program where
    pPrintPrec plevel _ (Program fs syns specs t) =
        text "(* functions *)" $+$ 
        vcat (map (\(f,ty,e) -> 
            text "let" <+> text (varName f) <+> colon <+> pPrintPrec plevel 0 ty <+> equals $+$
            nest 4 (pPrintPrec plevel 0 e <> text ";;")) fs) $+$
        text "(*{SPEC}" $+$
        vcat (map (\(x, ty) ->
          text "valcegar" <+> text x <+> text ":" <+> pPrint ty) specs) $+$
        text "{SPEC}*)" $+$
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
