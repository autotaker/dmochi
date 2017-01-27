{-# LANGUAGE GADTs, AllowAmbiguousTypes, TypeFamilies, LambdaCase #-}
module Language.DMoCHi.ML.Syntax.UnTyped( Exp(..), Id, Lit(..)
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
    Exp :: WellFormed l op1 op2 Exp arg => SLabel l -> arg -> UniqueKey -> Exp

type instance Ident Exp = Id
type instance Literal Exp = Lit

data Lit = CInt Integer | CBool Bool

type Id = String
type SynName = String

data Program = Program { functions :: [(Id,Type,Exp)] 
                       , synonyms :: [SynonymDef]
                       , typeAnn :: [(UniqueKey, Type)]
                       , mainTerm  :: Exp }

data SynonymDef = SynonymDef { synName :: SynName
                             , typVars :: [Id]
                             , synDef :: Type }

data Type = TInt | TBool | TPair Type Type 
          | TFun [Type] Type | TSyn [Type] SynName
          | TVar Id
          deriving(Eq,Show)

getKey :: Exp -> UniqueKey
getKey (Exp _ _ key) = key

{-# INLINE mkLiteral #-}
mkLiteral :: MonadId m => Lit -> m Exp
mkLiteral lit = Exp SLiteral lit <$> freshKey

{-# INLINE mkVar #-}
mkVar :: MonadId m => Id -> m Exp
mkVar lit = Exp SVar lit <$> freshKey

{-# INLINE mkUnary #-}
mkUnary :: MonadId m => SUniOp op -> Exp -> m Exp
mkUnary op e = Exp SUnary (op,e) <$> freshKey
{-# INLINE mkUnary' #-}
mkUnary' :: MonadId m => SUniOp op -> m (Exp -> Exp)
mkUnary' op = do
    key <- freshKey
    return (\e -> Exp SUnary (op,e) key)

{-# INLINE mkBinary #-}
mkBinary :: MonadId m => SBinOp op -> Exp -> Exp -> m Exp
mkBinary op e1 e2 = Exp SBinary (op,e1,e2) <$> freshKey

{-# INLINE mkBinary' #-}
mkBinary' :: MonadId m => SBinOp op -> m (Exp -> Exp -> Exp)
mkBinary' op = do
    key <- freshKey
    return (\e1 e2 -> Exp SBinary (op,e1,e2) key)

{-# INLINE mkPair #-}
mkPair :: MonadId m => Exp -> Exp -> m Exp
mkPair e1 e2 = Exp SPair (e1,e2) <$> freshKey

{-# INLINE mkLambda #-}
mkLambda :: MonadId m => [Id] -> Exp -> m Exp
mkLambda xs e = Exp SLambda (xs, e) <$> freshKey

{-# INLINE mkApp #-}
mkApp :: MonadId m => Id -> [Exp] -> m Exp
mkApp f es = Exp SApp (f, es) <$> freshKey

{-# INLINE mkLet #-}
mkLet :: MonadId m => Id -> Exp -> Exp -> m Exp
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
mkRand = Exp SFail () <$> freshKey

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
    pPrintPrec plevel = go False
        where
        go rightCont prec (Exp l arg key) = if plevel == prettyNormal then doc else comment key <+> doc
            where
            doc = case (l, arg) of
                (SLiteral, lit) -> case lit of
                    CInt i | i < 0     -> maybeParens (prec >= 9) (integer i)
                           | otherwise -> integer i
                    CBool True -> text "true"
                    CBool False -> text "false"
                (SVar, x) -> text x
                (SUnary, (op, e)) -> maybeParens (prec > prec') d
                    where
                    (prec',opName, prefix) = unaryPrec op
                    d = case prefix of
                        True -> (text opName <+> go rightCont prec' e)
                        False -> (go True prec' e <> text opName )
                (SBinary, (op, e1, e2)) -> maybeParens (prec > prec') d
                    where
                    (prec',opName, assoc) = binaryPrec op
                    f r e = go r prec' e
                    g r e = go r (prec'+1) e
                    d = case assoc of
                        AssocLeft  -> f True e1 <+> text opName <+> g rightCont e2
                        AssocRight -> g True e1 <+> text opName <+> f rightCont e2
                        AssocNone  -> g True e1 <+> text opName <+> g rightCont e2
                (SPair, (e1, e2)) -> parens $ go False 0 e1 <+> comma <+> go False 0 e2
                (SLambda, (xs, e)) -> maybeParens (prec > 8.5 || rightCont) $
                    text "fun" <+> hsep (map text xs) <+> text "->" $+$
                    nest 4 (go True 0 e)
                (SApp, (f, [])) -> maybeParens (prec > 8) $ text f <+> text "()"
                (SApp, (f, es)) -> maybeParens (prec > 8) $ text f <+> hsep (map (go True 9) es)
                (SLet, (x, e1, e2)) -> maybeParens (prec > 8.5 || rightCont) $ 
                    text "let" <+> text x <+> text "=" <+> go False 0 e1 <+> text "in" $+$
                    go False 0 e2
                (SAssume, (cond, e)) -> maybeParens rightCont $
                    text "assume" <+> go False 9 cond <> semi $+$
                    go False 0 e
                (SIf, (cond, e1, e2)) -> maybeParens rightCont $
                    text "if" <+> go False 0 cond $+$
                    nest 2 (text "then" <+> go False 0 e1) $+$
                    nest 2 (text "else" <+> go False 0 e2)
                (SBranch, (e1, e2)) -> maybeParens (prec > 0) $
                    go True 0 e1 <+> text "<>" <+> go False 1 e2
                (SFail, _) -> text "Fail"
                (SOmega, _) -> text "Omega"
                (SRand, _) -> text "*"

comment :: Pretty a => a -> Doc
comment a = text "(*" <+> pPrint a <+> text "*)"

unaryPrec :: SUniOp op -> (Rational, String, Bool)
unaryPrec SNeg = (8, "-", True)
unaryPrec SNot = (8, "not", True)
unaryPrec SFst = (9, ".fst", False)
unaryPrec SSnd = (9, ".snd", False)

binaryPrec :: SBinOp op -> (Rational, String, Assoc)
binaryPrec SAdd = (6, "+", AssocLeft)
binaryPrec SSub = (6, "-", AssocLeft)
binaryPrec SEq   = (4, "=", AssocNone)
binaryPrec SLt   = (4, "<", AssocNone)
binaryPrec SLte  = (4, "<=", AssocNone)
binaryPrec SGt   = (4, ">", AssocNone)
binaryPrec SGte  = (4, ">", AssocNone)
binaryPrec SAnd  = (3, "&&", AssocNone)
binaryPrec SOr   = (2, "||", AssocNone)

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


