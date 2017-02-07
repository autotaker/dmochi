{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeFamilies, ConstraintKinds, TypeOperators, PolyKinds, UndecidableInstances, FlexibleContexts #-}
module Language.DMoCHi.ML.Syntax.Base(Label(..), 
                                      BinOp(..),
                                      UniOp(..),
                                      Labels, Ident, Lit(..),
                                      BinOps, UniOps,
                                      AllLabels, AllBinOps, AllUniOps,
                                      WellFormed,
                                      SLabel(..),
                                      SBinOp(..),
                                      SUniOp(..),
                                      UniArg(..),
                                      BinArg(..),
                                      Assoc(..),
                                      Elem, Supported,
                                      unaryPrec,
                                      binaryPrec,
                                      genericPPrint,
                                      WellFormedPrinter(..),
                                      comment,
                                      Impossible(..))
                                       where
import GHC.Exts(Constraint)
import Text.Parsec.Expr(Assoc(..))
import Data.Type.Bool
import Data.Type.Equality
import Text.PrettyPrint.HughesPJClass

data Label = Literal | Var | Binary | Unary | Pair 
           | Lambda | App | Let 
           | Assume | If | Branch 
           | Fail | Omega | Rand

data BinOp = Add | Sub | Eq | Lt | Gt | Lte | Gte | And | Or 
data UniOp = Fst | Snd | Not | Neg

data Lit = CInt Integer | CBool Bool
    deriving(Eq,Ord)

type family Ident e
type family Labels e :: [Label]
type family BinOps e :: [BinOp]
type family UniOps e :: [UniOp]

type family AllBinOps where
    AllBinOps = '[ 'Add, 'Sub, 'Eq, 'Lt, 'Gt, 'Lte, 'Gte, 'And, 'Or ]

type family AllUniOps where
    AllUniOps = '[ 'Fst, 'Snd, 'Not, 'Neg ]

type family AllLabels where
    AllLabels = '[ 'Literal, 'Var, 'Binary, 'Unary, 'Pair,
                   'Lambda, 'App, 'Let, 
                   'Assume, 'If, 'Branch, 'Fail, 'Omega, 'Rand ]

type family Elem (x :: k) (xs :: [k]) where
    Elem x (x1 ': xs) = x == x1 || Elem x xs
    Elem x '[] = 'False

type family Supported (x :: k) (xs :: [k]) where
    Supported x xs = Elem x xs ~ 'True

data BinArg e where
    BinArg :: Elem op (BinOps e) ~ 'True => SBinOp op -> e -> e -> BinArg e
data UniArg e where
    UniArg :: Elem op (UniOps e) ~ 'True => SUniOp op -> e -> UniArg e


instance Eq e => Eq (BinArg e) where
    (==) (BinArg op1 e1 e2) (BinArg op2 e3 e4) = 
        case testEquality op1 op2 of
            Just Refl -> e1 == e3 && e2 == e4
            Nothing -> False

instance Eq e => Eq (UniArg e) where
    (==) (UniArg op1 e1) (UniArg op2 e2) = 
        case testEquality op1 op2 of
            Just Refl -> e1 == e2 
            Nothing -> False

type family WellFormed (l :: Label)  (e :: *)  (arg :: *) :: Constraint where
    WellFormed 'Literal e arg = arg ~ Lit
    WellFormed 'Var     e arg = arg ~ Ident e
    WellFormed 'Unary   e arg = arg ~ UniArg e
    WellFormed 'Binary  e arg = arg ~ BinArg e
    WellFormed 'Pair    e arg = arg ~ (e, e)
    WellFormed 'Lambda  e arg = arg ~ ([Ident e], e)
    WellFormed 'App     e arg = arg ~ (Ident e, [e])
    WellFormed 'Let     e arg = arg ~ (Ident e, e, e)
    WellFormed 'Assume  e arg = arg ~ (e, e)
    WellFormed 'If      e arg = arg ~ (e, e, e)
    WellFormed 'Branch  e arg = arg ~ (e, e)
    WellFormed 'Fail    e arg = arg ~ ()
    WellFormed 'Omega   e arg = arg ~ ()
    WellFormed 'Rand    e arg = arg ~ ()

data SLabel (l :: Label) where
    SLiteral :: SLabel 'Literal
    SVar     :: SLabel 'Var
    SBinary  :: SLabel 'Binary
    SUnary   :: SLabel 'Unary
    SPair    :: SLabel 'Pair
    SLambda  :: SLabel 'Lambda
    SApp     :: SLabel 'App
    SLet     :: SLabel 'Let
    SAssume  :: SLabel 'Assume
    SIf      :: SLabel 'If
    SBranch  :: SLabel 'Branch
    SFail    :: SLabel 'Fail
    SOmega   :: SLabel 'Omega
    SRand    :: SLabel 'Rand

type family EqLabel a b where
    EqLabel 'Literal 'Literal = 'True
    EqLabel 'Var 'Var = 'True
    EqLabel 'Binary 'Binary = 'True
    EqLabel 'Unary 'Unary = 'True
    EqLabel 'Pair 'Pair = 'True
    EqLabel 'Lambda 'Lambda = 'True
    EqLabel 'App 'App = 'True
    EqLabel 'Let 'Let = 'True
    EqLabel 'Assume 'Assume = 'True
    EqLabel 'If 'If = 'True
    EqLabel 'Branch 'Branch = 'True
    EqLabel 'Fail 'Fail = 'True
    EqLabel 'Omega 'Omega = 'True
    EqLabel 'Rand 'Rand = 'True
    EqLabel a b = 'False

data SBinOp (op :: BinOp) where
    SAdd     :: SBinOp 'Add
    SSub     :: SBinOp 'Sub
    SEq      :: SBinOp 'Eq
    SLt      :: SBinOp 'Lt
    SGt      :: SBinOp 'Gt
    SLte     :: SBinOp 'Lte
    SGte     :: SBinOp 'Gte
    SAnd     :: SBinOp 'And
    SOr      :: SBinOp 'Or

type family EqBinOp a b where
    EqBinOp 'Add 'Add = 'True
    EqBinOp 'Sub 'Sub = 'True
    EqBinOp 'Eq  'Eq = 'True
    EqBinOp 'Lt  'Lt = 'True
    EqBinOp 'Gt  'Gt = 'True
    EqBinOp 'Lte 'Lte = 'True
    EqBinOp 'Gte 'Gte = 'True
    EqBinOp 'And 'And = 'True
    EqBinOp 'Or  'Or = 'True
    EqBinOp a b = 'False

instance TestEquality SBinOp where
    testEquality SAdd SAdd = Just Refl
    testEquality SSub SSub = Just Refl
    testEquality SEq  SEq  = Just Refl
    testEquality SLt  SLt  = Just Refl
    testEquality SGt  SGt  = Just Refl
    testEquality SLte SLte = Just Refl
    testEquality SGte SGte = Just Refl
    testEquality SAnd SAnd = Just Refl
    testEquality SOr  SOr  = Just Refl
    testEquality _ _ = Nothing


data SUniOp (op :: UniOp) where
    SFst     :: SUniOp 'Fst
    SSnd     :: SUniOp 'Snd
    SNot     :: SUniOp 'Not
    SNeg     :: SUniOp 'Neg

type family EqUniOp a b where
    EqUniOp 'Fst 'Fst = 'True
    EqUniOp 'Snd 'Snd = 'True
    EqUniOp 'Not 'Not = 'True
    EqUniOp 'Neg 'Neg = 'True
    EqUniOp a b = 'False

instance TestEquality SUniOp where
    testEquality SFst SFst = Just Refl
    testEquality SSnd SSnd = Just Refl
    testEquality SNot SNot = Just Refl
    testEquality SNeg SNeg = Just Refl
    testEquality _ _ = Nothing

type instance (==) a b = EqUniOp a b
type instance (==) a b = EqBinOp a b
type instance (==) a b = EqLabel a b

class Impossible d  where
    impossible :: d -> b

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

instance Pretty Lit where
    pPrintPrec _ prec lit = 
        case lit of
            CInt i | i < 0     -> maybeParens (prec >= 9) (integer i)
                   | otherwise -> integer i
            CBool True -> text "true"
            CBool False -> text "false"

data WellFormedPrinter e = 
    WellFormedPrinter { pPrintExp    :: PrettyLevel -> Rational -> e -> Doc
                      , pPrintIdent  :: PrettyLevel -> Rational -> Ident e -> Doc }

genericPPrint :: (WellFormed l e arg) => WellFormedPrinter e ->
                 PrettyLevel -> Rational -> 
                 SLabel l -> arg -> Doc
genericPPrint pp pLevel prec op arg =
    case (op, arg) of
        (SLiteral, lit) -> pPrintPrec pLevel prec lit
        (SVar, x) -> pPrintIdent pp pLevel prec x
        (SUnary, (UniArg op  e)) -> maybeParens (prec > prec') d
            where
            (prec',opName, prefix) = unaryPrec op
            d = case prefix of
                True -> (text opName <+> pPrintExp pp pLevel prec' e)
                False -> (pPrintExp pp pLevel prec' e <> text opName )
        (SBinary, (BinArg op e1 e2)) -> maybeParens (prec > prec') d
            where
            (prec',opName, assoc) = binaryPrec op
            f e = pPrintExp pp pLevel prec' e
            g e = pPrintExp pp pLevel (prec'+1) e
            d = case assoc of
                AssocLeft  -> f e1 <+> text opName <+> g e2
                AssocRight -> g e1 <+> text opName <+> f e2
                AssocNone  -> g e1 <+> text opName <+> g e2
        (SPair, (e1, e2)) -> parens $ pPrintExp pp pLevel 0 e1 <+> comma <+> pPrintExp pp pLevel 0 e2
        (SLambda, (xs, e)) -> maybeParens (prec > 0) $
            text "fun" <+> hsep (map (pPrintIdent pp pLevel 0) xs) <+> text "->" $+$
            nest 4 (pPrintExp pp pLevel 0 e)
        (SApp, (f, [])) -> maybeParens (prec > 8) $ pPrintIdent pp pLevel prec f <+> text "()"
        (SApp, (f, es)) -> maybeParens (prec > 8) $ pPrintIdent pp pLevel 8 f <+> hsep (map (pPrintExp pp pLevel 9) es)
        (SLet, (x, e1, e2)) -> maybeParens (prec > 0) $ 
            text "let" <+> pPrintIdent pp pLevel 0 x <+> text "=" 
                       <+> pPrintExp pp pLevel 0 e1 <+> text "in" $+$
            pPrintExp pp pLevel 0 e2
        (SAssume, (cond, e)) -> maybeParens (prec > 0) $
            text "assume" <+> pPrintExp pp pLevel 9 cond <> semi $+$
            pPrintExp pp pLevel 0 e
        (SIf, (cond, e1, e2)) -> maybeParens (prec > 0) $
            text "if" <+> pPrintExp pp pLevel 0 cond $+$
            nest 2 (text "then" <+> pPrintExp pp pLevel 0 e1) $+$
            nest 2 (text "else" <+> pPrintExp pp pLevel 0 e2)
        (SBranch, (e1, e2)) -> maybeParens (prec > 0) $
            pPrintExp pp pLevel 1 e1 <+> text "<>" <+> pPrintExp pp pLevel 1 e2
        (SFail, _) -> text "Fail"
        (SOmega, _) -> text "Omega"
        (SRand, _) -> text "*"

comment :: Pretty a => a -> Doc
comment a = text "(*" <+> pPrint a <+> text "*)"
