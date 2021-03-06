{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeFamilies, ConstraintKinds, TypeOperators, PolyKinds, UndecidableInstances, FlexibleContexts, DeriveGeneric #-}
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
                                      AnnotVar(..),
                                      Elem, Supported,
                                      unaryPrec,
                                      binaryPrec,
                                      genericPPrint,
                                      WellFormedPrinter(..),
                                      prettyBind,
                                      comment,
                                      reflectLabel,
                                      reflectBinOp,
                                      reflectUniOp)
                                       where
import GHC.Exts(Constraint)
import Text.Parsec.Expr(Assoc(..))
import Data.Type.Bool
import Data.Hashable
import GHC.Generics(Generic)
import Data.Type.Equality
import Text.PrettyPrint.HughesPJClass
import Data.Aeson

data Label = Literal | Var | Binary | Unary | Pair 
           | Lambda | App | Let | LetRec
           | Assume | If | Branch | Mark
           | Fail | Omega | Rand | Atomic
           deriving(Eq,Ord)
           
data BinOp = Add | Sub | NEq | Eq | Lt | Gt | Lte | Gte | And | Or  | Mul | Div | Mod
    deriving (Eq,Ord)
data UniOp = Fst | Snd | Not | Neg
    deriving (Eq,Ord)

data Lit = CInt Integer | CBool Bool | CUnit
    deriving(Eq,Ord,Generic)

instance ToJSON Lit where
    toJSON (CInt i) = toJSON i
    toJSON (CBool b) = toJSON b
    toJSON CUnit = Null

type family Ident e
type family Labels e :: [Label]
type family BinOps e :: [BinOp]
type family UniOps e :: [UniOp]

type family AllBinOps where
    AllBinOps = '[ 'Add, 'Sub, 'NEq, 'Eq, 'Lt, 'Gt, 'Lte, 'Gte, 'And, 'Or, 'Mul, 'Div, 'Mod ]

type family AllUniOps where
    AllUniOps = '[ 'Fst, 'Snd, 'Not, 'Neg ]

type family AllLabels where
    AllLabels = '[ 'Literal, 'Var, 'Binary, 'Unary, 'Pair,
                   'Lambda, 'App, 'Let, 'LetRec, 'Mark,
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

reflectLabel :: SLabel l -> Label
reflectLabel l = case l of
    SLiteral -> Literal
    SVar -> Var 
    SBinary -> Binary 
    SUnary -> Unary 
    SPair -> Pair 
    SLambda -> Lambda 
    SApp -> App 
    SLet -> Let 
    SLetRec -> LetRec
    SAssume -> Assume 
    SIf -> If 
    SBranch -> Branch 
    SFail -> Fail 
    SOmega -> Omega 
    SRand-> Rand
    SAtomic -> Atomic
    SMark -> Mark

reflectBinOp :: SBinOp op -> BinOp
reflectBinOp l = case l of
    SAdd -> Add 
    SSub -> Sub
    SMul -> Mul
    SDiv -> Div
    SMod -> Mod
    SEq -> Eq
    SNEq -> NEq
    SLt -> Lt
    SLte -> Lte
    SGt -> Gt
    SGte -> Gte
    SAnd -> And
    SOr -> Or

reflectUniOp :: SUniOp op -> UniOp
reflectUniOp l = case l of
    SFst -> Fst
    SSnd -> Snd
    SNot -> Not
    SNeg -> Neg

instance Eq e => Eq (BinArg e) where
    (==) (BinArg op1 e1 e2) (BinArg op2 e3 e4) = 
        reflectBinOp op1 == reflectBinOp op2 &&
        e1 == e3 && e2 == e4

instance Eq e => Eq (UniArg e) where
    (==) (UniArg op1 e1) (UniArg op2 e2) = 
        reflectUniOp op1 == reflectUniOp op2 &&
        e1 == e2

instance Ord e => Ord (BinArg e) where
    compare (BinArg op1 e1 e2) (BinArg op2 e3 e4) =
        compare (reflectBinOp op1) (reflectBinOp op2)
        `mappend` compare e1 e3 
        `mappend` compare e2 e4

instance Ord e => Ord (UniArg e) where
    compare (UniArg op1 e1) (UniArg op2 e2) =
        compare (reflectUniOp op1) (reflectUniOp op2)
        `mappend` compare e1 e2

instance Hashable Lit where


instance Hashable (SBinOp op) where
    hashWithSalt salt op = salt `hashWithSalt` v
        where 
        v :: Int
        v = case op of
            SAdd -> 1
            SSub -> 2
            SEq  -> 3
            SLt  -> 4
            SGt  -> 5
            SLte -> 6 
            SGte -> 7 
            SAnd -> 8
            SOr  -> 9
            SNEq -> 10
            SMul -> 11
            SDiv -> 12
            SMod -> 13

instance Hashable (SUniOp op) where
    hashWithSalt salt op = salt `hashWithSalt` v
        where 
        v :: Int
        v = case op of
            SFst -> 1
            SSnd -> 2
            SNot -> 3
            SNeg -> 4

type family WellFormed (l :: Label)  (e :: *)  (arg :: *) :: Constraint where
    WellFormed 'Literal e arg = arg ~ Lit
    WellFormed 'Var     e arg = arg ~ Ident e
    WellFormed 'Unary   e arg = arg ~ UniArg e
    WellFormed 'Binary  e arg = arg ~ BinArg e
    WellFormed 'Pair    e arg = arg ~ (e, e)
    WellFormed 'Lambda  e arg = arg ~ ([Ident e], e)
    WellFormed 'App     e arg = arg ~ (e, [e])
    WellFormed 'Let     e arg = arg ~ (Ident e, e, e)
    WellFormed 'LetRec  e arg = arg ~ ([(Ident e, e)], e)
    WellFormed 'Assume  e arg = arg ~ (e, e)
    WellFormed 'If      e arg = arg ~ (e, e, e)
    WellFormed 'Branch  e arg = arg ~ (e, e)
    WellFormed 'Fail    e arg = arg ~ ()
    WellFormed 'Omega   e arg = arg ~ ()
    WellFormed 'Rand    e arg = arg ~ ()
    WellFormed 'Mark    e arg = arg ~ (Ident e, e)
    WellFormed 'Atomic  e arg = 'True ~ 'False

data SLabel (l :: Label) where
    SLiteral :: SLabel 'Literal
    SVar     :: SLabel 'Var
    SBinary  :: SLabel 'Binary
    SUnary   :: SLabel 'Unary
    SPair    :: SLabel 'Pair
    SLambda  :: SLabel 'Lambda
    SApp     :: SLabel 'App
    SLet     :: SLabel 'Let
    SLetRec  :: SLabel 'LetRec
    SAssume  :: SLabel 'Assume
    SIf      :: SLabel 'If
    SBranch  :: SLabel 'Branch
    SFail    :: SLabel 'Fail
    SOmega   :: SLabel 'Omega
    SRand    :: SLabel 'Rand
    SAtomic  :: SLabel 'Atomic
    SMark    :: SLabel 'Mark

type family EqLabel a b where
    EqLabel 'Literal 'Literal = 'True
    EqLabel 'Var 'Var = 'True
    EqLabel 'Binary 'Binary = 'True
    EqLabel 'Unary 'Unary = 'True
    EqLabel 'Pair 'Pair = 'True
    EqLabel 'Lambda 'Lambda = 'True
    EqLabel 'App 'App = 'True
    EqLabel 'Let 'Let = 'True
    EqLabel 'LetRec 'LetRec = True
    EqLabel 'Assume 'Assume = 'True
    EqLabel 'If 'If = 'True
    EqLabel 'Branch 'Branch = 'True
    EqLabel 'Fail 'Fail = 'True
    EqLabel 'Omega 'Omega = 'True
    EqLabel 'Rand 'Rand = 'True
    EqLabel 'Atomic 'Atomic = 'True
    EqLabel 'Mark 'Mark = 'True
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
    SNEq     :: SBinOp 'NEq
    SDiv     :: SBinOp 'Div
    SMul     :: SBinOp 'Mul
    SMod     :: SBinOp 'Mod

type family EqBinOp a b where
    EqBinOp 'Add 'Add = 'True
    EqBinOp 'Sub 'Sub = 'True
    EqBinOp 'Eq  'Eq = 'True
    EqBinOp 'NEq 'NEq = 'True
    EqBinOp 'Lt  'Lt = 'True
    EqBinOp 'Gt  'Gt = 'True
    EqBinOp 'Lte 'Lte = 'True
    EqBinOp 'Gte 'Gte = 'True
    EqBinOp 'And 'And = 'True
    EqBinOp 'Or  'Or = 'True
    EqBinOp 'Div 'Div = 'True
    EqBinOp 'Mod 'Mod = 'True
    EqBinOp 'Mul 'Mul = 'True
    EqBinOp a b = 'False

instance TestEquality SBinOp where
    testEquality SAdd SAdd = Just Refl
    testEquality SSub SSub = Just Refl
    testEquality SDiv SDiv = Just Refl
    testEquality SMod SMod = Just Refl
    testEquality SMul SMul = Just Refl
    testEquality SEq  SEq  = Just Refl
    testEquality SNEq SNEq  = Just Refl
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


instance Show (SBinOp op) where
    show SAdd = "SAdd"
    show SSub = "SSub"
    show SEq = "SEq"
    show SNEq = "SNEq"
    show SLt = "SLt"
    show SGt = "SGt"
    show SLte = "SLte"
    show SGte = "SLte"
    show SAnd = "SAnd"
    show SOr = "SOr"
    show SDiv = "SDiv"
    show SMul = "SMul"
    show SMod = "SMod"
instance Show (SUniOp op) where
    show SFst = "SFst"
    show SSnd = "SSnd"
    show SNot = "SNot"
    show SNeg = "SNeg"

unaryPrec :: SUniOp op -> (Rational, String, Bool)
unaryPrec SNeg = (8, "-", True)
unaryPrec SNot = (8, "not", True)
unaryPrec SFst = (9, ".fst", False)
unaryPrec SSnd = (9, ".snd", False)

binaryPrec :: SBinOp op -> (Rational, String, Assoc)
binaryPrec SAdd = (6, "+", AssocLeft)
binaryPrec SSub = (6, "-", AssocLeft)
binaryPrec SDiv = (7, "/", AssocLeft)
binaryPrec SMod = (7, "mod", AssocLeft)
binaryPrec SMul = (8, "*", AssocLeft)
binaryPrec SEq   = (4, "=", AssocNone)
binaryPrec SNEq  = (4, "<>", AssocNone)
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
            CUnit -> text "()"
instance Show Lit where
    show = render . pPrint
            

data WellFormedPrinter e = 
    WellFormedPrinter { pPrintExp    :: PrettyLevel -> Rational -> e -> Doc
                      , pPrintIdent  :: PrettyLevel -> Rational -> Ident e -> Doc }

prettyBind :: PrettyLevel
prettyBind = PrettyLevel 86029468

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
            hang (text "fun" <+> hsep (map (pPrintIdent pp prettyBind 0) xs) <+> text "->" ) 4 (pPrintExp pp pLevel 0 e)
        (SApp, (e, [])) -> maybeParens (prec > 8) $ pPrintExp pp pLevel 9 e <+> text "()"
        (SApp, (e, es)) -> maybeParens (prec > 8) $ pPrintExp pp pLevel 9 e <+> hsep (map (pPrintExp pp pLevel 9) es)
        (SLet, (x, e1, e2)) -> maybeParens (prec > 0) $ 
            let d1 = hang (text "let" <+> pPrintIdent pp prettyBind 0 x <+> text "=") 4 (pPrintExp pp pLevel 0 e1) in
            d1 <+> text "in" $+$
            pPrintExp pp pLevel 0 e2
        (SLetRec, (fs,e)) -> maybeParens (prec > 0) $
            let drec = vcat $ 
                    zipWith ($$) 
                        (text "let rec" : repeat (text "and"))
                        [ nest 8 $ hang (pPrintIdent pp prettyBind 0 x <+> text "=") 4 (pPrintExp pp pLevel 0 e1) | (x,e1) <- fs ]
                in
            drec <+> text "in" $+$ 
            pPrintExp pp pLevel 0 e
        (SAssume, (cond, e)) -> maybeParens (prec > 0) $
            text "assume" <+> pPrintExp pp pLevel 9 cond <> semi $+$
            pPrintExp pp pLevel 0 e
        (SIf, (cond, e1, e2)) -> maybeParens (prec > 0) $
            text "if" <+> pPrintExp pp pLevel 0 cond $+$
            (hang (text "then") 4 (pPrintExp pp pLevel 0 e1)) $+$
            (hang (text "else") 4 (pPrintExp pp pLevel 0 e2))
        (SBranch, (e1, e2)) -> maybeParens (prec > 0) $
            text "if" <+> text "_" $+$
            (hang (text "then") 4 (pPrintExp pp pLevel 0 e1)) $+$
            (hang (text "else") 4 (pPrintExp pp pLevel 0 e2))
        (SMark, (x, e)) -> maybeParens (prec > 0) $
            text "mark" <+> pPrintIdent pp prettyBind 0 x <> semi $+$
            pPrintExp pp pLevel 0 e
        (SFail, _) -> text "assert(false)"
        (SOmega, _) -> text "assume(false)"
        (SRand, _) -> text "random()"

comment :: Pretty a => a -> Doc
comment a = text "(*" <+> pPrint a <+> text "*)"

data AnnotVar a b = 
    V { varName :: a 
      , varType :: b }
      deriving(Eq,Show, Functor)

instance Foldable (AnnotVar a) where
    foldMap f (V _ b) = f b

instance Traversable (AnnotVar a) where
    traverse f (V a b) = V a <$> f b

