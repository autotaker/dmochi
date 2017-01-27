{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeFamilies, ConstraintKinds #-}
module Language.DMoCHi.ML.Syntax.Base(Label(..), 
                                      BinOp(..),
                                      UniOp(..),
                                      Literal,
                                      Ident,
                                      WellFormed,
                                      SLabel(..),
                                      SBinOp(..),
                                      SUniOp(..),
                                      Assoc(..),
                                      Impossible(..))
                                       where
import GHC.Exts(Constraint)
import Text.Parsec.Expr(Assoc(..))

data Label = Literal | Var | Binary | Unary | Pair 
           | Lambda | App | Let 
           | Assume | If | Branch 
           | Fail | Omega | Rand

data BinOp = Add | Sub | Eq | Lt | Gt | Lte | Gte | And | Or 
data UniOp = Fst | Snd | Not | Neg

type family Literal e
type family Ident e

type family WellFormed (l :: Label) (op1 :: UniOp) (op2 :: BinOp) (e :: *)  (arg :: *) :: Constraint where
    WellFormed 'Literal op1 op2 e arg = arg ~ Literal e
    WellFormed 'Var     op1 op2 e arg = arg ~ Ident e
    WellFormed 'Unary   op1 op2 e arg = arg ~ (SUniOp op1, e)
    WellFormed 'Binary  op1 op2 e arg = arg ~ (SBinOp op2, e, e)
    WellFormed 'Pair    op1 op2 e arg = arg ~ (e, e)
    WellFormed 'Lambda  op1 op2 e arg = arg ~ ([Ident e], e)
    WellFormed 'App     op1 op2 e arg = arg ~ (Ident e, [e])
    WellFormed 'Let     op1 op2 e arg = arg ~ (Ident e, e, e)
    WellFormed 'Assume  op1 op2 e arg = arg ~ (e, e)
    WellFormed 'If      op1 op2 e arg = arg ~ (e, e, e)
    WellFormed 'Branch  op1 op2 e arg = arg ~ (e, e)
    WellFormed 'Fail    op1 op2 e arg = arg ~ ()
    WellFormed 'Omega   op1 op2 e arg = arg ~ ()
    WellFormed 'Rand    op1 op2 e arg = arg ~ ()

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

data SUniOp (op :: UniOp) where
    SFst     :: SUniOp 'Fst
    SSnd     :: SUniOp 'Snd
    SNot     :: SUniOp 'Not
    SNeg     :: SUniOp 'Neg

class Impossible d  where
    impossible :: d -> b

