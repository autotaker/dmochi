module Language.DMoCHi.ML.Syntax.Atom(
  Atom(..), Formula, PredTemplate
  , mkBin, mkUni, mkLiteral, mkVar
  , module Language.DMoCHi.ML.Syntax.Base
  , module Language.DMoCHi.ML.Syntax.Type
  , Atomic(..), substAtomic, substAFormula, substFormula, desubstAtom
  , decompose, updateFormula, decomposeFormula
) where
import Language.DMoCHi.ML.Syntax.Base
import Language.DMoCHi.ML.Syntax.Type
import Language.DMoCHi.Common.Sized
import Language.DMoCHi.Common.Id(UniqueKey)
import Text.PrettyPrint.HughesPJClass
import qualified Data.Map as M
import Data.List(sortOn)

data Atom where
    Atom :: (WellFormed l Atom arg, Supported l (Labels Atom)) =>
            SLabel l -> arg -> Type -> Atom

type instance Ident Atom = TId

type instance Labels Atom  = '[ 'Literal, 'Var, 'Binary, 'Unary ]
type instance BinOps Atom  = '[ 'Add, 'Sub, 'Div, 'Mul, 'Mod, 'Eq, 'Lt, 'Lte, 'And, 'Or ]
type instance UniOps Atom  = '[ 'Fst, 'Snd, 'Not, 'Neg ]

mkBin :: SBinOp op -> Atom -> Atom -> Atom
mkBin op v1 v2 = case op of
    SAdd -> Atom SBinary (BinArg SAdd v1 v2) TInt
    SSub -> Atom SBinary (BinArg SSub v1 v2) TInt
    SDiv -> Atom SBinary (BinArg SDiv v1 v2) TInt
    SMul -> Atom SBinary (BinArg SMul v1 v2) TInt
    SMod -> Atom SBinary (BinArg SMod v1 v2) TInt
    SEq  -> Atom SBinary (BinArg SEq v1 v2) TBool
    SNEq  -> Atom SUnary (UniArg SNot (Atom SBinary (BinArg SEq v1 v2) TBool)) TBool
    SLt  -> Atom SBinary (BinArg SLt v1 v2) TBool
    SLte -> Atom SBinary (BinArg SLte v1 v2) TBool
    SGt  -> Atom SBinary (BinArg SLt v2 v1) TBool
    SGte -> Atom SBinary (BinArg SLte v2 v1) TBool
    SAnd -> Atom SBinary (BinArg SAnd v1 v2) TBool
    SOr  -> Atom SBinary (BinArg SOr  v1 v2) TBool


mkUni :: SUniOp op -> Atom -> Atom
mkUni op v1@(Atom _ _ sty) = case op of
    SNeg -> Atom SUnary (UniArg SNeg v1) TInt
    SNot -> Atom SUnary (UniArg SNot v1) TBool
    SFst -> case sty of
        TPair sty1 _ -> Atom SUnary (UniArg SFst v1) sty1
        _ -> error "mkUni: Fst"
    SSnd -> case sty of
        TPair _ sty2 -> Atom SUnary (UniArg SSnd v1) sty2
        _ -> error "mkUni: Snd"

mkLiteral :: Lit -> Atom
mkLiteral l@(CInt _) = Atom SLiteral l TInt
mkLiteral l@(CBool _) = Atom SLiteral l TBool
mkLiteral CUnit = error "mkLiteral: unexpected unit literal"

mkVar :: TId -> Atom
mkVar x@(TId sty _) = Atom SVar x sty

instance HasType Atom where
    getType (Atom _ _ sty) = sty

instance Pretty Atom where
    pPrintPrec plevel prec (Atom op arg sty) =
        if plevel == prettyNormal
            then doc
            else comment sty <+> doc
        where
        doc = genericPPrint pp plevel prec op arg
        pp :: WellFormedPrinter Atom
        pp = WellFormedPrinter { pPrintExp   = pPrintPrec
                               , pPrintIdent = pPrintPrec }
instance Show Atom where
  show = render . pPrint

instance Eq Atom where
    (==) (Atom l1 arg1 _) (Atom l2 arg2 _) =
        case (l1,l2) of
            (SLiteral, SLiteral) -> arg1 == arg2
            (SLiteral, _) -> False
            (SVar, SVar) -> arg1 == arg2
            (SVar, _) -> False
            (SBinary, SBinary) -> arg1 == arg2
            (SBinary, _) -> False
            (SUnary, SUnary) -> arg1 == arg2
            (SUnary, _) -> False

instance Sized Atom where
    getSize (Atom l arg _) =
        case l of
            SLiteral -> 1
            SVar     -> 1
            SBinary | BinArg _ a1 a2 <- arg -> 1 + getSize a1 + getSize a2
            SUnary  | UniArg _ a1 <- arg -> 1 + getSize a1

class Atomic a where
  atomic :: a -> Maybe Atom
  opFst  :: a -> a
  opSnd  :: a -> a
  fromAtom :: Atom -> a
  {-# INLINE unsafeAtomic #-}
  unsafeAtomic :: a -> Atom
  unsafeAtomic a = case atomic a of
    Just v -> v
    Nothing -> error "unsafeAtomic: cannot convert to Atom"

instance Atomic Atom where
  atomic = Just
  opFst = mkUni SFst
  opSnd = mkUni SSnd
  fromAtom = id
  unsafeAtomic = id


{-# INLINE substAtomic #-}
substAtomic :: forall a. Atomic a => M.Map TId a -> Atom -> Atom
substAtomic subst = unsafeAtomic . go
  where
  go :: Atom -> a
  go e@(Atom l arg _) =
    case (l, arg) of
      (SLiteral, _) -> fromAtom e
      (SVar, x) -> case M.lookup x subst of
        Just v -> v
        Nothing -> fromAtom e
      (SUnary, UniArg SFst v1) -> opFst (go v1)
      (SUnary, UniArg SSnd v1) -> opSnd (go v1)
      (SUnary, UniArg op v1) ->
        fromAtom $ mkUni op (unsafeAtomic $ go v1)
      (SBinary, BinArg op v1 v2) ->
        fromAtom $ mkBin op (unsafeAtomic $ go v1) (unsafeAtomic $ go v2)


-- Formula is an Atom whose type is TBool.
type Formula = Atom

-- Template for predicate generation.
-- ``key`` identifies the location of the predicate
-- ``atoms`` are arguments for the predicates. Each atom must have a base type.
type PredTemplate = (UniqueKey, [Atom])

substAFormula :: M.Map TId Atom -> Formula -> Formula
substAFormula = substAtomic

substFormula :: M.Map TId TId -> Formula -> Formula
substFormula  = substAFormula . fmap mkVar

desubstAtom :: M.Map TId Atom -> Atom -> Atom
desubstAtom env atom = foldr f atom assocs
    where
    assocs = sortOn (getSize.snd) $ M.assocs env
    f :: (TId, Atom) -> Atom -> Atom
    f (x, v) a@(Atom l arg _)
        | a == v = mkVar x
        | otherwise =
            case l of
                SLiteral -> a
                SVar -> a
                SBinary | BinArg op a1 a2 <- arg ->
                    mkBin op (f (x, v) a1) (f (x, v) a2)
                SUnary  | UniArg op a1 <- arg ->
                    mkUni op (f (x, v) a1)

decomposeFormula :: Formula -> [Formula] -> [Formula]
decomposeFormula a@(Atom l arg _) acc =
    case (l, arg) of
        (SLiteral, _) -> acc
        (SBinary, BinArg SAnd a1 a2) ->
            decomposeFormula a1 (decomposeFormula a2 acc)
        (SBinary, BinArg SOr a1 a2) ->
            decomposeFormula a1 (decomposeFormula a2 acc)
        (SUnary, UniArg SNot a1) ->
            decomposeFormula a1 acc
        (_, _) -> a : acc

updateFormula :: Formula -> [Formula] -> [Formula]
updateFormula phi fml = foldr f fml (decomposeFormula phi [])
  where f p fml | p `elem` fml = fml
                | otherwise = p : fml

{- decompose x l: decompose into list of atoms whose types are base sorts -}
decompose :: Atom -> [Atom] -> [Atom]
decompose x l = case getType x of
    TPair _ _ -> decompose (mkUni SFst x) (decompose (mkUni SSnd x) l)
    TFun _ _  -> l
    TInt -> x : l
    TBool -> x : l