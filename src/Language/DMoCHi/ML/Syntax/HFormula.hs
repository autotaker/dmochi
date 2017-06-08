{-# LANGUAGE LambdaCase, BangPatterns, DeriveGeneric, GeneralizedNewtypeDeriving, MultiParamTypeClasses #-}
module Language.DMoCHi.ML.Syntax.HFormula where

import qualified Data.HashTable.IO as H
import           Data.Hashable
import           Text.PrettyPrint.HughesPJClass
import           Data.Type.Equality
import qualified Z3.Monad as Z3

-- import           Language.DMoCHi.Common.Id
import           Language.DMoCHi.Common.Util
import           Language.DMoCHi.ML.Syntax.Type
import           Language.DMoCHi.ML.Syntax.PType hiding(Env)
import           Language.DMoCHi.ML.Syntax.PNormal hiding(mkBin, mkUni, mkVar, mkLiteral)
-- import           Language.DMoCHi.ML.Flow
import qualified Language.DMoCHi.ML.SMT as SMT

type HashTable k v = H.BasicHashTable k v

data HFormula where
    HFormula :: (WellFormed l HFormula arg, Supported l (Labels HFormula)) => 
                SLabel l -> arg -> Type -> SMT.IValue -> Int -> HFormula

getIdent :: HFormula -> Int
getIdent (HFormula _ _ _ _ key) = key

getIValue :: HFormula -> SMT.IValue
getIValue (HFormula _ _ _ iv _) = iv

type instance Ident HFormula  = TId
type instance Labels HFormula  = '[ 'Literal, 'Var, 'Unary, 'Binary ]
type instance BinOps HFormula = '[ 'Add, 'Sub, 'Div, 'Mul, 'Eq, 'Lt, 'Lte, 'And, 'Or ]
type instance UniOps HFormula = '[ 'Fst, 'Snd, 'Not, 'Neg ]


instance Hashable (BinArg HFormula) where
    hashWithSalt salt (BinArg l v1 v2) = 
        salt `hashWithSalt` l 
             `hashWithSalt` getIdent v1 
             `hashWithSalt` getIdent v2

instance Hashable (UniArg HFormula) where
    hashWithSalt salt (UniArg l v) = 
        salt `hashWithSalt` l 
             `hashWithSalt` getIdent v 

instance Hashable HFormula where
    hashWithSalt salt (HFormula l arg _ _ _) =
        case l of
            SLiteral -> salt `hashWithSalt` (1 :: Int) `hashWithSalt` arg
            SVar     -> salt `hashWithSalt` (2 :: Int) `hashWithSalt` arg
            SBinary  -> salt `hashWithSalt` (3 :: Int) `hashWithSalt` arg
            SUnary   -> salt `hashWithSalt` (4 :: Int) `hashWithSalt` arg

instance Eq HFormula where
    (==) (HFormula l1 arg1 _ _ _) (HFormula l2 arg2 _ _ _) =
        case (l1,l2) of
            (SLiteral, SLiteral) -> arg1 == arg2
            (SLiteral, _) -> False
            (SVar, SVar) -> arg1 == arg2
            (SVar, _) -> False
            (SBinary, SBinary) -> 
                case (arg1, arg2) of
                    (BinArg op1 v1 v2, BinArg op2 v3 v4) -> 
                        case testEquality op1 op2 of
                            Just _ -> v1 === v3 && v2 === v4
                            Nothing -> False
            (SBinary, _) -> False
            (SUnary, SUnary) ->
                case (arg1, arg2) of
                    (UniArg op1 v1, UniArg op2 v2) ->
                        case testEquality op1 op2 of
                            Just _ -> v1 === v2
                            Nothing -> False
            (SUnary, _) -> False

infix 4 ===

(===) :: HFormula -> HFormula -> Bool
(===) = (==) `on` getIdent

class Z3.MonadZ3 m => HFormulaFactory m where
    genHFormula :: (SMT.IValue -> Int -> HFormula) -> m SMT.IValue -> m HFormula
 
mkBin :: (HFormulaFactory m, Supported op (BinOps HFormula))  => SBinOp op -> HFormula -> HFormula -> m HFormula
mkBin op v1 v2 = 
    let iv1 = getIValue v1
        iv2 = getIValue v2
        SMT.ASTValue v1' = iv1
        SMT.ASTValue v2' = iv2
        isLinear = case (v1, v2) of
            (HFormula SLiteral (CInt _) _ _ _, _ ) -> True
            (_, HFormula SLiteral (CInt _) _ _ _) -> True
            _ -> False
    in case op of
        SAdd -> genHFormula (HFormula SBinary (BinArg SAdd v1 v2) TInt) (SMT.ASTValue <$> Z3.mkAdd [v1', v2']) 
        SSub -> genHFormula (HFormula SBinary (BinArg SSub v1 v2) TInt) (SMT.ASTValue <$> Z3.mkSub [v1', v2'])
        SDiv -> genHFormula (HFormula SBinary (BinArg SDiv v1 v2) TInt) (SMT.mkUDiv iv1 iv2)
        SMul -> genHFormula (HFormula SBinary (BinArg SMul v1 v2) TInt) (SMT.mkUMul isLinear iv1 iv2)
        SEq  -> genHFormula (HFormula SBinary (BinArg SEq v1 v2) TBool) (SMT.mkEqIValue iv1 iv2)
        SLt  -> genHFormula (HFormula SBinary (BinArg SLt v1 v2) TBool) (SMT.ASTValue <$> Z3.mkLt v1' v2')
        SLte -> genHFormula (HFormula SBinary (BinArg SLte v1 v2) TBool) (SMT.ASTValue <$> Z3.mkLe v1' v2')
        SAnd -> genHFormula (HFormula SBinary (BinArg SAnd v1 v2) TBool) (SMT.ASTValue <$> Z3.mkAnd [v1', v2'])
        SOr  -> genHFormula (HFormula SBinary (BinArg SOr  v1 v2) TBool) (SMT.ASTValue <$> Z3.mkOr [v1', v2'])

mkUni :: HFormulaFactory m => SUniOp op -> HFormula -> m HFormula
mkUni op v1@(HFormula _ _ sty _ _) = 
    case op of
        SNeg -> 
            let SMT.ASTValue v1' = getIValue v1 in
            genHFormula (HFormula SUnary (UniArg SNeg v1) TInt) (SMT.ASTValue <$> Z3.mkUnaryMinus v1')
        SNot -> 
            let SMT.ASTValue v1' = getIValue v1 in
            genHFormula (HFormula SUnary (UniArg SNot v1) TBool) (SMT.ASTValue <$> Z3.mkNot v1')
        SFst -> case sty of
            TPair sty1 _ -> 
                let SMT.IPair iv_fst _ = getIValue v1 in
                genHFormula (HFormula SUnary (UniArg SFst v1) sty1) (pure iv_fst)
            _ -> error "mkUni: Fst"
        SSnd -> case sty of
            TPair _ sty2 -> 
                let SMT.IPair _ iv_snd = getIValue v1 in
                genHFormula (HFormula SUnary (UniArg SSnd v1) sty2) (pure iv_snd)
            _ -> error "mkUni: Snd"

mkLiteral :: HFormulaFactory m => Lit -> m HFormula
mkLiteral l@(CInt i)  = genHFormula (HFormula SLiteral l TInt) (SMT.ASTValue <$> Z3.mkInteger i)
mkLiteral l@(CBool b) = genHFormula (HFormula SLiteral l TBool) (SMT.ASTValue <$> Z3.mkBool b)
mkLiteral CUnit = error "unexpected pattern"

mkVar :: HFormulaFactory m => TId -> m HFormula
mkVar x@(TId sty name_x) = genHFormula (HFormula SVar x sty) (SMT.toIValueId sty (show name_x))

toHFormula :: HFormulaFactory m => Formula -> m HFormula
toHFormula (Atom l arg _) = 
    case (l, arg) of
        (SLiteral, arg) -> mkLiteral arg
        (SVar, arg) -> mkVar arg
        (SBinary, BinArg op v1 v2) -> do
            f1 <- toHFormula v1
            f2 <- toHFormula v2
            mkBin op f1 f2
        (SUnary, UniArg op v1) -> do
            f1 <- toHFormula v1
            mkUni op f1

fromHFormula :: HFormula -> Formula
fromHFormula (HFormula l arg sty _ _) = 
    case (l, arg) of
        (SLiteral, arg) -> Atom l arg sty
        (SVar, arg) -> Atom l arg sty
        (SBinary, BinArg op v1 v2) -> 
            Atom l (BinArg op (fromHFormula v1) (fromHFormula v2)) sty
        (SUnary, UniArg op v1) -> 
            Atom l (UniArg op (fromHFormula v1)) sty

instance Pretty HFormula where
    pPrintPrec plevel prec v = pPrintPrec plevel prec (fromHFormula v)

{-
data IType = IInt | IBool | IPair IType IType | IFun [([IType], BFormula, ITermType)]
    deriving (Eq,Ord,Show, Generic)
data ITermType = IFail | ITerm IType BFormula
    deriving (Eq,Ord,Show, Generic)

instance Hashable IType
instance Hashable ITermType

instance Pretty IType where
    pPrintPrec plevel prec ity =
        case ity of
            IInt  -> text "int"
            IBool -> text "bool"
            IPair ity1 ity2 -> maybeParens (prec > 0) d 
                where
                    d1 = pPrintPrec plevel 1 ity1
                    d2 = pPrintPrec plevel 1 ity2
                    d  = d1 <+> text "*" <+> d2
            IFun ty_assoc -> 
                braces $ vcat $ punctuate comma $ 
                    map (\(ty_xs, fml, ty_ret) -> 
                            let d_xs = hsep $ punctuate comma (map (pPrintPrec plevel 0) ty_xs)
                                d_fml = text $ show fml
                                d_ret = pPrintPrec plevel 0 ty_ret
                            in braces (d_xs <+> text "|" <+> d_fml) <+> text "->" <+> d_ret) ty_assoc
instance Pretty ITermType where
    pPrintPrec _ _ IFail = text "fail"
    pPrintPrec plevel _ (ITerm ty fml) = braces $ pPrintPrec plevel 0 ty <+> text "|" <+> text (show fml)

subTypeOf :: IType -> IType -> Bool
subTypeOf IInt IInt = True
subTypeOf IInt _    = error "subTypeOf: sort mismatch"
subTypeOf IBool IBool = True
subTypeOf IBool _    = error "subTypeOf: sort mismatch"
subTypeOf (IFun as1) (IFun as2) =
    all (\(thetas_i, fml_i, iota_i) ->
       any (\(thetas_j, fml_j, iota_j) ->
           thetas_i == thetas_j && 
           fml_i == fml_j && 
           iota_i `subTermTypeOf` iota_j
           ) as1
       ) as2
subTypeOf (IFun _) _ = error "subTypeOf: sort mismatch"
subTypeOf (IPair ty1 ty2) (IPair ty3 ty4) = subTypeOf ty1 ty3 && subTypeOf ty2 ty4
subTypeOf (IPair _ _) _ = error "subTypeOf: sort mismatch"

subTermTypeOf :: ITermType -> ITermType -> Bool
subTermTypeOf IFail IFail = True
subTermTypeOf IFail _ = False
subTermTypeOf (ITerm theta1 fml1) (ITerm theta2 fml2) =
    fml1 == fml2 && subTypeOf theta1 theta2
subTermTypeOf (ITerm _ _) _ = False

data BFormula = BAnd BFormula BFormula | BOr BFormula BFormula | BVar Int | BConst Bool
    deriving (Eq,Ord,Generic)
instance Show BFormula where
    showsPrec p (BVar i) = showsPrec p i
    showsPrec _ (BConst True) = showString "true"
    showsPrec _ (BConst False) = showString "false"
    showsPrec p (BAnd b1 b2) = showParen (p > 2) $ showsPrec 2 b1 . showString " && " . showsPrec 2 b2
    showsPrec p (BOr b1 b2)  = showParen (p > 1) $ showsPrec 1 b1 . showString " || " . showsPrec 1 b2

instance Hashable BFormula

mkBAnd, mkBOr :: BFormula -> BFormula -> BFormula
mkBAnd (BConst True) b = b
mkBAnd (BConst False) _ = BConst False
mkBAnd b (BConst True) = b
mkBAnd _ (BConst False) = BConst False
mkBAnd b1 b2 = BAnd b1 b2

mkBOr (BConst False) b = b
mkBOr (BConst True) _ = BConst True
mkBOr b (BConst False) = b
mkBOr _ (BConst True) = BConst True
mkBOr b1 b2 = BOr b1 b2
-}
