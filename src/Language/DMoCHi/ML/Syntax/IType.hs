{-# LANGUAGE DeriveGeneric #-}
module Language.DMoCHi.ML.Syntax.IType(
    IType, ITypeBody(..), 
    ITermType, ITermTypeBody(..), 
    ITypeFactory(..),
    genIType, genITermType, 
    mkIBase, mkIPair, mkIFun,
    mkIFail, mkITerm,
    concatMerge, merge,
    subTypeOf, subTermTypeOf, mkIntersection, appType,
    module Language.DMoCHi.ML.Syntax.BFormula
    )
    where

import           Data.Hashable
import           Text.PrettyPrint.HughesPJClass
import           GHC.Generics (Generic)
import           Language.DMoCHi.Common.Util
import           Control.Monad.IO.Class
import           Data.List(sort,foldl')
import           Language.DMoCHi.Common.Cache
import           Language.DMoCHi.ML.Syntax.BFormula

type IType = Identified ITypeBody

data ITypeBody 
  = IBase
  | IPair !IType !IType
  | IFun  [([IType], BFormula, ITermType)]
  deriving(Eq, Ord, Generic)

instance Hashable ITypeBody
instance Show ITypeBody where
    show = render . pPrint

type ITermType = Identified ITermTypeBody

data ITermTypeBody
  = IFail
  | ITerm !IType !BFormula
  deriving(Eq, Ord, Generic)

instance Hashable ITermTypeBody

instance Show ITermTypeBody where
    show = render . pPrint

instance Pretty ITypeBody where
    pPrintPrec plevel prec ity =
        case ity of
            IBase -> text "base"
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

instance Pretty ITermTypeBody where
    pPrintPrec _ _ IFail = text "fail"
    pPrintPrec plevel _ (ITerm ty fml) = braces $ pPrintPrec plevel 0 ty <+> text "|" <+> text (show fml)


class BFormulaFactory m => ITypeFactory m where
    getITypeCache :: m (Cache IType)
    getITermCache :: m (Cache ITermType)

{-# INLINE genIType #-}
genIType :: ITypeFactory m => ITypeBody -> m IType
genIType body = getITypeCache >>= liftIO . flip genIdentified body

{-# INLINE genITermType #-}
genITermType :: ITypeFactory m => ITermTypeBody -> m ITermType
genITermType body = getITermCache >>= liftIO . flip genIdentified body

{-# INLINE mkIPair #-}
mkIPair :: ITypeFactory m => IType -> IType -> m IType
mkIPair ity1 ity2 = genIType (IPair ity1 ity2)

{-# INLINE mkIBase #-}
mkIBase :: ITypeFactory m => m IType
mkIBase = genIType IBase

{-# INLINE mkIFun #-}
mkIFun :: ITypeFactory m => [([IType], BFormula, ITermType)] -> m IType
mkIFun assoc = genIType (IFun assoc)

{-# INLINE mkIFail #-}
mkIFail :: ITypeFactory m => m ITermType
mkIFail = genITermType IFail

{-# INLINE mkITerm #-}
mkITerm :: ITypeFactory m => IType -> BFormula -> m ITermType
mkITerm ity fml = genITermType (ITerm ity fml)

subTypeOf :: IType -> IType -> Bool
subTypeOf = sub `on` body
    where
    sub IBase IBase = True
    sub IBase _ = error "subTypeOf: sort mismatch"
    sub (IFun as1) (IFun as2) =
        all (\(thetas_i, fml_i, iota_i) ->
           any (\(thetas_j, fml_j, iota_j) ->
               thetas_i == thetas_j && 
               fml_i == fml_j && 
               iota_i `subTermTypeOf` iota_j
               ) as1
           ) as2
    sub (IFun _) _ = error "subTypeOf: sort mismatch"
    sub (IPair ty1 ty2) (IPair ty3 ty4) = subTypeOf ty1 ty3 && subTypeOf ty2 ty4
    sub (IPair _ _) _ = error "subTypeOf: sort mismatch"


subTermTypeOf :: ITermType -> ITermType -> Bool
subTermTypeOf = sub `on` body
    where
    sub IFail IFail = True
    sub IFail _     = False
    sub (ITerm theta1 fml1) (ITerm theta2 fml2) =
        fml1 == fml2 && subTypeOf theta1 theta2
    sub (ITerm _ _) _ = False

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys) = case compare x y of
    EQ -> x : merge xs ys
    LT -> x : merge xs (y:ys)
    GT -> y : merge (x:xs) ys

concatMerge :: Ord a => [[a]] -> [a]
concatMerge [] = []
concatMerge [x] = x
concatMerge (x:y:xs) = concatMerge (merge x y:xs)

{-# INLINE mkIntersection #-}
mkIntersection :: ITypeFactory m => IType -> IType -> m IType
mkIntersection ty1 ty2 = 
    case (body ty1, body ty2) of
        (IFun assoc1, IFun assoc2) -> mkIFun (merge assoc1 assoc2)
        _ -> error $ "mkIntersection: defined only on function types: " ++ show (ty1, ty2)

appType :: IType -> [IType] -> BFormula -> [ITermType]
appType (body -> IFun assoc) thetas phi = 
    foldl' (\acc x -> x `seq` acc) () l `seq` l
    where
    l = sort [ iota | (thetas', phi', iota) <- assoc, thetas == thetas' && phi == phi' ]
appType ity _ _ = error $ "appType: unexpected argument: " ++ show ity

