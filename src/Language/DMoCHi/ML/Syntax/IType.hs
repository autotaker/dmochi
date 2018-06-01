{-# LANGUAGE DeriveGeneric, PatternSynonyms #-}
module Language.DMoCHi.ML.Syntax.IType(
    IType, -- ITypeBody(..), 
    ITermType, -- ITermTypeBody(..), 
    ITypeFactory(..),
    -- genIType, genITermType, 
    mkIBase, mkIPair, mkIFun,
    mkIFail, mkITerm,
    isFail, 
    pattern IBase, pattern IPair, pattern IFun,
    pattern IFail, pattern ITerm,
    concatMerge, merge,
    subTypeOf, subTermTypeOf, mkIntersection, appType,
    module Language.DMoCHi.ML.Syntax.BFormula
    )
    where

import           Data.Hashable
import           Text.PrettyPrint.HughesPJClass
import           GHC.Generics (Generic)
-- import           Language.DMoCHi.Common.Util
import           Control.Monad.IO.Class
import           Data.List(sort,foldl')
import           Language.DMoCHi.Common.Cache
import           Language.DMoCHi.ML.Syntax.BFormula

type IType = Identified ITypeBody

data ITypeBody 
  = IBase'
  | IPair' !IType !IType
  | IFun'  [([IType], BFormula, ITermType)]
  deriving(Eq, Ord, Generic)

pattern IBase <- Identified { body = IBase' }
pattern IPair v1 v2 <- Identified { body = IPair' v1 v2 }
pattern IFun as <- Identified { body = IFun' as }
{-# COMPLETE IBase, IPair, IFun #-}

instance Hashable ITypeBody
instance Show ITypeBody where
    show = render . pPrint

type ITermType = Identified ITermTypeBody

data ITermTypeBody
  = IFail'
  | ITerm' !IType !BFormula
  deriving(Eq, Ord, Generic)

pattern IFail <- Identified { body = IFail' }
pattern ITerm ty fml <- Identified { body = ITerm' ty fml }
{-# COMPLETE IFail, ITerm #-}

instance Hashable ITermTypeBody

instance Show ITermTypeBody where
    show = render . pPrint

instance Pretty ITypeBody where
    pPrintPrec plevel prec ity =
        case ity of
            IBase' -> text "base"
            IPair' ity1 ity2 -> maybeParens (prec > 0) d 
                where
                    d1 = pPrintPrec plevel 1 ity1
                    d2 = pPrintPrec plevel 1 ity2
                    d  = d1 <+> text "*" <+> d2
            IFun' ty_assoc -> 
                braces $ vcat $ punctuate comma $ 
                    map (\(ty_xs, fml, ty_ret) -> 
                            let d_xs = hsep $ punctuate comma (map (pPrintPrec plevel 0) ty_xs)
                                d_fml = text $ show fml
                                d_ret = pPrintPrec plevel 0 ty_ret
                            in braces (d_xs <+> text "|" <+> d_fml) <+> text "->" <+> d_ret) ty_assoc

instance Pretty ITermTypeBody where
    pPrintPrec _ _ IFail' = text "fail"
    pPrintPrec plevel _ (ITerm' ty fml) = 
        braces $ pPrintPrec plevel 0 ty <+> text "|" <+> text (show fml)


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
mkIPair ity1 ity2 = genIType (IPair' ity1 ity2)

{-# INLINE mkIBase #-}
mkIBase :: IType
mkIBase = reserved (-1) IBase'

{-# INLINE mkIFun #-}
mkIFun :: ITypeFactory m => [([IType], BFormula, ITermType)] -> m IType
mkIFun assoc = genIType (IFun' assoc)

{-# INLINE mkIFail #-}
mkIFail :: ITermType
mkIFail = reserved (-1) IFail'

{-# INLINE isFail #-}
isFail :: ITermType -> Bool
isFail IFail = True
isFail _ = False

{-# INLINE mkITerm #-}
mkITerm :: ITypeFactory m => IType -> BFormula -> m ITermType
mkITerm ity fml = genITermType (ITerm' ity fml)

subTypeOf :: IType -> IType -> Bool
subTypeOf = sub
    where
    sub IBase IBase = True
    sub (IFun as1) (IFun as2) =
        all (\(thetas_i, fml_i, iota_i) ->
           any (\(thetas_j, fml_j, iota_j) ->
               thetas_i == thetas_j && 
               fml_i == fml_j && 
               iota_i `subTermTypeOf` iota_j
               ) as1
           ) as2
    sub (IPair ty1 ty2) (IPair ty3 ty4) = subTypeOf ty1 ty3 && subTypeOf ty2 ty4
    sub ty1 ty2 = error $ "subTypeOf: sort mismatch" ++ show (ty1, ty2)

subTermTypeOf :: ITermType -> ITermType -> Bool
subTermTypeOf = sub
    where
    sub IFail IFail = True
    sub (ITerm theta1 fml1) (ITerm theta2 fml2) =
        fml1 == fml2 && subTypeOf theta1 theta2
    sub _ _     = False

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
mkIntersection (IFun assoc1) (IFun assoc2) = mkIFun (merge assoc1 assoc2)
mkIntersection ty1 ty2 = 
    error $ "mkIntersection: defined only on function types: " ++ show (ty1, ty2)

appType :: IType -> [IType] -> BFormula -> [ITermType]
appType (IFun assoc) thetas phi = 
    foldl' (\acc x -> x `seq` acc) () l `seq` l
    where
    l = sort [ iota | (thetas', phi', iota) <- assoc, thetas == thetas' && phi == phi' ]
appType ity _ _ = error $ "appType: unexpected argument: " ++ show ity

