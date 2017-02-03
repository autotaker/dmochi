{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, Rank2Types #-}
module Language.DMoCHi.ML.Syntax.Type where
import Language.DMoCHi.Common.Util
import qualified Language.DMoCHi.Common.Id as Id
import Text.PrettyPrint.HughesPJClass
import Data.Type.Equality

data Id = Id { _type :: Type, name :: String } deriving(Show)

instance Eq Id where
    (==) = (==) `on` name

instance Ord Id where
    compare = compare `on` name

data Type = TInt | TBool | TPair Type Type | TFun [Type] Type deriving(Eq)
data TypeLabel = LBase | LPair | LFun

data SId where
    SId ::  SType ty -> Id.Id String -> SId

instance Eq SId where
    SId _ x == SId _ y = x == y
instance Ord SId where
    compare (SId _ x) (SId _ y) = compare x y

foldArg :: (forall ty. SType ty -> b -> b) -> b -> STypeArg -> b
foldArg _ acc SArgNil = acc
foldArg f acc (SArgCons x xs) = f x (foldArg f acc xs)

mapArg :: (forall ty. SType ty -> a) -> STypeArg -> [a]
mapArg f = foldArg (\x acc -> f x : acc) []

instance Pretty (SType ty) where
    pPrintPrec _ _ STInt = text "int"
    pPrintPrec _ _ STBool = text "bool"
    pPrintPrec plevel prec (STPair t1 t2) =
        maybeParens (prec > 0) (d1 <+> text "*" <+> d2)
        where
            d1 = pPrintPrec plevel 1 t1
            d2 = pPrintPrec plevel 1 t2
    pPrintPrec plevel prec (STFun tys t) =
        maybeParens (prec > 0) (d1 <+> text "->" <+> d2)
        where
            d1 = brackets $ 
                 hsep $ 
                 punctuate comma $ 
                 mapArg (pPrintPrec plevel 0) tys
            d2 = pPrintPrec plevel 0 t
instance Pretty SomeSType where
    pPrint (SomeSType ty) = pPrint ty

instance Show SomeSType where
    show = render . pPrint
instance Show (SType ty) where
    show = render . pPrint

data SType (ty :: TypeLabel) where
    STInt :: SType 'LBase
    STBool :: SType 'LBase
    STPair :: SType ty1 -> SType ty2 -> SType 'LPair
    STFun  :: STypeArg -> SType ty -> SType 'LFun

instance TestEquality SType where
    testEquality STInt STInt = Just Refl
    testEquality STBool STBool = Just Refl
    testEquality (STPair ty1 ty2) (STPair ty1' ty2') = 
        testEquality ty1 ty1' >> 
        testEquality ty2 ty2' >> 
        Just Refl
    testEquality (STFun tys ty) (STFun tys' ty') =
        let go SArgNil SArgNil = Just ()
            go (SArgCons x xs) (SArgCons y ys) = testEquality x y >> go xs ys
            go _ _ = Nothing
        in go tys tys' >> testEquality ty ty' >> Just Refl
    testEquality _ _ = Nothing

data SomeSType where
    SomeSType :: SType ty -> SomeSType

data STypeArg where
    SArgNil :: STypeArg
    SArgCons :: SType ty -> STypeArg -> STypeArg 

class HasType m where
    getType :: m -> Type

instance HasType Id where
    getType = _type

pprintT :: Int -> Type -> Doc
pprintT _ TInt = text "int"
pprintT _ TBool = text "bool"
pprintT assoc (TPair t1 t2) =
    let d1 = pprintT 1 t1
        d2 = pprintT 1 t2
        d  = d1 <+> text "*" <+> d2
    in if assoc <= 0 then d else parens d
pprintT assoc (TFun ts t2) =
    let d1 = brackets $ hsep $ punctuate comma (map (pprintT 0) ts)
        d2 = pprintT 0 t2
        d  = d1 <+> text "->" <+> d2
    in if assoc == 0 then d else parens d

instance Show Type where
    show = render . pprintT 0

orderT :: Type -> Int
orderT TInt = 0
orderT TBool = 0
orderT (TPair t1 t2) = max (orderT t1) (orderT t2)
orderT (TFun ts t2)  = 
    max (maximum (0: map orderT ts) + 1) (orderT t2)

