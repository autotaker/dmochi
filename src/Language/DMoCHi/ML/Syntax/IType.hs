{-# LANGUAGE DeriveGeneric #-}
module Language.DMoCHi.ML.Syntax.IType(
    IType, ITypeBody(..), ityBody,
    ITermType, ITermTypeBody(..), itermBody,
    BFormula, BFormulaBody(..), bfmlBody,
    ITypeFactory(..),
    genIType, genITermType, genBFormula,
    mkIBase, mkIPair, mkIFun,
    mkIFail, mkITerm,
    mkBLeaf, mkBNode, concatMerge, merge,
    subTypeOf, subTermTypeOf, mkIntersection, appType
    )
    where

import qualified Data.HashTable.IO as H
import           Data.IORef
import           Data.Hashable
import           Text.PrettyPrint.HughesPJClass
import           GHC.Generics (Generic)
import           Language.DMoCHi.Common.Util
import           Control.Monad.IO.Class
import           Data.List(sort,foldl')

data IType 
  = IType { 
      ityBody  :: !ITypeBody,
      ityIdent :: !Int
    }
type HashTable k v = H.BasicHashTable k v

instance Eq IType where
    (==) = (==) `on` ityIdent
instance Ord IType where
    compare = compare `on` ityIdent
instance Hashable IType where
    hashWithSalt salt = hashWithSalt salt . ityIdent
instance Show IType where
    show = render . pPrint

data ITypeBody 
  = IBase
  | IPair !IType !IType
  | IFun  [([IType], BFormula, ITermType)]
  deriving(Eq, Ord, Generic)

instance Hashable ITypeBody
instance Show ITypeBody where
    show = render . pPrint

data ITermType 
  = ITermType { 
      itermBody  :: !ITermTypeBody,
      itermIdent :: !Int 
    }

instance Eq ITermType where
    (==) = (==) `on` itermIdent
instance Ord ITermType where
    compare = compare `on` itermIdent
instance Hashable ITermType where
    hashWithSalt salt = hashWithSalt salt . itermIdent
instance Show ITermType where
    show = render . pPrint

data ITermTypeBody
  = IFail
  | ITerm !IType !BFormula
  deriving(Eq, Ord, Generic)

instance Hashable ITermTypeBody

instance Show ITermTypeBody where
    show = render . pPrint

data BFormula 
  = BFormula {
      bfmlBody  :: BFormulaBody,
      bfmlIdent :: Int
  }

instance Eq BFormula where
    (==) = (==) `on` bfmlIdent
instance Ord BFormula where
    compare = compare `on` bfmlIdent
instance Hashable BFormula where
    hashWithSalt salt = hashWithSalt salt . bfmlIdent
instance Show BFormula where
    show = render . pPrint

data BFormulaBody
  = BNode !Int !BFormula !BFormula
  | BLeaf !Bool
  deriving (Eq,Ord,Generic)

instance Hashable BFormulaBody
instance Show BFormulaBody where
    show = render . pPrint

instance Pretty IType where
    pPrintPrec plevel prec = pPrintPrec plevel prec . ityBody
        
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

instance Pretty ITermType where
    pPrintPrec plevel prec = pPrintPrec plevel prec . itermBody

instance Pretty ITermTypeBody where
    pPrintPrec _ _ IFail = text "fail"
    pPrintPrec plevel _ (ITerm ty fml) = braces $ pPrintPrec plevel 0 ty <+> text "|" <+> text (show fml)

instance Pretty BFormula where
    pPrintPrec plevel prec = pPrintPrec plevel prec . bfmlBody

instance Pretty BFormulaBody where
    pPrint (BNode i v1 v2) =
        parens $ text "if" <+> int i <+> pPrint v1 <+> pPrint v2
    pPrint (BLeaf True) = text "true"
    pPrint (BLeaf False) = text "false"

class MonadIO m => ITypeFactory m where
    getITypeTable      :: m (HashTable ITypeBody IType)
    getITypeCounter    :: m (IORef Int)
    getITermTable      :: m (HashTable ITermTypeBody ITermType)
    getITermCounter    :: m (IORef Int)
    getBFormulaTable   :: m (HashTable BFormulaBody BFormula)
    getBFormulaCounter :: m (IORef Int)

gen :: (Hashable k, Eq k) => HashTable k v -> IORef Int -> k -> (k -> Int -> v) -> IO v
gen tbl cnt k cnstr =
    H.lookup tbl k >>= \case
        Just v -> return v
        Nothing -> do
            i <- readIORef cnt
            writeIORef cnt $! i + 1
            let v = cnstr k i
            H.insert tbl k $! v
            return v

{-# INLINE genIType #-}
genIType :: ITypeFactory m => ITypeBody -> m IType
genIType key = do
    tbl <- getITypeTable
    cnt <- getITypeCounter
    liftIO $ gen tbl cnt key IType

{-# INLINE genITermType #-}
genITermType :: ITypeFactory m => ITermTypeBody -> m ITermType
genITermType key = do
    tbl <- getITermTable
    cnt <- getITermCounter
    liftIO $ gen tbl cnt key ITermType

{-# INLINE genBFormula #-}
genBFormula  :: ITypeFactory m => BFormulaBody -> m BFormula
genBFormula key = do
    tbl <- getBFormulaTable
    cnt <- getBFormulaCounter
    liftIO $ gen tbl cnt key BFormula

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

{-# INLINE mkBLeaf #-}
mkBLeaf :: ITypeFactory m => Bool -> m BFormula
mkBLeaf b = genBFormula (BLeaf b)

{-# INLINE mkBNode #-}
mkBNode :: ITypeFactory m => Int -> BFormula -> BFormula -> m BFormula
mkBNode x v1 v2 | v1 == v2  = return v1 
                | otherwise = genBFormula (BNode x v1 v2)

subTypeOf :: IType -> IType -> Bool
subTypeOf = sub `on` ityBody
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
subTermTypeOf = sub `on` itermBody
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
    case (ityBody ty1, ityBody ty2) of
        (IFun assoc1, IFun assoc2) -> mkIFun (merge assoc1 assoc2)
        _ -> error $ "mkIntersection: defined only on function types: " ++ show (ty1, ty2)

appType :: IType -> [IType] -> BFormula -> [ITermType]
appType (ityBody -> IFun assoc) thetas phi = 
    foldl' (\acc x -> x `seq` acc) () l `seq` l
    where
    l = sort [ iota | (thetas', phi', iota) <- assoc, thetas == thetas' && phi == phi' ]
appType ity _ _ = error $ "appType: unexpected argument: " ++ show ity

