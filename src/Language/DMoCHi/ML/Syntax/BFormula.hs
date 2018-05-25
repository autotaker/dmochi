{-# LANGUAGE DeriveGeneric #-}
module Language.DMoCHi.ML.Syntax.BFormula(
    BFormula, BFormulaBody(..),
    BFormulaFactory(..), mkBLeaf, mkBNode, toDNF
    )
    where

import           Data.Hashable
import           Text.PrettyPrint.HughesPJClass
import           GHC.Generics (Generic)
import           Control.Monad.IO.Class
import           Language.DMoCHi.Common.Cache

type BFormula = Identified BFormulaBody

data BFormulaBody =  
    BNode !Int !BFormula !BFormula -- if x then fml1 else fml2
  | BLeaf !Bool
  deriving (Eq, Ord, Generic)

instance Hashable BFormulaBody

instance Show BFormulaBody where
    show = render . pPrint

instance Pretty BFormulaBody where
    pPrint (BNode i v1 v2) =
        parens $ text "if" <+> int i <+> pPrint v1 <+> pPrint v2
    pPrint (BLeaf True) = text "true"
    pPrint (BLeaf False) = text "false"

class MonadIO m => BFormulaFactory m where
    getBFormulaCache   :: m (Cache BFormula)


mkBFormula :: BFormulaFactory m => BFormulaBody -> m BFormula
mkBFormula body = getBFormulaCache >>= liftIO . flip genIdentified body 

{-# INLINE mkBLeaf #-}
mkBLeaf :: BFormulaFactory m => Bool -> m BFormula
mkBLeaf b = mkBFormula (BLeaf b)

{-# INLINE mkBNode #-}
mkBNode :: BFormulaFactory m => Int -> BFormula -> BFormula -> m BFormula
mkBNode x v1 v2 
    | v1 == v2  = return v1 
    | otherwise = mkBFormula (BNode x v1 v2)

toDNF :: BFormula -> [[Int]]
toDNF = go []
    where 
    go cls fml = case body fml of
        BNode i thenFml elseFml -> 
            go (i : cls) thenFml ++ go (-i : cls)  elseFml
        BLeaf True -> [cls]
        BLeaf False -> []
