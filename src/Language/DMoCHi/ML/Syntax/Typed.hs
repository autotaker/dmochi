{-# LANGUAGE FlexibleContexts, BangPatterns, GADTs, TypeFamilies, DataKinds #-}
module Language.DMoCHi.ML.Syntax.Typed {- ( Program(..)
                                      , Exp(..)
                                      , Value(..)
                                      , Op(..)
                                      , LetValue(..)
                                      , FunDef(..)
                                      , substV
                                      , evalV
                                      , size
                                      , sizeE
                                      , sizeV
                                      , sizeLV
                                      , freeVariables
                                      , module Language.DMoCHi.ML.Syntax.Type
                                      ) -} where
-- import qualified Data.Map as M
-- import qualified Data.Set as S
import Language.DMoCHi.Common.Id 
import Language.DMoCHi.ML.Syntax.Type
import Language.DMoCHi.ML.Syntax.Base
import Text.PrettyPrint.HughesPJClass

data Program = Program { functions :: [(TId, UniqueKey, [TId], Exp)] 
                       , mainTerm  :: Exp }

data Exp where
    Exp :: ( WellFormed l Exp arg
           , Supported l (Labels Exp)) => SLabel l -> arg -> Type -> UniqueKey -> Exp

type instance Labels Exp = AllLabels
type instance BinOps Exp = AllBinOps
type instance UniOps Exp = AllUniOps
type instance Ident Exp = TId

instance HasType Exp where
    getType (Exp _ _ sty _) = sty
instance HasUniqueKey Exp where
    getUniqueKey (Exp _ _ _ key) = key

instance Pretty Exp where
    pPrintPrec plevel prec (Exp op arg sty key) =
        if plevel == prettyNormal
            then doc 
            else comment (key, sty) <+> doc
        where
        doc = genericPPrint pp plevel prec op arg
        pp :: WellFormedPrinter Exp
        pp = WellFormedPrinter { pPrintExp   = pPrintPrec
                               , pPrintIdent = pPrintPrec }

instance Pretty Program where
    pPrintPrec plevel _ (Program fs t) = 
        text "(* functions *)" $+$ 
        vcat (map (\(f,key,xs,e) -> 
            comment key $+$
            text "let" <+> pPrintPrec plevel 0 f <+> hsep (map (pPrintPrec prettyBind 1) xs) <+> colon <+> pPrint (getType e) <+> equals $+$
            nest 4 (pPrintPrec plevel 0 e <> text ";;")) fs) $+$
        text "(*main*)" $+$
        pPrintPrec plevel 0 t
