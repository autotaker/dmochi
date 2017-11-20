module Language.DMoCHi.ML.Syntax.Type where
-- import Language.DMoCHi.Common.Util
import qualified Language.DMoCHi.Common.Id as Id
import Text.PrettyPrint.HughesPJClass 
import Data.Hashable
import Language.DMoCHi.Common.Util
import Language.DMoCHi.ML.Syntax.Base(prettyBind)

data TId = TId { _type :: !Type, name :: !(Id.Id String) }

instance Eq TId where
    (==) = (==) `on` name

instance Ord TId where
    compare = compare `on` name

instance Hashable TId where
    hashWithSalt salt t = hashWithSalt salt (name t)

data Type = TInt | TBool | TPair Type Type | TFun [Type] Type deriving(Eq)

isBase :: Type -> Bool
isBase TInt = True
isBase TBool = True
isBase _ = False

alphaTId :: Id.MonadId m => TId -> m TId
alphaTId (TId sty x) = TId sty <$> Id.refresh x

instance Pretty Type where
    pPrintPrec _ _ TInt = text "int"
    pPrintPrec _ _ TBool = text "bool"
    pPrintPrec plevel prec (TPair t1 t2) =
        maybeParens (prec > 0) (d1 <+> text "*" <+> d2)
        where
            d1 = pPrintPrec plevel 1 t1
            d2 = pPrintPrec plevel 1 t2
    pPrintPrec plevel prec (TFun tys t) =
        maybeParens (prec > 0) (d1 <+> text "->" <+> d2)
        where
            d1 = brackets $ 
                 hsep $ 
                 punctuate comma $ 
                 map (pPrintPrec plevel 0) tys
            d2 = pPrintPrec plevel 0 t

instance Pretty TId where
    pPrintPrec plevel prec (TId sty f) 
        | plevel == prettyBind = maybeParens (prec > 0) $
                        pPrintPrec plevel 0 f 
                        <+> text ":" 
                        <+> pPrintPrec plevel 0 sty
        | otherwise = pPrintPrec plevel prec f

instance Show TId where
    show (TId sty f) = show f ++ " : " ++ prettyShow sty

class HasType m where
    getType :: m -> Type

instance HasType TId where
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

