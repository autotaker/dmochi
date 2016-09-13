module Language.DMoCHi.ML.Syntax.Type where
import Language.DMoCHi.Common.Util
import Text.PrettyPrint

data Id = Id { _type :: Type, name :: String } deriving(Show)

instance Eq Id where
    (==) = (==) `on` name

instance Ord Id where
    compare = compare `on` name

data Type = TInt | TBool | TPair Type Type | TFun [Type] Type deriving(Eq)

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

