module Language.DMoCHi.Common.PolyAssoc (
  Assoc, EntryParam, assoc, update, AssocList, emptyAssoc, access
  ) where
-- type-safe polymorphic assoc list
-- avoids name conflictions by using type-level symbols 

import GHC.TypeLits
import Data.Proxy
import Data.Aeson
import Data.Hashable
import Data.Type.Equality
import qualified Data.HashMap.Strict as H
import Data.Text(pack)
import Data.Kind(Constraint)
import Unsafe.Coerce
import Lens.Micro

-- name represents namespace
type family Assoc (name :: *) (k :: Symbol) :: *
type family EntryParam n k v :: Constraint where
    EntryParam n k v = (KnownSymbol k, v ~ Assoc n k, ToJSON v, Show v, Eq v)

data Entry n where
    Entry :: (EntryParam n k v) => Proxy k -> Assoc n k -> Entry n

instance Eq (Entry n) where
    (Entry k1 v1) == (Entry k2 v2) =
        case sameSymbol k1 k2 of
            Just Refl -> v1 == v2
            Nothing -> False
    
instance Show (Entry n) where
    show (Entry proxy v) = "(" ++ symbolVal proxy ++ "," ++ show v ++ ")"

instance ToJSON (AssocList n) where
    toJSON (AssocList l) = object [ pack (symbolVal k) .= toJSON v | Entry k v <- H.elems l ]

newtype AssocList n = AssocList (H.HashMap (Hashed String) (Entry n))

instance Show (AssocList n) where
    show = show . toJSON

instance Eq (AssocList n) where
    AssocList v1 == AssocList v2 = v1 == v2

access :: (EntryParam n k v) => Proxy k -> Lens' (AssocList n) (Maybe v)
access key = lens getter setter
    where 
    getter (AssocList h) = do
        Entry _ v <- H.lookup (hashed (symbolVal key)) h
        return (unsafeCoerce v)
    setter (AssocList h) (Just !v) = AssocList h'
        where h' = H.insert (hashed (symbolVal key)) (Entry key v) h
    setter (AssocList h) Nothing = AssocList h'
        where h' = H.delete (hashed (symbolVal key)) h


assoc :: (EntryParam n k v) => Proxy k -> AssocList n -> (Maybe (Assoc n k))
assoc key l = l ^. access key

update :: (EntryParam n k v) => Proxy k -> v -> (v -> v) -> AssocList n -> AssocList n
update key defVal updateFun h = over (access key) (\case
    Nothing -> Just defVal
    Just v  -> Just (updateFun v)) h

emptyAssoc :: AssocList n
emptyAssoc = AssocList H.empty

