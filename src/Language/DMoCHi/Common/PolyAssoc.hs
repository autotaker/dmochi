module Language.DMoCHi.Common.PolyAssoc where
-- type-safe polymorphic assoc list
-- avoids name conflictions by using type-level symbols 

import GHC.TypeLits
import Data.Proxy
import Data.Type.Equality
import Data.Aeson
import Data.Text(pack)
import Data.Kind(Constraint)

-- name represents namespace
type family Assoc (name :: *) (k :: Symbol) :: *
type family EntryParam n k v :: Constraint where
    EntryParam n k v = (KnownSymbol k, v ~ Assoc n k, ToJSON v, Show v)

data Entry n where
    Entry :: (EntryParam n k v) => Proxy k -> Assoc n k -> Entry n

instance Show (Entry n) where
    show (Entry proxy v) = "(" ++ symbolVal proxy ++ "," ++ show v ++ ")"

instance ToJSON (AssocList n) where
    toJSON l = object [ pack (symbolVal k) .= toJSON v | Entry k v <- l ]

-- current implementation is naive assoc list
type AssocList n = [Entry n]

assoc :: (KnownSymbol k) => Proxy k -> AssocList n -> (Maybe (Assoc n k))
assoc _ [] = Nothing 
assoc key (Entry k v : l) = 
    case sameSymbol key k of
        Just Refl -> Just v
        Nothing -> assoc key l

update :: (EntryParam n k v) => Proxy k -> v -> (v -> v) -> AssocList n -> AssocList n
update key defVal updateFun es = case es of
    [] -> [Entry key defVal]
    (Entry k v : es') -> 
        case sameSymbol key k of
            Just Refl -> 
                let !v' = updateFun v in (Entry k v') : es'
            Nothing -> Entry k v : update key defVal updateFun es'

emptyAssoc :: AssocList n
emptyAssoc = []

{-
 -- example
data Test
type instance Assoc Test "test" = Int

sample :: AssocList Test
sample = [Entry kTest 0]

kTest :: Proxy "test"
kTest = Proxy

v :: Maybe Int
v = assoc kTest sample
-- => Just 0
-- -}
