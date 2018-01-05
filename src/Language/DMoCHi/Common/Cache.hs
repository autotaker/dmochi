module Language.DMoCHi.Common.Cache where
import Data.IORef
import qualified Data.HashTable.IO as H
import Text.PrettyPrint.HughesPJClass
import Data.Hashable
import Language.DMoCHi.Common.Util
import Control.Monad.IO.Class

type HashTable k v = H.BasicHashTable k v

data Identified a = Identified { body :: a, ident :: !Int }

type instance Key (Identified a) = a

instance Eq (Identified a) where
    (==) = (==) `on` ident

instance Ord (Identified a) where
    compare = compare `on` ident

instance Show a => Show (Identified a) where
    show = show . body

instance Hashable (Identified a) where
    hashWithSalt salt = hashWithSalt salt . ident

instance Pretty a => Pretty (Identified a) where
    pPrintPrec level prec = pPrintPrec level prec . body

type family Key (a :: *) :: *

data Cache e = Cache {
    entries :: HashTable (Key e) e 
  , counter  :: IORef Int
}

newCache :: IO (Cache e)
newCache = Cache <$> H.new <*> newIORef 0

{-# INLINE genEntry #-}
genEntry :: (Eq (Key e),Hashable (Key e),MonadIO m) => Cache e -> Key e -> (Int -> m e) -> m e
genEntry cache key cnstr = 
    liftIO (H.lookup (entries cache) key) >>= \case
        Just v -> return v
        Nothing -> do
            i <- liftIO $ readIORef (counter cache)
            liftIO $ writeIORef (counter cache) $! i + 1
            v <- cnstr i
            liftIO $ H.insert (entries cache) key $! v
            return v

genIdentified :: (Eq e, Hashable e) => Cache (Identified e) -> e -> IO (Identified e) 
genIdentified cache key = genEntry cache key (return . Identified key)
