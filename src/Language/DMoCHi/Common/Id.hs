{-# Language FlexibleContexts, FlexibleInstances, UndecidableInstances, MultiParamTypeClasses #-}
module Language.DMoCHi.Common.Id(UniqueKey, runFreshIO, FreshIO, Id, HasUniqueKey(..)
                                , MonadId(..), freshId, reserved, reservedKey, maybeReserved, fromReserved
                                , MonadLogger(..), logMsg, defaultLogger, filterLogger, noLogger, fileLogger
                                , logInfo, logDebug, LogKey, Logging, updateKey, Assoc
                                , getName
                                , refresh, identify) where

import Control.Monad.State
import qualified Control.Monad.State.Strict as Strict
import qualified Control.Monad.RWS.Strict as Strict
-- import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Writer hiding((<>))
import Control.Monad.Except
import Control.Monad.Cont
-- import Data.Functor.Identity
import Data.Proxy
import Text.Parsec(ParsecT)
import Text.PrettyPrint.HughesPJClass
import Data.Hashable
import Data.Time
import Data.Aeson(encode)
import qualified Data.ByteString.Lazy as B
import Text.Printf
import GHC.TypeLits
import Data.IORef
import System.IO

import Language.DMoCHi.Common.PolyAssoc

newtype UniqueKey = UniqueKey { unUniqueKey :: Int }
    deriving(Eq,Ord)

instance Pretty UniqueKey where
    pPrint (UniqueKey i) = int i
instance Show UniqueKey where
    show (UniqueKey i) = show i
instance Hashable UniqueKey where
    hashWithSalt salt (UniqueKey i) = hashWithSalt salt i

class Monad m => MonadId m where
    freshInt :: m Int
    freshInt = unUniqueKey <$> freshKey 
    freshKey :: m UniqueKey
    freshKey = UniqueKey <$> freshInt

class MonadIO m => MonadLogger m where
    getLogger :: m Logger
    updateSummary :: (AssocList Logging -> AssocList Logging) -> m ()

data Logging

data LogContext = LogContext { 
    logger  :: Logger,
    summary :: IORef (AssocList Logging)
}

type Logger = LogKey -> Severity -> LogText -> IO ()
    
type LogKey = SomeSymbol
type LogText = String

data Severity 
  = Debug
  | Info
  | Warning
  | Error
  deriving(Eq,Ord, Show)
 
logMsg :: MonadLogger m => LogKey -> Severity -> String -> m ()
logMsg (SomeSymbol key) severity s = do
    timeStamp <- liftIO $ getCurrentTime
    let logStr = printf "[%-32s],[%s],[%s] %s" 
                        (show timeStamp) 
                        (symbolVal key) 
                        (show severity)
                        s
    logger <- getLogger
    liftIO $ logger (SomeSymbol key) severity logStr

updateKey :: (MonadLogger m, EntryParam Logging k v) => Proxy k -> v -> (v -> v) -> m ()
updateKey key defVal updateFun = updateSummary (update key defVal updateFun)

logInfo, logDebug :: MonadLogger m => LogKey -> String -> m ()
logInfo key s = logMsg key Info s

logDebug key s = logMsg key Debug s

newtype FreshIO a = FreshIO { unFreshIO :: LogContext -> Int -> IO (a, Int) }

{- Ident -}
data Id a = Id !UniqueKey a

instance Eq a => Eq (Id a) where
    Id (UniqueKey 0) b == Id (UniqueKey 0) d = b == d
    Id a _ == Id c _ = a == c

instance Ord a => Ord (Id a) where
    compare (Id (UniqueKey 0) b) (Id (UniqueKey 0) d) = compare b d
    compare (Id a _) (Id c _) = compare a c

instance Pretty (Id String) where
    pPrintPrec _ _ (Id (UniqueKey 0) x) = text x
    pPrintPrec level prec (Id i x) = 
        text x <> text "_" <> (pPrintPrec level prec i)

instance (Pretty (Id a)) => Show (Id a) where
    show = render . pPrint

instance (Hashable a) => Hashable (Id a) where
    hashWithSalt salt (Id (UniqueKey 0) a) =
        salt `hashWithSalt` (1 :: Int) `hashWithSalt` a
    hashWithSalt salt (Id key _) =
        salt `hashWithSalt` key
         
class HasUniqueKey a where
    getUniqueKey :: a -> UniqueKey

instance HasUniqueKey (Id a) where
    getUniqueKey (Id i _) = i

{-# INLINE freshId #-}
freshId :: MonadId m => String -> m String
freshId s = fmap (\i -> s ++ "_" ++ show i) freshInt

{-# INLINE reserved #-}
reserved :: a -> Id a
reserved x = Id (UniqueKey 0) x

{-# INLINE reservedKey #-}
reservedKey :: UniqueKey
reservedKey = UniqueKey 0

{-# INLINE maybeReserved #-}
maybeReserved :: Id a -> Maybe a
maybeReserved (Id (UniqueKey 0) v) = Just v
maybeReserved (Id _ _) = Nothing

{-# INLINE fromReserved #-}
fromReserved :: Id a -> a
fromReserved (Id (UniqueKey 0) v) = v
fromReserved _ = error "fromReserved: this is unreserved value"

{-# INLINE getName #-}
getName :: Id a -> a
getName (Id _ v) = v

{-# INLINE identify #-}
identify :: MonadId m => a -> m (Id a)
identify v = do
    key <- freshKey
    return $! Id key v

{-# INLINE refresh #-}
refresh :: MonadId m => Id a -> m (Id a)
refresh (Id _ v) = do
    key <- freshKey
    return $! Id key v

{-# INLINE runFreshIO #-}
runFreshIO :: Logger -> Handle -> FreshIO a -> IO a
runFreshIO logger handle m = do
    ref <- newIORef emptyAssoc
    let ctx = LogContext logger ref
    (v, _) <- unFreshIO m ctx 1
    stat <- readIORef ref
    B.hPut handle $ encode stat
    return v

noLogger :: Logger 
noLogger = \_ _ _ -> return ()

defaultLogger :: Logger
defaultLogger = \_ _ s -> putStrLn s

fileLogger :: Handle -> Logger
fileLogger h = \_ _ msg -> hPutStrLn h msg

filterLogger :: (LogKey -> Severity -> Bool) -> Logger -> Logger
filterLogger pred logger = \key s msg ->
    if pred key s
    then logger key s msg
    else return ()

instance Monad FreshIO where
    return a = FreshIO $ \_ !s -> return (a, s)
    {-# INLINE return #-}
    FreshIO f >>= m = FreshIO $ \ctx s -> 
        f ctx s >>= \(a, s') -> 
        unFreshIO (m a) ctx s'
    {-# INLINE (>>=) #-}

instance Functor FreshIO where
    fmap f (FreshIO m) = FreshIO $ \ctx s -> 
        fmap (\(a, s') -> (f a, s')) (m ctx s)
    {-# INLINE fmap #-}

instance Applicative FreshIO where
    pure = return
    {-# INLINE pure #-}
    (<*>) = ap
    {-# INLINE (<*>) #-}

{-
instance (Functor m, MonadPlus m) => Alternative (FreshT m) where
    empty = mzero
    (<|>) = mplus

instance (MonadPlus m) => MonadPlus (FreshT m) where
    mzero = FreshT mzero
    mplus m n = FreshT $ unFreshT m `mplus` unFreshT n
-}


instance MonadIO FreshIO where
    liftIO m = FreshIO $ \_ s -> m >>= \a -> pure (a,s)
    {-# INLINE liftIO #-}

instance MonadFix FreshIO where
    mfix f = FreshIO $ \ctx s -> mfix $ \ ~(a, _) -> unFreshIO (f a) ctx s
    {-# INLINE mfix #-}

instance MonadLogger FreshIO where
    getLogger = FreshIO $ \ctx s -> return (logger ctx,s)
    {-# INLINE getLogger #-}
    updateSummary f = FreshIO $ \ctx s -> do
        modifyIORef' (summary ctx) f
        return ((), s)
    {-# INLINE updateSummary #-}

instance MonadId FreshIO where
    freshInt = FreshIO $ \_ s -> return (s, s+1)
    {-# INLINE freshInt #-}

instance MonadId m => MonadId (ReaderT r m) where
    freshInt = lift freshInt
    {-# INLINE freshInt #-}

instance MonadLogger m => MonadLogger (ReaderT r m) where
    getLogger = lift getLogger
    {-# INLINE getLogger #-}
    updateSummary = lift . updateSummary
    {-# INLINE updateSummary #-}

instance MonadId m => MonadId (ParsecT s u m) where
    freshInt = lift freshInt
    {-# INLINE freshInt #-}

instance MonadLogger m => MonadLogger (ParsecT s u m) where
    getLogger = lift getLogger
    {-# INLINE getLogger #-}
    updateSummary = lift . updateSummary
    {-# INLINE updateSummary #-}

instance (Monoid w,MonadId m) => MonadId (WriterT w m) where
    freshInt = lift freshInt
    {-# INLINE freshInt #-}

instance (Monoid w, MonadLogger m) => MonadLogger (WriterT w m) where
    getLogger = lift getLogger
    {-# INLINE getLogger #-}
    updateSummary = lift . updateSummary
    {-# INLINE updateSummary #-}

instance MonadId m => MonadId (ExceptT e m) where
    freshInt = lift freshInt
    {-# INLINE freshInt #-}

instance MonadLogger m => MonadLogger (ExceptT e m) where
    getLogger = lift getLogger
    {-# INLINE getLogger #-}
    updateSummary = lift . updateSummary
    {-# INLINE updateSummary #-}

instance MonadId m => MonadId (StateT s m) where
    freshInt = lift freshInt
    {-# INLINE freshInt #-}

instance MonadLogger m => MonadLogger (StateT s m) where
    getLogger = lift getLogger
    {-# INLINE getLogger #-}
    updateSummary = lift . updateSummary
    {-# INLINE updateSummary #-}

instance MonadId m => MonadId (Strict.StateT s m) where
    freshInt = lift freshInt
    {-# INLINE freshInt #-}

instance MonadLogger m => MonadLogger (Strict.StateT s m) where
    getLogger = lift getLogger
    {-# INLINE getLogger #-}
    updateSummary = lift . updateSummary
    {-# INLINE updateSummary #-}

instance (MonadId m, Monoid w) => MonadId (Strict.RWST r w s m) where
    freshInt = lift freshInt
    {-# INLINE freshInt #-}

instance (MonadLogger m, Monoid w) => MonadLogger (Strict.RWST r w s m) where
    getLogger = lift getLogger
    {-# INLINE getLogger #-}
    updateSummary = lift . updateSummary
    {-# INLINE updateSummary #-}

instance (MonadId m) => MonadId (ContT r m) where
    freshInt = lift freshInt
    {-# INLINE freshInt #-}

instance MonadLogger m => MonadLogger (ContT r m) where
    getLogger = lift getLogger
    {-# INLINE getLogger #-}
    updateSummary = lift . updateSummary
    {-# INLINE updateSummary #-}
