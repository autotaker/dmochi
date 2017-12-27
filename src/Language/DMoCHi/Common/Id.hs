{-# Language FlexibleContexts, FlexibleInstances, UndecidableInstances, MultiParamTypeClasses #-}
module Language.DMoCHi.Common.Id(UniqueKey, unUniqueKey, runFreshT, FreshT, Id, HasUniqueKey(..)
                                , MonadId(..), freshId, reserved, reservedKey, maybeReserved, fromReserved
                                , getName
                                , refresh, identify) where

import Control.Monad.State
import qualified Control.Monad.State.Strict as Strict
import qualified Control.Monad.RWS.Strict as Strict
import Control.Monad.Reader
import Control.Monad.Writer hiding((<>))
import Control.Monad.Except
import Control.Monad.Cont
import Control.Monad.CTrace
import Control.Monad.Logger
import Text.Parsec(ParsecT)
import Text.PrettyPrint.HughesPJClass
import Data.Hashable

newtype UniqueKey = UniqueKey { unUniqueKey :: Int }
    deriving(Eq,Ord)

instance Pretty UniqueKey where
    pPrint (UniqueKey i) = int i
instance Show UniqueKey where
    show (UniqueKey i) = show i
instance Hashable UniqueKey where
    hashWithSalt salt (UniqueKey i) = hashWithSalt salt i

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

class Monad m => MonadId m where
    freshInt :: m Int
    freshInt = unUniqueKey <$> freshKey 
    {-# INLINE freshInt #-}
    freshKey :: m UniqueKey
    freshKey = UniqueKey <$> freshInt
    {-# INLINE freshKey #-}

newtype FreshT m a = FreshT { unFreshT :: Int -> m (Id a) }

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

{-# INLINE runFreshT #-}
runFreshT :: Monad m => FreshT m a -> m a
runFreshT m = do
    Id _ v <- unFreshT m 1
    return v

instance Monad m => Monad (FreshT m) where
    return a = FreshT $ \ !s -> return (Id (UniqueKey s) a)
    {-# INLINE return #-}
    FreshT f >>= m = FreshT $ \ !s -> 
        f s >>= \ (Id s' a) -> 
        unFreshT (m a) (unUniqueKey s')
    {-# INLINE (>>=) #-}

instance Functor m => Functor (FreshT m) where
    fmap f (FreshT m) = FreshT $ \s -> 
        fmap (\(Id s' a) -> Id s' (f a)) (m s)
    {-# INLINE fmap #-}

instance Monad m => Applicative (FreshT m) where
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

mapFreshT :: (m (Id a) -> m' (Id b)) -> FreshT m a -> FreshT m' b
mapFreshT f m = FreshT $ f . unFreshT m

instance MonadIO m => MonadIO (FreshT m) where
    liftIO m = FreshT $ \s -> fmap (Id (UniqueKey s)) (liftIO m)
    {-# INLINE liftIO #-}

instance MonadFix m => MonadFix (FreshT m) where
    -- mfix :: (a -> m a) -> m a
    mfix f = FreshT $ \s -> mfix $ \v -> unFreshT (f (getName v)) s
    {-# INLINE mfix #-}

instance Monad m => MonadId (FreshT m) where
    freshInt = FreshT $ \s -> return (Id (UniqueKey $ s+1) s)
    {-# INLINE freshInt #-}

instance MonadTrans FreshT where
    lift m = FreshT $ \s -> (Id (UniqueKey s)) <$> m
    {-# INLINE lift #-}

instance MonadTrace c m => MonadTrace c (FreshT m) where
    update = lift . update
    {-# INLINE update #-}
    zoom' = mapFreshT . zoom'
    {-# INLINE zoom' #-}

instance MonadLogger m => MonadLogger (FreshT m) where
    monadLoggerLog l s v msg = lift (monadLoggerLog l s v msg)
    {-# INLINE monadLoggerLog #-}

instance MonadLoggerIO m => MonadLoggerIO (FreshT m) 
 
instance MonadId m => MonadId (ReaderT r m) where
    freshInt = lift freshInt
    {-# INLINE freshInt #-}

instance MonadId m => MonadId (ParsecT s u m) where
    freshInt = lift freshInt
    {-# INLINE freshInt #-}

instance (Monoid w,MonadId m) => MonadId (WriterT w m) where
    freshInt = lift freshInt
    {-# INLINE freshInt #-}

instance MonadId m => MonadId (ExceptT e m) where
    freshInt = lift freshInt
    {-# INLINE freshInt #-}

instance MonadId m => MonadId (StateT s m) where
    freshInt = lift freshInt
    {-# INLINE freshInt #-}

instance MonadId m => MonadId (Strict.StateT s m) where
    freshInt = lift freshInt
    {-# INLINE freshInt #-}

instance (MonadId m, Monoid w) => MonadId (Strict.RWST r w s m) where
    freshInt = lift freshInt
    {-# INLINE freshInt #-}

instance (MonadId m) => MonadId (ContT r m) where
    freshInt = lift freshInt
    {-# INLINE freshInt #-}

instance (MonadId m) => MonadId (LoggingT m) where
    freshInt = lift freshInt
    {-# INLINE freshInt #-}

instance (MonadId m) => MonadId (TracerT c m) where
    freshInt = lift freshInt
    {-# INLINE freshInt #-}


{-
instance MonadLogger FreshIO where
    getLogger = FreshIO $ \ctx s -> return (logger ctx,s)
    {-# INLINE getLogger #-}
    updateSummary f = FreshIO $ \ctx s -> do
        modifyIORef' (summary ctx) f
        return ((), s)
    {-# INLINE updateSummary #-}
instance MonadLogger m => MonadLogger (ReaderT r m) where
    getLogger = lift getLogger
    {-# INLINE getLogger #-}
    updateSummary = lift . updateSummary
    {-# INLINE updateSummary #-}

instance MonadLogger m => MonadLogger (ParsecT s u m) where
    getLogger = lift getLogger
    {-# INLINE getLogger #-}
    updateSummary = lift . updateSummary
    {-# INLINE updateSummary #-}
instance (Monoid w, MonadLogger m) => MonadLogger (WriterT w m) where
    getLogger = lift getLogger
    {-# INLINE getLogger #-}
    updateSummary = lift . updateSummary
    {-# INLINE updateSummary #-}
instance MonadLogger m => MonadLogger (ExceptT e m) where
    getLogger = lift getLogger
    {-# INLINE getLogger #-}
    updateSummary = lift . updateSummary
    {-# INLINE updateSummary #-}
instance MonadLogger m => MonadLogger (StateT s m) where
    getLogger = lift getLogger
    {-# INLINE getLogger #-}
    updateSummary = lift . updateSummary
    {-# INLINE updateSummary #-}
instance MonadLogger m => MonadLogger (Strict.StateT s m) where
    getLogger = lift getLogger
    {-# INLINE getLogger #-}
    updateSummary = lift . updateSummary
    {-# INLINE updateSummary #-}
instance (MonadLogger m, Monoid w) => MonadLogger (Strict.RWST r w s m) where
    getLogger = lift getLogger
    {-# INLINE getLogger #-}
    updateSummary = lift . updateSummary
    {-# INLINE updateSummary #-}
instance MonadLogger m => MonadLogger (ContT r m) where
    getLogger = lift getLogger
    {-# INLINE getLogger #-}
    updateSummary = lift . updateSummary
    {-# INLINE updateSummary #-}
    -}

