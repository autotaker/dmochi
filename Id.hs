module Id where

import Control.Monad.State
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Except

class Monad m => MonadId m where
    freshId :: String -> m String

newtype FreshT m a = FreshT { unFreshT :: StateT Int m a }

runFreshT :: Monad m => FreshT m a -> m a
runFreshT m = evalStateT (unFreshT m) 0

instance Monad m => Monad (FreshT m) where
    return = FreshT . return
    f >>= m = FreshT $ unFreshT f >>= unFreshT . m

instance Functor m => Functor (FreshT m) where
    fmap f = FreshT . fmap f . unFreshT

instance (Functor m, Monad m) => Applicative (FreshT m) where
    pure = return
    (<*>) = ap

instance (Functor m, MonadPlus m) => Alternative (FreshT m) where
    empty = mzero
    (<|>) = mplus

instance (MonadPlus m) => MonadPlus (FreshT m) where
    mzero = FreshT mzero
    mplus m n = FreshT $ unFreshT m `mplus` unFreshT n

instance MonadTrans FreshT where
    lift = FreshT . lift

instance MonadIO m => MonadIO (FreshT m) where
    liftIO = lift . liftIO

instance Monad m => MonadId (FreshT m) where
    freshId x = FreshT $ do
        i <- get
        put (i+1)
        return $ x ++ "_" ++ show i

instance MonadId m => MonadId (ReaderT r m) where
    freshId = lift . freshId

instance MonadId m => MonadId (ExceptT e m) where
    freshId = lift . freshId

