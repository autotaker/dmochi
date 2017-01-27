module Language.DMoCHi.Common.Id(UniqueKey, FreshT, runFreshT, Fresh, runFresh, MonadId(..)) where

import Control.Monad.State
import qualified Control.Monad.State.Strict as Strict
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Except
import Data.Functor.Identity
import Text.Parsec(ParsecT)
import Text.PrettyPrint.HughesPJClass

newtype UniqueKey = UniqueKey Int
    deriving(Show,Eq,Ord)

instance Pretty UniqueKey where
    pPrint (UniqueKey i) = int i

class Monad m => MonadId m where
    freshId :: String -> m String
    freshId s = do
        i <- freshInt
        return $ s ++ "_" ++ show i
    freshInt :: m Int
    freshKey :: m UniqueKey
    freshKey = UniqueKey <$> freshInt

newtype FreshT m a = FreshT { unFreshT :: Strict.StateT Int m a }

type Fresh a = FreshT Identity a


runFreshT :: Monad m => FreshT m a -> m a
runFreshT m = Strict.evalStateT (unFreshT m) 0

runFresh :: Fresh a -> a
runFresh m = Strict.evalState (unFreshT m) 0

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

instance MonadFix m => MonadFix (FreshT m) where
    mfix f = FreshT (mfix (unFreshT .f))

instance Monad m => MonadId (FreshT m) where
    freshInt = FreshT $ do
        i <- get
        put $! (i+1)
        return i

instance MonadId m => MonadId (ReaderT r m) where
    freshInt = lift freshInt

instance MonadId m => MonadId (ParsecT s u m) where
    freshInt = lift freshInt

instance (Monoid w,MonadId m) => MonadId (WriterT w m) where
    freshInt = lift freshInt

instance MonadId m => MonadId (ExceptT e m) where
    freshInt = lift freshInt

instance MonadId m => MonadId (StateT s m) where
    freshInt = lift freshInt

instance MonadId m => MonadId (Strict.StateT s m) where
    freshInt = lift freshInt

