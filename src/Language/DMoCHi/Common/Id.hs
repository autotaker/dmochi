{-# Language FlexibleContexts, FlexibleInstances, UndecidableInstances #-}
module Language.DMoCHi.Common.Id(UniqueKey, FreshT, runFreshT, Fresh, FreshIO, runFresh, Id
                                , MonadId(..), freshId, reserved, reservedKey, maybeReserved, fromReserved
                                , getName
                                , refresh, identify) where

import Control.Monad.State
import qualified Control.Monad.State.Strict as Strict
import qualified Control.Monad.RWS.Strict as Strict
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Writer hiding((<>))
import Control.Monad.Except
import Control.Monad.Cont
import Data.Functor.Identity
import Text.Parsec(ParsecT)
import Text.PrettyPrint.HughesPJClass

newtype UniqueKey = UniqueKey { unUniqueKey :: Int }
    deriving(Eq,Ord)

instance Pretty UniqueKey where
    pPrint (UniqueKey i) = int i
instance Show UniqueKey where
    show (UniqueKey i) = show i

class Monad m => MonadId m where
    freshInt :: m Int
    freshInt = unUniqueKey <$> freshKey 
    freshKey :: m UniqueKey
    freshKey = UniqueKey <$> freshInt

newtype FreshT m a = FreshT { unFreshT :: Strict.StateT Int m a }
type FreshIO = FreshT IO

type Fresh a = FreshT Identity a

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

freshId :: MonadId m => String -> m String
freshId s = do
    i <- freshInt
    return $ s ++ "_" ++ show i

reserved :: a -> Id a
reserved x = Id (UniqueKey 0) x

reservedKey :: UniqueKey
reservedKey = UniqueKey 0

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

runFreshT :: Monad m => FreshT m a -> m a
runFreshT m = Strict.evalStateT (unFreshT m) 1

runFresh :: Fresh a -> a
runFresh m = Strict.evalState (unFreshT m) 1

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

instance (MonadId m, Monoid w) => MonadId (Strict.RWST r w s m) where
    freshInt = lift freshInt

instance (MonadId m) => MonadId (ContT r m) where
    freshInt = lift freshInt
