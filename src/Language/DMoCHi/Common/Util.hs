{-# LANGUAGE OverloadedStrings #-}
module Language.DMoCHi.Common.Util( rec
                                  , module Data.Function
                                  , module Data.Proxy
                                  , module Lens.Micro
                                  , FreshIO
                                  , measure
                                  , KnownSymbol
                                  , module Control.Monad.Logger
                                  , module Control.Monad.CTrace
                                  , measureWithLens) where

import Data.Function
import Data.Proxy
import GHC.TypeLits
import Data.Time
import Text.Printf
import Lens.Micro
import Control.Monad.Except
import Control.Monad.CTrace
import Control.Monad.Logger
import Language.DMoCHi.Common.Id
import Data.Text(pack)
import Data.PolyDict

rec :: a -> ((a -> b) -> a -> b) -> b
rec = flip fix

measure :: (MonadIO m, MonadLogger m
           , MonadTrace (Dict n) m
           , Assoc n k ~ NominalDiffTime
           , KnownSymbol k) => Key k -> m a -> m a
measure key doit = 
    measureWithLens (pack (symbolVal key)) (access' key 0) doit
{-# INLINE measure #-}    


measureWithLens :: (MonadIO m, MonadLogger m, MonadTrace c m) => LogSource -> Lens' c NominalDiffTime -> m a -> m a
measureWithLens header lens doit = do
    let f t = fromRational (toRational t) :: Double
    t_start <- liftIO $ getCurrentTime
    $(logInfoS) header "BEGIN"
    v <- doit
    t_end <- liftIO $ getCurrentTime
    let time = diffUTCTime t_end t_start
    $(logInfoS) header (pack $ printf "END %.5f sec" (f time))
    update (lens %~ (+time))
    return v

type FreshIO c = TracerT c (FreshT (LoggingT IO))

-- Orphan Instances
instance MonadLogger m => MonadLogger (TracerT c m) where
    monadLoggerLog l s v msg = lift $ monadLoggerLog l s v msg
    {-# INLINE monadLoggerLog #-}

instance MonadFix m => MonadFix (LoggingT m) where
    mfix f = LoggingT $ \s -> mfix $ \v -> runLoggingT (f v) s
    {-# INLINE mfix #-}


{-
measureError :: (MonadIO m, MonadError e m) => String -> m a -> m a
measureError header doit = do
    let f t = fromRational (toRational t) :: Double
    let showB s = "[" ++ show s ++ "]"
    t_start <- liftIO $ getCurrentTime
    liftIO $ printf "LOG %-32s %s BEGIN\n" (showB t_start) header
    let cont m = do
            t_end <- liftIO $ getCurrentTime
            let time = f $ diffUTCTime t_end t_start
            liftIO $ printf "LOG %-32s %s END: %.5f sec\n" (showB t_end) header time
            m
    v <- catchError doit (cont . throwError) 
    cont (return v)
    -}
