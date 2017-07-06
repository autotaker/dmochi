module Language.DMoCHi.Common.Util( rec
                                  , module Data.Function
                                  , module Data.Proxy
                                  , module GHC.TypeLits
                                  , logKey
                                  , measure) where

import Data.Function
import Data.Proxy
import GHC.TypeLits
import Data.Time
import Text.Printf
import Control.Monad.Except
import Language.DMoCHi.Common.Id
import Language.Haskell.TH
import Language.DMoCHi.Common.PolyAssoc

rec :: a -> ((a -> b) -> a -> b) -> b
rec = flip fix

logKey :: String -> ExpQ
logKey s = sigE (conE 'Data.Proxy.Proxy) (appT (conT ''Data.Proxy.Proxy) (litT (strTyLit s)))

measure :: (MonadLogger m, EntryParam Logging k Double) => Proxy k -> m a -> m a
measure header doit = do
    let f t = fromRational (toRational t) :: Double
    t_start <- liftIO $ getCurrentTime
    logInfo (SomeSymbol header) "BEGIN"
    v <- doit
    t_end <- liftIO $ getCurrentTime
    let time = f $ diffUTCTime t_end t_start
    logInfo (SomeSymbol header) (printf "END %.5f sec" time)
    updateSummary (update header time (+time))
    return v

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
