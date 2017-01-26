module Language.DMoCHi.Common.Util( rec
                                  , module Data.Function
                                  , measure ) where

import Data.Function
import Data.Time
import Text.Printf
import Control.Monad.Except

rec :: a -> ((a -> b) -> a -> b) -> b
rec = flip fix

measure :: (MonadIO m, MonadError e m) => String -> m a -> m a
measure header doit = do
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
