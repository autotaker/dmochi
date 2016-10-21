module Language.DMoCHi.Common.Util( rec
                                  , module Data.Function
                                  , measure ) where

import Data.Function
import Data.Time
import Text.Printf
import Control.Monad.IO.Class

rec :: a -> ((a -> b) -> a -> b) -> b
rec = flip fix

measure :: MonadIO m => String -> m a -> m a
measure header doit = do
    let f t = fromRational (toRational t) :: Double
    let showB s = "[" ++ show s ++ "]"
    t_start <- liftIO $ getCurrentTime
    liftIO $ printf "LOG %-32s %s BEGIN\n" (showB t_start) header
    v <- doit
    t_end <- liftIO $ getCurrentTime
    let time = f $ diffUTCTime t_end t_start
    liftIO $ printf "LOG %-32s %s END: %.5f sec\n" (showB t_end) header time
    return v
