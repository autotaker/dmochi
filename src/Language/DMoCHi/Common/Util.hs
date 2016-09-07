module Language.DMoCHi.Common.Util( rec, 
                                    module Data.Function ) where

import Data.Function

rec :: a -> ((a -> b) -> a -> b) -> b
rec = flip fix

