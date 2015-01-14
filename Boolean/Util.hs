module Boolean.Util where

import qualified Data.Set as S
import Control.Monad.Except

type Err = String

assert :: (MonadError e m) => Bool -> e -> m ()
assert b e = unless b $ throwError e

allDifferent :: (Ord a) => [a] -> Bool
allDifferent xs = length xs == S.size (S.fromList xs)

nub :: (Ord a) => [a] -> [a]
nub = S.toList . S.fromList
