{-# LANGUAGE ViewPatterns #-}
module Language.DMoCHi.ML.ElimUnreachable where

import Control.Monad
import Language.DMoCHi.Common.Util
import Language.DMoCHi.Common.Id
import Language.DMoCHi.ML.Syntax.Typed

import qualified Data.Set as S
import qualified Data.Map as M
import Debug.Trace

elimUnreachable :: Program -> Program
elimUnreachable prog = prog' where
    fs = functions prog
    e0 = mainTerm prog
    prog' = Program fs' e0
    fs' = filter reachable fs
    funMap = M.fromList fs
    reachable (x,_) = S.member x reachableSet
    reachableSet = go S.empty (freeVariables S.empty e0)
    go vis (S.minView -> Just (f, queue)) 
        | S.notMember f vis = 
            let vis' = S.insert f vis 
                fdef = funMap M.! f
                fs = freeVariables (S.singleton (arg fdef)) (body fdef)
            in go vis' (S.union queue fs)
        | otherwise = go vis queue
    go vis _ = vis
