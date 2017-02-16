{-# LANGUAGE ViewPatterns #-}
module Language.DMoCHi.ML.ElimUnreachable where

import Language.DMoCHi.ML.Syntax.PNormal

import qualified Data.Set as S
import qualified Data.Map as M

elimUnreachable :: Program -> Program
elimUnreachable prog = prog' where
    fs = functions prog
    e0 = mainTerm prog
    prog' = Program fs' e0
    fs' = filter reachable fs
    funMap = M.fromList $ map (\(f,key,xs,e) -> (f, (key,xs,e))) fs
    reachable (x,_,_,_) = S.member x reachableSet
    reachableSet = go S.empty (freeVariables S.empty e0)
    go vis (S.minView -> Just (f, queue)) 
        | S.notMember f vis = 
            let vis' = S.insert f vis 
                (_,xs,e) = funMap M.! f 
                fs = freeVariables (S.fromList xs) e 
            in go vis' (S.union queue fs)
        | otherwise = go vis queue
    go vis _ = vis
