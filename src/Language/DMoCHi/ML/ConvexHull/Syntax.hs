module Language.DMoCHi.ML.ConvexHull.Syntax where

import Language.DMoCHi.ML.Syntax.PNormal
import Data.AttoLisp
import Data.Text(Text, unpack)
import qualified Data.Map as M
import Control.Monad
--import Debug.Trace

type DNFFormula = [[Atom]]

data Query = Query [TId] DNFFormula
newtype Answer = Answer [Atom]

type LinearExp = ([(TId, Integer)], Integer)

convLinearExp :: Text -> LinearExp -> Lisp
convLinearExp op (l, v) = List [Symbol op, l', toLisp v]
    where
    l' = List $ map (\(x, c) -> List [Symbol "*", toLisp c, toLisp (show (name x))]) l

addLinear :: LinearExp -> LinearExp -> LinearExp
addLinear (xs,c1) (ys, c2) = (xs ++ ys, c1 + c2)

subLinear :: LinearExp -> LinearExp -> LinearExp
subLinear (xs,c1) (ys, c2) = (xs ++ map (\(y,v) -> (y, -v)) ys, c1 - c2)

scalarLinear :: Integer -> LinearExp -> LinearExp
scalarLinear c (xs, c1) = (map (\(x, v) -> (x, c * v)) xs, c * c1)

convLinear :: Atom -> [LinearExp]
convLinear a@(Atom l arg _) =
    case (l, arg) of
        (SLiteral, CInt x) -> pure ([], x)
        (SLiteral, _) -> error $ "convLinear: type error:" ++ show a
        (SVar, x) -> pure ([(x, 1)], 0)
        (SBinary, BinArg SAdd a1 a2) ->
            addLinear <$> convLinear a1 <*> convLinear a2
        (SBinary, BinArg SSub a1 a2) ->
            subLinear <$> convLinear a1 <*> convLinear a2
        (SBinary, BinArg SDiv _ _) -> []
        (SBinary, BinArg SMul a1 a2) -> do
            l1 <- convLinear a1
            l2 <- convLinear a2
            case (l1, l2) of
                (([],v), _) -> pure $ scalarLinear v l2
                (_, ([],v)) -> pure $ scalarLinear v l1
                _ -> []
        (SBinary, BinArg _ _ _) -> error $ "convLinear: type error:" ++ show a
        (SUnary, UniArg SNeg a1) -> 
           subLinear ([],0) <$> convLinear a1 
        (SUnary, UniArg _ _) -> error $ "convLinear: type error:" ++ show a

convFormula :: Atom -> [Lisp]
convFormula a@(Atom l arg _) =
    case (l, arg) of
        (SLiteral, _) -> []
        (SVar, _) -> []
        (SBinary, BinArg op a1 a2) -> do
            l1 <- convLinear a1
            l2 <- convLinear a2
            case op of
                SEq -> return $ convLinearExp "=" (subLinear l1 l2)
                SLt -> return $ convLinearExp ">" (subLinear l2 l1)
                SLte -> return $ convLinearExp ">=" (subLinear l2 l1)
                _ -> error $ "convFormula: type error:" ++ show a
        (SUnary, UniArg SNot (Atom l1 arg1 _)) -> 
            case (l1, arg1) of
                (SBinary, BinArg op a1 a2) -> do
                    l1 <- convLinear a1
                    l2 <- convLinear a2
                    case op of
                        SEq -> []
                        SLt -> return $ convLinearExp ">=" (subLinear l1 l2)
                        SLte -> return $ convLinearExp ">" (subLinear l1 l2)
                        _ -> error $ "convFormula: type error:" ++ show a
                (SLiteral, _) -> []
                (SVar, _) -> []
                (SUnary, _) -> []
        (SUnary, UniArg _ _) -> error $ "convFormula: type error:" ++ show a

instance ToLisp Query where
    toLisp (Query vs dnf) = List (Symbol "q" : toLisp vs' : dnfLisp)
        where
        vs' = [ toLisp (show (name x)) | x <- vs, getType x == TInt ]
        dnfLisp = map (\cls -> List $ cls >>= convFormula) dnf



parseAnswer :: M.Map String TId -> Lisp -> Parser Answer
parseAnswer env (List (Symbol "a" : poly)) = Answer <$> parsePoly env poly
parseAnswer _ _ = mzero

fromLinear :: LinearExp -> Atom
fromLinear (xs,c) = 
    let acc0 = mkLiteral (CInt c) in
    foldl (\acc (x,v) -> 
        let vx = mkVar x
            vc = mkLiteral (CInt (abs v)) in
        if v == 0 then acc
        else if v == 1  then mkBin SAdd acc vx
        else if v == -1 then mkBin SSub acc vx
        else if v <  0  then mkBin SSub acc (mkBin SMul vc vx)
        else mkBin SAdd acc (mkBin SMul vc vx)) acc0 xs

parseVar :: M.Map String TId -> Lisp -> Parser TId
parseVar env (Symbol x) = pure $ env M.! (unpack x)
parseVar _ _ = mzero

parseLinear :: M.Map String TId -> Lisp -> Parser Atom
parseLinear env (List [Symbol op, List l, c]) = do
    lin <- (,) <$> mapM f l <*> parseLisp c
    case op of
        "=" -> pure $ mkBin SEq (fromLinear lin) (mkLiteral (CInt 0))
        ">" -> pure $ mkBin SLt (mkLiteral (CInt 0)) (fromLinear lin)
        ">=" -> pure $ mkBin SLte (mkLiteral (CInt 0)) (fromLinear lin)
        _ -> mzero
    where f (List [Symbol "*", c, x]) = 
            (,) <$> parseVar env x <*> parseLisp c
          f _ = mzero
parseLinear _ _ = mzero

parsePoly :: M.Map String TId -> [Lisp] -> Parser [Atom]
parsePoly env poly = forM poly (parseLinear env)

