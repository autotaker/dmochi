{-# LANGUAGE BangPatterns #-}
module Language.DMoCHi.ML.InteractiveCEGen where

import           Control.Monad.Fix
import           Control.Monad.IO.Class
import           System.Process
import           Text.Printf

import           Language.DMoCHi.ML.SymbolicExec
import           Language.DMoCHi.ML.Syntax.PNormal as ML
import           Language.DMoCHi.Common.Id
import qualified Language.DMoCHi.ML.SMT as SMT

imgPath :: FilePath -> FilePath
imgPath path = path ++ ".png"

dotCommand :: FilePath -> String
dotCommand path = printf "dot -Tpng %s -o %s" path (imgPath path)

viewerCommand :: FilePath -> String
viewerCommand path = printf "gnome-open %s" (imgPath path)

convertTrace :: Trace -> String -> Trace
convertTrace !trace [] = trace
convertTrace !trace (op:ops) = case op of
    'L' -> convertTrace (trace ++ [True]) ops
    'R' -> convertTrace (trace ++ [False]) ops
    'U' -> case trace of
        [] -> trace
        _ -> convertTrace (init trace) ops
    'C' -> convertTrace [] ops
    _ -> convertTrace trace ops

interactiveCEGen :: (MonadIO m, MonadId m, MonadFix m) => ML.Program -> FilePath -> Trace -> m (Trace, Maybe Bool)
interactiveCEGen prog path = loop
    where
    loop trace = do
        (_,log,tree) <- symbolicExec prog trace
        _ <- liftIO $ SMT.sat (map fromSValue (logCnstr log))
        liftIO $ writeFile path (renderCompTree tree)
        liftIO $ callCommand $ dotCommand path
        liftIO $ callCommand $ viewerCommand path
        s <- liftIO getLine
        case s of
            "OK" ->
                return (trace, Nothing)
            "FOOL" ->
                return (trace, Just True)
            "NONFOOL" ->
                return (trace, Just False)
            _ -> do
                let trace' = convertTrace trace s
                loop trace'





