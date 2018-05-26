{-# LANGUAGE TypeApplications #-}
module Language.DMoCHi.ML.ConvexHull.Solver where
import System.Process
import Data.AttoLisp
import Data.Attoparsec.ByteString
import qualified Data.ByteString.Lazy as LB
import qualified Data.ByteString as SB
import qualified Data.Map as M
import Language.DMoCHi.ML.ConvexHull.Syntax
import Language.DMoCHi.Common.Util
import Language.DMoCHi.ML.Syntax.Type(name)
import Control.Monad.Except
import System.IO(hFlush)
import Data.IORef

type Solver = Query -> ExceptT SolverError FreshLogging Answer

data SolverError = ParseError String
                 | ConversionError Lisp String
                 deriving(Show)

convexHullSolver :: FilePath -> IO (Solver, IO ())
convexHullSolver cmdPath = do
    let process = (proc cmdPath ["-debug"]){ std_out = CreatePipe, std_in = CreatePipe }
    (Just hin, Just hout, _, ph) <- createProcess process
    remain <- newIORef @SB.ByteString ""
    let query q@(Query xs _) = do
            liftIO $ LB.hPutStr hin $ encode q
            liftIO $ hFlush hin
            let env = M.fromList [ (show (name x), x) | x <- xs ]
            result <- liftIO $ readIORef remain >>= parseWith (SB.hGetSome hout 4096) lisp
            case result of
                Done rest dat -> do
                    liftIO $ writeIORef remain rest
                    let res = parseEither (parseAnswer env) dat
                    case res of
                        Left err -> throwError $ ConversionError dat err
                        Right answer -> return answer
                Fail _ _ _ -> throwError $ ParseError (show result)
                _ -> error "unexpected"
        exit = terminateProcess ph
    return (query, exit)
