module Language.DMoCHi.ML.HornClause.Solver where

import Language.DMoCHi.ML.HornClause.Syntax
import Language.DMoCHi.ML.HornClause.Parser(parseSolution, Predicate)
import qualified Language.DMoCHi.ML.HornClause.SMTLibParser as SMTLib
import Language.DMoCHi.Common.Util
import Control.Monad.Except
import Text.Parsec(ParseError)
import System.Process(callCommand)
import Text.Printf
import qualified Data.Map as M

data SolverError = 
    ParseError ParseError 
  | NoSolution 
  deriving(Show,Eq)

type Solver = HCCS -> Int -> ExceptT SolverError FreshLogging [Predicate]

rcamlSolver :: FilePath -> String -> String -> Solver
rcamlSolver cmdPath option baseName hccs ident = do
        let cmd = printf "%s %s -print-hccs-solution %s %s" cmdPath option file_ans file_hcs
            file_hcs = printf "%s_%d.hcs" baseName ident 
            file_ans = file_hcs ++ ".ans"
        liftIO $ writeFile file_hcs $ show hccs
        liftIO $ callCommand cmd
        liftIO (parseSolution file_ans) >>= \case
            Left err -> throwError (ParseError err)
            Right Nothing -> throwError NoSolution
            Right (Just r) -> return r

mergePredicate :: HCCS -> HCCS
mergePredicate (HCCS clause) = renamePVar rename (HCCS clause)
  where
  pnames = [ s | Clause { cHead = PVar s _} <- clause]
  basename s = takeWhile (/='[') s
  env = M.fromList [ (basename s, s) | s <- pnames ]
  rename s = env M.! (basename s)

hoiceSolver :: FilePath -> String -> Solver
hoiceSolver cmdPath baseName hccs ident = do
  let cmd = printf "%s %s > %s" cmdPath file_smt2 file_ans
      file_smt2 = printf "%s_%d.smt2" baseName ident
      file_ans = file_smt2 ++ ".ans"

  liftIO $ writeFile file_smt2 $ renderSMTLib2 (mergePredicate hccs)
  liftIO $ callCommand cmd
  lift (lift (SMTLib.parseSolution file_ans)) >>= \case
      Left err -> throwError (ParseError err)
      Right Nothing -> throwError NoSolution
      Right (Just r) -> do
        logPretty "HornClauseSolver" LevelDebug "Predicates" r
        return r
