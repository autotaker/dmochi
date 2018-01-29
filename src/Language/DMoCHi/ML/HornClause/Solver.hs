module Language.DMoCHi.ML.HornClause.Solver where

import Language.DMoCHi.ML.HornClause.Syntax
import Language.DMoCHi.ML.HornClause.Parser(parseSolution, Predicate)
import Language.DMoCHi.Common.Util
import Control.Monad.Except
import Text.Parsec(ParseError)
import System.Process(callCommand)
import Text.Printf

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

