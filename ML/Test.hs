import System.Environment
import System.IO
import Text.Printf
import ML.Syntax.UnTyped
import ML.Parser
import qualified Boolean.Syntax as B
import qualified ML.Syntax.Typed as Typed
import ML.Convert
import ML.PrettyPrint.UnTyped
import qualified ML.PrettyPrint.Typed as Typed
import Boolean.Test 
import Control.Monad.Except
import Text.Parsec(ParseError)

data MainError = NoInputSpecified
               | ParseFailed ParseError
               | IllTyped Typed.TypeError 
               | BooleanError String

instance Show MainError where
    show NoInputSpecified = "NoInputSpecified"
    show (ParseFailed err) = "ParseFailed: " ++ show err
    show (IllTyped err)    = "IllTyped: " ++ show err
    show (BooleanError s) = "Boolean: " ++ s

main :: IO ()
main = do
    m <- runExceptT doit
    case m of
        Left err -> print err
        Right _ -> return ()

doit :: ExceptT MainError IO ()
doit = do
    -- check args
    pname <- liftIO $ getProgName
    args <- liftIO $ getArgs
    when (length args == 0) $ throwError NoInputSpecified
    
    -- parsing
    let path = head args
    parseRes <- liftIO $ parseProgramFromFile path
    program <- case parseRes of
        Left err -> throwError $ ParseFailed err
        Right p  -> return p
    liftIO $ printProgram program

    -- type checking
    typedProgram <- withExceptT IllTyped $ Typed.fromUnTyped program
    liftIO $ Typed.printProgram typedProgram

    -- predicate abst
    boolProgram <- liftIO $ convert typedProgram
    liftIO $ B.printProgram boolProgram

    -- model checking
    r <- withExceptT BooleanError $ test boolProgram
    liftIO $ print r

