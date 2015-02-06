import System.Environment
import System.IO
import Text.Printf
import ML.Syntax.UnTyped
import ML.Parser
import qualified Boolean.Syntax as B
import qualified Boolean.Sort   as B
import qualified ML.Syntax.Typed as Typed
import ML.Convert
import ML.PrettyPrint.UnTyped
import qualified ML.PrettyPrint.Typed as Typed
import qualified ML.TypeCheck as Typed
import Boolean.Test 
import Control.Monad.Except
import Text.Parsec(ParseError)
import Data.Time


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
    t_begin <- liftIO $ getCurrentTime
    -- check args
    t_input_begin <- liftIO $ getCurrentTime
    pname <- liftIO $ getProgName
    args <- liftIO $ getArgs
    when (length args == 0) $ throwError NoInputSpecified
    t_input_end <- liftIO $ getCurrentTime
    
    -- parsing
    t_parsing_begin <- liftIO $ getCurrentTime
    let path = head args
    parseRes <- liftIO $ parseProgramFromFile path
    program <- case parseRes of
        Left err -> throwError $ ParseFailed err
        Right p  -> return p
    liftIO $ printProgram program
    t_parsing_end <- liftIO $ getCurrentTime

    -- type checking
    t_type_checking_begin <- liftIO $ getCurrentTime
    typedProgram <- withExceptT IllTyped $ Typed.fromUnTyped program
    liftIO $ Typed.printProgram typedProgram
    liftIO $ printf "SIZE = %d\n" $ Typed.size typedProgram
    t_type_checking_end <- liftIO $ getCurrentTime

    -- predicate abst
    t_predicate_abst_begin <- liftIO $ getCurrentTime
    boolProgram <- liftIO $ convert typedProgram
    liftIO $ B.printProgram boolProgram
    t_predicate_abst_end <- liftIO $ getCurrentTime

    -- model checking
    t_model_checking_begin <- liftIO $ getCurrentTime
    r <- withExceptT BooleanError $ test boolProgram
    liftIO $ print r
    t_model_checking_end <- liftIO $ getCurrentTime

    let t_input          = f $ diffUTCTime t_input_end t_input_begin
        t_parsing        = f $ diffUTCTime t_parsing_end t_parsing_begin
        t_type_checking  = f $ diffUTCTime t_type_checking_end t_type_checking_begin
        t_predicate_abst = f $ diffUTCTime t_predicate_abst_end t_predicate_abst_begin
        t_model_checking = f $ diffUTCTime t_model_checking_end t_model_checking_begin
        f t = fromRational (toRational t) :: Double
        s_typed_program = Typed.size typedProgram
        types = Typed.gatherPTypes typedProgram
        o_typed_program = maximum $ 0:map (Typed.orderT . Typed.getType) types
        p_typed_program = maximum $ 0:map Typed.sizeP types
        s_boolean_program = B.size boolProgram
    liftIO $ do
        printf "-- statistics --\n"
        printf "time stamp: %s\n" $ show t_begin
        printf "\tInput Program Size    : %5d\n" s_typed_program
        printf "\tInput Program Order   : %5d\n" o_typed_program
        printf "\tMax Number of Predicates : %5d\n" p_typed_program
        printf "\tBoolean Program Size  : %5d\n" s_boolean_program
        printf "\tHandle Input Args : %7.3f sec\n" t_input
        printf "\tParsing           : %7.3f sec\n" t_parsing
        printf "\tType Checking     : %7.3f sec\n" t_type_checking
        printf "\tPredicate Abst    : %7.3f sec\n" t_predicate_abst
        printf "\tModel Checking    : %7.3f sec\n" t_model_checking



