import System.Environment
import System.IO
import Text.Printf
import ML.Syntax.UnTyped
import ML.Parser
import qualified Boolean.Syntax as B
import qualified Boolean.Sort   as B
import qualified Boolean.CPS    as B
import qualified Boolean.HORS   as B
import Boolean.Syntax.Typed as B(toUnTyped,tCheck)
import Boolean.PrettyPrint.HORS(pprintHORS,printHORS)
import qualified ML.Syntax.Typed as Typed
import ML.Convert
import ML.PrettyPrint.UnTyped
import ML.Alpha
import qualified ML.PrettyPrint.Typed as Typed
import qualified ML.TypeCheck as Typed
import ML.RandomPredicate(addRandomPredicatesDef)
import Boolean.Test 
import Control.Monad.Except
import Text.Parsec(ParseError)
import Data.Time
import Text.PrettyPrint
import Id

data MainError = NoInputSpecified
               | ParseFailed ParseError
               | AlphaFailed AlphaError
               | IllTyped Typed.TypeError 
               | BooleanError String

instance Show MainError where
    show NoInputSpecified = "NoInputSpecified"
    show (ParseFailed err) = "ParseFailed: " ++ show err
    show (AlphaFailed err) = "AlphaFailed: " ++ show err
    show (IllTyped err)    = "IllTyped: " ++ show err
    show (BooleanError s) = "Boolean: " ++ s

main :: IO ()
main = do
    m <- runFreshT $ runExceptT doit
    case m of
        Left err -> print err
        Right _ -> return ()


doit :: ExceptT MainError (FreshT IO) ()
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
    program  <- case parseRes of
        Left err -> throwError $ ParseFailed err
        Right p  -> return p
    liftIO $ putStrLn "Parsed Program"
    liftIO $ printProgram program
    t_parsing_end <- liftIO $ getCurrentTime

    alphaProgram <- withExceptT AlphaFailed $ alpha program
    liftIO $ putStrLn "Alpha Converted Program"
    liftIO $ printProgram alphaProgram

    -- add random predicates
    randomProgram <- addRandomPredicatesDef alphaProgram
    liftIO $ printProgram randomProgram
    let file_rand = path ++ ".rnd"
    liftIO $ writeFile file_rand $ render $ pprintProgram randomProgram


{-
    -- predicate abst
    t_predicate_abst_begin <- liftIO $ getCurrentTime
    boolProgram' <- convert typedProgram
    let boolProgram = B.toUnTyped boolProgram'
    case runExcept (B.tCheck boolProgram') of
        Left (s1,s2,str,ctx) -> liftIO $ do
            printf "type mismatch: %s. %s <> %s\n" str (show s1) (show s2)
            forM_ (zip [(0::Int)..] ctx) $ \(i,t) -> do
                printf "Context %d: %s\n" i (show t)
        Right _ -> return ()
    liftIO $ B.printProgram boolProgram
    t_predicate_abst_end <- liftIO $ getCurrentTime

    -- cps transformation
    liftIO $ printf "--CPS--\n"
    {-
    cps1 <- B.cps boolProgram'
    cps2 <- B.elimTupleP cps1
    liftIO $ print cps2
    case runExcept (B.tCheck1 cps2) of
        Left (s1,s2,str,ctx) -> liftIO $ do
            printf "type mismatch: %s. %s <> %s\n" str (show s1) (show s2)
            forM_ (zip [(0::Int)..] ctx) $ \(i,t) -> do
                printf "Context %d: %s\n" i (show t)
        Right _ -> return ()
        -}
    
    hors <- B.toHORS boolProgram'
    let file_hors = path ++ ".hrs"
    liftIO $ writeFile file_hors $ render $ pprintHORS hors
--    liftIO $ printHORS hors
--    liftIO $ B.printProgram cpsProgram

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

-}


