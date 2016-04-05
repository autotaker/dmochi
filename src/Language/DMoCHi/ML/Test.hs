module Language.DMoCHi.ML.Test(run) where
import System.Environment
import System.IO
import System.Process(callCommand)
import Text.Printf
import Language.DMoCHi.ML.Syntax.UnTyped
import Language.DMoCHi.ML.Parser
import qualified Language.DMoCHi.Boolean.Syntax as B
import qualified Language.DMoCHi.Boolean.Sort   as B
import qualified Language.DMoCHi.Boolean.CPS    as B
import qualified Language.DMoCHi.Boolean.HORS   as B
import Language.DMoCHi.Boolean.Syntax.Typed as B(toUnTyped,tCheck)
import Language.DMoCHi.Boolean.PrettyPrint.HORS(pprintHORS,printHORS)
import Language.DMoCHi.Boolean.PrettyPrint.Typed as B(pprintProgram)
import qualified Language.DMoCHi.ML.Syntax.Typed as Typed
import Language.DMoCHi.ML.Convert
import Language.DMoCHi.ML.PrettyPrint.UnTyped
import Language.DMoCHi.ML.Alpha
import qualified Language.DMoCHi.ML.PrettyPrint.Typed as Typed
import qualified Language.DMoCHi.ML.TypeCheck as Typed
import Language.DMoCHi.Boolean.Test 
import Control.Monad.Except
import Text.Parsec(ParseError)
import Data.Time
import Text.PrettyPrint
import Language.DMoCHi.Common.Id
import Language.DMoCHi.ML.Refine
import qualified Language.DMoCHi.ML.HornClause as Horn
import Language.DMoCHi.ML.HornClauseParser(parseSolution)

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

hccsSolver :: FilePath
hccsSolver = "/Users/autotaker/Documents/cloud/Enshu3/Kobayashi/impl/cvb/hccs/main"

run :: IO ()
run = do
    hSetBuffering stdout NoBuffering
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

    -- type checking
    t_type_checking_begin <- liftIO $ getCurrentTime
    typedProgram <- withExceptT IllTyped $ Typed.fromUnTyped alphaProgram
    liftIO $ Typed.printProgram typedProgram
    t_type_checking_end <- liftIO $ getCurrentTime

    let cegar prog = do
            -- predicate abst
            t_predicate_abst_begin <- liftIO $ getCurrentTime
            boolProgram' <- convert prog
            let boolProgram = B.toUnTyped boolProgram'
            case runExcept (B.tCheck boolProgram') of
                Left (s1,s2,str,ctx) -> liftIO $ do
                    printf "type mismatch: %s. %s <> %s\n" str (show s1) (show s2)
                    forM_ (zip [(0::Int)..] ctx) $ \(i,t) -> do
                        printf "Context %d: %s\n" i (show t)
                Right _ -> return ()
            let file_boolean = path ++ ".bool"
            liftIO $ writeFile file_boolean $ (++"\n") $ render $ B.pprintProgram boolProgram'
            liftIO $ B.printProgram boolProgram
            t_predicate_abst_end <- liftIO $ getCurrentTime

        {-
            -- cps transformation
            liftIO $ printf "--CPS--\n"
            hors <- B.toHORS boolProgram'
            let file_hors = path ++ ".hrs"
            liftIO $ writeFile file_hors $ (++"\n") $ render $ pprintHORS hors
        --    liftIO $ printHORS hors
        --    liftIO $ B.printProgram cpsProgram
        --    -}

            -- model checking
            t_model_checking_begin <- liftIO $ getCurrentTime
            r <- withExceptT BooleanError $ test file_boolean boolProgram
            liftIO $ print r
            t_model_checking_end <- liftIO $ getCurrentTime

            -- refinement
            case r of
                Just trace -> do
                    (clauses, env) <- refineCGen prog trace
                    let file_hcs = path ++ ".hcs"
                    liftIO $ putStr $ show (Horn.HCCS clauses)
                    liftIO $ writeFile file_hcs $ show (Horn.HCCS clauses)
                    liftIO $ callCommand (hccsSolver ++ " " ++ file_hcs)
                    parseRes <- liftIO $ parseSolution (file_hcs ++ ".ans")
                    solution  <- case parseRes of
                        Left err -> throwError $ ParseFailed err
                        Right p  -> return p
                    let refinedProgram = refine prog env solution
                    liftIO $ Typed.printProgram refinedProgram
                    cegar refinedProgram
                    
                    return ()
                _ -> return ()
    cegar typedProgram
                {-
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


