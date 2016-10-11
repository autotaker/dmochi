module Language.DMoCHi.ML.Test(run) where
import System.Environment
import System.IO
import System.Process(callCommand)
import System.Exit
import Text.Printf
import qualified Language.DMoCHi.Boolean.Syntax as B
import qualified Language.DMoCHi.Boolean.Sort   as B
import qualified Language.DMoCHi.Boolean.HORS   as B
import Language.DMoCHi.Boolean.Syntax.Typed as B(toUnTyped,tCheck)
import Language.DMoCHi.Boolean.PrettyPrint.HORS(pprintHORS,printHORS)
import Language.DMoCHi.Boolean.PrettyPrint.Typed as B(pprintProgram)
import Language.DMoCHi.ML.Syntax.UnTyped
import Language.DMoCHi.ML.Parser
import qualified Language.DMoCHi.ML.Syntax.Typed as Typed
import Language.DMoCHi.ML.PrettyPrint.UnTyped
import Language.DMoCHi.ML.Alpha
import qualified Language.DMoCHi.ML.CallNormalize as CallNormalize
import qualified Language.DMoCHi.ML.Inline  as Inline
import qualified Language.DMoCHi.ML.ElimUnreachable  as Unreachable
import qualified Language.DMoCHi.ML.PrettyPrint.Typed as Typed
import qualified Language.DMoCHi.ML.TypeCheck as Typed
import qualified Language.DMoCHi.ML.Syntax.PNormal as PNormal
import qualified Language.DMoCHi.ML.PrettyPrint.PNormal as PNormal
import qualified Language.DMoCHi.ML.PredicateAbstraction as PAbst
import qualified Language.DMoCHi.ML.Refine as Refine
import Language.DMoCHi.Boolean.Test 
import Control.Monad.Except
import Text.Parsec(ParseError)
import Data.Time
import Text.PrettyPrint
import Language.DMoCHi.Common.Id

import qualified Language.DMoCHi.ML.HornClause as Horn
import qualified Language.DMoCHi.ML.HornClauseParser as Horn
import Paths_dmochi

data MainError = NoInputSpecified
               | ParseFailed ParseError
               | AlphaFailed AlphaError
               | IllTyped Typed.TypeError 
               | Debugging
               | BooleanError String

instance Show MainError where
    show NoInputSpecified = "NoInputSpecified"
    show (ParseFailed err) = "ParseFailed: " ++ show err
    show (AlphaFailed err) = "AlphaFailed: " ++ show err
    show (IllTyped err)    = "IllTyped: " ++ show err
    show (BooleanError s) = "Boolean: " ++ s
    show Debugging = "Debugging"

getHCCSSolver :: IO FilePath
getHCCSSolver = Paths_dmochi.getDataFileName "hcsolver"


run :: IO ()
run = do
    hSetBuffering stdout NoBuffering
    m <- runFreshT $ runExceptT doit
    case m of
        Left err -> print err >> exitFailure
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

    hccsSolver <- liftIO getHCCSSolver
    
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

    -- alpha conversion
    alphaProgram <- withExceptT AlphaFailed $ alpha program
    liftIO $ putStrLn "Alpha Converted Program"
    liftIO $ printProgram alphaProgram

    -- Call normalizing
    alphaNormProgram <- CallNormalize.normalize alphaProgram
    liftIO $ putStrLn "Call Normalized Program"
    liftIO $ printProgram alphaNormProgram

    -- type checking
    liftIO $ putStrLn "Typed Program"
    t_type_checking_begin <- liftIO $ getCurrentTime
    _typedProgram <- withExceptT IllTyped $ Typed.fromUnTyped alphaNormProgram
    liftIO $ Typed.printProgram _typedProgram
    t_type_checking_end <- liftIO $ getCurrentTime

    -- inlining
    liftIO $ putStrLn "Inlined Program"
    typedProgram' <- Inline.inline 1000 _typedProgram
    liftIO $ Typed.printProgram typedProgram'

    -- unreachable code elimination
    liftIO $ putStrLn "Unreachable Code Elimination"
    typedProgram <- return $ Unreachable.elimUnreachable typedProgram'
    liftIO $ Typed.printProgram typedProgram

    -- normalizing
    liftIO $ putStrLn "Normalizing"
    normalizedProgram<- PNormal.normalize typedProgram
    liftIO $ PNormal.printProgram normalizedProgram


    (typeMap0, fvMap) <- PAbst.initTypeMap normalizedProgram
    let lim = 20 :: Int
    let cegar _ k hcs | k >= lim = return ()
        cegar typeMap k hcs = measure (printf "CEGAR-%d" k) $ do
            liftIO $ putStrLn "Predicate Abstracion"
            boolProgram' <- measure "Predicate Abstraction" $ PAbst.abstProg typeMap normalizedProgram
            let file_boolean = printf "%s_%d.bool" path k
            liftIO $ writeFile file_boolean $ (++"\n") $ render $ B.pprintProgram boolProgram'
            liftIO $ putStrLn "Converted program"
            liftIO $ putStrLn $ render $ B.pprintProgram boolProgram'
            case runExcept (B.tCheck boolProgram') of
                Left (s1,s2,str,ctx) -> do
                    liftIO $ do
                        printf "type mismatch: %s. %s <> %s\n" str (show s1) (show s2)
                        forM_ (zip [(0::Int)..] ctx) $ \(i,t) -> do
                            printf "Context %d: %s\n" i (show t)
                    throwError $ BooleanError "Abstracted Program is ill-typed"
                Right _ -> return ()
            let boolProgram = B.toUnTyped boolProgram'
            -- liftIO $ B.printProgram boolProgram

            
            r <- measure "Model Checking" $ withExceptT BooleanError $ testTyped file_boolean boolProgram'
            case r of
                Just trace -> do
                    refine <- Refine.refineCGen normalizedProgram trace
                    case refine of
                        Nothing -> liftIO $ putStrLn "UnSafe!!"
                        Just (clauses, (rtyAssoc,rpostAssoc)) -> do
                            let file_hcs = printf "%s_%d.hcs" path k
                            liftIO $ putStr $ show (Horn.HCCS clauses)
                            liftIO $ writeFile file_hcs $ show (Horn.HCCS clauses)
                            liftIO $ callCommand (hccsSolver ++ " " ++ file_hcs)
                            parseRes <- liftIO $ Horn.parseSolution (file_hcs ++ ".ans")
                            --liftIO $ print parseRes
                            solution  <- case parseRes of
                                Left err -> throwError $ ParseFailed err
                                Right p  -> return p
                            let typeMap' = Refine.refine fvMap rtyAssoc rpostAssoc solution typeMap
                            cegar typeMap' (k+1) (clauses ++ hcs)
                Nothing -> do
                    liftIO $ putStrLn "Safe!!"
                    return ()

            return ()
    cegar typeMap0 0 []

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


