module Language.DMoCHi.ML.Test(run) where
import System.Environment
import System.IO
import System.Process(callCommand)
import System.Exit
import System.Console.GetOpt
import Control.Monad.Except
import Data.Monoid
import Data.Maybe(fromMaybe)
import Text.Parsec(ParseError)
import Text.PrettyPrint hiding((<>))
import Text.Printf

import qualified Language.DMoCHi.Boolean.Syntax as B
import qualified Language.DMoCHi.Boolean.Sort   as B
import qualified Language.DMoCHi.Boolean.HORS   as B
import           Language.DMoCHi.Boolean.Syntax.Typed as B(toUnTyped,tCheck)
import           Language.DMoCHi.Boolean.PrettyPrint.HORS(pprintHORS,printHORS)
import           Language.DMoCHi.Boolean.PrettyPrint.Typed as B(pprintProgram)
import           Language.DMoCHi.ML.Syntax.UnTyped
import           Language.DMoCHi.ML.Parser
import qualified Language.DMoCHi.ML.Syntax.Typed as Typed
import           Language.DMoCHi.ML.PrettyPrint.UnTyped
import           Language.DMoCHi.ML.Alpha
import qualified Language.DMoCHi.ML.CallNormalize as CallNormalize
import qualified Language.DMoCHi.ML.Inline  as Inline
import qualified Language.DMoCHi.ML.ElimUnreachable  as Unreachable
import qualified Language.DMoCHi.ML.PrettyPrint.Typed as Typed
import qualified Language.DMoCHi.ML.TypeCheck as Typed
import qualified Language.DMoCHi.ML.Syntax.PNormal as PNormal
import qualified Language.DMoCHi.ML.PrettyPrint.PNormal as PNormal
import qualified Language.DMoCHi.ML.PredicateAbstraction as PAbst
import qualified Language.DMoCHi.ML.ElimCast as PAbst
import qualified Language.DMoCHi.ML.Saturate as Saturate
import qualified Language.DMoCHi.ML.Syntax.PType as PAbst
import qualified Language.DMoCHi.ML.Refine as Refine
import qualified Language.DMoCHi.ML.InteractiveCEGen as Refine
import           Language.DMoCHi.Boolean.Test 
import           Language.DMoCHi.Common.Id
import           Language.DMoCHi.Common.Util

import qualified Language.DMoCHi.ML.HornClause as Horn
import qualified Language.DMoCHi.ML.HornClauseParser as Horn
import           Paths_dmochi

data MainError = NoInputSpecified
               | ParseFailed ParseError
               | RefinementFailed ParseError
               | AlphaFailed AlphaError
               | IllTyped Typed.TypeError 
               | Debugging
               | BooleanError String

instance Show MainError where
    show NoInputSpecified = "NoInputSpecified"
    show (ParseFailed err) = "ParseFailed: " ++ show err
    show (AlphaFailed err) = "AlphaFailed: " ++ show err
    show (IllTyped err)    = "IllTyped: " ++ show err
    show (RefinementFailed err)    = "RefinementFailed: " ++ show err
    show (BooleanError s) = "Boolean: " ++ s
    show Debugging = "Debugging"

data Flag = Help 
          | HCCS HCCSSolver 
          | CEGARLimit Int 
          | AccErrTraces 
          | ContextSensitive 
          | Interactive
          | FoolTraces Int
          deriving Eq
data HCCSSolver = IT | GCH  deriving Eq

data Config = Config { targetProgram :: FilePath
                     , hornOption :: String
                     , cegarLimit :: Int
                     , accErrTraces :: Bool
                     , contextSensitive :: Bool
                     , foolTraces :: Bool
                     , foolThreshold :: Int
                     , interactive :: Bool }


getHCCSSolver :: IO FilePath
--getHCCSSolver = Paths_dmochi.getDataFileName "hcsolver"
getHCCSSolver = return "rcaml.opt"

defaultConfig :: FilePath -> Config
defaultConfig path = Config { targetProgram = path
                            , hornOption = ""
                            , cegarLimit = 20
                            , accErrTraces = False
                            , contextSensitive = False
                            , foolTraces = False
                            , foolThreshold = 1
                            , interactive = False }

run :: IO ()
run = do
    hSetBuffering stdout NoBuffering
    m <- measure "Total" $ runFreshT $ runExceptT doit
    case m of
        Left err -> putStr "Error: " >> print err >> exitFailure
        Right _ -> return ()
        
options :: [ OptDescr Flag ]
options = [ Option ['h'] ["help"] (NoArg Help) "Show this help message"
          , Option [] ["hccs"] (ReqArg parseSolver "it|gch") "Set hccs solver"
          , Option ['l'] ["limit"] (ReqArg (CEGARLimit . read) "N") "Set CEGAR round limit (default = 20)"
          , Option [] ["acc-traces"] (NoArg AccErrTraces) "Accumrate error traces"
          , Option [] ["context-sensitive"] (NoArg ContextSensitive) 
                   "Enable context sensitive predicate discovery, this also enables --acc-traces flag"
          , Option [] ["fool-traces"] (OptArg (FoolTraces . fromMaybe 1 . fmap read) "N")  "Distinguish fool error traces in refinement phase, and set threshold (default = 1)"
          , Option [] ["interactive"] (NoArg Interactive) "interactive counterexample generation" ]
    where
    parseSolver "it" = HCCS IT
    parseSolver "gch" = HCCS GCH
    parseSolver s = error $ "Not Supported Parameter for --hccs: " ++ s

parseArgs :: IO Config
parseArgs = doit
  where
  parse argv = getOpt RequireOrder options argv
  header = "Usage: dmochi [OPTION..] target"
  dump = hPutStrLn stderr
  info = usageInfo header options
  die errs = dump (concat errs ++ info) >> exitFailure
  help = dump info >> exitSuccess
  doit = do
    pname <- getProgName
    argv <- getArgs
    printf "Command: %s %s\n" pname (unwords $ map show argv)
    case parse argv of
        (opts, files, []) | Help `elem` opts -> help
        (opts, [file], []) -> return $
            foldl (\acc opt -> case opt of
                     HCCS IT -> acc { hornOption = "-hccs it" }
                     HCCS GCH -> acc { hornOption = "-hccs gch" }
                     CEGARLimit l -> acc { cegarLimit = l }
                     AccErrTraces -> acc { accErrTraces = True }
                     ContextSensitive -> acc { accErrTraces = True, contextSensitive = True }
                     FoolTraces n -> acc { foolTraces = True, foolThreshold = n }
                     Interactive -> acc { interactive = True } ) 
                  (defaultConfig file) opts
        (opts, [], []) -> die ["No target specified\n"]
        (opts, files, []) -> die ["Multiple targets Specified\n"]
        (_,_,errs) -> die errs

data CEGARResult a = Safe | Unsafe | Refine a

doit :: ExceptT MainError (FreshT IO) ()
doit = do
    -- check args
    conf <- measure "ParseArg" $ liftIO parseArgs
    hccsSolver <- liftIO getHCCSSolver
    
    -- parsing
    let path = targetProgram conf
    parsedProgram <- measure "Parse" $ do
        parseRes <- liftIO $ parseProgramFromFile path
        program  <- case parseRes of
            Left err -> throwError $ ParseFailed err
            Right p  -> return p
        liftIO $ putStrLn "Parsed Program"
        liftIO $ printProgram program
        return program

    normalizedProgram <- measure "Preprocess" $ do
        -- alpha conversion
        alphaProgram <- withExceptT AlphaFailed $ alpha parsedProgram
        liftIO $ putStrLn "Alpha Converted Program"
        liftIO $ printProgram alphaProgram

        -- Call normalizing
        alphaNormProgram <- CallNormalize.normalize alphaProgram
        liftIO $ putStrLn "Call Normalized Program"
        liftIO $ printProgram alphaNormProgram

        -- type checking
        liftIO $ putStrLn "Typed Program"
        _typedProgram <- withExceptT IllTyped $ Typed.fromUnTyped alphaNormProgram
        liftIO $ Typed.printProgram _typedProgram

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
        normalizedProgram <- PNormal.normalize typedProgram
        liftIO $ PNormal.printProgram normalizedProgram
        return normalizedProgram

    (typeMap0, fvMap) <- PAbst.initTypeMap normalizedProgram
    let cegar _ k _  | k >= cegarLimit conf = return ()
        cegar (typeMap,typeMapFool) k (rtyAssoc0,rpostAssoc0,hcs) = do
            res <- measure (printf "CEGAR-%d" k) $ do

                liftIO $ putStrLn "Predicate Abstracion"
                liftIO $ PAbst.printTypeMap typeMap
                let curTypeMap = PAbst.mergeTypeMap typeMap typeMapFool

                liftIO $ putStrLn "Elim cast"
                castFreeProgram <- PAbst.elimCast curTypeMap normalizedProgram
                liftIO $ PNormal.printProgram castFreeProgram

                liftIO $ putStrLn "Saturate"
                saturationResult <- liftIO $ Saturate.saturate curTypeMap castFreeProgram
                liftIO $ print saturationResult

                boolProgram' <- measure "Predicate Abstraction" $ PAbst.abstProg curTypeMap castFreeProgram
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
                    Just trace -> measure "Refinement" $ do
                        let traceFile = printf "%s_%d.trace.dot" path k
                        (trace,isFoolI) <- case interactive conf of
                            True -> Refine.interactiveCEGen normalizedProgram traceFile trace
                            False -> return (trace, Nothing)
                        refine <- Refine.refineCGen normalizedProgram 
                                                    traceFile 
                                                    (contextSensitive conf) 
                                                    (foolThreshold conf) trace
                        case refine of
                            Nothing -> return Unsafe
                            Just (isFool,(clauses, assoc)) -> do
                                let file_hcs = printf "%s_%d.hcs" path k
                                let bf = case isFoolI of
                                        Just b -> b
                                        Nothing -> foolTraces conf && isFool
                                if bf then do
                                    liftIO $ putStrLn "Fool counterexample refinement"
                                    let hcs' = clauses
                                    liftIO $ writeFile file_hcs $ show (Horn.HCCS hcs')
                                    let cmd = printf "%s -hccs it -print-hccs-solution %s %s" 
                                                     hccsSolver (file_hcs ++ ".ans") file_hcs
                                    liftIO $ callCommand cmd
                                    parseRes <- liftIO $ Horn.parseSolution (file_hcs ++ ".ans")
                                    liftIO $ readFile (file_hcs ++ ".ans") >>= putStr 
                                    let (rtyAssoc,rpostAssoc) = assoc
                                    solution  <- case parseRes of
                                        Left err -> throwError $ RefinementFailed err
                                        Right p  -> return p
                                    let typeMapFool' = Refine.refine fvMap rtyAssoc rpostAssoc solution typeMapFool
                                    return $ Refine (typeMap, typeMapFool', hcs, rtyAssoc0, rpostAssoc0)
                                else do
                                    let hcs' = if accErrTraces conf then clauses ++ hcs else clauses
                                    let (rtyAssoc,rpostAssoc) = 
                                            if accErrTraces conf then assoc <> (rtyAssoc0,rpostAssoc0)
                                                                 else assoc
                                    liftIO $ writeFile file_hcs $ show (Horn.HCCS hcs')
                                    let opts = hornOption conf
                                    let cmd = printf "%s %s -print-hccs-solution %s %s" 
                                                     hccsSolver opts (file_hcs ++ ".ans") file_hcs
                                    liftIO $ callCommand cmd
                                    parseRes <- liftIO $ Horn.parseSolution (file_hcs ++ ".ans")
                                    liftIO $ readFile (file_hcs ++ ".ans") >>= putStr 
                                    solution  <- case parseRes of
                                        Left err -> throwError $ RefinementFailed err
                                        Right p  -> return p
                                    let typeMap' | accErrTraces conf = Refine.refine fvMap rtyAssoc rpostAssoc solution typeMap0
                                                 | otherwise         = Refine.refine fvMap rtyAssoc rpostAssoc solution typeMap
                                    return $ Refine (typeMap', typeMapFool, hcs', rtyAssoc, rpostAssoc)
                    Nothing -> return Safe
            case res of
                Safe -> liftIO $ putStrLn "Safe!"
                Unsafe -> liftIO $ putStrLn "Unsafe!"
                Refine (typeMap',typeMapFool', hcs', rtyAssoc, rpostAssoc) ->
                    cegar (typeMap',typeMapFool') (k+1) (rtyAssoc,rpostAssoc,hcs')
    cegar (typeMap0,typeMap0) 0 ([],[],[])

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


