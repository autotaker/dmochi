module Language.DMoCHi.ML.Main(run, verify, Config(..), defaultConfig) where
import System.Environment
import System.IO
import System.Process(callCommand)
import System.Exit
import System.Console.GetOpt
import Control.Monad.Except
import Data.Monoid
import Data.List(isSuffixOf)
import Data.Maybe(fromMaybe)
import Text.Parsec(ParseError)
import Text.PrettyPrint.HughesPJClass hiding((<>))
import Text.Printf

import           Language.DMoCHi.Boolean.Syntax.Typed as B(tCheck)
import           Language.DMoCHi.Boolean.PrettyPrint.Typed as B(pprintProgram)
import           Language.DMoCHi.Boolean.LiftRec as B(liftRec)
import           Language.DMoCHi.Boolean.Test 
import qualified Language.DMoCHi.ML.Parser as Parser
import qualified Language.DMoCHi.ML.MLParser as MLParser
import           Language.DMoCHi.ML.Alpha
import qualified Language.DMoCHi.ML.Inline  as Inline
import qualified Language.DMoCHi.ML.ElimUnreachable  as Unreachable
import qualified Language.DMoCHi.ML.TypeCheck as Typed
import qualified Language.DMoCHi.ML.Syntax.PNormal as PNormal
import qualified Language.DMoCHi.ML.PredicateAbstraction as PAbst
import qualified Language.DMoCHi.ML.ElimCast as PAbst
import qualified Language.DMoCHi.ML.IncSaturation as IncSat
import qualified Language.DMoCHi.ML.UnliftRec as IncSat
import qualified Language.DMoCHi.ML.Syntax.PType as PAbst
import qualified Language.DMoCHi.ML.Refine as Refine
import qualified Language.DMoCHi.ML.InteractiveCEGen as Refine
import           Language.DMoCHi.Common.Id
import           Language.DMoCHi.Common.Util

import qualified Language.DMoCHi.ML.HornClause as Horn
import qualified Language.DMoCHi.ML.HornClauseParser as Horn

data MainError = NoInputSpecified
               | ParseFailed String
               | RefinementFailed ParseError
               | AlphaFailed AlphaError
               | IllTyped Typed.TypeError 
               | CEGARLimitExceeded
               | Debugging
               | OtherError String
               | BooleanError String
               deriving(Eq)

instance Show MainError where
    show NoInputSpecified = "NoInputSpecified"
    show (ParseFailed err) = "ParseFailed: " ++ err
    show (AlphaFailed err) = "AlphaFailed: " ++ show err
    show (IllTyped err)    = "IllTyped: " ++ show err
    show (RefinementFailed err)    = "RefinementFailed: " ++ show err
    show (BooleanError s) = "Boolean: " ++ s
    show (OtherError s) = "Other: " ++ s
    show CEGARLimitExceeded = "CEGARLimitExceeded"
    show Debugging = "Debugging"

data Flag = Help 
          | HCCS HCCSSolver 
          | CEGARLimit Int 
          | AccErrTraces 
          | ContextSensitive 
          | Interactive
          | FoolTraces Int
          | Fusion
          | Incremental
          | Verbose
          deriving Eq
data HCCSSolver = IT | GCH  deriving Eq

data Config = Config { targetProgram :: FilePath
                     , hornOption :: String
                     , cegarLimit :: Int
                     , accErrTraces :: Bool
                     , contextSensitive :: Bool
                     , foolTraces :: Bool
                     , foolThreshold :: Int
                     , fusion :: Bool
                     , incremental :: Bool
                     , verbose :: Bool
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
                            , fusion = False
                            , incremental = False
                            , verbose = False
                            , interactive = False }

run :: IO ()
run = do
    -- check args
    conf <- parseArgs
    verify conf >>= \case
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
          , Option [] ["fusion"] (NoArg Fusion) "enable model checking fusion"
          , Option [] ["incremental"] (NoArg Incremental) "enable incremental saturation algorithm"
          , Option ['v'] ["verbose"] (NoArg Verbose) "set pretty level to verbose"
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
        (opts, _, []) | Help `elem` opts -> help
        (opts, [file], []) -> return $
            foldl (\acc opt -> case opt of
                     HCCS IT -> acc { hornOption = "-hccs it" }
                     HCCS GCH -> acc { hornOption = "-hccs gch" }
                     CEGARLimit l -> acc { cegarLimit = l }
                     AccErrTraces -> acc { accErrTraces = True }
                     ContextSensitive -> acc { accErrTraces = True, contextSensitive = True }
                     FoolTraces n -> acc { foolTraces = True, foolThreshold = n }
                     Fusion -> acc { fusion = True }
                     Incremental -> acc { fusion = True, incremental = True }
                     Interactive -> acc { interactive = True } 
                     Help -> error "unexpected"
                     Verbose -> acc { verbose = True }
                     ) 
                  (defaultConfig file) opts
        (_, [], []) -> die ["No target specified\n"]
        (_, _, []) -> die ["Multiple targets Specified\n"]
        (_,_,errs) -> die errs

data CEGARResult a = Safe | Unsafe | Refine a
    deriving(Eq,Show)

verify :: Config -> IO (Either MainError (CEGARResult ()))
verify conf = runFreshIO defaultLogger $ measure $(logKey "ML.Verify") $ runExceptT $ do
    hccsSolver <- liftIO getHCCSSolver
    
    -- parsing
    let path = targetProgram conf
    let prettyPrint :: Pretty a => a -> ExceptT MainError FreshIO ()
        prettyPrint | verbose conf = liftIO . putStrLn . render . pPrintPrec (PrettyLevel 1) 0
                    | otherwise    = liftIO . putStrLn . render . pPrint
    parsedProgram <- measure $(logKey "ML.Parse") $ do
        program <- if ".ml" `isSuffixOf` path
            then withExceptT ParseFailed $ ExceptT $ liftIO $ MLParser.parseProgramFromFile path
            else withExceptT (ParseFailed. show) $ ExceptT $ liftIO $ Parser.parseProgramFromFile path
        liftIO $ putStrLn "Parsed Program"
        prettyPrint program
        return program

    normalizedProgram <- measure $(logKey "ML.Preprocess") $ do
        -- alpha conversion
        alphaProgram <- withExceptT AlphaFailed $ ExceptT $ alpha parsedProgram
        liftIO $ putStrLn "Alpha Converted Program"
        prettyPrint alphaProgram

        -- type checking
        liftIO $ putStrLn "Typed Program"
        typedProgram <- withExceptT IllTyped $ Typed.fromUnTyped alphaProgram
        prettyPrint typedProgram

        -- normalizing
        liftIO $ putStrLn "Normalizing"
        _normalizedProgram <- lift $ PNormal.normalize typedProgram
        prettyPrint _normalizedProgram
        
        -- inlining
        liftIO $ putStrLn "Inlined Program"
        _normalizedProgram <- lift $ Inline.inline 1000 _normalizedProgram
        prettyPrint _normalizedProgram
        
        -- unreachable code elimination
        liftIO $ putStrLn "Unreachable Code Elimination"
        _normalizedProgram <- return $ Unreachable.elimUnreachable _normalizedProgram
        prettyPrint _normalizedProgram
        return _normalizedProgram

    (typeMap0, fvMap) <- lift $ PAbst.initTypeMap normalizedProgram
    let mc k curTypeMap castFreeProgram 
            | incremental conf = measure $(logKey "Fusion(Inc)") $ do
                unliftedProgram <- IncSat.unliftRec castFreeProgram
                (_,res) <- liftIO $ IncSat.saturate curTypeMap unliftedProgram
                liftIO $ print res
                return (snd res)
                {-
            | fusion conf = measure "Fusion" $ do
                (_,res) <- liftIO $ Saturate.saturate curTypeMap castFreeProgram
                liftIO $ print res
                return (snd res)
                -}
            | otherwise = do
                boolProgram <- measure $(logKey "Predicate Abstraction") $ lift $ PAbst.abstProg curTypeMap castFreeProgram
                liftIO $ putStrLn "Converted program"
                liftIO $ putStrLn $ render $ B.pprintProgram boolProgram
                case runExcept (B.tCheck boolProgram) of
                    Left (s1,s2,str,ctx) -> do
                        liftIO $ do
                            printf "type mismatch: %s. %s <> %s\n" str (show s1) (show s2)
                            forM_ (zip [(0::Int)..] ctx) $ \(i,t) -> do
                                printf "Context %d: %s\n" i (show t)
                        throwError $ BooleanError "Abstracted Program is ill-typed"
                    Right _ -> return ()
                boolProgram' <- lift $ B.liftRec boolProgram
                liftIO $ putStrLn "Recursion lifted program"
                liftIO $ putStrLn $ render $ B.pprintProgram boolProgram'
                let file_boolean = printf "%s_%d.bool" path k
                liftIO $ writeFile file_boolean $ (++"\n") $ render $ B.pprintProgram boolProgram'
                r <- measure $(logKey "Model Checking") $ withExceptT BooleanError $ testTyped file_boolean boolProgram'
                return r
        cegar _ k _  | k >= cegarLimit conf = throwError CEGARLimitExceeded
        cegar (typeMap,typeMapFool) k (rtyAssoc0,rpostAssoc0,hcs,traces) = do
            res <- measure $(logKey "ML.CEGAR") $ do

                liftIO $ putStrLn "Predicate Abstracion"
                liftIO $ PAbst.printTypeMap typeMap
                let curTypeMap = PAbst.mergeTypeMap typeMap typeMapFool

                liftIO $ putStrLn "Elim cast"
                castFreeProgram <- lift $ PAbst.elimCast curTypeMap normalizedProgram
                prettyPrint castFreeProgram

                mc k curTypeMap castFreeProgram >>= \case
                    Nothing -> return Safe
                    Just trace -> measure $(logKey "ML.Refinement") $ do
                        when (elem trace traces) $ throwError $ OtherError "No progress"
                        let traceFile = printf "%s_%d.trace.dot" path k
                        (trace,isFoolI) <- case interactive conf of
                            True -> Refine.interactiveCEGen normalizedProgram traceFile trace
                            False -> return (trace, Nothing)
                        Refine.refineCGen normalizedProgram 
                                          traceFile 
                                          (contextSensitive conf) 
                                          (foolThreshold conf) trace >>= \case
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
                                    let cmd = printf "%s -hccs it -print-hccs-solution %s %s > %s" 
                                                     hccsSolver (file_hcs ++ ".ans") file_hcs (file_hcs ++ ".log")
                                    liftIO $ callCommand cmd
                                    parseRes <- liftIO $ Horn.parseSolution (file_hcs ++ ".ans")
                                    liftIO $ readFile (file_hcs ++ ".ans") >>= putStr 
                                    let (rtyAssoc,rpostAssoc) = assoc
                                    solution  <- case parseRes of
                                        Left err -> throwError $ RefinementFailed err
                                        Right p  -> return p
                                    let typeMapFool' = Refine.refine fvMap rtyAssoc rpostAssoc solution typeMapFool
                                    return $ Refine (typeMap, typeMapFool', hcs, rtyAssoc0, rpostAssoc0, trace)
                                else do
                                    let hcs' = if accErrTraces conf then clauses ++ hcs else clauses
                                    let (rtyAssoc,rpostAssoc) = 
                                            if accErrTraces conf then assoc <> (rtyAssoc0,rpostAssoc0)
                                                                 else assoc
                                    liftIO $ writeFile file_hcs $ show (Horn.HCCS hcs')
                                    let opts = hornOption conf
                                    let cmd = printf "%s %s -print-hccs-solution %s %s > %s" 
                                                     hccsSolver opts (file_hcs ++ ".ans") file_hcs (file_hcs ++ ".log")
                                    liftIO $ callCommand cmd
                                    parseRes <- liftIO $ Horn.parseSolution (file_hcs ++ ".ans")
                                    liftIO $ readFile (file_hcs ++ ".ans") >>= putStr 
                                    solution  <- case parseRes of
                                        Left err -> throwError $ RefinementFailed err
                                        Right p  -> return p
                                    let typeMap' | accErrTraces conf = Refine.refine fvMap rtyAssoc rpostAssoc solution typeMap0
                                                 | otherwise         = Refine.refine fvMap rtyAssoc rpostAssoc solution typeMap
                                    return $ Refine (typeMap', typeMapFool, hcs', rtyAssoc, rpostAssoc, trace)
            case res of
                Safe -> liftIO $ putStrLn "Safe!" >> return Safe
                Unsafe -> liftIO $ putStrLn "Unsafe!" >> return Unsafe
                Refine (typeMap',typeMapFool', hcs', rtyAssoc, rpostAssoc, trace) ->
                    cegar (typeMap',typeMapFool') (k+1) (rtyAssoc,rpostAssoc,hcs', trace:traces)
    cegar (typeMap0,typeMap0) 0 ([],[],[],[])


