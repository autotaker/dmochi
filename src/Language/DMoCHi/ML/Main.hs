{-# LANGUAGE OverloadedStrings #-}
module Language.DMoCHi.ML.Main(run, verify, Config(..), defaultConfig, CEGARMethod(..)) where
import System.Environment
import System.IO
import System.Exit
import System.Console.GetOpt
import Control.Monad.Except
import Data.Monoid
import Data.List(isSuffixOf)
import Data.IORef
import Data.Maybe(fromMaybe)
import Text.PrettyPrint.HughesPJClass hiding((<>))
import Text.Printf
import qualified Data.Text as Text
import Lens.Micro.GHC()
import Data.Time(NominalDiffTime)
import qualified Data.IntMap as IM
import qualified Data.PolyDict as Dict
import Data.PolyDict(Dict, access',Assoc,access)
-- import Data.Aeson
--import qualified Data.ByteString.Lazy as ByteString
import qualified Data.ByteString.Lazy.Char8 as ByteString
import Data.Aeson(encode)

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
import qualified Language.DMoCHi.ML.Syntax.HFormula as HFormula
import qualified Language.DMoCHi.ML.PredicateAbstraction as PAbst
import qualified Language.DMoCHi.ML.AbstractSemantics as AbstSem
import qualified Language.DMoCHi.ML.ToCEGAR as CEGAR
-- import qualified Language.DMoCHi.ML.ElimCast as PAbst
import qualified Language.DMoCHi.ML.IncSaturation as IncSat
import qualified Language.DMoCHi.ML.UnliftRec as IncSat
import qualified Language.DMoCHi.ML.Syntax.PType as PAbst
import qualified Language.DMoCHi.ML.Refine as Refine
import qualified Language.DMoCHi.ML.SymbolicExec as SExec
import qualified Language.DMoCHi.ML.InteractiveCEGen as Refine
import qualified Language.DMoCHi.ML.EtaNormalize as Eta
import qualified Language.DMoCHi.ML.ConstPropagation as ConstProp
import qualified Language.DMoCHi.ML.TailOptimization as TailOpt
import           Language.DMoCHi.Common.Id
import           Language.DMoCHi.Common.Util
import qualified Language.DMoCHi.ML.SMT as SMT

import qualified Language.DMoCHi.ML.HornClause as Horn

data MainError = NoInputSpecified
               | ParseFailed String
               | RefinementFailed Horn.SolverError
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
          | CEGARMethod CEGARMethod
          deriving Eq
data HCCSSolver = IT | GCH  deriving Eq
data CEGARMethod = DepType | AbstSemantics deriving Eq

data Config = Config { targetProgram :: FilePath
                     , hornOption :: String
                     , cegarLimit :: Int
                     , accErrTraces :: Bool
                     , contextSensitive :: Bool
                     , foolTraces :: Bool
                     , foolThreshold :: Int
                     , fusion :: Bool
                     , incremental :: Bool
                     , cegarMethod :: CEGARMethod
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
                            , cegarMethod = DepType
                            , interactive = False }

run :: IO ()
run = do
    -- check args
    conf <- parseArgs
    (r, d) <- verify conf
    ByteString.writeFile (targetProgram conf ++ ".result.json") (encode d <> ByteString.pack "\n")
    putStrLn ""
    case r of
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
          , Option [] ["cegar"] (ReqArg parseMethod "dep|abst") "Set CEGAR method (default = dep)"  
          , Option [] ["interactive"] (NoArg Interactive) "interactive counterexample generation" ]
    where
    parseSolver "it" = HCCS IT
    parseSolver "gch" = HCCS GCH
    parseSolver s = error $ "Non Supported Parameter for --hccs: " ++ s
    parseMethod "dep" = CEGARMethod DepType
    parseMethod "abst" = CEGARMethod AbstSemantics
    parseMethod s = error $ "Non Supported Parameter for --cegar: " ++ s

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
                     CEGARMethod m -> acc { cegarMethod = m }
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

data Main
data CEGAR

type instance Assoc Main "total"      = NominalDiffTime
type instance Assoc Main "parse"      = NominalDiffTime
type instance Assoc Main "preprocess" = NominalDiffTime
type instance Assoc Main "cegar"      = IM.IntMap (Dict CEGAR)
type instance Assoc Main "cycles"     = Int
type instance Assoc Main "result"     = String

type instance Assoc CEGAR "refine" = NominalDiffTime
type instance Assoc CEGAR "abst" = Dict PAbst.Abst
type instance Assoc CEGAR "fusion" = NominalDiffTime
type instance Assoc CEGAR "fusion_sat" = Dict IncSat.IncSat
type instance Assoc CEGAR "modelchecking" = Dict Boolean
type instance Assoc CEGAR "abstractsemantics" = Dict AbstSem.AbstractSemantics


verify :: Config -> IO (Either MainError (CEGARResult ()), Dict Main)
verify conf = runStdoutLoggingT $ (if verbose conf then id else filterLogger (\_ level -> level >= LevelInfo)) $ runFreshT $ ioTracerT Dict.empty $ measure #total $ runExceptT $ do
    -- ExceptT MainError (FreshT (TracerT c (LoggingT IO))) a
    let path = targetProgram conf
    
    hccsSolverPath <- liftIO getHCCSSolver
    let defaultSolver = Horn.rcamlSolver hccsSolverPath "-hccs it" path
        gchSolver     = Horn.rcamlSolver hccsSolverPath "-hccs gch" path
        currentSolver = Horn.rcamlSolver hccsSolverPath (hornOption conf) path

    -- parsing
    let prettyPrint :: Pretty a => Text.Text -> String -> a -> ExceptT MainError (FreshIO c) ()
        prettyPrint header title body = logPretty header LevelDebug title body
            {-
        prettyPrint | verbose conf = liftIO . putStrLn . render . pPrintPrec (PrettyLevel 1) 0
                    | otherwise    = liftIO . putStrLn . render . pPrint
                    -}
    parsedProgram <- measure #parse $ do
        program <- if ".ml" `isSuffixOf` path
            then withExceptT ParseFailed $ ExceptT $ liftIO $ MLParser.parseProgramFromFile path
            else withExceptT (ParseFailed. show) $ ExceptT $ liftIO $ Parser.parseProgramFromFile path
        program <$ prettyPrint "parse" "Parsed Program" program

-- forall f. Functor f => (a -> f a) -> b -> f b
    normalizedProgram <- measure #preprocess $ (do
        -- alpha conversion
        alphaProgram <- mapExceptT lift $ withExceptT AlphaFailed $ alpha parsedProgram
        prettyPrint "preprocess" "Alpha Converted alphaProgram" alphaProgram

        -- type checking
        typedProgram <- withExceptT IllTyped $ Typed.fromUnTyped alphaProgram
        prettyPrint "preprocess" "Typed Program" typedProgram

        -- normalizing
        _normalizedProgram <- lift $ lift $ PNormal.normalize typedProgram
        prettyPrint "preprocess" "Normalized Program" _normalizedProgram
        
        -- inlining
        _normalizedProgram <- lift $ lift $ Inline.inline 1000 _normalizedProgram
        prettyPrint "preprocess" "Inlined Program" _normalizedProgram
        
        -- unreachable code elimination
        _normalizedProgram <- return $ Unreachable.elimUnreachable _normalizedProgram
        prettyPrint "preprocess" "Unreachable Code Elimination" _normalizedProgram


        _normalizedProgram <- lift $Eta.normalize _normalizedProgram
        prettyPrint "preprocess" "Eta normalization" _normalizedProgram
        
        -- const propagation
        _normalizedProgram <- return $ ConstProp.simplify _normalizedProgram
        prettyPrint "preprocess" "Constant Propagation" _normalizedProgram
        
        -- tail optimization
        _normalizedProgram <- return $ TailOpt.simplify _normalizedProgram
        prettyPrint "preprocess" "Tail optimization" _normalizedProgram

        return _normalizedProgram) :: ExceptT MainError (FreshIO (Dict Main)) PNormal.Program
    
    hContext <- liftIO HFormula.newContext

    {- TODO: Fix this BAD HACK -}
    currentProgramRef <- liftIO $ newIORef undefined

    (typeMap0, fvMap) <- lift $ PAbst.initTypeMap normalizedProgram
    let mc k curTypeMap castFreeProgram 
            | incremental conf = 
                measure #fusion $ do
                    unliftedProgram <- IncSat.unliftRec castFreeProgram
                    cegarProgram <- liftIO $ CEGAR.convert hContext curTypeMap unliftedProgram
                    liftIO $ writeIORef currentProgramRef cegarProgram
                    (_,res) <- lift $ zoom (access' #fusion_sat Dict.empty) $ mapTracerT lift $ IncSat.saturate hContext cegarProgram
                    logPretty "fusion" LevelDebug "result" res
                    return (snd res)
            | otherwise = do
                boolProgram <- lift $ zoom (access' #abst Dict.empty) $ PAbst.abstProg curTypeMap castFreeProgram
                prettyPrint "modelchecking" "Converted Program" boolProgram
                case runExcept (B.tCheck boolProgram) of
                    Left (s1,s2,str,ctx) -> do
                        logErrorNS "typecheck" $ Text.pack $ printf "type mismatch: %s. %s <> %s\n" str (show s1) (show s2)
                        forM_ (zip [(0::Int)..] ctx) $ \(i,t) -> do
                            logErrorNS "typecheck" $ Text.pack $ printf "Context %d: %s\n" i (show t)
                        throwError $ BooleanError "Abstracted Program is ill-typed"
                    Right _ -> return ()
                boolProgram' <- lift $ B.liftRec boolProgram
                prettyPrint "modelchecking" "Recursion lifted program" boolProgram'
                let file_boolean = printf "%s_%d.bool" path k
                liftIO $ writeFile file_boolean $ (++"\n") $ render $ B.pprintProgram boolProgram'
                r <- mapExceptT (zoom (access' #modelchecking Dict.empty)) $ withExceptT BooleanError $ testTyped file_boolean boolProgram'
                return r
        cegar _ k _  | k >= cegarLimit conf = throwError CEGARLimitExceeded
        cegar (typeMap,typeMapFool) k (rtyAssoc0,rpostAssoc0,hcs,traces) = do
            update $ access' #cycles 0 %~ succ
            res <- mapExceptT (zoom (access' #cegar IM.empty . at k . non Dict.empty)) $ do
                -- liftIO $ putStrLn "Predicate Abstracion"
                -- liftIO $ PAbst.printTypeMap typeMap
                let curTypeMap = PAbst.mergeTypeMap typeMap typeMapFool
                --castFreeProgram <- lift $ PAbst.elimCast curTypeMap normalizedProgram
                --prettyPrint "cegar" "Elim cast" castFreeProgram

                mc k curTypeMap normalizedProgram >>= \case
                    Nothing -> return Safe
                    Just trace -> measure #refine $ do
                        when (elem trace traces) $ throwError $ OtherError "No progress"
                        let traceFile = printf "%s_%d.trace.dot" path k
                        (trace,isFoolI) <- case interactive conf of
                            True -> Refine.interactiveCEGen normalizedProgram traceFile trace
                            False -> return (trace, Nothing)
                        case cegarMethod conf of
                            AbstSemantics -> do
                                prog <- liftIO $ readIORef currentProgramRef
                                res <- mapExceptT (zoom (access' #abstractsemantics Dict.empty)) 
                                          $ withExceptT RefinementFailed 
                                          $ fmap Just (AbstSem.refine hContext currentSolver k trace curTypeMap prog)
                                          `catchError` (\err -> do
                                              (_, log, _compTree) <- SExec.symbolicExec normalizedProgram trace
                                              let cs = map SExec.fromSValue $ SExec.logCnstr log
                                              isFeasible <- liftIO $ SMT.sat cs
                                              if isFeasible
                                                  then return Nothing
                                                  else throwError err)
                                case res of
                                    Just typeMap' -> return $ Refine (typeMap', typeMapFool, [], [], [], trace)
                                    Nothing -> return Unsafe
                            DepType -> 
                                Refine.refineCGen normalizedProgram 
                                                  traceFile 
                                                  (contextSensitive conf) 
                                                  (foolThreshold conf) trace >>= \case
                                    Nothing -> return Unsafe
                                    Just (isFool,(clauses, assoc)) -> do
                                        --let file_hcs_smt2 = printf "%s_%d.smt2" path k
                                        let bf = case isFoolI of
                                                Just b -> b
                                                Nothing -> foolTraces conf && isFool
                                        if bf then do
                                            logInfoNS "refinement" "Fool counterexample refinement"
                                            let hcs' = clauses
                                            solution <- mapExceptT lift 
                                                      $ withExceptT RefinementFailed 
                                                      $ defaultSolver (Horn.HCCS hcs') k
                                            let (rtyAssoc,rpostAssoc) = assoc
                                            let typeMapFool' = Refine.refine fvMap rtyAssoc rpostAssoc solution typeMapFool
                                            return $ Refine (typeMap, typeMapFool', hcs, rtyAssoc0, rpostAssoc0, trace)
                                        else do
                                            let hcs' = if accErrTraces conf then clauses ++ hcs else clauses
                                            let (rtyAssoc,rpostAssoc) = 
                                                    if accErrTraces conf then assoc <> (rtyAssoc0,rpostAssoc0)
                                                                         else assoc
                                            
                                            solution <- mapExceptT lift 
                                                      $ withExceptT RefinementFailed 
                                                      $ currentSolver (Horn.HCCS hcs') k
                                            --liftIO $ writeFile file_hcs_smt2 $ Horn.renderSMTLib2 (Horn.HCCS hcs')
                                            let typeMap' | accErrTraces conf = Refine.refine fvMap rtyAssoc rpostAssoc solution typeMap0
                                                         | otherwise         = Refine.refine fvMap rtyAssoc rpostAssoc solution typeMap
                                            return $ Refine (typeMap', typeMapFool, hcs', rtyAssoc, rpostAssoc, trace)

                                
            case res of
                Safe   -> do
                    update (access #result ?~ "Safe")
                    Safe <$ logInfoNS "result" "Safe"
                Unsafe -> do
                    update (access #result ?~ "Unsafe")
                    Unsafe <$ logInfoNS "result" "Unsafe" 
                Refine (typeMap',typeMapFool', hcs', rtyAssoc, rpostAssoc, trace) ->
                    cegar (typeMap',typeMapFool') (k+1) (rtyAssoc,rpostAssoc,hcs', trace:traces)
    cegar (typeMap0,typeMap0) 0 ([],[],[],[])


