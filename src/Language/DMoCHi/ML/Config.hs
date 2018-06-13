module Language.DMoCHi.ML.Config where
import System.Console.GetOpt
import Text.Printf
import System.Environment
import System.Exit
import System.IO
import qualified Language.DMoCHi.ML.HornClause as Horn

data Flag = Help 
          | HCCS HCCSSolver 
          | CEGARLimit Int 
          | AccErrTraces 
          | ContextSensitive 
          | Interactive
          | FoolTraces Int
          | PredicateGen
          | NoEmbedCurCond
          | LogFilter String
          | RCamlCommand String
          | HoiceCommand String
          | ConvexHullCommand String
 --         | Fusion
 --         | Incremental
          | Verbose
          | CEGARMethod CEGARMethod
          deriving Eq
data HCCSSolver = Fpat FpatSolver | Hoice  deriving Eq
data FpatSolver = IT | GCH
  deriving Eq

data CEGARMethod = DepType | AbstSemantics deriving Eq

data Config = Config { targetProgram :: FilePath
                     , hornOption :: String
                     , hornSolver :: HCCSSolver
                     , rcamlCommand :: String
                     , hoiceCommand :: String
                     , logFilterExp :: Maybe String
                     , convexHullCommand :: String
                     , cegarLimit :: Int
                     , accErrTraces :: Bool
                     , contextSensitive :: Bool
                     , foolTraces :: Bool
                     , foolThreshold :: Int
                     , predicateGen :: Bool
                     , embedCurCond :: Bool
                     , cegarMethod :: CEGARMethod
                     , verbose :: Bool
                     , interactive :: Bool }


getHCCSSolver :: Config -> FilePath -> Horn.Solver
--getHCCSSolver = Paths_dmochi.getDataFileName "hcsolver"
getHCCSSolver Config{ hornSolver = Fpat _
                    , hornOption = option
                    , rcamlCommand = cmd } basename =
  Horn.rcamlSolver cmd option basename
getHCCSSolver Config{ hornSolver = Hoice
                    , hoiceCommand = cmd } basename =
  Horn.hoiceSolver cmd basename

defaultConfig :: FilePath -> Config
defaultConfig path = 
  Config { targetProgram = path
         , hornOption = ""
         , hornSolver = Hoice
         , rcamlCommand = "rcaml"
         , hoiceCommand = "hoice"
         , convexHullCommand = "convex-hull"
         , logFilterExp =  Nothing
         , cegarLimit = 20
         , accErrTraces = False
         , contextSensitive = False
         , foolTraces = False
         , foolThreshold = 1
         , predicateGen = False
         , embedCurCond = True
         , verbose = False
         , cegarMethod = AbstSemantics
         , interactive = False }

eagerConfig :: FilePath -> Config
eagerConfig path = 
  Config { targetProgram = path
         , hornOption = ""
         , hornSolver = Fpat IT
         , rcamlCommand = "rcaml"
         , hoiceCommand = "hoice"
         , convexHullCommand = "convex-hull"
         , logFilterExp =  Nothing
         , cegarLimit = 20
         , accErrTraces = False
         , contextSensitive = False
         , foolTraces = False
         , foolThreshold = 1
         , predicateGen = False
         , embedCurCond = True
         , verbose = False
         , cegarMethod = DepType
         , interactive = False }

options :: [ OptDescr Flag ]
options = [ Option ['h'] ["help"] (NoArg Help) "Show this help message"
          , Option [] ["hccs"] (ReqArg parseSolver "it|gch|hoice") "Set hccs solver"
          , Option ['l'] ["limit"] (ReqArg (CEGARLimit . read) "N") "Set CEGAR round limit (default = 20)"
          , Option [] ["acc-traces"] (NoArg AccErrTraces) "Accumrate error traces"
          , Option [] ["pred-gen"] (NoArg PredicateGen) "Generalize Predicate based on AI"
          , Option [] ["no-embed-cur-cond"] (NoArg NoEmbedCurCond) "Disable Embed current condition in Horn clauses"
          , Option [] ["context-sensitive"] (NoArg ContextSensitive) 
                   "Enable context sensitive predicate discovery, this also enables --acc-traces flag"
          , Option [] ["fool-traces"] (OptArg (FoolTraces . maybe 1 read) "N")  "Distinguish fool error traces in refinement phase, and set threshold (default = 1)"
--          , Option [] ["fusion"] (NoArg Fusion) "enable model checking fusion"
--          , Option [] ["incremental"] (NoArg Incremental) "enable incremental saturation algorithm"
          , Option ['v'] ["verbose"] (NoArg Verbose) "set pretty level to verbose"
          , Option [] ["filter"] (ReqArg LogFilter "pattern") "set log filtering expression"
          , Option [] ["cegar"] (ReqArg parseMethod "dep|abst") "Set CEGAR method (default = dep)"  
          , Option [] ["rcaml"] (ReqArg RCamlCommand "cmd") "Set RCaml Command (default = rcaml)"
          , Option [] ["hoice"] (ReqArg HoiceCommand "cmd") "Set Hoice Command (default = hoice)"
          , Option [] ["convex-hull"] (ReqArg RCamlCommand "cmd") "Set ConvexHull Command (default = convex-hull)"
          , Option [] ["interactive"] (NoArg Interactive) "interactive counterexample generation" ]
    where
    parseSolver "it" = HCCS (Fpat IT)
    parseSolver "gch" = HCCS (Fpat GCH)
    parseSolver "hoice" = HCCS Hoice
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
                     HCCS (Fpat IT) -> acc { hornSolver = Fpat IT, hornOption = "-hccs it" }
                     HCCS (Fpat GCH) -> acc { hornSolver = Fpat GCH, hornOption = "-hccs gch" }
                     HCCS Hoice -> acc { hornSolver = Hoice, hornOption = ""}
                     CEGARLimit l -> acc { cegarLimit = l }
                     CEGARMethod m -> acc { cegarMethod = m }
                     AccErrTraces -> acc { accErrTraces = True }
                     ContextSensitive -> acc { accErrTraces = True, contextSensitive = True }
                     FoolTraces n -> acc { foolTraces = True, foolThreshold = n }
                     PredicateGen -> acc { predicateGen = True }
                     NoEmbedCurCond -> acc { embedCurCond = False }
                     HoiceCommand cmd -> acc { hoiceCommand = cmd }
                     RCamlCommand cmd -> acc { rcamlCommand = cmd }
                     LogFilter str -> acc { logFilterExp = Just str }
                     ConvexHullCommand cmd -> acc { convexHullCommand = cmd }
   --                  Fusion -> acc { fusion = True }
   --                  Incremental -> acc { fusion = True, incremental = True }
                     Interactive -> acc { interactive = True } 
                     Help -> error "unexpected"
                     Verbose -> acc { verbose = True }
                     ) 
                  (defaultConfig file) opts
        (_, [], []) -> die ["No target specified\n"]
        (_, _, []) -> die ["Multiple targets Specified\n"]
        (_,_,errs) -> die errs