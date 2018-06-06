{-# LANGUAGE OverloadedStrings #-}
module Language.DMoCHi.ML.Main(run, verify, Config(..), defaultConfig, CEGARMethod(..)) where
import System.Exit
import Control.Monad.Except
import Data.Monoid
import Data.Maybe(fromMaybe)
import Data.List(isSuffixOf)
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

import           Language.DMoCHi.ML.Config
import           Language.DMoCHi.Boolean.Syntax.Typed as B(tCheck)
import           Language.DMoCHi.Boolean.PrettyPrint.Typed as B(pprintProgram)
import           Language.DMoCHi.Boolean.LiftRec as B(liftRec)
import           Language.DMoCHi.Boolean.Test 
import qualified Language.DMoCHi.ML.Parser as Parser
import qualified Language.DMoCHi.ML.MLParser as MLParser
import qualified Language.DMoCHi.ML.Syntax.PNormal as PNormal
import qualified Language.DMoCHi.ML.Syntax.HFormula as HFormula
import qualified Language.DMoCHi.ML.Syntax.UnTyped as UnTyped
import qualified Language.DMoCHi.ML.Syntax.CEGAR as CEGAR
import qualified Language.DMoCHi.ML.PredicateAbstraction as PAbst
import qualified Language.DMoCHi.ML.AbstractSemantics as AbstSem
import qualified Language.DMoCHi.ML.ToCEGAR as CEGAR
import qualified Language.DMoCHi.ML.IncSaturation as IncSat
import qualified Language.DMoCHi.ML.UnliftRec as IncSat
import qualified Language.DMoCHi.ML.Syntax.PType as PAbst
import qualified Language.DMoCHi.ML.Refine as Refine
import qualified Language.DMoCHi.ML.SymbolicExec as SExec
import qualified Language.DMoCHi.ML.InteractiveCEGen as Refine
import Language.DMoCHi.ML.Preprocess(preprocess, PreprocessError)
import qualified Language.DMoCHi.ML.PredicateGeneralizer as PredicateGen
import           Language.DMoCHi.Common.Id
import           Language.DMoCHi.Common.Util
import qualified Language.DMoCHi.ML.ConvexHull.Solver as ConvexHull
import qualified Language.DMoCHi.ML.SMT as SMT

import qualified Language.DMoCHi.ML.HornClause as Horn
import Control.Exception(bracket)

data MainError = NoInputSpecified
               | ParseFailed String
               | RefinementFailed Horn.SolverError
               | PreprocessFailed PreprocessError
               | CEGARLimitExceeded
               | Debugging
               | OtherError String
               | BooleanError String
               deriving(Eq)

instance Show MainError where
    show NoInputSpecified = "NoInputSpecified"
    show (ParseFailed err) = "ParseFailed: " ++ err
    show (PreprocessFailed err) = "PreprocessFailed: " ++ show err
    show (RefinementFailed err)    = "RefinementFailed: " ++ show err
    show (BooleanError s) = "Boolean: " ++ s
    show (OtherError s) = "Other: " ++ s
    show CEGARLimitExceeded = "CEGARLimitExceeded"
    show Debugging = "Debugging"

run :: IO ()
run = do
    -- check args
    conf <- parseArgs
    (r, d) <- verify conf
    ByteString.writeFile (targetProgram conf ++ ".result.json") (encode d <> ByteString.pack "\n")
    putStrLn "### Verification Result ###"
    case r of
        Left err -> putStr "Error: " >> print err >> exitFailure
        Right _ -> return ()
        
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
type instance Assoc CEGAR "predicategeneralizer" = Dict PredicateGen.PredicateGeneralizer
type instance Assoc CEGAR "abstractsemantics" = Dict AbstSem.AbstractSemantics

data CEGARContext (method :: CEGARMethod) where
    FusionContext :: CEGAR.Program -> HFormula.Context -> CEGARContext AbstSemantics
    EagerContext  :: PNormal.Program -> PAbst.TypeMap -> PAbst.TypeMap -> [Horn.Clause] ->
                     Refine.RTypeAssoc -> Refine.RPostTypeAssoc -> CEGARContext DepType

verify :: Config -> IO (Either MainError (CEGARResult ()), Dict Main)
verify conf = setup doit
  where 
  logFilter | verbose conf = id
            | otherwise = filterLogger (\_ level -> level >= LevelInfo)
  setup cont 
    | predicateGen conf = 
        bracket 
            (ConvexHull.convexHullSolver $ convexHullCommand conf)
            snd
            (cont . fst)
    | otherwise = cont (error "convex full is not required")
  doit convexHullSolver = 
        runStdoutLoggingT 
        $ logFilter 
        $ runFreshT 
        $ ioTracerT Dict.empty 
        $ measure #total 
        $ runExceptT $ do
    -- ExceptT MainError (FreshT (TracerT c (LoggingT IO))) a
    let path = targetProgram conf
    
    let defaultSolver = Horn.rcamlSolver "rcaml.opt" "-hccs it" path
        currentSolver = getHCCSSolver conf path

    -- parsing
    let prettyPrint :: Pretty a => Text.Text -> String -> a -> ExceptT MainError (FreshIO c) ()
        prettyPrint header title body = logPretty header LevelDebug title body
            {-
        prettyPrint | verbose conf = liftIO . putStrLn . render . pPrintPrec (PrettyLevel 1) 0
                    | otherwise    = liftIO . putStrLn . render . pPrint
                    -}
    parsedProgram <- measure #parse $ do
        program <- if ".ml" `isSuffixOf` path
            then withExceptT ParseFailed 
                $ ExceptT $ liftIO $ MLParser.parseProgramFromFile path
            else withExceptT (ParseFailed. show) 
                $ ExceptT $ liftIO $ Parser.parseProgramFromFile path
        program <$ prettyPrint "parse" "Parsed Program" program
    let specs = UnTyped.specs parsedProgram

    normalizedProgram <- measure #preprocess 
                    $ withExceptT PreprocessFailed 
                    $ preprocess parsedProgram
    
    (typeMap0, fvMap) <- lift $ PAbst.initTypeMap specs normalizedProgram
    prettyPrint "PAbst" "initial type map" $ PPrinted (PAbst.pprintTypeMap typeMap0)

    let mc :: CEGARContext method -> Int -> ExceptT MainError (FreshIO (Dict CEGAR)) (Maybe SExec.Trace)
        mc (FusionContext cegarProgram hContext) _ = measure #fusion $ do
            prettyPrint "fusion" "CEGAR Program" cegarProgram
            (_, res) <- lift $ zoom (access' #fusion_sat Dict.empty) 
                            $ mapTracerT lift 
                            $ IncSat.saturate hContext cegarProgram
            logPretty "fusion" LevelDebug "result" res
            return $ snd res
        mc (EagerContext castFreeProgram typeMap typeMapFool _ _ _) k = do
            let curTypeMap = PAbst.mergeTypeMap typeMap typeMapFool
            boolProgram <- lift $ zoom (access' #abst Dict.empty) 
                                $ PAbst.abstProg curTypeMap castFreeProgram
            prettyPrint "modelchecking" "Converted Program" boolProgram
            case runExcept (B.tCheck boolProgram) of
                Left (s1,s2,str,ctx) -> do
                    logErrorNS "typecheck" $ Text.pack 
                        $ printf "type mismatch: %s. %s <> %s\n" str (show s1) (show s2)
                    forM_ (zip [(0::Int)..] ctx) $ \(i,t) -> 
                        logErrorNS "typecheck" 
                            $ Text.pack $ printf "Context %d: %s\n" i (show t)
                    throwError $ BooleanError "Abstracted Program is ill-typed"
                Right _ -> return ()
            boolProgram' <- lift $ B.liftRec boolProgram
            prettyPrint "modelchecking" "Recursion lifted program" boolProgram'
            let file_boolean = printf "%s_%d.bool" path k
            liftIO $ writeFile file_boolean $ (++"\n") 
                   $ render $ B.pprintProgram boolProgram'
            mapExceptT (zoom (access' #modelchecking Dict.empty)) 
                $ withExceptT BooleanError $ testTyped file_boolean boolProgram'

        -- refine :: CEGARContext method -> Trace -> m (CEGARContext method)
        refine :: CEGARContext method -> Int -> SExec.Trace -> Maybe Bool -> FilePath -> 
                    ExceptT MainError (FreshIO (Dict CEGAR)) (CEGARContext method)
        refine (FusionContext cegarProgram hContext) k trace _ _ = do
            let rconf = AbstSem.RefineConf { AbstSem.solver = currentSolver
                                           , AbstSem.embedCurCond = embedCurCond conf
                                           , AbstSem.decompose =
                                                predicateGen conf || Hoice /= hornSolver conf }
            refinedProg <- mapExceptT (zoom (access' #abstractsemantics Dict.empty)) 
                      $ withExceptT RefinementFailed 
                      $ AbstSem.refine hContext rconf k trace cegarProgram
            if predicateGen conf 
                then do
                    refinedProg <- lift $ zoom (access' #predicategeneralizer Dict.empty) $
                        PredicateGen.calc hContext convexHullSolver [trace] refinedProg
                    return $ FusionContext refinedProg hContext
                else return $ FusionContext refinedProg hContext

        refine (EagerContext castFreeProgram typeMap typeMapFool hcs
                             rtyAssoc0 rpostAssoc0) k trace isFoolI traceFile = do
            (isFool, clauses, assoc) <- 
                Refine.refineCGen normalizedProgram 
                              traceFile 
                              (contextSensitive conf) 
                              (foolThreshold conf) trace >>= \case
                    Nothing -> throwError (RefinementFailed Horn.NoSolution)
                    Just (isFool,(clauses, assoc)) -> return (isFool, clauses, assoc)
            
            let bf = fromMaybe (foolTraces conf && isFool) isFoolI
            if bf then do
                logInfoNS "refinement" "Fool counterexample refinement"
                let hcs' = clauses
                solution <- mapExceptT lift 
                          $ withExceptT RefinementFailed 
                          $ defaultSolver (Horn.HCCS hcs') k
                let (rtyAssoc,rpostAssoc) = assoc
                let typeMapFool' = Refine.refine fvMap rtyAssoc rpostAssoc solution typeMapFool
                return $ EagerContext castFreeProgram typeMap typeMapFool' hcs rtyAssoc0 rpostAssoc0
            else do
                let hcs' = if accErrTraces conf then clauses ++ hcs else clauses
                let (rtyAssoc,rpostAssoc) = 
                        if accErrTraces conf then assoc <> (rtyAssoc0,rpostAssoc0)
                                             else assoc
                
                solution <- mapExceptT lift 
                          $ withExceptT RefinementFailed 
                          $ currentSolver (Horn.HCCS hcs') k
                --liftIO $ writeFile file_hcs_smt2 $ Horn.renderSMTLib2 (Horn.HCCS hcs')
                let typeMap' 
                     | accErrTraces conf = 
                        Refine.refine fvMap rtyAssoc rpostAssoc solution typeMap0
                     | otherwise         = 
                        Refine.refine fvMap rtyAssoc rpostAssoc solution typeMap
                return $ EagerContext castFreeProgram typeMap' typeMapFool hcs' rtyAssoc rpostAssoc

    let cegarLoop :: Int -> CEGARContext method -> [SExec.Trace] -> 
                        ExceptT MainError (FreshIO (Dict Main)) (CEGARResult ())
        cegarLoop k _ _ | k >= cegarLimit conf = throwError CEGARLimitExceeded
        cegarLoop k cegarContext traces = do
            update $ access' #cycles 0 %~ succ
            res <- mapExceptT (zoom (access' #cegar IM.empty 
                                    . at k 
                                    . non Dict.empty)) $ 
                mc cegarContext k >>= 
                    maybe (return Safe) 
                          (\trace -> measure #refine $ do
                        when (elem trace traces) $ throwError $ OtherError "No progress"
                        let traceFile = printf "%s_%d.trace.dot" path k
                        (trace,isFoolI) <- 
                            if interactive conf 
                                then Refine.interactiveCEGen normalizedProgram traceFile trace
                                else return (trace, Nothing)
                        (Refine . (,trace) <$> refine cegarContext k trace isFoolI traceFile)
                            `catchError` (\case
                                err@(RefinementFailed _) -> do
                                    (_, log, _compTree) <- 
                                        SExec.symbolicExec normalizedProgram trace
                                    let cs = map SExec.fromSValue $ SExec.logCnstr log
                                    isFeasible <- liftIO $ SMT.sat cs
                                    if isFeasible
                                        then return Unsafe
                                        else throwError err
                                err -> throwError err))
            case res of
                Safe   -> do
                    update (access #result ?~ "Safe")
                    Safe <$ logInfoNS "result" "Safe"
                Unsafe -> do
                    update (access #result ?~ "Unsafe")
                    Unsafe <$ logInfoNS "result" "Unsafe" 
                Refine (cegarContext', trace) ->
                    cegarLoop (k+1) cegarContext' (trace:traces)
    
    case cegarMethod conf of
        AbstSemantics -> do
            hContext <- liftIO HFormula.newContext
            unliftedProgram <- IncSat.unliftRec normalizedProgram
            cegarProgram <- liftIO $ CEGAR.convert hContext typeMap0 unliftedProgram
            cegarLoop 0 (FusionContext cegarProgram hContext) []
        DepType -> 
            cegarLoop 0 (EagerContext normalizedProgram typeMap0 typeMap0 [] [] []) []