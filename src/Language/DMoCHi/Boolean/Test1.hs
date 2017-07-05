module Language.DMoCHi.Boolean.Test1 where
import Language.DMoCHi.Boolean.Parser.Typed hiding(Parser)
import qualified Language.DMoCHi.Boolean.Syntax.Typed as Typed
import Language.DMoCHi.Boolean.PrettyPrint.Typed
import Language.DMoCHi.Common.Util
import Language.DMoCHi.Common.Id
import Text.PrettyPrint(render)
import Control.Monad.Except
import Language.DMoCHi.Boolean.Test(test,testTyped)
import Text.Printf
import Options.Applicative

data Mode = Typed | UnTyped
data Config = Config { mode :: Mode
                     , arg  :: FilePath } 

config :: Parser Config
config = Config <$> (flag UnTyped Typed ( long "typed" 
                                        <> short 't'
                                        <> help "enable typed model checking"))
                <*> (argument str (metavar "FILE"))


main :: IO ()
main = do
    let opts = info (helper <*> config)
                    (fullDesc <> progDesc "Check the safety for boolena programs"
                              <> header "hiboch - Higher-order Boolean Model Checker")
    conf <- liftIO $ execParser opts
    let path = arg conf

    runFreshIO defaultLogger $ measure $(logKey "Elapsed Time") $ do
        res <- runExceptT $ do
            p <- withExceptT show $ ExceptT $ liftIO $ parseFile path
            liftIO $ putStrLn $ render $ pprintProgram p
            let s_boolean_program = Typed.size p
            case runExcept (Typed.tCheck p) of
                Left (s1,s2,str,ctx) -> do 
                    liftIO $ do
                        printf "type mismatch: %s. %s <> %s\n" str (show s1) (show s2)
                        forM_ (zip [(0::Int)..] ctx) $ \(i,t) -> do
                            printf "Context %d: %s\n" i (show t)
                    throwError "Input Program is ill-typed!"
                Right _ -> return ()
            case mode conf of
                Typed   -> testTyped path p
                UnTyped -> test path (Typed.toUnTyped p)
            liftIO $ printf "\tBoolean Program Size  : %5d\n" s_boolean_program
        case res of
            Left err -> liftIO $ putStrLn err
            Right r -> liftIO $ print r
