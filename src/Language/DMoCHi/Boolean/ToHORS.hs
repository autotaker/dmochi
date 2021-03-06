module Language.DMoCHi.Boolean.ToHORS(run) where
import System.Environment
import Text.Printf
import Language.DMoCHi.Boolean.Parser.Typed
import Language.DMoCHi.Boolean.PrettyPrint.Typed
import Text.PrettyPrint(render)
import Language.DMoCHi.Boolean.PrettyPrint.HORS(pprintHORS,SyntaxParam(..))
import Control.Monad.Except
import qualified Language.DMoCHi.Boolean.HORS   as HORS
import qualified Language.DMoCHi.Boolean.HORS2  as HORS2
import Language.DMoCHi.Common.Id
import System.IO

doit :: (MonadId m, MonadIO m, Functor m) => FilePath -> ExceptT String m ()
doit path = do
    p <- withExceptT show $ ExceptT $ liftIO $ parseFile path
    liftIO $ putStrLn $ render $ pprintProgram p
    liftIO $ printf "--CPS--\n"
    hors1 <- HORS.toHORS p
    hors2 <- HORS2.toHORS p
    hors3 <- HORS2.toHORSChurch p
    let path1 = path ++ ".naive.hrs"
    let path2_horsat = path ++ ".selective.horsat.hrs"
    let path2_preface = path ++ ".selective.preface.hrs"
    let path3 = path ++ ".selective.church.hrs"
    liftIO $ do 
        let f param hors = (++"\n") $ render $ pprintHORS param hors
        writeFile path1 $ f Horsat hors1
        writeFile path2_horsat $ f Horsat hors2
        writeFile path2_preface $ f Preface hors2
        writeFile path3 $ f Horsat hors3

run :: IO ()
run = do
    args <- getArgs
    case args of
        [path] -> do
            h <- openFile "/dev/null" WriteMode
            res <- runFreshT $ runExceptT $ doit path

            case res of
                Left err -> putStrLn err
                Right r -> print r
        _ -> putStrLn "Please specify input file."
