import System.Environment
import Text.Printf
import Language.DMoCHi.Boolean.Parser.Typed
import Language.DMoCHi.Boolean.PrettyPrint.Typed
import Text.PrettyPrint(render)
import Language.DMoCHi.Boolean.Syntax.Typed(tCheck)
import Language.DMoCHi.Boolean.HORS2
import Language.DMoCHi.Boolean.PrettyPrint.HORS(pprintHORS,SyntaxParam(..))
import qualified Language.DMoCHi.Boolean.PrettyPrint.SelectiveCPS as CPS
import Control.Monad.Except
import qualified Language.DMoCHi.Boolean.SelectiveCPS as CPS
import Language.DMoCHi.Common.Id

main :: IO ()
main = do
    args <- getArgs
    case args of
        [path] -> do
            res <- runFreshT $ runExceptT $ do
                p <- withExceptT show $ ExceptT $ liftIO $ parseFile path
                withExceptT show $ ExceptT $ return $ runExcept (tCheck p)
                liftIO $ putStrLn $ render $ pprintProgram p
                liftIO $ printf "--Selective CPS--\n"
--                cps1 <- CPS.selectiveCPS p 
--                liftIO $ putStrLn $ render $ CPS.pprintProgram cps1
--                cps2 <- CPS.elimTupleP cps1
--                withExceptT show $ CPS.tCheck cps2
                --hors <- toHORS p
                hors <- toHORSChurch p
                liftIO $ putStrLn $ render $ pprintHORS Horsat hors
                liftIO $ writeFile (path++".horsat.hrs") $ (++"\n") $ render $ pprintHORS Horsat hors
                liftIO $ writeFile (path++".preface.hrs") $ (++"\n") $ render $ pprintHORS Preface hors
            case res of
                Left err -> putStrLn err
                Right r -> print r
        _ -> putStrLn "Please specify input file."
