import System.Environment
import Text.Printf
import Boolean.Parser.Typed
import Boolean.PrettyPrint.Typed
import Text.PrettyPrint(render)
import Boolean.Syntax.Typed(tCheck)
import Boolean.HORS2
import Boolean.PrettyPrint.HORS(pprintHORS,SyntaxParam(..))
import qualified Boolean.PrettyPrint.SelectiveCPS as CPS
import Control.Monad.Except
import qualified Boolean.SelectiveCPS as CPS
import Id

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
