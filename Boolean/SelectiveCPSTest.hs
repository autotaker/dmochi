import System.Environment
import Text.Printf
import Boolean.Parser.Typed
import Boolean.PrettyPrint.Typed
import Text.PrettyPrint(render)
import Boolean.Syntax.Typed(tCheck)
import Boolean.HORS2
import Boolean.PrettyPrint.HORS(pprintHORS)
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
                hors <- toHORS p
                cps1 <- CPS.selectiveCPS p 
                cps2 <- CPS.elimTupleP cps1
                liftIO $ putStrLn $ render $ pprintHORS hors
                liftIO $ writeFile (path++".hrs") $ (++"\n") $ render $ pprintHORS hors
                liftIO $ putStrLn $ render $ CPS.pprintProgram cps1
                liftIO $ putStrLn ""
                liftIO $ putStrLn $ render $ CPS.pprintProgram cps2
                withExceptT show $ CPS.tCheck cps2
            case res of
                Left err -> putStrLn err
                Right r -> print r
        _ -> putStrLn "Please specify input file."
