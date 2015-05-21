import System.Environment
import Text.Printf
import Boolean.Parser.Typed
import Boolean.PrettyPrint.Typed
import Text.PrettyPrint(render)
import Boolean.Syntax.Typed(tCheck)
--import Boolean.PrettyPrint.HORS(pprintHORS)
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
                cps <- CPS.selectiveCPS p
                liftIO $ print cps
                withExceptT show $ CPS.tCheck cps
            case res of
                Left err -> putStrLn err
                Right r -> print r
        _ -> putStrLn "Please specify input file."
