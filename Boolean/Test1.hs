import System.Environment
import Boolean.Parser.Typed
import Boolean.Alpha
import Boolean.Flow hiding(Context)
import Boolean.SortCheck
import Boolean.Type
import Boolean.Syntax
import qualified Boolean.Syntax.Typed as Typed
import Boolean.PrettyPrint.Typed
import Text.PrettyPrint(render)
import Control.Monad.Except
import qualified Data.Map as M
import Boolean.Test(test)

main :: IO ()
main = do
    args <- getArgs
    case args of
        [path] -> do
            res <- runExceptT $ do
                p <- withExceptT show $ ExceptT $ parseFile path
                liftIO $ putStrLn $ render $ pprintProgram p
                test $ Typed.toUnTyped p
            case res of
                Left err -> putStrLn err
                Right r -> print r
        _ -> putStrLn "Please specify input file."
