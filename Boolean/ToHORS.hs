import System.Environment
import Text.Printf
import Boolean.Parser.Typed
import Boolean.PrettyPrint.Typed
import Text.PrettyPrint(render)
import Boolean.PrettyPrint.HORS(pprintHORS,SyntaxParam(..))
import Control.Monad.Except
import qualified Boolean.HORS   as B
import Id

main :: IO ()
main = do
    args <- getArgs
    case args of
        [path] -> do
            res <- runFreshT $ runExceptT $ do
                p <- withExceptT show $ ExceptT $ liftIO $ parseFile path
                liftIO $ putStrLn $ render $ pprintProgram p
                liftIO $ printf "--CPS--\n"
                hors <- B.toHORS p
                let file_hors = path ++ ".hrs"
                liftIO $ writeFile file_hors $ (++"\n") $ render $ pprintHORS Horsat hors
            case res of
                Left err -> putStrLn err
                Right r -> print r
        _ -> putStrLn "Please specify input file."
