import System.Environment
import Boolean.Parser.Typed
import Boolean.Alpha
import Boolean.Flow hiding(Context)
import Boolean.SortCheck
import Boolean.Syntax
import qualified Boolean.Syntax.Typed as Typed
import Boolean.PrettyPrint.Typed
import Text.PrettyPrint(render)
import Control.Monad.Except
import qualified Data.Map as M
import Boolean.Test(test)
import Text.Printf
import Data.Time

main :: IO ()
main = do
    args <- getArgs
    case args of
        [path] -> do
            res <- runExceptT $ do
                p <- withExceptT show $ ExceptT $ parseFile path
                liftIO $ putStrLn $ render $ pprintProgram p
                let p' = Typed.toUnTyped p 
                    f t = fromRational (toRational t) :: Double
                t_model_checking_begin <- liftIO $ getCurrentTime
                test path $ Typed.toUnTyped p
                t_model_checking_end <- liftIO $ getCurrentTime
                let s_boolean_program = size p'
                    t_model_checking = f $ diffUTCTime t_model_checking_end t_model_checking_begin
                liftIO $ do
                    printf "\tBoolean Program Size  : %5d\n" s_boolean_program
                    printf "\tModel Checking    : %7.3f sec\n" t_model_checking
            case res of
                Left err -> putStrLn err
                Right r -> print r
        _ -> putStrLn "Please specify input file."
