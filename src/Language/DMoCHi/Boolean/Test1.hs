module Language.DMoCHi.Boolean.Test1 where
import System.Environment
import Language.DMoCHi.Boolean.Parser.Typed
import Language.DMoCHi.Boolean.Alpha
import qualified Language.DMoCHi.Boolean.Flow2 as Flow
import Language.DMoCHi.Boolean.SortCheck
import Language.DMoCHi.Boolean.Syntax
import Language.DMoCHi.Common.Id
import qualified Language.DMoCHi.Boolean.Syntax.Typed as Typed
import qualified Language.DMoCHi.Boolean.Type3 as Sat
import Language.DMoCHi.Boolean.PrettyPrint.Typed
import Text.PrettyPrint(render)
import Control.Monad.Except
import qualified Data.Map as M
import Language.DMoCHi.Boolean.Test(test)
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
                case runExcept (Typed.tCheck p) of
                    Left (s1,s2,str,ctx) -> do 
                        liftIO $ do
                            printf "type mismatch: %s. %s <> %s\n" str (show s1) (show s2)
                            forM_ (zip [(0::Int)..] ctx) $ \(i,t) -> do
                                printf "Context %d: %s\n" i (show t)
                        throwError "Input Program is ill-typed!"
                    Right _ -> return ()
                let graph_path = path ++ ".typed.dot"
                let p_flow = Flow.buildGraph p
                liftIO $ writeFile graph_path $ Flow.ppGraph (Flow.termTable p_flow) (Flow.cfg p_flow)
                liftIO $ Sat.saturate p_flow >>= \b -> do
                        printf "Typed saturation result %s\n" (show b)

{-
                let p' = Typed.toUnTyped p 
                let f t = fromRational (toRational t) :: Double
                t_model_checking_begin <- liftIO $ getCurrentTime
                test path p'
                t_model_checking_end <- liftIO $ getCurrentTime
                let s_boolean_program = size p'
                    t_model_checking = f $ diffUTCTime t_model_checking_end t_model_checking_begin
                liftIO $ do
                    printf "\tBoolean Program Size  : %5d\n" s_boolean_program
                    printf "\tModel Checking    : %7.3f sec\n" t_model_checking
                    -}
            case res of
                Left err -> putStrLn err
                Right r -> print r
        _ -> putStrLn "Please specify input file."
