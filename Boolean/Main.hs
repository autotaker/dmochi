import System.Environment
import Boolean.Parser.Typed
--import Boolean.Alpha
--import Boolean.Flow hiding(Context)
--import Boolean.SortCheck
--import Boolean.Type
--import Boolean.Syntax
import qualified Boolean.Syntax.Typed as Typed
import qualified Boolean.Syntax.TypedSimple as Simple
import qualified Boolean.Flow2 as Flow
import Boolean.PrettyPrint.Typed
import qualified Boolean.PrettyPrint.TypedSimple as Simple
import Text.PrettyPrint(render)
import Data.Array
import Control.Monad.Except
--import qualified Data.Map as M
--import Boolean.Test(test)
import Text.Printf
--import Data.Time
import Id

{-
test :: MonadIO m => FilePath -> Program -> ExceptT String m Bool
test path input = do
    (p,syms) <- ExceptT $ return $ alphaConversion input
    liftIO $ mapM_ print (definitions p)
    --liftIO $ print p
    senv <- ExceptT $ return $ sortCheck p (map fst syms)
    liftIO $ forM_ (M.assocs senv) print
    let env = M.fromList [ (x,(s,t)) | (x,t) <- syms, let s = senv M.! x]
    let ((lbl,edges),env') = buildGraph env p
    let g@(x,_,y) = reduce1 lbl edges env'
    let graph_path = path ++ ".dot"
    liftIO $ writeFile graph_path $ ppGraph (fmap (\t -> case t of
        Just x -> x
        Nothing -> V () "") y) x
    (b,_ctx) <- liftIO $ saturate p g
    return b
    -}

doit :: FilePath -> ExceptT String (FreshT IO) ()
doit path = do
    parseRes <- liftIO $ parseFile path
    typed_program <- case parseRes of
        Left err -> throwError $ show err
        Right p -> return p
    liftIO $ putStrLn "* parsed *"
    liftIO $ putStrLn $ render $ pprintProgram typed_program
    case runExcept (Typed.tCheck typed_program) of
        Left (s1,s2,str,ctx) -> do
            liftIO $ do
                printf "type mismatch: %s. %s <> %s\n" str (show s1) (show s2)
                forM_ (zip [(0::Int)..] ctx) $ \(i,t) -> do
                    printf "Context %d: %s\n" i (show t)
            throwError "failed"
        Right _ -> return ()
    liftIO $ putStrLn "* to_simple *"
    simple_program <- Simple.toSimpleProgram typed_program
    case runExcept (Simple.tCheck simple_program) of
        Left (s1,s2,str) -> do
            liftIO $ printf "type mismatch: %s. %s <> %s\n" str (show s1) (show s2)
            throwError "failed"
        Right _ -> return ()
    liftIO $ putStrLn $ render $ Simple.pprintProgram simple_program

    let graph_path = path ++ ".dot"
    let cfg@(lblTbl, graph, symMap) = Flow.buildGraph simple_program
    liftIO $ writeFile graph_path $ Flow.ppGraph (fmap (\t -> t) lblTbl) graph
    liftIO $ do
        putStrLn "* cfa *"
        forM_ (assocs lblTbl) $ \(i,t) -> printf "%d %s\n" i (show t)
    return ()

main :: IO ()
main = do
    args <- getArgs
    case args of
        [path] -> do
            res <- runFreshT $ runExceptT (doit path)
                {-
                t_model_checking_begin <- liftIO $ getCurrentTime
                test path $ Typed.toUnTyped p
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
