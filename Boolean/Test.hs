module Boolean.Test(test) where
import System.Environment
import Boolean.Parser.MoCHi
import Boolean.Alpha
import Boolean.Flow hiding(Context)
import Boolean.SortCheck
import Boolean.Type2
import Boolean.Syntax
import Control.Monad.Except
import qualified Data.Map as M

{-
test :: MonadIO m => FilePath -> Program -> ExceptT String m [TType]
test path input = do
    (p,syms) <- ExceptT $ return $ alphaConversion input
    liftIO $ mapM print (definitions p)
    --liftIO $ print p
    senv <- ExceptT $ return $ sortCheck p (map fst syms)
    liftIO $ forM_ (M.assocs senv) print
    let env = M.fromList [ (x,(s,t)) | (x,t) <- syms, let s = senv M.! x]
    let ((lbl,edges),env') = buildGraph env p
    let g@(x,_,y) = reduce1 lbl edges env'
    let graph_path = path ++ ".dot"
    liftIO $ writeFile graph_path $ ppGraph (fmap (\t -> case t of
        Just x -> x
        Nothing -> V "") y) x
    let l = saturate p g
    let go (x:xs) | TFail `elem` saturateTerm (flowEnv x) (symEnv x) (mainTerm p) = return x
        go (x:y:_) | x == y = liftIO (printContext x) >> return x
        go (x:xs) = liftIO (printContext x) >> go xs
        go _ = undefined
    c <- go l
    return $ saturateTerm (flowEnv c) (symEnv c) (mainTerm p)
-}

test :: MonadIO m => FilePath -> Program -> ExceptT String m Bool
test path input = do
    (p,syms) <- ExceptT $ return $ alphaConversion input
    liftIO $ mapM print (definitions p)
    --liftIO $ print p
    senv <- ExceptT $ return $ sortCheck p (map fst syms)
    liftIO $ forM_ (M.assocs senv) print
    let env = M.fromList [ (x,(s,t)) | (x,t) <- syms, let s = senv M.! x]
    let ((lbl,edges),env') = buildGraph env p
    let g@(x,_,y) = reduce1 lbl edges env'
    let graph_path = path ++ ".dot"
    liftIO $ writeFile graph_path $ ppGraph (fmap (\t -> case t of
        Just x -> x
        Nothing -> V "") y) x
    (b,_ctx) <- liftIO $ saturate p g
    return b

main :: IO ()
main = do
    args <- getArgs
    case args of
        [path] -> do
            res <- runExceptT $ do
                p <- withExceptT show $ ExceptT $ parseFile path
                test path p
            case res of
                Left err -> putStrLn err
                Right r -> print r
        _ -> putStrLn "Please specify input file."
