import System.Environment
import Parser.MoCHi
import Alpha
import Flow hiding(Context)
import SortCheck
import Type
import Syntax
import Control.Monad.Except
import qualified Data.Map as M


--test :: Program -> ExceptT String IO [TType]
test input = do
    (p,syms) <- ExceptT $ return $ alphaConversion input
    liftIO $ mapM print (definitions p)
    --liftIO $ print p
    senv <- ExceptT $ return $ sortCheck p (map fst syms)
    liftIO $ forM_ (M.assocs senv) print
    let env = M.fromList [ (x,(s,t)) | (x,t) <- syms, let s = senv M.! x]
    let ((lbl,edges),env') = buildGraph env p
    let g@(x,_,y) = reduce1 lbl edges env'
    liftIO $ putStrLn $ ppGraph (fmap (\t -> case t of
        Just x -> x
        Nothing -> V "") y) x
    let l = saturate p g
    let go (x:y:_) | x == y = liftIO (printContext x) >> return x
        go (x:xs) = liftIO (printContext x) >> go xs
        go _ = undefined
    c <- go l
    return $ saturateTerm (flowEnv c) (symEnv c) (mainTerm p)

main :: IO ()
main = do
    args <- getArgs
    case args of
        [path] -> do
            res <- runExceptT $ do
                p <- withExceptT show $ ExceptT $ parseFile path
                test p
            case res of
                Left err -> putStrLn err
                Right r -> print r
        _ -> putStrLn "Please specify input file."
