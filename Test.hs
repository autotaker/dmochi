import System.Environment
import Text.Parsec.String
import Parser
import Alpha
import Flow hiding(Context)
import SortCheck
import Type
import Syntax
import Control.Monad.Except


test :: Program -> ExceptT String IO [TType]
test input = do
    (p,syms) <- ExceptT $ return $ alphaConversion input
    senv <- ExceptT $ return $ sortCheck p syms
    let ((lbl,edges),env) = buildGraph senv p
    let g = reduce1 lbl edges env
    let l = saturate p g
    let go (x:y:_) | x == y = liftIO (printContext x) >> return x
        go (x:xs) = liftIO (printContext x) >> go xs
    c <- go l
    return $ saturateTerm (flowEnv c) (symEnv c) (mainTerm p)


main :: IO ()
main = do
    args <- getArgs
    case args of
        [path] -> do
            res <- runExceptT $ do
                p <- withExceptT show $ ExceptT $ parse path
                test p
            case res of
                Left err -> putStrLn err
                Right r -> print r
        _ -> return ()
