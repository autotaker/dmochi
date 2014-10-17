import System.Environment
import Text.Parsec.String
import Parser
import Alpha

main :: IO ()
main = do
    args <- getArgs
    case args of
        [path] -> do
            p <- parseFromFile program path
            print $ fmap alphaConversion p
        _ -> return ()
