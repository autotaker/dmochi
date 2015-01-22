import System.Environment
import System.IO
import Text.Printf
import ML.Syntax.UnTyped
import ML.Parser
import qualified Boolean.Syntax as B
--import ML.Convert
import ML.PrettyPrint.UnTyped
import Boolean.Test 
import Control.Monad.Except

main :: IO ()
main = do
    pname <- getProgName
    args <- getArgs
    if length args == 0 then
        hPrintf stderr "usage: %s file\n" pname
    else do
        let path = head args
        parseRes <- parseProgramFromFile path
        case parseRes of
            Left err -> hPrintf stderr "parse failed:%s\n" (show err)
            Right p -> do
                printProgram p
                {-
                p' <- convert p
                B.printProgram p'
                r <- runExceptT (test p')
                case r of
                    Left err -> putStrLn err
                    Right r -> print r
                    -}

        

