module Language.DMoCHi.Boolean.Test where
--import Language.DMoCHi.Boolean.Parser.MoCHi
import Language.DMoCHi.Boolean.Alpha
import Language.DMoCHi.Boolean.Flow hiding(Context)
import Language.DMoCHi.Boolean.SortCheck
import Language.DMoCHi.Boolean.Type2
import qualified Language.DMoCHi.Boolean.Flow2 as Flow2
import qualified Language.DMoCHi.Boolean.Type3 as Sat
import qualified Language.DMoCHi.Boolean.Syntax.Typed as Typed
--import Language.DMoCHi.Boolean.Type
import Language.DMoCHi.Boolean.Syntax
import Control.Monad.Except
import qualified Data.Map as M
import Data.Time
import Text.Printf

measure :: MonadIO m => String -> m a -> m a
measure header doit = do
    let f t = fromRational (toRational t) :: Double
    t_start <- liftIO $ getCurrentTime
    v <- doit
    t_end <- liftIO $ getCurrentTime
    let time = f $ diffUTCTime t_end t_start
    liftIO $ printf "%s: %.5f sec\n" header time
    return v

test :: MonadIO m => FilePath -> Program -> ExceptT String m (Maybe [Bool])
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

testTyped :: MonadIO m => FilePath -> Typed.Program -> ExceptT String m (Maybe [Bool])
testTyped path p = do
    let graph_path = path ++ ".typed.dot"
    p_flow <- measure "0CFA" $ do
        let p_flow = Flow2.buildGraph p
        liftIO $ writeFile graph_path $ Flow2.ppGraph (Flow2.termTable p_flow) (Flow2.cfg p_flow)
        return p_flow
    measure "Saturation" $ do
        b <- liftIO $ Sat.saturate p_flow
        liftIO $ printf "Typed saturation result %s\n" (show b)
        return b
{-
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
        -}
