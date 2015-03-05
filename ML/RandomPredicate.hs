module ML.RandomPredicate where

import ML.Syntax.UnTyped
import System.Random
import Control.Monad
import Control.Monad.Reader
import Control.Applicative
import Id

data Param = Param { pSize :: Int
                   , pConst :: Int
                   , pCount :: Int }

defaultParam :: Param
defaultParam = Param 2 10 2
addRandomPredicatesDef :: (MonadIO m,MonadId m,Applicative m) => Program -> m Program
addRandomPredicatesDef = addRandomPredicates defaultParam

addRandomPredicates :: (MonadIO m,MonadId m,Applicative m) => Param -> Program -> m Program
addRandomPredicates param (Program fs t0) = runReaderT doit param where
    doit = do
        fs' <- forM fs $ \(x,pty,e) -> (,,) x <$> convertP pty <*> convertE e
        t0' <- convertE t0
        return $ Program fs' t0'

convertP :: (MonadIO m,MonadId m,Applicative m) => PType -> ReaderT Param m PType
convertP = go [] where
    go vs (PInt ps) = do
        count <- pCount <$> ask
        qs <- replicateM count $ do
            r <- freshId "r"
            q <- randomGen ((Var r):vs) 
            return (r,q)
        return $ PInt $ ps ++ qs
    go _ (PBool ps) = return (PBool ps)
    go vs (PPair ty_f (x,ty_s)) = do
        ty_f' <- go vs ty_f
        let vs' = decompose (Var x) ty_f ++ vs
        ty_s' <- go vs' ty_s
        return $ PPair ty_f' (x,ty_s')
    go vs (PFun ty_x (x,ty_r)) = do
        ty_x' <- go vs ty_x
        let vs' = decompose (Var x) ty_x ++ vs
        ty_r' <- go vs' ty_r
        return $ PFun ty_x' (x,ty_r')

    decompose :: Value -> PType -> [Value]
    decompose v (PInt _) = return v
    decompose v (PPair t1 (_,t2)) = decompose (Op $ OpFst v) t1 
                                 <|> decompose (Op $ OpSnd v) t2
    decompose _ _ = empty
        

genCoefficient :: (MonadIO m,Functor m) => ReaderT Param m Integer
genCoefficient = do
    s <- pConst <$> ask
    fromIntegral <$> liftIO (randomRIO (-s,s))

randomGen :: (MonadIO m,Functor m) => [Value] -> ReaderT Param m Value
randomGen vs = do
    param <- ask 
    c <- genCoefficient
    s <- liftIO $ randomRIO (0,pSize param)
    xs <- replicateM s $ do
        i <- liftIO $ randomRIO (0,length vs-1)
        return $ vs !! i
    let z = foldl (\acc v -> Op $ OpAdd acc v) (CInt 0) xs
    return $ Op $ OpLte z (CInt c)

convertE :: (MonadId m,MonadIO m) => Exp -> ReaderT Param m Exp
convertE e = return e

