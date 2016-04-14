{-# LANGUAGE BangPatterns #-}
module Language.DMoCHi.ML.SMT(sat,abst,fromBDD) where

import Language.DMoCHi.ML.Syntax.Typed
import Z3.Monad
import Control.Monad.IO.Class
import Control.Monad
import Data.Function(on)
import qualified Data.HashTable.IO as HT
import Data.Hashable
import Data.IORef

data IValue = Func | ASTValue AST | IPair IValue IValue

toIValue :: MonadZ3 z3 => Value -> z3 IValue
toIValue (Var x) = case getType x of
    TInt -> do
        y <- mkStringSymbol (name x)
        s <- mkIntSort
        v <- mkConst y s
        return $ ASTValue v
    TBool -> do
        y <- mkStringSymbol (name x)
        s <- mkBoolSort
        v <- mkConst y s
        return $ ASTValue v
    TFun _ _ -> return Func
    TPair t1 t2 -> do
        iv1 <- toIValue (Var $ Id t1 (name x ++ ".fst"))
        iv2 <- toIValue (Var $ Id t2 (name x ++ ".snd"))
        return $ IPair iv1 iv2
toIValue (CInt i) = ASTValue <$> mkInteger i
toIValue (CBool b) = ASTValue <$> mkBool b
toIValue (Pair v1 v2) = IPair <$> toIValue v1 <*> toIValue v2
toIValue (Op op) = case op of
    OpAdd v1 v2 -> do
        ASTValue v1' <- toIValue v1
        ASTValue v2' <- toIValue v2
        ASTValue <$> mkAdd [v1', v2']
    OpSub v1 v2 -> do
        ASTValue v1' <- toIValue v1
        ASTValue v2' <- toIValue v2
        ASTValue <$> mkSub [v1', v2']
    OpEq v1 v2 -> do
        iv1 <- toIValue v1
        iv2 <- toIValue v2
        mkEqIValue iv1 iv2
    OpLt v1 v2 -> do
        ASTValue v1' <- toIValue v1
        ASTValue v2' <- toIValue v2
        ASTValue <$> mkLt v1' v2'
    OpLte v1 v2 -> do
        ASTValue v1' <- toIValue v1
        ASTValue v2' <- toIValue v2
        ASTValue <$> mkLe v1' v2'
    OpAnd v1 v2 -> do
        ASTValue v1' <- toIValue v1
        ASTValue v2' <- toIValue v2
        ASTValue <$> mkAnd [v1',v2']
    OpOr v1 v2 -> do
        ASTValue v1' <- toIValue v1
        ASTValue v2' <- toIValue v2
        ASTValue <$> mkOr [v1',v2']
    OpNot v1 -> do
        ASTValue v1' <- toIValue v1
        ASTValue <$> mkNot v1'
    OpFst _ v -> do
        IPair iv1 _ <- toIValue v
        return iv1
    OpSnd _ v -> do
        IPair _ iv2 <- toIValue v
        return iv2

mkEqIValue :: MonadZ3 z3 => IValue -> IValue -> z3 IValue
mkEqIValue iv1 iv2 = ASTValue <$> go iv1 iv2
    where
    go Func Func = mkTrue
    go (ASTValue v1) (ASTValue v2) = mkEq v1 v2
    go (IPair v1 v2) (IPair v3 v4) = do
        b1 <- go v1 v3
        b2 <- go v2 v4
        mkAnd [b1,b2]

mkAnd' :: MonadZ3 z3 => [AST] -> z3 AST
mkAnd' [] = mkTrue
mkAnd' l  = mkAnd l

sat :: [Value] -> IO Bool
sat vs = evalZ3 $ do
    ivs <- mapM toIValue vs
    assert =<< mkAnd' [ v | ASTValue v <- ivs]
    (res, model) <- getModel
    liftIO $ print res
    case res of
        Sat -> do 
            case model of 
                Just m -> showModel m >>= liftIO . putStrLn
                Nothing -> return ()
            return True
        Unsat -> return False
        Undef -> return True

data BDDNode a = Leaf !Int !Bool
               | Node !Int a (BDDNode a) (BDDNode a)
data BDDHashKey = KeyLeaf !Bool
                | KeyNode !Int !Int !Int
                deriving(Eq,Ord)

bDDNodeId :: BDDNode a -> Int
bDDNodeId (Leaf i _) = i
bDDNodeId (Node i _ _ _) = i

hiChild :: BDDNode a -> BDDNode a
hiChild (Node _ _ hi _) = hi
hiChild _ = error "hiChild: Node expected"

lowChild :: BDDNode a -> BDDNode a
lowChild (Node _ _ _ lo) = lo
lowChild _ = error "lowChild: Node expected"

instance Eq (BDDNode a) where
    (==) = (==) `on` bDDNodeId

instance Hashable BDDHashKey where
    salt `hashWithSalt` (KeyLeaf b) = 
        salt `hashWithSalt` (1 :: Int) `hashWithSalt` b
    salt `hashWithSalt` (KeyNode v l r) = 
        salt  `hashWithSalt` (2 :: Int) 
              `hashWithSalt` v
              `hashWithSalt` l
              `hashWithSalt` r

fromBDD :: BDDNode a -> [[(a,Bool)]]
fromBDD (Leaf _ b) = guard b >> return []
fromBDD (Node _ v hi lo) | hi == lo = fromBDD hi
                         | otherwise = 
    map (\l -> (v,True)  : l) (fromBDD hi) ++
    map (\l -> (v,False) : l) (fromBDD lo)

abst :: [Value] -> [Value] -> IO (BDDNode Value)
abst constraints predicates = evalZ3 $ do
    let f (ASTValue v) = v
        f _ = error "Expecting an SMT value"
    assert =<< mkAnd' =<< mapM (toIValue >=> (return . f)) constraints
    z3_predicates  <- mapM (toIValue >=> (return . f)) predicates
    hashTable <- liftIO $ HT.new :: Z3 (HT.BasicHashTable BDDHashKey (BDDNode Value))
    nodeCounter <- liftIO $ newIORef (0 :: Int)
    let mkPVar d = do
            x <- mkStringSymbol $ "p_" ++ show d
            s <- mkBoolSort
            mkConst x s
        bDDConst :: Bool -> IO (BDDNode Value)
        bDDConst b = do
            let key = KeyLeaf b
            r <- HT.lookup hashTable key
            case r of
                Just v -> return v
                Nothing -> do
                    i <- readIORef nodeCounter
                    writeIORef nodeCounter $! i+1
                    let val = Leaf i b
                    HT.insert hashTable key val
                    return val
        bDDNode :: Int -> Value -> (BDDNode Value) -> (BDDNode Value) -> IO (BDDNode Value)
        bDDNode varId v hi low = do
            let key = KeyNode varId (bDDNodeId hi) (bDDNodeId low)
            r <- HT.lookup hashTable key
            case r of
                Just v -> return v
                Nothing -> do
                    i <- readIORef nodeCounter
                    writeIORef nodeCounter $! i+1
                    let val = Node i v hi low
                    HT.insert hashTable key val
                    return val
            

    let search :: [(Value,AST)] -> Int -> Z3 (BDDNode Value)
        search ((v,z3_v):l) !d = do
            -- assumption: the current assumptions are consistent
            push
            solverAssertAndTrack z3_v =<< mkPVar d
            res <- check
            case res of
                Unsat -> do
                    liftIO $ print d
                    getUnsatCore >>= mapM astToString >>= liftIO . print
                    pop 1
                    -- the following assertion must be redundant
                    -- because Unsat(z3_v) means that NOT(z3_v) is valid
                    -- assert =<< mkNot z3_v
                    push
                    low <- search l (d+1)
                    hi <- liftIO $ bDDConst False
                    pop 1
                    liftIO $ bDDNode d v hi low
                _  -> do -- regard Undef as Sat
                    hi <- search l (d+1)
                    pop 1
                    push
                    mkNot z3_v >>= (\z3_nv -> solverAssertAndTrack z3_nv =<< mkPVar (-d))
                    res_not <- check
                    case res_not of
                        Unsat -> do
                            liftIO $ print d
                            getUnsatCore >>= mapM astToString >>= liftIO . print
                            pop 1
                            low <- liftIO $ bDDConst False
                            liftIO $ bDDNode d v hi low
                        _ -> do -- Regard undefined as satifiable
                            low <- search l (d+1)
                            pop 1
                            liftIO $ bDDNode d v hi low
        search [] _ = liftIO $ bDDConst True
    res <- check
    case res of
        Unsat -> liftIO $ bDDConst False
        _ -> search (zip predicates z3_predicates) 0
