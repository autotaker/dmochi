{-# LANGUAGE BangPatterns, GADTs #-}
module Language.DMoCHi.ML.SMT(sat,abst,fromBDD,BDDNode(..), mkUMul, mkUDiv,
                              getSMTCount, resetSMTCount,IValue(..), toIValueId, mkEqIValue) where

import Language.DMoCHi.ML.Syntax.PNormal hiding(mkApp)
import Z3.Monad 
import Control.Monad.IO.Class
import Control.Monad
import Data.Function(on)
import qualified Data.HashTable.IO as HT
import Data.Hashable
import Data.IORef
import Debug.Trace
import System.IO.Unsafe

{-# NOINLINE smtCounter #-}
smtCounter :: IORef Int
smtCounter = unsafePerformIO (newIORef 0)


data IValue = Func | ASTValue AST | IPair IValue IValue deriving(Show)

getSMTCount :: IO Int
getSMTCount = readIORef smtCounter

resetSMTCount :: IO ()
resetSMTCount = writeIORef smtCounter 0

toIValue :: MonadZ3 z3 => Value -> z3 IValue
toIValue v = case valueView v of
    VAtom av -> toIValueA av
    VOther SLambda _ ->return Func
    VOther SPair (v1, v2) -> IPair <$> toIValue v1 <*> toIValue v2

mkUDiv :: MonadZ3 z3 => IValue -> IValue -> z3 IValue
mkUDiv (ASTValue v1) (ASTValue v2) = ASTValue <$> mkDiv v1 v2
mkUDiv _ _ = error "unexpected pattern"

{- the first boolean argument represents that this is scalar or not -}
mkUMul :: MonadZ3 z3 => Bool -> IValue -> IValue -> z3 IValue
mkUMul _ (ASTValue v1) (ASTValue v2) = ASTValue <$> mkMul [v1, v2]
mkUMul _ _ _ = error "unexpected pattern"
    

toIValueId :: MonadZ3 z3 => Type -> String -> z3 IValue
toIValueId TInt x = do
    y <- mkStringSymbol x
    s <- mkIntSort
    v <- mkConst y s
    return $ ASTValue v
toIValueId TBool x = do
    y <- mkStringSymbol x
    s <- mkBoolSort
    v <- mkConst y s
    return $ ASTValue v
toIValueId (TFun _ _) _ = return Func
toIValueId (TPair t1 t2) x = do
    iv1 <- toIValueId t1 (x ++ ".fst")
    iv2 <- toIValueId t2 (x ++ ".snd")
    return $ IPair iv1 iv2
    
toIValueA :: MonadZ3 z3 => Atom -> z3 IValue
toIValueA (Atom l arg sty) = case (l,arg) of
    (SVar,(TId _ name_x)) -> toIValueId sty (show name_x)
    (SLiteral, CInt i)  -> ASTValue <$> mkInteger i
    (SLiteral, CBool b) -> ASTValue <$> mkBool b
    (SLiteral, CUnit) -> error "toIValueA: unexpected"
    (SBinary, BinArg op v1 v2) -> do
        iv1 <- toIValueA v1
        iv2 <- toIValueA v2
        let (ASTValue v1') = iv1
            (ASTValue v2') = iv2
        case op of
            SAdd -> ASTValue <$> mkAdd [v1',v2']
            SSub -> ASTValue <$> mkSub [v1',v2']
            SMul -> case (v1, v2) of
                (Atom SLiteral (CInt _) _, _) -> mkUMul True iv1 iv2
                (_, Atom SLiteral (CInt _) _) -> mkUMul True iv1 iv2
                _ -> mkUMul False iv1 iv2
            SDiv -> mkUDiv iv1 iv2
            SEq -> mkEqIValue iv1 iv2
            SLt -> ASTValue <$> mkLt v1' v2'
            SLte -> ASTValue <$> mkLe v1' v2'
            SAnd -> ASTValue <$> mkAnd [v1', v2']
            SOr  -> ASTValue <$> mkOr  [v1', v2']
    (SUnary, UniArg SNot v) -> do
        ASTValue v' <- toIValueA v
        ASTValue <$> mkNot v'
    (SUnary, UniArg SNeg v) -> do
        ASTValue v' <- toIValueA v
        ASTValue <$> mkUnaryMinus v'
    (SUnary, UniArg SFst v) -> do
        IPair iv1 _ <- toIValueA v
        return iv1
    (SUnary, UniArg SSnd v) -> do
        IPair _ iv2 <- toIValueA v
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
    go v1 v2 = traceShow ("mkEqIValue",v1,v2) undefined


mkAnd' :: MonadZ3 z3 => [AST] -> z3 AST
mkAnd' [] = mkTrue
mkAnd' l  = mkAnd l

sat :: [Value] -> IO Bool
sat vs = evalZ3 $ do
    ivs <- mapM toIValue vs
    {-
    forM_ ivs $ \(ASTValue v) -> do
        astToString v >>= liftIO . putStrLn
    -}
    assert =<< mkAnd' [ v | ASTValue v <- ivs]
    (res, _model) <- getModel
    -- liftIO $ print res
    case res of
        Sat -> return True
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

{-
hiChild :: BDDNode a -> BDDNode a
hiChild (Node _ _ hi _) = hi
hiChild _ = error "hiChild: Node expected"

lowChild :: BDDNode a -> BDDNode a
lowChild (Node _ _ _ lo) = lo
lowChild _ = error "lowChild: Node expected"
-}

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

abst :: [Atom] -> [Atom] -> IO (BDDNode Atom)
abst constraints predicates = evalZ3 $ do
    let f (ASTValue v) = v
        f _ = error "Expecting an SMT value"
    assert =<< mkAnd' =<< mapM (toIValueA >=> (return . f)) constraints
    z3_predicates  <- mapM (toIValueA >=> (return . f)) predicates
    hashTable <- liftIO $ HT.new :: Z3 (HT.BasicHashTable BDDHashKey (BDDNode Atom))
    nodeCounter <- liftIO $ newIORef (0 :: Int)
    let mkPVar d = do
            x <- mkStringSymbol $ "p_" ++ show d
            s <- mkBoolSort
            mkConst x s
        bDDConst :: Bool -> IO (BDDNode Atom)
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
        bDDNode :: Int -> Atom -> (BDDNode Atom) -> (BDDNode Atom) -> IO (BDDNode Atom)
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
    let incrCounter = liftIO $ modifyIORef' smtCounter succ

    let search :: [(Atom,AST)] -> Int -> Z3 (BDDNode Atom)
        search ((v,z3_v):l) !d = do
            -- assumption: the current assumptions are consistent
            push
            solverAssertAndTrack z3_v =<< mkPVar d
            res <- check
            incrCounter
            case res of
                Unsat -> do
                    -- liftIO $ print d
                    -- getUnsatCore >>= mapM astToString >>= liftIO . print
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
                    incrCounter
                    case res_not of
                        Unsat -> do
                            -- liftIO $ print d
                            -- getUnsatCore >>= mapM astToString >>= liftIO . print
                            pop 1
                            low <- liftIO $ bDDConst False
                            liftIO $ bDDNode d v hi low
                        _ -> do -- Regard undefined as satifiable
                            low <- search l (d+1)
                            pop 1
                            liftIO $ bDDNode d v hi low
        search [] _ = liftIO $ bDDConst True
    res <- check
    incrCounter
    case res of
        Unsat -> liftIO $ bDDConst False
        _ -> search (zip predicates z3_predicates) 0
