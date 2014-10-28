{-# LANGUAGE BangPatterns,TupleSections #-}
module Flow where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad
import Control.Monad.State
import Control.Applicative
import Data.STRef
import Data.Maybe
import Syntax
import Sort
import Data.Hashable
import qualified Data.HashTable.Class as HT
import Data.HashTable.ST.Basic (HashTable)
import Control.Monad.ST
import Data.Array.Unboxed
import Data.Array.ST
import Control.Arrow(first,second)
import Data.Function
import Debug.Trace

import Language.Dot hiding(Id)

newtype VarId = VarId { getId :: Int }deriving(Ord,Eq)
instance Show VarId where
    show = show . getId

type Id = Int

data FlowTerm = Var Id !VarId
              | App Id !FlowTerm !FlowTerm
              | Abst Id !FlowTerm !FlowTerm 
              | Br    Id ![FlowTerm]
              | Tuple Id ![FlowTerm] [Term] -- for memo
              | Proj Id !Int !FlowTerm
              | Dom Id !FlowTerm 
              | Cod Id !FlowTerm
              deriving(Show)

data FlowKey = KVar VarId
             | KApp Int Int
             | KAbst Int Int
             | KBr ![Id]
             | KTuple ![Id]
             | KProj !Int !Id
             | KDom !Id
             | KCod !Id
             deriving(Eq)

instance Hashable FlowKey where
    hashWithSalt s (KVar i) = s `hashWithSalt` (1::Int) `hashWithSalt` getId i
    hashWithSalt s (KApp i1 i2) = s `hashWithSalt` (2::Int) 
                                    `hashWithSalt` i1 
                                    `hashWithSalt` i2
    hashWithSalt s (KAbst i1 i2) = s `hashWithSalt`(3::Int) 
                                     `hashWithSalt` i1
                                     `hashWithSalt` i2
    hashWithSalt s (KBr is) = s `hashWithSalt` (4::Int) `hashWithSalt` is
    hashWithSalt s (KTuple is) = s `hashWithSalt` (5::Int) `hashWithSalt` is
    hashWithSalt s (KProj j i) = s `hashWithSalt` (6::Int) `hashWithSalt` j `hashWithSalt` i
    hashWithSalt s (KDom i) = s `hashWithSalt` (7::Int) `hashWithSalt` i
    hashWithSalt s (KCod i) = s `hashWithSalt` (8::Int) `hashWithSalt` i

instance Ord FlowTerm where
    compare = compare `on` termId
instance Eq FlowTerm where
    (==) = (==) `on` termId
         
termId :: FlowTerm -> Id
termId (Var i _) = i
termId (Flow.App i _ _) = i
termId (Abst i _ _) = i
termId (Br i _) = i
termId (Tuple i _ _) = i
termId (Proj i _ _) = i
termId (Dom i _) = i
termId (Cod i _) = i

key :: FlowTerm -> FlowKey
key (Var _ i) = KVar i
key (Flow.App _ t1 t2) = KApp (termId t1) (termId t2)
key (Abst _ t1 t2) = KAbst (termId t1) (termId t2)
key (Br _ ts) = KBr $ map termId ts
key (Tuple _ ts _) = KTuple $ map termId ts
key (Proj _ j t) = KProj j $ termId t
key (Dom _ t) = KDom $ termId t
key (Cod _ t) = KCod $ termId t

var :: VarId -> Constructor
var j i = Var i j
app :: FlowTerm -> FlowTerm -> Constructor
app t1 t2 i = Flow.App i t1 t2
abst :: FlowTerm -> FlowTerm -> Constructor
abst x t i = Abst i x t
br :: [FlowTerm] -> Constructor
br ts i = Br i ts
tuple :: [FlowTerm] -> [Term] -> Constructor
tuple ts _ts i = Tuple i ts _ts
proj :: Int -> FlowTerm -> Constructor
proj j t i = Proj i j t
dom :: FlowTerm -> Constructor
dom t i = Dom i t
cod :: FlowTerm -> Constructor
cod t i = Cod i t

type Constructor = Id -> FlowTerm
data Context s = Context { nodeTable     :: HashTable s FlowKey FlowTerm
                         , labelTable    :: HashTable s Id FlowTerm
                         , counter   :: STRef s Id }

buildGraph :: M.Map Symbol Sort -> Program -> ((Array Id FlowTerm,Array Id [Id]),M.Map Symbol' Id)
buildGraph senv p = runST $ do
    ctx <- newContext
    (env,edgeSet) <- execStateT (gatherPrimProgram ctx senv p) (M.empty,S.empty)
    es <- calcClosure ctx (S.elems edgeSet)
    lbl <- getNodes ctx
    let edgeTbl = accumArray (flip (:)) [] (bounds lbl) es
    return ((lbl,edgeTbl),fmap termId env)

newContext :: ST s (Context s)
newContext = Context <$> HT.new <*> HT.new <*> newSTRef 0

getNodes :: Context s -> ST s (Array Id FlowTerm)
getNodes ctx = do
    n <- readSTRef $ counter ctx
    array (0,n-1) <$> HT.toList (labelTable ctx)

type Symbol' = Either Symbol [Symbol]
type Sort' = Either Sort [Sort]

gatherPrimProgram :: Context s -> M.Map Symbol Sort -> Program -> StateT (M.Map Symbol' FlowTerm,S.Set (Id,Id,Sort')) (ST s) ()
gatherPrimProgram ctx senv (Program defs t0) = do
    void $ newVar ctx $ Left "true"
    void $ newVar ctx $ Left "false"
    forM_ defs $ \(f,_) -> newVar ctx $ Left f
    forM_ defs $ \(f,t) -> do
        vf <- lookupVar f
        (v,sort) <- gatherPrimTerm ctx senv t
        pushEdge vf v (Left sort)
    void $ gatherPrimTerm ctx senv t0

push :: Symbol' -> FlowTerm -> StateT (M.Map Symbol' FlowTerm, S.Set (Id,Id,Sort')) (ST s) ()
push x v = modify $ first $ M.insert x v

lookupVar :: Symbol -> StateT (M.Map Symbol' FlowTerm, S.Set (Id,Id,Sort')) (ST s) FlowTerm
lookupVar x = (M.! Left x).fst <$> get 

newVar :: Context s -> Symbol' -> StateT (M.Map Symbol' FlowTerm, S.Set (Id, Id, Sort')) (ST s) FlowTerm
newVar ctx x = get >>= lift . genNode ctx . var . VarId . M.size . fst >>= \t -> push x t >> pure t

gatherPrimTerm :: Context s -> M.Map Symbol Sort -> Term -> StateT (M.Map Symbol' FlowTerm, S.Set (Id,Id,Sort')) (ST s) (FlowTerm,Sort)
gatherPrimTerm ctx senv = go where
    go (V x) = (,senv M.! x) <$> lookupVar x 
    go (C True) = (,Base) <$> lookupVar "true"
    go (C False) = (,Base) <$> lookupVar "false"
    go (Omega x) = (,senv M.! x) <$> newVar ctx (Left x)
    go (Fail x) = (,senv M.! x) <$> newVar ctx (Left x)
    go (Lam xs t) = do
        vx <- newVar ctx $ Right xs
        forM_ (zip [0..] xs) $ \(j,x) -> lift (genNode ctx (proj j vx)) >>= push (Left x)
        let sortArgs = map (senv M.!) xs
        (vb,sortb) <- go t
        vt   <- lift $ genNode ctx (abst vx vb)
        vdom <- lift $ genNode ctx (dom vt)
        vcod <- lift $ genNode ctx (cod vt)
        pushEdge vx vdom (Right sortArgs)
        pushEdge vcod vb (Left sortb)
        return (vt,sortArgs :-> sortb)
    go (Syntax.App t ts) = do
        (v, _ :-> sort) <- go t
        (vs,sorts) <- unzip <$> mapM go ts
        vtup <- lift $ genNode ctx (tuple vs ts)
        vt   <- lift $ genNode ctx (app v vtup)
        vdom <- lift $ genNode ctx (dom v)
        vcod <- lift $ genNode ctx (cod v)
        pushEdge vdom vtup (Right sorts)
        pushEdge vt vcod (Left sort)
        forM_ (zip [0..] (zip vs sorts)) $ \(j,(vj,sortj)) -> do
            vp <- lift $ genNode ctx (proj j vtup)
            pushEdge vp vj (Left sortj)
        return (vt,sort)
    go (t1 :+: t2) = do
        (v1,sort) <- go t1
        (v2,_) <- go t2
        vt <- lift $ genNode ctx (br [v1,v2])
        pushEdge vt v1 $ Left sort
        pushEdge vt v2 $ Left sort
        return (vt,sort)
    go (If t1 t2 t3) = do
        (v1,_) <- go t1
        (v2,sort) <- go t2
        (v3,_) <- go t3
        vt <- lift $ genNode ctx (br [v1,v2,v3])
        pushEdge vt v2 $ Left sort
        pushEdge vt v3 $ Left sort
        return (vt,sort)

genNode :: Context s -> Constructor -> ST s FlowTerm
genNode ctx constructor = fmap constructor $ mfix $ \i -> do
    let v = constructor i
        k = key v
        tbl = nodeTable ctx
    mv <- HT.lookup tbl k
    case mv of
        Just v' -> return $ termId v'
        Nothing -> do 
            HT.insert tbl k v 
            i' <- incr (counter ctx)
            HT.insert (labelTable ctx) i' v
            return i'

incr :: STRef s Id -> ST s Id
incr st = readSTRef st <* modifySTRef st (+1)

pushEdge :: Monad m => FlowTerm -> FlowTerm -> Sort' -> StateT (a, S.Set (Id,Id,Sort')) m ()
pushEdge s t sort' = modify $ second $ S.insert (termId s,termId t,sort')

readTable :: (Hashable k,Eq k) => HashTable s k v -> k -> ST s v
readTable tbl i = fromJust <$> HT.lookup tbl i

containTable :: (Hashable k,Eq k) => HashTable s k v -> k -> ST s Bool
containTable tbl i = isJust <$> HT.lookup tbl i

calcClosure :: Context s -> [(Id,Id,Sort')] -> ST s [(Id,Id)]
calcClosure ctx = go [] [] where
    go !acc [] [] = return acc
    go !acc [] qs = go acc qs []
    go !acc ((i1,i2,sort):es) qs = do
        let acc' = (i1,i2):acc
        case sort of
            Left Base -> go acc' es qs
            Left (s1 :-> s2) -> do
                v1 <- readTable (labelTable ctx) i1
                v2 <- readTable (labelTable ctx) i2
                i1dom <- fmap termId $ genNode ctx $ dom v1
                i2dom <- fmap termId $ genNode ctx $ dom v2
                i1cod <- fmap termId $ genNode ctx $ cod v1
                i2cod <- fmap termId $ genNode ctx $ cod v2
                go acc' es ((i1cod,i2cod,Left s2):(i2dom,i1dom,Right s1):qs)
            Right ss -> do
                v1 <- readTable (labelTable ctx) i1
                v2 <- readTable (labelTable ctx) i2
                l <- forM (zip [0..] ss) $ \(i,s) -> do
                    pi1 <- fmap termId $ genNode ctx $ proj i v1
                    pi2 <- fmap termId $ genNode ctx $ proj i v2
                    return (pi1,pi2,Left s)
                go acc' es (l++qs)

type ReducedFlowGraph = (Array Id [Id],M.Map [Symbol] Id,Array Id (Maybe [Term]))

reduce1 :: Array Id FlowTerm -> Array Id [Id] -> M.Map Symbol' Id -> ReducedFlowGraph
reduce1 lbl g label = (g',label',lbl')
    where
    bb = bounds g
    rename = runSTUArray $ do
        arr <- newArray bb (-1)
        c <- newSTRef 0
        let dfs v = do
            x <- readArray arr v
            when ( x == -1 ) $ do
                incr c >>= writeArray arr v
                forM_ (g ! v) dfs
        forM_ [ i | (Right _,i) <- M.assocs label ] dfs
        return arr
    n = maximum $ elems rename
    g' = array (0,n) [ (rename ! i,map (rename!) l) | (i,l) <- assocs g, rename ! i /= -1 ]
    label' = M.fromList [ (xs,rename ! i) | (Right xs,i) <- M.toList label]
    lbl' = array (0,n) [ (j,f t) | (i,j) <- assocs rename, j /= -1, let t = lbl ! i ]
    f (Tuple _ _ ts) = return ts
    f _ = Nothing

-- pretty printing
ppGraph :: (Show a) => Array Id a -> Array Id [Id] -> String
ppGraph lbl edges = renderDot g where
    g = Graph StrictGraph DirectedGraph Nothing (nodeS ++ edgeS)
    node i = NodeId (NameId (show i)) Nothing
    label v = AttributeSetValue (NameId "label") (StringId (show v))
    nodeS = [ NodeStatement (node i) [label v] | (i,v) <- assocs lbl] 
    edgeS = [ EdgeStatement [ENodeId NoEdge (node s),ENodeId DirectedEdge (node t)] [] | (s,l) <- assocs edges, t <- l ]


