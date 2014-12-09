{-# LANGUAGE BangPatterns,TupleSections #-}
module Flow where

import qualified Data.Map as M
import qualified Data.Set as S
--import Control.Monad
import Control.Monad.State
import Control.Applicative
import Data.STRef
import Data.Maybe
import Syntax hiding(Proj,Let)
import Sort hiding(Tuple)
import qualified Sort
import qualified Syntax
import Data.Hashable
import qualified Data.HashTable.Class as HT
import Data.HashTable.ST.Basic (HashTable)
import Control.Monad.ST
import Data.Array.Unboxed
import Data.Array.ST
import Data.Function
import Debug.Trace

import Language.Dot hiding(Id)

data VarId = VarId { getId :: Int
                   , name  :: Symbol }deriving(Ord,Eq)
instance Show VarId where
    show = name

type Id = Int

data FlowTerm = Var Id !VarId
              | App Id !FlowTerm !FlowTerm
              | Abst Id !VarId !FlowTerm 
              | Br    Id !FlowTerm !FlowTerm !FlowTerm
              | Tuple Id ![FlowTerm]
              | Let  Id !VarId !FlowTerm !FlowTerm
              | Proj Id !ProjN !ProjD !FlowTerm
              | Dom Id !FlowTerm 
              | Cod Id !FlowTerm
              deriving(Show)

data FlowKey = KVar !VarId
             | KApp !Id !Id
             | KAbst !VarId !Id
             | KBr !Id !Id !Id
             | KTuple ![Id]
             | KLet !VarId !Id !Id
             | KProj !ProjN !ProjD !Id
             | KDom !Id
             | KCod !Id
             deriving(Eq)

instance Hashable FlowKey where
    hashWithSalt s (KVar i) = s `hashWithSalt` (1::Int) `hashWithSalt` getId i
    hashWithSalt s (KApp i1 i2) = s `hashWithSalt` (2::Int) 
                                    `hashWithSalt` i1 
                                    `hashWithSalt` i2
    hashWithSalt s (KAbst i1 i2) = s `hashWithSalt`(3::Int) 
                                     `hashWithSalt` getId i1
                                     `hashWithSalt` i2
    hashWithSalt s (KBr i1 i2 i3) = s `hashWithSalt` (4::Int) 
                                      `hashWithSalt` i1
                                      `hashWithSalt` i2
                                      `hashWithSalt` i3
    hashWithSalt s (KTuple is) = s `hashWithSalt` (5::Int) `hashWithSalt` is
    hashWithSalt s (KProj n d i) = s `hashWithSalt` (6::Int) `hashWithSalt` projN n 
                                                             `hashWithSalt` projD d
                                                             `hashWithSalt` i
    hashWithSalt s (KDom i) = s `hashWithSalt` (7::Int) `hashWithSalt` i
    hashWithSalt s (KCod i) = s `hashWithSalt` (8::Int) `hashWithSalt` i
    hashWithSalt s (KLet x i1 i2) = s `hashWithSalt` (9::Int) 
                                      `hashWithSalt` getId x
                                      `hashWithSalt` i1 
                                      `hashWithSalt` i2

instance Ord FlowTerm where
    compare = compare `on` termId
instance Eq FlowTerm where
    (==) = (==) `on` termId
         
termId :: FlowTerm -> Id
termId (Var i _) = i
termId (Flow.App i _ _) = i
termId (Abst i _ _) = i
termId (Br i _ _ _) = i
termId (Tuple i _) = i
termId (Proj i _ _ _) = i
termId (Let i _ _ _) = i
termId (Dom i _) = i
termId (Cod i _) = i

key :: FlowTerm -> FlowKey
key (Var _ i) = KVar i
key (Flow.App _ t1 t2) = KApp (termId t1) (termId t2)
key (Abst _ t1 t2) = KAbst t1 (termId t2)
key (Br _ t1 t2 t3) = KBr (termId t1) (termId t2) (termId t3)
key (Tuple _ ts) = KTuple $ map termId ts
key (Proj _ n d t) = KProj n d $ termId t
key (Let _ x t1 t2) = KLet x (termId t1) (termId t2)
key (Dom _ t) = KDom $ termId t
key (Cod _ t) = KCod $ termId t

var :: VarId -> Constructor
var j i = Var i j
app :: FlowTerm -> FlowTerm -> Constructor
app t1 t2 i = Flow.App i t1 t2
abst :: VarId -> FlowTerm -> Constructor
abst x t i = Abst i x t
letc :: VarId -> FlowTerm -> FlowTerm -> Constructor
letc x t t' i = Let i x t t'
br :: FlowTerm -> FlowTerm -> FlowTerm -> Constructor
br t1 t2 t3 i = Br i t1 t2 t3
tuple :: [FlowTerm] ->  Constructor
tuple ts i = Tuple i ts
proj :: ProjN -> ProjD -> FlowTerm -> Constructor
proj n d t i = Proj i n d t
dom :: FlowTerm -> Constructor
dom t i = Dom i t
cod :: FlowTerm -> Constructor
cod t i = Cod i t

type Constructor = Id -> FlowTerm
data Context s = Context { nodeTable     :: HashTable s FlowKey FlowTerm
                         , labelTable    :: HashTable s Id FlowTerm
                         , termTable     :: HashTable s Id (Maybe Term)
                         , counter       :: STRef s Id }

buildGraph :: M.Map Symbol (Sort,Term) -> Program -> ((Array Id (Maybe Term),Array Id [Id]),M.Map Symbol Id)
buildGraph senv p = runST $ do
    ctx <- newContext
    env <- fmap M.fromList $ forM (zip (M.assocs senv) [0..]) $ \((x,(s,t)),i) -> do
        ft <- genNode ctx (Just t) (var (VarId i x))
        return (x,(ft,s))
    edgeSet <- execStateT (gatherPrimProgram ctx env p) S.empty
    es <- calcClosure ctx (S.elems edgeSet)
    lbl <- getNodes ctx
    let edgeTbl = accumArray (flip (:)) [] (bounds lbl) es
    _ <- do
        n <- readSTRef $ counter ctx
        arr <- array (0,n-1) <$> HT.toList (labelTable ctx)
        trace (ppGraph arr edgeTbl) $ return ()
    return ((lbl,edgeTbl),fmap (termId . fst) env)

newContext :: ST s (Context s)
newContext = Context <$> HT.new <*> HT.new <*> HT.new <*> newSTRef 0

getNodes :: Context s -> ST s (Array Id (Maybe Term))
getNodes ctx = do
    n <- readSTRef $ counter ctx
    array (0,n-1) <$> HT.toList (termTable ctx)

gatherPrimProgram :: Context s -> M.Map Symbol (FlowTerm,Sort) -> Program -> StateT (S.Set (Id,Id,Sort)) (ST s) ()
gatherPrimProgram ctx env (Program defs t0) = do
    forM_ defs $ \(f,t) -> do
        let vf = lookupVar env f
        (v,sort) <- gatherPrimTerm ctx env t
        pushEdge vf v sort
    void $ gatherPrimTerm ctx env t0


lookupVar :: M.Map Symbol (FlowTerm,Sort) -> Symbol -> FlowTerm
lookupVar env x = fst $ env M.! x

varId :: FlowTerm -> VarId
varId (Var _ v) = v
varId _ = undefined

gatherPrimTerm :: Context s -> M.Map Symbol (FlowTerm,Sort) -> Term -> StateT (S.Set (Id,Id,Sort)) (ST s) (FlowTerm,Sort)
gatherPrimTerm ctx env = go where
    go (V x) = pure $ env M.! x
    go (C True) = pure $ env M.! "true"
    go (C False) = pure $ env M.! "false"
    go (Fail x) = pure $ env M.! x
    go (Omega x) = pure $ env M.! x
    go TF = pure $ env M.! "*"
    go _t@(Lam x t) = do
        let (vx,sx) = env M.! x
        (vb,sb) <- go t
        vt   <- lift $ genNode ctx (Just _t) (abst (varId vx) vb)
        vdom <- lift $ genNode ctx Nothing   (dom vt)
        vcod <- lift $ genNode ctx Nothing   (cod vt)
        pushEdge vx vdom sx
        pushEdge vcod vb sb
        return (vt,sx :-> sb)
    go _t@(Syntax.App t1 t2) = do
        (vf, _ :-> sort1) <- go t1
        (vt,sort2) <- go t2
        v    <- lift $ genNode ctx (Just _t) (app vf vt)
        vdom <- lift $ genNode ctx Nothing   (dom vf)
        vcod <- lift $ genNode ctx Nothing   (cod vf)
        pushEdge vdom vt sort2
        pushEdge v vcod sort1
        return (v,sort1)
    go _t@(If t1 t2 t3) = do
        (v1,_) <- go t1
        (v2,sort) <- go t2
        (v3,_) <- go t3
        vt <- lift $ genNode ctx (Just _t) (br v1 v2 v3)
        pushEdge vt v2 sort
        pushEdge vt v3 sort
        return (vt,sort)
    go _t@(T ts) = do
        (fts,ss) <- unzip <$> mapM go ts
        vt <- lift $ genNode ctx (Just _t) (tuple fts)
        let n = ProjD $ length ts
        forM_ (zip (zip fts ss) [0..]) $ \((ft,s),i) -> do
            ti <- lift $ genNode ctx (Just $ Syntax.Proj (ProjN i) n _t) (proj (ProjN i) n vt)
            pushEdge ti ft s
        return (vt,Sort.Tuple ss)
    go _t@(Syntax.Let x tx t) = do
        (ftx,sx) <- go tx
        (ft,s)   <- go t
        let (fx,_) = env M.! x
        vt <- lift $ genNode ctx (Just _t) (letc (varId fx) ftx ft)
        pushEdge fx ftx sx
        pushEdge vt ft s
        return (vt,s)
    go _t@(Syntax.Proj n d t) = do
        (t',Sort.Tuple ss) <- go t
        vt <- lift $ genNode ctx (Just _t) (proj n d t')
        return (vt,ss !! projN n)
    
genNode :: Context s -> Maybe Term -> Constructor -> ST s FlowTerm
genNode ctx mt constructor = fmap constructor $ mfix $ \i -> do
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
                HT.insert (termTable ctx) i' mt
                return i'

incr :: STRef s Id -> ST s Id
incr st = readSTRef st <* modifySTRef st (+1)

pushEdge :: Monad m => FlowTerm -> FlowTerm -> Sort -> StateT (S.Set (Id,Id,Sort)) m ()
pushEdge s t sort = modify $ S.insert (termId s,termId t,sort)

readTable :: (Hashable k,Eq k) => HashTable s k v -> k -> ST s v
readTable tbl i = fromJust <$> HT.lookup tbl i

containTable :: (Hashable k,Eq k) => HashTable s k v -> k -> ST s Bool
containTable tbl i = isJust <$> HT.lookup tbl i

calcClosure :: Context s -> [(Id,Id,Sort)] -> ST s [(Id,Id)]
calcClosure ctx = go [] [] where
    go !acc [] [] = return acc
    go !acc [] qs = go acc qs []
    go !acc ((i1,i2,sort):es) qs = do
        let acc' = (i1,i2):acc
        case sort of
            Base -> go acc' es qs
            (s1 :-> s2) -> do
                v1 <- readTable (labelTable ctx) i1
                v2 <- readTable (labelTable ctx) i2
                i1dom <- fmap termId $ genNode ctx Nothing $ dom v1
                i2dom <- fmap termId $ genNode ctx Nothing $ dom v2
                i1cod <- fmap termId $ genNode ctx Nothing $ cod v1
                i2cod <- fmap termId $ genNode ctx Nothing $ cod v2
                go acc' es ((i1cod,i2cod,s2):(i2dom,i1dom,s1):qs)
            Sort.Tuple ss -> do
                v1 <- readTable (labelTable ctx) i1
                v2 <- readTable (labelTable ctx) i2
                l <- forM (zip [0..] ss) $ \(i,s) -> do
                    let n = ProjN i
                        d = ProjD $ length ss
                    pi1 <- fmap termId $ genNode ctx Nothing $ proj n d v1
                    pi2 <- fmap termId $ genNode ctx Nothing $ proj n d v2
                    return (pi1,pi2,s)
                go acc' es (l++qs)

type ReducedFlowGraph = (Array Id [Id],M.Map Symbol Id,Array Id (Maybe Term))

reduce1 :: Array Id (Maybe Term) -> Array Id [Id] -> M.Map Symbol Id -> ReducedFlowGraph
reduce1 tlbl g label = (g2,label',lbl')
    where
    bb = bounds g
    rename = runSTUArray $ do
        arr <- newArray bb (-1)
        c <- newSTRef 0
        let dfs v = do
            x <- readArray arr v
            when ( x == -1 ) $ do
                incr c >>= writeArray arr v
                forM_ (g1 ! v) dfs
        forM_ (M.elems label) dfs
        return arr
    n = maximum $ elems rename
    g1 :: Array Id [Id]
    g1 = listArray bb [ l | (_,l) <- assocs g]
    g2 = array (0,n) [ (rename ! i,map (rename!) l) | (i,l) <- assocs g1, rename ! i /= -1 ]
    label' = M.fromList [ (x,rename ! i) | (x,i) <- M.toList label]
    lbl' = array (0,n) [ (j,tlbl ! i) | (i,j) <- assocs rename, j /= -1 ]

-- pretty printing
ppGraph :: (Show a) => Array Id a -> Array Id [Id] -> String
ppGraph lbl edges = renderDot g where
    g = Graph StrictGraph DirectedGraph Nothing (nodeS ++ edgeS)
    node i = NodeId (NameId (show i)) Nothing
    label v = AttributeSetValue (NameId "label") (StringId (show v))
    nodeS = [ NodeStatement (node i) [label v] | (i,v) <- assocs lbl] 
    edgeS = [ EdgeStatement [ENodeId NoEdge (node s),ENodeId DirectedEdge (node t)] [] | (s,l) <- assocs edges, t <- l ]


