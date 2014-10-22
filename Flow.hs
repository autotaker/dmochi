{-# LANGUAGE BangPatterns #-}
module Flow where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Array.Unboxed
import Control.Monad
import Control.Monad.State
import Control.Applicative
import Text.Printf
import Data.Maybe
import Data.Tree
import Data.Graph
import Data.Monoid
import Data.STRef
import Data.Array.ST
import Sort 
import Syntax
import qualified Data.DList as DL
import Data.List(intersperse)
import Control.DeepSeq
import Data.Hashable
import qualified Data.HashTable.ST.Basic as HT
import Control.Monad.ST

type Id = Int

data FlowTerm = Cst Id !Term
              | Var Id Int
              | App Id !FlowTerm !FlowTerm
              | Abst Id !FlowTerm !FlowTerm -- Abst i (Var j) t
              | Br Id ![FlowTerm]
              | Tuple Id ![FlowTerm]
              | Proj Id !Int !FlowTerm
              | Dom Id !FlowTerm 
              | Cod Id !FlowTerm
              deriving(Show)

data FlowKey = KCst Term
             | KVar Int
             | KApp Id Id
             | KAbst Id Id
             | KBr [Id]
             | KTuple [Id]
             | KProj Int Id
             | KDom Id
             | KCod Id
             deriving(Eq)

instance Hashable FlowKey where
    hashWithSalt s (KCst t) = s `hashWithSalt` (0::Int) `hashWithSalt` t
    hashWithSalt s (KVar i) = s `hashWithSalt` (1::Int) `hashWithSalt` i
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
         

termId :: FlowTerm -> Id
termId (Cst i _) = i
termId (Var i _) = i
termId (Flow.App i _ _) = i
termId (Abst i _ _) = i
termId (Br i _) = i
termId (Tuple i _) = i
termId (Proj i _ _) = i
termId (Dom i _) = i
termId (Cod i _) = i

key :: FlowTerm -> FlowKey
key = undefined
{-
buildGraph :: Program -> FlowGraph
buildGraph (Program defs t0) = where
    (g,env) = runST $ do
        ctx <- newContext
        env <- execStateT (doit ctx) M.empty
        calcClosure ctx
        g <- getGraph ctx
        return (g,env)
    push x v = modify $ M.insert x v
    lookupVar x = (M.! x) <$> get 
    doit ctx = do
        ts <- forM defs $ \(f,t) -> do
            vf <- fmap M.size get >>= (\j -> lift $ genNode ctx (\i -> Var i j))
            push f vf
            return (vf,t)
        forM_ ts $ \(vf,t) -> do
            v <- go t
            lift $ addEdge ctx vf v
        go t0
    go (V x) = lookupVar x
    go (Lam xs t) = do
        vx   <- fmap M.size get >>= (\j -> lift $ genNode ctx (\i -> Var i j))
        forM (zip [0..] xs) $ \(j,x) -> lift $ genNode ctx (\i -> Proj i j vx) >>= push x
        vb   <- go t
        vt   <- lift $ genNode ctx (\i -> Abst i vx vb)
        vdom <- lift $ genNode ctx (\i -> Dom i vt)
        vcod <- lift $ genNode ctx (\i -> Cod i vt)
        lift $ addEdge vx vdom
        lift $ addEdge vcod vt
        return vt
    go (Syntax.App t ts) = do
        v    <- go t
        vs   <- mapM go ts
        vtup <- lift $ genNode ctx (\i -> Tuple i vs)
        vt   <- lift $ genNode ctx (\i -> Flow.App i v vtup)
        vdom <- lift $ genNode ctx (\i -> Dom i v)
        vcod <- lift $ genNode ctx (\i -> Cod i v)
        lift $ addEdge ctx vdom vtup
        lift $ addEdge ctx vt vcod
        forM_ (zip [0..] vs) $ \(j,vj) -> do
            vp <- lift $ genNode ctx (\i -> Proj i j vtup)
            lift $ addEdge ctx vp vj
        return vt
    go (t1 :+: t2) = do
        v1 <- go t1
        v2 <- go t2
        vt <- lift $ genNode ctx (\i -> Br i [v1,v2])
        lift $ addEdge ctx vt v1
        lift $ addEdge ctx vt v2
        return vt
    go (If t1 t2 t3) = do
        v1 <- go t1
        v2 <- go t2
        v3 <- go t3
        vt <- lift $ genNode ctx (\i -> Br i [v1,v2,v3])
        lift $ addEdge ctx vt v2
        lift $ addEdge ctx vt v3
        return vt
    go t = lift $ genNode ctx (\i -> Cst i t)
    -}

type Constructor = Id -> FlowTerm
data Context s = Context { nodeTable :: HT.HashTable s FlowKey FlowTerm
                         , counter   :: STRef s Id }

genNode :: Context s -> Constructor -> ST s FlowTerm
genNode ctx constructor = fmap constructor $ mfix $ \i -> do
    let v = constructor i
        k = key v
        tbl = nodeTable ctx
    mv <- HT.lookup tbl k
    case mv of
        Just v -> return $ termId v
        Nothing -> HT.insert k v >> incr (counter ctx)

incr :: STRef s Id -> ST s Id
incr st = readSTRef st <* modifySTRef st (+1)




{-

labelGrammar :: A.Grammar -> SortEnv -> ([(Id,Id)], M.Map Key FlowTerm)
labelGrammar g senv = runState doit M.empty
    where
        smap = M.fromList senv
        doit = do
            forM_ (A.terminals g) $ registerTerm smap . A.Term
            forM (A.rules g) $ registerRule smap

linearClosure :: M.Map Key FlowTerm -> [(Id,Id)] -> [(Id,Id)]
linearClosure tmap es = liftEdges tmap $ (++es) $ primEdges tmap $ M.elems tmap

primEdges :: M.Map Key FlowTerm -> [FlowTerm] -> [(Id,Id)]
primEdges tmap terms = do
    t <- terms
    case  t of
        Abst i x t ->
            let i1 = termId $ tmap M.! KBase x
                i2 = termId $ tmap M.! KDom i
                i3 = termId $ tmap M.! KCod i
                i4 = termId t in
            [(i1,i2),(i3,i4)]
        App i t1 t2 ->
            let i1 = termId $ tmap M.! KDom (termId t1)
                i2 = termId t2
                i3 = i
                i4 = termId $ tmap M.! KCod (termId t1)
            in
            [(i1,i2),(i3,i4)]
        _ -> []

liftEdges :: M.Map Key FlowTerm -> [(Id,Id)] -> [(Id,Id)]
liftEdges tmap edges = concat $ takeWhile (not . null) $ iterate lift edges
    where
        lift es = do
            (i1,i2) <- es
            guard $ KDom i1 `M.member` tmap
            let i3 = termId $ tmap M.! KDom i1
                i4 = termId $ tmap M.! KDom i2
                i5 = termId $ tmap M.! KCod i1
                i6 = termId $ tmap M.! KCod i2
            [(i4,i3),(i5,i6)]

registerTerm :: SortMap -> A.AlphaTerm -> State LabelState (FlowTerm,Sort)
registerTerm smap = go
    where
        go :: A.AlphaTerm -> State LabelState (FlowTerm,Sort)
        go (A.Nonterm s) = goBase s $ flip Nonterm s
        go (A.Term s)    = goBase s $ flip Term s
        go (A.Var s)     = goBase s $ flip Var s
        go (A.App t1 t2) = do
            (t1',Fun _ k) <- go t1
            (t2',_) <- go t2
            t <- register (KApp (termId t1') (termId t2'))  (\i-> App i t1' t2')
            registerDomCod t k
            return (t,k)
        goBase s f = do
            t <- register (KBase s) f
            let k = smap M.! s
            registerDomCod t k
            return (t,k)

registerRule :: SortMap -> (String,[String],A.AlphaTerm) -> State LabelState (Id,Id)
registerRule smap (f,args,t) = do
    (tf,_) <- registerTerm smap $ A.Nonterm f
    forM_ args $ registerTerm smap . A.Var
    r <- registerTerm smap t
    (t,_) <- foldM registerAbst r $ reverse args
    return (termId tf,termId t)
        where
            registerAbst (t,k) x = do
                let k' = Fun (smap M.! x) k
                t' <- register (KAbst x (termId t)) (\i -> Abst i x t)
                registerDomCod t' k'
                return (t',k')

register :: Key -> (Id -> FlowTerm) -> State LabelState FlowTerm
register k f = do
    b <- M.member k <$> get
    if b then
        (M.! k) <$> get
    else do
        t <- f . M.size <$> get 
        modify $ M.insert k t
        return t

registerDomCod :: FlowTerm -> Sort -> State LabelState ()
registerDomCod _ O = return ()
registerDomCod t (Fun k1 k2) = do
    t1 <- register (KDom (termId t)) $ flip Dom t
    t2 <- register (KCod (termId t)) $ flip Cod t
    registerDomCod t1 k1
    registerDomCod t2 k2


isVar :: FlowTerm -> Bool
isVar (Var _ _) = True
isVar _ = False
isATerm :: FlowTerm -> Bool
isATerm (Nonterm _ _) = True
isATerm (Term _ _   ) = True
isATerm (Var _ _    ) = True
isATerm (App _ _ _  ) =  True
isATerm  _ = False

unique :: Ord a => [a] -> [a]
unique = S.toList . S.fromList 
reduceGraphSCC :: FlowGraph -> Array Id [Id]
reduceGraphSCC g = accumArray (flip (:)) [] (bounds $ graph g) es'
    where
    p = not . isATerm . (label g !)
    es = [ (i,j) | (i,l) <- assocs $ graph g, p i, j <- l, p j]
    cs = map flatten $ scc $ buildG (bounds $ graph g) es
    es' = unique [(f i,f j) | (i,l) <- assocs $ graph g, j <- l, f i /= f j]
    f i = a ! i
    a :: Array Id Id
    a = array (bounds $ graph g) [(j,head l) | l <- cs, j <- l]

data ReducedNode f = VarNode (f String) | TermNode A.AlphaTerm | EmptyNode
type ReducedFlowGraph f = (Array Id (ReducedNode f),Array Id [Id])

instance NFData (ReducedNode []) where
    rnf (VarNode s) = rnf s
    rnf (TermNode t) = rnf t
    rnf EmptyNode = ()

instance Show (ReducedNode []) where
    show (VarNode l) = concat $ intersperse "," l
    show (TermNode t) = (filter (/='"') $ show t)
    show EmptyNode = ""

isVarNode :: ReducedNode f -> Bool
isVarNode (VarNode _) = True
isVarNode _ = False

fromFlowTerm :: FlowTerm -> ReducedNode DL.DList
fromFlowTerm (Nonterm _ s) = TermNode $ (A.Nonterm s)
fromFlowTerm (Term _ s) = TermNode (A.Term s)
fromFlowTerm (Var _ s) = VarNode (DL.singleton s)
fromFlowTerm (Abst _ _ _) = EmptyNode
fromFlowTerm (Dom _ _) = EmptyNode
fromFlowTerm (Cod _ _) = EmptyNode
fromFlowTerm t = TermNode (t')
    where
    t' = cata (FTermAlgebra (const A.Nonterm) (const A.Term) (const A.Var) (const A.App) undefined undefined undefined) t

instance Monoid (f String) => Monoid (ReducedNode f) where
    mempty = EmptyNode
    mappend (VarNode v1) (VarNode v2) = VarNode (v1 <> v2)
--    mappend (TermNode (t,v1)) (VarNode v2) = TermNode (t,v1++v2)
--    mappend (VarNode v1) (TermNode (t,v2)) = TermNode (t,v1++v2)
    mappend v1 EmptyNode = v1
    mappend EmptyNode v2 = v2
    mappend _ _ = undefined

reduceGraph :: FlowGraph -> [ReducedFlowGraph DL.DList]
reduceGraph g = g2:g3:[]
    where
    g1 = reduce1 g
    g2 = reduce2 g1
    g3 = reduce3 g2

-- 変数でない項から出ている辺を除いてSCC
-- 500k edgeくらいでSCCがstack overflowする
reduce1 :: FlowGraph -> ReducedFlowGraph DL.DList
reduce1 g = (label1, g')
    where
    bb = bounds $ graph g
    a = array bb $ map (\(i,l) -> if f i then (i,[]) else (i,l)) $ assocs $ graph g
    f i = let x = (label g ! i) in isATerm x && not (isVar x)
    cs = map flatten $ scc $ a
    rename = array bb [ (j,i) | (l,i) <- zip cs [0..], j <- l] :: UArray Id Id
    label1 :: Array Id (ReducedNode DL.DList)
    label1 = accumArray mappend mempty (0,length cs-1) [ (rename ! i,fromFlowTerm t)  | (i,t) <- assocs $ label g]
    es' = unique $ [ (rename ! i, rename ! j) | (i,l) <- assocs a, j <- l, rename ! i /= rename ! j ]
    g' :: Array Id [Id]
    g' = accumArray (flip (:)) [] (0,length cs-1) es'

-- 変数から到達不可能な頂点を削除
reduce2 :: ReducedFlowGraph DL.DList -> ReducedFlowGraph DL.DList
reduce2 (label,g) = (label1, g')
    where
    es = [ (i,j) | (i,l) <- assocs g, j <- l]
    rename :: Array Id (Maybe (Maybe Id))
    rename = runSTArray $ do
        a <- newArray (bounds label) Nothing
        c <- newSTRef 0
        forM_ (range $ bounds label) $ \i ->
            when (isVarNode $ label ! i) $ void $ dfs a c i
        return a
    es' = unique $ [ (v,u) | (i,j) <- es, Just v <- return $ join $ rename ! i, Just u <- return $ join $ rename ! j, u /= v ]
    vmax = maximumDef (-1) $ map (uncurry max) es'
    g' = accumArray (flip (:)) [] (0,vmax) es'
    label1 = accumArray mappend mempty (0,vmax) [(v,t)  | (i,t) <- assocs label, Just v <- return $ join $ rename ! i]
    incr c = readSTRef c >>= (\v -> modifySTRef c succ >> return v)
    dfs a c i = do
        b <- readArray a i
        case b of
            Just x -> return x
            Nothing -> do
                l <- catMaybes <$> forM (g ! i) (dfs a c)
                r <- case (l,label ! i) of
                    ([], EmptyNode) -> return Nothing
                    _ -> Just <$> incr c
                writeArray a i (Just r)
                return r

-- 同じFlowが流れるノードを統合(O(n^2))なのでだめ
-- 出次数が1のノードをつぶす
-- 
reduce3 :: ReducedFlowGraph DL.DList -> ReducedFlowGraph DL.DList
reduce3 (label,g) = (label',g')
    where
    vmax = maximumDef (-1)$ elems rename
    label' :: Array Id (ReducedNode DL.DList)
    label' = accumArray mappend mempty (0,vmax) [ (rename ! i,t)  | (i,t) <- assocs label ]
    g' :: Array Id [Id]
    g' = accumArray (flip (:)) [] (0,vmax) es
    es = unique $ [ (rename ! i, rename ! j) | (i,l) <- assocs g, j <- l, rename ! i /= rename ! j ]
    rename :: UArray Id Id
    rename = runSTUArray $ do
        a <- newArray (bounds label) (-1)
        c <- newSTRef 0
        forM_ (range $ bounds label) $ dfs a c
        return a
    incr c = readSTRef c >>= (\v -> modifySTRef c succ >> return v)
    dfs a c i = do
        k <- readArray a i
        if k /= -1 then return k else do
            l <- forM (g ! i) $ dfs a c
            k' <- case (l,label ! i) of
                ([k],EmptyNode) -> return k
                _ -> incr c
            writeArray a i k'
            return k'

freezeNode :: ReducedNode DL.DList -> ReducedNode []
freezeNode (VarNode l) = VarNode (DL.toList l)
freezeNode (TermNode t) = TermNode t
freezeNode EmptyNode = EmptyNode

freezeGraph :: ReducedFlowGraph DL.DList -> ReducedFlowGraph []
freezeGraph (label,g) = (fmap freezeNode label,g)

-}
