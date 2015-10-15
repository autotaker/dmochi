{-# LANGUAGE BangPatterns,TupleSections #-}
module Boolean.Flow2 where

import qualified Data.Map as M
--import Control.Monad
import Control.Monad.State
import Control.Applicative
import Data.STRef
import Data.Maybe
import qualified Boolean.Syntax.TypedSimple as B
import Boolean.Syntax.Typed(Size,Index,Symbol,Sort(..),HasSort(..))
import qualified Boolean.Syntax.Typed as Typed
import Data.Hashable
import qualified Data.HashTable.Class as HT
import Data.HashTable.ST.Basic (HashTable)
import Control.Monad.ST
import Data.Array.Unboxed
--import Data.Array.ST
import Data.Function
--import Debug.Trace

import Language.Dot hiding(Id)

data VarId = VarId { getId :: Int
                   , name  :: Symbol }deriving(Ord,Eq)
instance Show VarId where
    show = Typed.name.name

type Id = Int

data FlowTerm = C      Id Bool
              | V      VarId
              | T      Id [FlowTerm]
              | Lam    Id VarId FlowTerm
              | And    Id FlowTerm FlowTerm
              | Or     Id FlowTerm FlowTerm
              | Not    Id FlowTerm
              | App    Id !Sort FlowTerm FlowTerm
              | Let    Id !Sort VarId FlowTerm FlowTerm
              | Assume Id !Sort FlowTerm FlowTerm
              | Branch Id !Sort FlowTerm FlowTerm
              | Fail   VarId
              | Proj   Id !Sort !Index !Size !FlowTerm
              | Dom    Id !Sort !FlowTerm 
              | Cod    Id !Sort !FlowTerm
              deriving Show

data FlowKey = KC      !Bool
             | KV      !Id
             | KT      ![Id]
             | KLam    !Id !Id
             | KAnd    !Id !Id
             | KOr     !Id !Id
             | KNot    !Id
             | KApp    !Id !Id
             | KLet    !Id !Id !Id
             | KAssume !Id !Id
             | KBranch !Id !Id
             | KFail   !Id
             | KProj   !Index !Size !Id
             | KDom    !Id
             | KCod    !Id
             deriving(Eq)

instance Hashable FlowKey where
    hashWithSalt s (KV i) = s `hashWithSalt` (1::Int) `hashWithSalt` i
    hashWithSalt s (KApp i1 i2) = s `hashWithSalt` (2::Int) 
                                    `hashWithSalt` i1 
                                    `hashWithSalt` i2
    hashWithSalt s (KLam i1 i2) = s `hashWithSalt`(3::Int) 
                                     `hashWithSalt` i1
                                     `hashWithSalt` i2
    hashWithSalt s (KBranch i1 i2) = s `hashWithSalt` (4::Int) `hashWithSalt` i1 `hashWithSalt` i2
    hashWithSalt s (KT is) = s `hashWithSalt` (5::Int) `hashWithSalt` is
    hashWithSalt s (KProj n d i) = s `hashWithSalt` (6::Int) `hashWithSalt` n 
                                                             `hashWithSalt` d
                                                             `hashWithSalt` i
    hashWithSalt s (KDom i) = s `hashWithSalt` (7::Int) `hashWithSalt` i
    hashWithSalt s (KCod i) = s `hashWithSalt` (8::Int) `hashWithSalt` i
    hashWithSalt s (KLet i0 i1 i2) = s `hashWithSalt` (9::Int) 
                                      `hashWithSalt` i0
                                      `hashWithSalt` i1 
                                      `hashWithSalt` i2
    hashWithSalt s (KC b) = s `hashWithSalt` (10::Int) `hashWithSalt` b
    hashWithSalt s (KAnd i1 i2) = s `hashWithSalt` (11::Int) `hashWithSalt` i1 `hashWithSalt` i2
    hashWithSalt s (KOr i1 i2) = s `hashWithSalt` (12::Int) `hashWithSalt` i1 `hashWithSalt` i2
    hashWithSalt s (KNot i1) = s `hashWithSalt` (13::Int) `hashWithSalt` i1
    hashWithSalt s (KAssume i1 i2) = s `hashWithSalt` (14::Int) `hashWithSalt` i1 `hashWithSalt` i2
    hashWithSalt s (KFail i) = s `hashWithSalt` (15::Int) `hashWithSalt` i


instance Ord FlowTerm where
    compare = compare `on` termId
instance Eq FlowTerm where
    (==) = (==) `on` termId
         
termId :: FlowTerm -> Id
termId (V i) = getId i
termId (C i _) = i
termId (And i _ _) = i
termId (Or i _ _) = i
termId (Not i _) = i
termId (Assume i _ _ _) = i
termId (App i _ _ _) = i
termId (Lam i _ _) = i
termId (Branch i _ _ _) = i
termId (T i _) = i
termId (Proj i _ _ _ _) = i
termId (Let i _ _ _ _) = i
termId (Dom i _ _) = i
termId (Cod i _ _) = i
termId (Fail i) = getId i

key :: FlowTerm -> FlowKey
key (C _ b) = KC b
key (V x) = KV $ getId x
key (T _ ts) = KT $ map termId ts
key (App _ _ t1 t2) = KApp (termId t1) (termId t2)
key (Lam _ x t2) = KLam (getId x) (termId t2)
key (Branch _ _ t1 t2) = KBranch (termId t1) (termId t2)
key (Proj _ _ n d t) = KProj n d $ termId t
key (Let _ _ x t1 t2) = KLet (getId x) (termId t1) (termId t2)
key (Dom _ _ t) = KDom $ termId t
key (Cod _ _ t) = KCod $ termId t
key (And _ t1 t2) = KAnd (termId t1) (termId t2)
key (Or _ t1 t2) = KOr (termId t1) (termId t2)
key (Not _ t1) = KNot (termId t1)
key (Assume _ _ t1 t2) = KAssume (termId t1) (termId t2)
key (Fail x) = KFail $ getId x

instance HasSort VarId where
    getSort = getSort . name

instance HasSort FlowTerm where
    getSort (C _ _) = Bool
    getSort (V x)   = getSort x
    getSort (T _ ts) = Tuple $ map getSort ts
    getSort (Lam _ x t) = getSort x :-> getSort t
    getSort (And _ _ _) = Bool
    getSort (Or  _ _ _) = Bool
    getSort (Not _ _) = Bool
    getSort (App _ s _ _) = s
    getSort (Let _ s _ _ _) = s
    getSort (Assume _ s _ _) = s
    getSort (Branch _ s _ _) = s
    getSort (Fail x) = getSort x
    getSort (Proj _ s _ _ _) = s
    getSort (Dom _ s _) = s
    getSort (Cod _ s _) = s

c_const :: Bool -> Constructor
c_const b i = C i b
c_app :: FlowTerm -> FlowTerm -> Constructor
c_app t1 t2 i = App i s t1 t2
    where _ :-> s = getSort t1
c_lam :: VarId -> FlowTerm -> Constructor
c_lam x t i = Lam i x t
c_let :: VarId -> FlowTerm -> FlowTerm -> Constructor
c_let x t t' i = Let i (getSort t') x t t'
c_branch :: FlowTerm -> FlowTerm -> Constructor
c_branch t1 t2 i = Branch i (getSort t1) t1 t2
c_tuple :: [FlowTerm] ->  Constructor
c_tuple ts i = T i ts
c_assume :: FlowTerm -> FlowTerm -> Constructor
c_assume t1 t2 i = Assume i (getSort t2) t1 t2
c_proj :: Index -> Size -> FlowTerm -> Constructor
c_proj n d t i = Proj i (ss !! n) n d t where
    Tuple ss = getSort t
c_dom :: FlowTerm -> Constructor
c_dom t i = Dom i s t
    where s :-> _ = getSort t
c_cod :: FlowTerm -> Constructor
c_cod t i = Cod i s t
    where _ :-> s = getSort t
c_and, c_or :: FlowTerm -> FlowTerm -> Constructor
c_and t1 t2 i = And i t1 t2
c_or  t1 t2 i = Or  i t1 t2
c_not :: FlowTerm -> Constructor
c_not t i = Not i t

type Constructor = Id -> FlowTerm
data Context s = Context { nodeTable     :: HashTable s FlowKey FlowTerm
                         , labelTable    :: HashTable s Id FlowTerm
                         , edgeTable     :: HashTable s (Id,Id) ()
                         , counter       :: STRef s Id }

data Program = Program { definitions :: [(VarId, FlowTerm)]
                       , mainTerm    :: FlowTerm
                       , termTable   :: Array Id FlowTerm
                       , cfg         :: Array Id [Id] }


buildGraph :: B.Program -> Program
buildGraph (B.Program ds d0) = runST $ do
    ctx <- newContext
    env <- fmap M.fromList $ forM ds $ \(f, _) -> do
        var <- genVarNode ctx f
        return (f,var)
    ds' <- forM ds $ \(f,t) -> do
        t' <- gatherVTermEdges ctx env t
        addEdge ctx (V (env M.! f)) t'
        return (env M.! f, t')
    d0' <- gatherTermEdges ctx env d0
    calcClosure ctx
    lbls <- HT.toList (labelTable ctx)
    edges <- map fst <$> HT.toList (edgeTable ctx)
    n <- readSTRef (counter ctx) 
    let termTbl :: Array Id FlowTerm
        termTbl = array (0,n-1) lbls
        edgeTbl :: Array Id [Id]
        edgeTbl = accumArray (flip (:)) [] (0,n-1) edges
--        symMap :: M.Map Symbol Id
--        symMap = M.fromList $ [ (name x,getId x)   | (_,V x) <- lbls ]
    return $ Program ds' d0' termTbl edgeTbl 

newContext :: ST s (Context s)
newContext = Context <$> HT.new <*> HT.new <*> HT.new <*> newSTRef 0

lookupVar :: M.Map Symbol (FlowTerm,Sort) -> Symbol -> FlowTerm
lookupVar env x = fst $ env M.! x

varId :: FlowTerm -> VarId
varId (V v) = v
varId (Fail v) = v
varId _ = undefined

addEdge :: Context s -> FlowTerm -> FlowTerm -> ST s ()
addEdge ctx t1 t2 = HT.insert (edgeTable ctx) (termId t1,termId t2) ()

gatherVTermEdges :: Context s -> M.Map Symbol VarId -> B.VTerm -> ST s FlowTerm
gatherVTermEdges ctx = go where
    go env (B.V x) = return $ V (env M.! x)
    go _ (B.C b) = genNode ctx (c_const b)
    go env (B.T ts) = do
        ts' <- mapM (go env) ts
        t0 <- genNode ctx $ c_tuple ts'
        -- proj_i^n t -> ti
        let n = length ts
        forM_ (zip [0..n-1] ts') $ \(i,ti) -> do
            ti' <- genNode ctx $ c_proj i n t0
            addEdge ctx ti' ti
        return t0
    go env (B.Lam x t) = do
        var <- genVarNode ctx x
        t' <- gatherTermEdges ctx (M.insert x var env) t
        t0 <- genNode ctx $ c_lam var t'
        -- x -> dom(\x.t)
        -- cod(\x.t) -> t
        dom <- genNode ctx $ c_dom t0
        cod <- genNode ctx $ c_cod t0
        addEdge ctx (V var) dom
        addEdge ctx cod t'
        return t0
    go env (B.Proj _ i s t) = 
        go env t >>= genNode ctx . c_proj i s
    go env (B.And t1 t2) = do
        t1' <- go env t1 
        t2' <- go env t2
        genNode ctx (c_and t1' t2')
    go env (B.Or t1 t2) = do
        t1' <- go env t1 
        t2' <- go env t2
        genNode ctx (c_or t1' t2')
    go env (B.Not t) = 
        go env t >>= genNode ctx . c_not

gatherTermEdges :: Context s -> M.Map Symbol VarId -> B.Term -> ST s FlowTerm
gatherTermEdges ctx = go where
    go env (B.Pure t) = gatherVTermEdges ctx env t
    go env (B.App _ t1 t2) = do
        t1' <- gatherVTermEdges ctx env t1
        t2' <- gatherVTermEdges ctx env t2
        t0 <- genNode ctx (c_app t1' t2')
        -- dom(t1) -> t2
        -- t1 t2 -> cod(t1)
        dom <- genNode ctx (c_dom t1')
        cod <- genNode ctx (c_cod t1')
        addEdge ctx dom t2'
        addEdge ctx t0  cod
        return t0
    go env (B.Let _ x t1 t2) = do
        var <- genVarNode ctx x
        t1' <- go env t1
        t2' <- go (M.insert x var env) t2
        -- x -> t1
        addEdge ctx (V var) t1'
        t0 <- genNode ctx (c_let var t1' t2')
        addEdge ctx t0 t2'
        return t0
    go env (B.Assume _ t1 t2) = do
        t1' <- gatherVTermEdges ctx env t1
        t2' <- go env t2
        t0 <- genNode ctx (c_assume t1' t2')
        -- assume t1; t2 -> t2
        addEdge ctx t0 t2'
        return t0
    go env (B.Branch _ t1 t2) = do
        t1' <- go env t1
        t2' <- go env t2
        t0 <- genNode ctx (c_branch t1' t2')
        -- t1 + t2 -> t1
        -- t1 + t2 -> t2
        addEdge ctx t0 t1'
        addEdge ctx t0 t2'
        return t0
    go _ (B.Fail x) = do
        var <- genFailNode ctx x
        return (Fail var)

genVarNode :: Context s -> Symbol -> ST s VarId
genVarNode ctx x = do
    i <- incr (counter ctx)
    let var = VarId i x
        v   = V var
        k   = key v
    HT.insert (nodeTable ctx) k v
    HT.insert (labelTable ctx) i v
    return var

genFailNode :: Context s -> Symbol -> ST s VarId
genFailNode ctx x = do
    i <- incr (counter ctx)
    let var = VarId i x
        v   = Fail var
        k   = key v
    HT.insert (nodeTable ctx) k v
    HT.insert (labelTable ctx) i v
    return var

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

readTable :: (Hashable k,Eq k) => HashTable s k v -> k -> ST s v
readTable tbl i = fromJust <$> HT.lookup tbl i

calcClosure :: Context s -> ST s ()
calcClosure ctx = do 
    l <- map fst <$> HT.toList (edgeTable ctx)
    forM_ l $ \(i1,i2) -> do
        v1 <- readTable (labelTable ctx) i1
        v2 <- readTable (labelTable ctx) i2
        go (getSort v1) v1 v2
    where
    go (s1 :-> s2) v1 v2 = do
        dom1 <- genNode ctx $ c_dom v1
        dom2 <- genNode ctx $ c_dom v2
        cod1 <- genNode ctx $ c_cod v1
        cod2 <- genNode ctx $ c_cod v2
        addEdge ctx cod1 cod2
        addEdge ctx dom2 dom1
        go s2 cod1 cod2
        go s1 dom2 dom1
    go (Tuple ss) v1 v2 =
        forM_ (zip [0..] ss) $ \(i,s) -> do
            let n = i
                d = length ss
            vi1 <- genNode ctx $ c_proj n d v1
            vi2 <- genNode ctx $ c_proj n d v2
            addEdge ctx vi1 vi2
            go s vi1 vi2
    go _ _ _ = return ()

{-
type FlowGraph = (Array Id [Id], M.Map Symbol Id, Array Id (Maybe (Term ())))

reduce1 :: Array Id (Maybe (Term ())) -> Array Id [Id] -> M.Map Symbol Id -> FlowGraph
reduce1 tlbl g label = (g2,label',lbl') where
    bb = bounds g
    rename = runSTUArray $ do
        arr <- newArray bb (-1)
        c   <- newSTRef 0
        let dfs v = do
                x <- readArray arr v
                when (x == -1) $ do
                    i <- incr c
                    writeArray arr v i
                    forM_ (g1 ! v) sub
            sub v = do
                x <- readArray arr v
                if x == -1 then
                    case g1 ! v of
                        [w] | tlbl ! v == Nothing -> do
                            i <- sub w 
                            writeArray arr v i
                            return i
                        l   -> do
                            i <- incr c
                            writeArray arr v i
                            forM_ l sub
                            return i
                else
                    return x
        forM_ (M.elems label) dfs
        return arr
    n = maximum $ elems rename
    g1 :: Array Id [Id]
    g1 = array bb $ do (i,l) <- assocs g 
                       case tlbl ! i of
                         Just (V () _) -> return (i,l)
                         Just _ -> return (i,[])
                         Nothing -> return (i,l)
    g2 = accumArray (flip (:)) [] (0,n) $ do 
            (i,l) <- assocs g1
            guard (rename ! i  /= -1)
            j <- l
            let i' = rename ! i
                j' = rename ! j
            guard $ i' /= j'
            return (i',j')
    label' = M.fromList [ (x,rename ! i) | (x,i) <- M.toList label]
    lbl' = accumArray add empty (0,n) [ (j,tlbl ! i) | (i,j) <- assocs rename, j /= -1 ]

add :: Maybe t -> Maybe t -> Maybe t
add Nothing a = a
add a Nothing = a
add _ _ = undefined
-}

-- pretty printing
ppGraph :: (Show a) => Array Id a -> Array Id [Id] -> String
ppGraph lbl edges = renderDot g where
    g = Graph StrictGraph DirectedGraph Nothing (nodeS ++ edgeS)
    node i = NodeId (NameId (show i)) Nothing
    label v = AttributeSetValue (NameId "label") (StringId (take 15 (show v)))
    nodeS = [ NodeStatement (node i) [label v] | (i,v) <- assocs lbl] 
    edgeS = [ EdgeStatement [ENodeId NoEdge (node s),ENodeId DirectedEdge (node t)] [] | (s,l) <- assocs edges, t <- l ]

