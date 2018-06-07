{-# LANGUAGE DeriveGeneric, GeneralizedNewtypeDeriving, MultiParamTypeClasses, UndecidableInstances, RecordWildCards, OverloadedLabels #-}
module Language.DMoCHi.ML.IncSaturationPre (  
    R(..), IncSat,HContext,Node(..), SomeNode(..), UpdateQuery(..), LExpNode, ExpNode, ValueNode,
    CValue(..), CEnv, IEnv, TermExtractor, ValueExtractor, Extractor, SatType, NodeId, HashTable,
    QueryType(..), Context(..),
    getStatistics,  extractTrace,  initContext, runR,
    pushQuery, popQuery,  getNode,  genNode, setParent, getTypes, setTypes,
    extendConstraintVar, extendConstraintCond, genericPrint,  branch, 
    insertTbl, lookupTbl) where
import           Language.DMoCHi.ML.Syntax.CEGAR 
import           Language.DMoCHi.ML.Syntax.HFormula hiding(Context)
import qualified Language.DMoCHi.ML.Syntax.HFormula as HFormula
import           Language.DMoCHi.Common.Id
import           Language.DMoCHi.Common.Util
import           Language.DMoCHi.Common.Cache
import           Language.DMoCHi.ML.Flow
import           Language.DMoCHi.ML.Syntax.IType

import           GHC.Generics (Generic)
import           Control.Applicative
import           Control.Monad.Fix
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import qualified Z3.Monad as Z3
import           Data.IORef
import           Data.Time
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.HashTable.IO as H
import           Data.Hashable
import qualified Data.Sequence as Q
import           Text.PrettyPrint.HughesPJClass
import qualified Data.PolyDict as Dict
import           Data.PolyDict(Dict,access)
import qualified Data.DList as DL

type NodeId = Int
type HashTable k v = H.BasicHashTable k v
type HContext = HFormula.Context

data Context = 
  Context { 
    ctxFlowTbl :: !(HashTable UniqueKey (S.Set ([IType], BFormula)))
  , ctxFlowReg :: !(HashTable UniqueKey [NodeId])
  , ctxFlowMap :: !FlowMap
  , ctxNodeCounter   :: !(IORef Int)
  , ctxNodeTbl       :: !(HashTable NodeId SomeNode)
  -- dependency graph, nodes in ctxNodeDepG (ident n) should be updated if node n is updated
  , ctxNodeDepG      :: !(HashTable NodeId [NodeId])
  
  , ctxFreeVarTbl    :: !(HashTable UniqueKey (S.Set TId))
  , ctxITypeCache    :: !(Cache IType)
  , ctxITermCache    :: !(Cache ITermType)
  , ctxUpdated       :: !(IORef Bool)
  , ctxTimer :: !(HashTable MeasureKey NominalDiffTime)
  }

data MeasureKey = CheckSat | CalcCondition | Total | MSaturation | MExtraction
    deriving (Eq, Ord, Show, Generic)

instance Hashable MeasureKey 

newtype R a = R { unR :: ReaderT Context (StateT (Queue UpdateQuery, S.Set Int) (HFormulaT (LoggingT IO))) a }
    deriving (Monad, Applicative, Functor, MonadFix, MonadIO,MonadLogger)

instance MonadReader Context R where
    ask = R ask
    local f a = R (local f $ unR a)

getHFormulaContext :: R HFormula.Context
getHFormulaContext = R (lift ask)

runR :: HContext -> Context -> R a -> LoggingT IO a
runR hctx ctx doit = do
    runHFormulaT (evalStateT (runReaderT (unR doit) ctx) (emptyQueue, S.empty)) hctx

instance MonadState (Queue UpdateQuery, S.Set Int) R where
    get = R get
    put x = R (put x)

instance BFormulaFactory R where
    getBFormulaCache = ctxBFormulaCache <$> getHFormulaContext

instance Z3.MonadZ3 R where
    getSolver = R (lift $ lift $ Z3.getSolver)
    getContext = R (lift $ lift $ Z3.getContext)


instance HFormulaFactory R where
    getHFormulaCache = R (lift $ lift $ getHFormulaCache)
    checkSat a b = R (lift $ lift $ checkSat a b)


instance ITypeFactory R where
    getITypeCache = ctxITypeCache <$> ask
    getITermCache = ctxITermCache <$> ask


type IEnv = M.Map TId IType

initContext :: Program -> LoggingT IO Context
initContext prog = do
    flowMap <- flowAnalysis prog
    liftIO $ do
        ctxFlowTbl     <- H.new
        ctxFlowReg     <- H.new
        ctxFlowMap     <- pure flowMap
        ctxNodeCounter <- newIORef 1
        ctxNodeTbl     <- H.new
        ctxNodeDepG    <- H.new
        ctxFreeVarTbl  <- H.new
        ctxITypeCache  <- newCache
        ctxITermCache  <- newCache
        ctxUpdated     <- newIORef False
        ctxTimer       <- H.new
        return (Context {..})

data CValue = CBase | CPair CValue CValue 
            | CRec CEnv TId (HashTable (TId, ArgType, ITermType) ValueNode)
            | CCls CEnv [TId] (HashTable ArgType ExpNode)
type CEnv = M.Map TId CValue
-- type History = HashTable (TId, ArgType, ITermType) ValueNode

type ArgType = ([IType],BFormula)

type Queue a = Q.Seq a
emptyQueue :: Queue a
emptyQueue = Q.empty

popQueue :: Queue a -> Maybe (a, Queue a)
popQueue queue = case Q.viewl queue of
    Q.EmptyL -> Nothing
    a Q.:< queue' -> Just (a, queue')

pushQueue :: a -> Queue a -> Queue a
pushQueue a queue = queue Q.|> a

data SomeNode where
    SomeNode :: Node e -> SomeNode

data Node e where
    Node :: (Eq (SatType e)) => 
            { typeEnv    :: IEnv
            , constraint :: HFormula
            , ident      :: !NodeId
            , types      :: !(IORef (SatType e))
            , recalcator :: R (SatType e)
            , extractor  :: Extractor e
            , destructor :: R ()
            , pprinter   :: IO Doc
            , alive      :: !(IORef Bool)
            , term       :: e
            } -> Node e

nodeId :: Node e -> NodeId
nodeId (Node { ident = ident }) = ident


instance Eq SomeNode where
    (SomeNode n1) == (SomeNode n2) = nodeId n1 == nodeId n2

instance Ord SomeNode where
    compare (SomeNode n1) (SomeNode n2) = compare (nodeId n1) (nodeId n2)

type family SatType e where
    SatType Exp = [ITermType]
    SatType LExp = [ITermType]
    SatType Value = IType

type family Extractor e where
    Extractor Exp   = TermExtractor
    Extractor LExp  = TermExtractor
    Extractor Value = ValueExtractor
type TermExtractor = CEnv -> ITermType -> Extract CValue
type ValueExtractor = CEnv -> CValue

newtype Extract a = Extract { runExtract :: R (DL.DList Bool, Maybe a) }

extractTrace :: Extract a -> R [Bool]
extractTrace m = DL.toList . fst <$> runExtract m

branch :: Bool -> Extract ()
branch b = Extract $ pure (DL.singleton b, Just ())

instance Functor Extract where
    {-# INLINE fmap #-}
    fmap f (Extract a) = Extract (fmap (\(tr, r) -> (tr, fmap f r)) a)
instance Applicative Extract where
    {-# INLINE pure #-}
    {-# INLINE (<*>) #-}
    pure a = Extract $ pure (mempty, Just a)
    (<*>) = ap
instance Alternative Extract where
    {-# INLINE empty #-}
    {-# INLINE (<|>) #-}
    empty = Extract $ pure (mempty, Nothing)
    Extract a <|> Extract b = Extract $ do
        (tr1, ma) <- a
        case ma of
            Just _ -> pure (tr1, ma)
            Nothing -> b
instance MonadPlus Extract 

instance Monad Extract where
    {-# INLINE (>>=) #-}
    Extract mv >>= f = Extract $ do
        (tr, mv) <- mv
        case mv of
            Just v -> do
                (tr', mr) <- runExtract (f v)
                pure (tr `mappend` tr', mr)
            Nothing -> pure (tr, Nothing)
instance MonadIO Extract where
    {-# INLINE liftIO #-}
    liftIO ioaction = Extract $ (mempty,) . Just <$> liftIO ioaction


type ValueNode = Node Value
type ExpNode = Node Exp
type LExpNode = Node LExp


data UpdateQuery = UpdateQuery QueryType NodeId

data QueryType = QFlow | QEdge

queryId :: UpdateQuery -> NodeId
queryId (UpdateQuery _ i) = i

incrNodeCounter :: R NodeId
incrNodeCounter = 
    asks ctxNodeCounter >>= \tbl -> 
        liftIO $ do
            v <- readIORef tbl
            v <$ (writeIORef tbl $! v+1)

{- 
measureTime :: MeasureKey -> R a -> R a
measureTime key action = do
    t_start <- liftIO getCurrentTime
    res <- action
    t_end <- liftIO getCurrentTime
    let dt = diffUTCTime t_end t_start
    asks ctxTimer >>= \tbl -> liftIO $ do
        r <- H.lookup tbl key
        case r of
            Nothing -> H.insert tbl key $! dt
            Just t  -> H.insert tbl key $! dt + t
    return res
    -}

data IncSat
type instance Dict.Assoc IncSat "graph_size" = Int
type instance Dict.Assoc IncSat "number_hformula" = Int
type instance Dict.Assoc IncSat "number_bformula" = Int
type instance Dict.Assoc IncSat "number_itype" = Int
type instance Dict.Assoc IncSat "number_iterm" = Int
type instance Dict.Assoc IncSat "number_smt_call" = Int
type instance Dict.Assoc IncSat "number_smt_hit" = Int
type instance Dict.Assoc IncSat "time" = M.Map String NominalDiffTime

getStatistics :: HFormula.Context -> Context -> IO (Dict IncSat)
getStatistics hctx ctx = do
    nodeSize <- readIORef (ctxNodeCounter ctx)
    hfmlSize <- getCacheSize (ctxHFormulaCache hctx)
    bfmlSize <- getCacheSize (ctxBFormulaCache hctx)
    itypSize <- getCacheSize (ctxITypeCache ctx)
    itrmSize <- getCacheSize (ctxITermCache ctx)
    smtCalls <- readIORef (ctxSMTCount hctx)
    smtHits  <- readIORef (ctxSMTCountHit hctx)
    times <- M.fromList . map (\(a,b) -> (show a, b))<$> H.toList (ctxTimer ctx)
    return $ Dict.empty & access #graph_size ?~ nodeSize
                        & access #number_hformula ?~ hfmlSize
                        & access #number_bformula ?~ bfmlSize
                        & access #number_itype    ?~ itypSize
                        & access #number_iterm    ?~ itrmSize
                        & access #number_smt_call ?~ smtCalls
                        & access #number_smt_hit  ?~ smtHits
                        & access #time ?~ times

genericPrint :: IEnv -> HFormula -> e -> IORef (SatType e) -> Int -> (e -> Doc) -> (SatType e -> Doc) -> IO Doc
genericPrint env fml e tys_ref ident termPrinter typePrinter = do
    tys <- readIORef tys_ref
    let doc_term = termPrinter e
        doc_ity = typePrinter tys
        doc = text "env: " <+> (nest 4 $
              brackets $ vcat $ [ pPrint (name f) <+> text ":" <+> pPrint ity | (f,ity) <- M.assocs env ])
          $+$ text "cond: " <+> (pPrint fml)
          $+$ text "idnt: " <+> (pPrint ident)
          $+$ text "term: " <+> (text (takeWhile (/='\n') $ show doc_term))
          $+$ text "type:" <+> doc_ity
    return doc
    

popQuery :: R (Maybe UpdateQuery)
popQuery = state $ \(que, nodes) -> case popQueue que of
                Nothing -> (Nothing, (que, nodes))
                Just (a,que') -> (Just a, (que', S.delete (queryId a) nodes))

pushQuery :: UpdateQuery -> R ()
pushQuery q = modify' $ \(que, nodes) -> 
    let ident = queryId q in
    if S.member ident nodes
    then (que, nodes)
    else (pushQueue q que, S.insert ident nodes)


genNode :: (NodeId -> R (Node e)) -> R (Node e)
genNode constr = do
    i <- incrNodeCounter
    n <- constr i
    n <$ (asks ctxNodeTbl >>= (\tbl -> 
                liftIO (H.insert tbl i (SomeNode n))))

getNode :: NodeId -> R SomeNode
getNode i = do
    tbl <- asks ctxNodeTbl
    liftIO (H.lookup tbl i) >>= \case
        Just v -> return v
        Nothing -> error $ "getNode: This node id " ++ (show i) ++ " is not registered!"

setParent :: NodeId -> Node e -> R (Node e)
setParent pId node = 
    node <$ (asks ctxNodeDepG >>= \tbl -> 
                insertTbl tbl (nodeId node) [pId])

{-# INLINE getTypes #-}
getTypes :: MonadIO m => Node e -> m (SatType e)
getTypes (Node { types = types }) = liftIO $ readIORef types

{-# INLINE setTypes #-}
setTypes :: MonadIO m => Node e -> SatType e -> m ()
setTypes (Node { types = types }) ty = liftIO $ writeIORef types ty

{-# INLINE extendConstraintVar #-}
extendConstraintVar :: HFormulaFactory m => HFormula -> TId -> HFormula -> m HFormula
extendConstraintVar fml x vx = 
    mkBin SAnd fml =<< (mkVar x >>= \x -> mkBin SEq x vx)

{-# INLINE extendConstraintCond #-}
extendConstraintCond :: HFormulaFactory m => HFormula -> HFormula -> m HFormula
extendConstraintCond = mkBin SAnd

{-# INLINE insertTbl #-}
insertTbl :: (MonadIO m, Eq key, Hashable key, Monoid a) => HashTable key a -> key -> a -> m ()
insertTbl tbl key value = liftIO $ 
    H.lookup tbl key >>= \case
        Just l -> H.insert tbl key (value `mappend` l)
        Nothing -> H.insert tbl key value

{-# INLINE lookupTbl #-}
lookupTbl :: (MonadIO m, Eq key, Hashable key, Monoid a) => HashTable key a -> key -> m a 
lookupTbl tbl key = liftIO $ 
    H.lookup tbl key >>= \case
        Just l -> return l
        Nothing -> return mempty
