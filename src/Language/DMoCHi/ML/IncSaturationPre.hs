{-# LANGUAGE DeriveGeneric, GeneralizedNewtypeDeriving, MultiParamTypeClasses, UndecidableInstances, RecordWildCards, OverloadedLabels #-}
module Language.DMoCHi.ML.IncSaturationPre where
import           Language.DMoCHi.ML.Syntax.CEGAR hiding(mkBin, mkUni, mkVar, mkLiteral)
import           Language.DMoCHi.ML.Syntax.PNormal (Atom(..))
import           Language.DMoCHi.ML.Syntax.HFormula hiding(Context)
import qualified Language.DMoCHi.ML.Syntax.HFormula as HFormula
import           Language.DMoCHi.ML.Syntax.PType hiding(ArgType)
import           Language.DMoCHi.Common.Id
import           Language.DMoCHi.Common.Util
import           Language.DMoCHi.Common.Cache
import           Language.DMoCHi.ML.Flow
import           Language.DMoCHi.ML.Syntax.IType

import           GHC.Generics (Generic)
-- import           Data.Kind(Constraint)
import           Control.Monad.Fix
import           Control.Monad.Reader
import           Control.Monad.Writer hiding((<>))
import           Control.Monad.State.Strict
import qualified Z3.Monad as Z3
-- import qualified Z3.Base as Z3Base
import           Data.IORef
import           Data.Time
--import           Data.Type.Equality
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.HashTable.IO as H
import           Data.Hashable
import qualified Data.Sequence as Q
import           Text.PrettyPrint.HughesPJClass
import qualified Data.PolyDict as Dict
import           Data.PolyDict(Dict,access)

type NodeId = Int
type HashTable k v = H.BasicHashTable k v

data Context = 
  Context { 
    ctxFlowTbl :: HashTable UniqueKey (S.Set ([IType], BFormula))
  , ctxFlowReg :: HashTable UniqueKey [NodeId]
  , ctxFlowMap :: FlowMap
  , ctxNodeCounter   :: IORef Int
  , ctxNodeTbl       :: HashTable NodeId SomeNode
  -- dependency graph, nodes in ctxNodeDepG (ident n) should be updated if node n is updated
  , ctxNodeDepG      :: HashTable NodeId [NodeId]
  
--  , ctxRtnTypeTbl    :: HashTable UniqueKey ([HFormula], Scope) 
--  , ctxArgTypeTbl    :: HashTable UniqueKey ([HFormula], Scope) 
  , ctxFreeVarTbl    :: HashTable UniqueKey (S.Set TId)
  , ctxITypeCache    :: Cache IType
  , ctxITermCache    :: Cache ITermType
  , ctxUpdated       :: IORef Bool
  , ctxTimer :: HashTable MeasureKey NominalDiffTime
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


type PEnv = M.Map TId PType
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
        -- ctxRtnTypeTbl  <- H.new
        -- ctxArgTypeTbl  <- H.new
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
type History = HashTable (TId, ArgType, ITermType) ValueNode

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
            , types      :: IORef (SatType e)
            , recalcator :: R (SatType e)
            , extractor  :: Extractor e
            , destructor :: R ()
            , pprinter   :: IO Doc
            , alive      :: IORef Bool
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
type TermExtractor = CEnv -> ITermType -> WriterT [Bool] R (Maybe CValue)
type ValueExtractor = CEnv -> CValue

type ValueNode = Node Value
type ExpNode = Node Exp
type LExpNode = Node LExp


data UpdateQuery = UpdateQuery QueryType NodeId

data QueryType = QFlow | QEdge

queryId :: UpdateQuery -> NodeId
queryId (UpdateQuery _ i) = i

incrNodeCounter :: R NodeId
incrNodeCounter = ask >>= \ctx -> liftIO $ do
    v <- readIORef (ctxNodeCounter ctx)
    writeIORef (ctxNodeCounter ctx) $! v+1
    return v


measureTime :: MeasureKey -> R a -> R a
measureTime key action = do
    t_start <- liftIO getCurrentTime
    res <- action
    t_end <- liftIO getCurrentTime
    let dt = diffUTCTime t_end t_start
    ask >>= \ctx -> liftIO $ do
        r <- H.lookup (ctxTimer ctx) key
        case r of
            Nothing -> H.insert (ctxTimer ctx) key $! dt
            Just t  -> H.insert (ctxTimer ctx) key $! dt + t
    return res

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
    
printNode :: Node e -> IO ()
printNode (Node { pprinter = pp }) = pp >>= print

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


scopeOfAtom :: M.Map TId [Atom] -> Atom -> [Atom]
scopeOfAtom env (Atom l arg _) = 
    case (l, arg) of
        (SLiteral, _) -> []
        (SVar, x) -> (env M.! x)
        (SUnary, UniArg _ a1) ->  scopeOfAtom env a1
        (SBinary, _) -> []

genNode :: (NodeId -> R (Node e)) -> R (Node e)
genNode constr = do
    i <- incrNodeCounter
    n <- constr i
    tbl <- ctxNodeTbl <$> ask
    liftIO $ H.insert tbl i (SomeNode n)
    return n

getNode :: NodeId -> R SomeNode
getNode i = do
    tbl <- ctxNodeTbl <$> ask
    liftIO (H.lookup tbl i) >>= \case
        Just v -> return v
        Nothing -> error $ "getNode: This node id " ++ (show i) ++ " is not registered!"

setParent :: NodeId -> Node e -> R (Node e)
setParent pId node = ask >>= \ctx -> do
    liftIO $ insertTbl (ctxNodeDepG ctx) (nodeId node) pId
    return node

getTypes :: MonadIO m => Node e -> m (SatType e)
getTypes (Node { types = types }) = liftIO $ readIORef types

setTypes :: MonadIO m => Node e -> SatType e -> m ()
setTypes (Node { types = types }) ty = liftIO $ writeIORef types ty

insertTbl :: (Eq key, Hashable key) => HashTable key [a] -> key -> a -> IO ()
insertTbl tbl key value = 
    H.lookup tbl key >>= \case
        Just l -> H.insert tbl key (value : l)
        Nothing -> H.insert tbl key [value]

lookupTbl :: (Eq key,Hashable key) => HashTable key [a] -> key -> IO [a]
lookupTbl tbl key =
    H.lookup tbl key >>= \case
        Just l -> return l
        Nothing -> return []

