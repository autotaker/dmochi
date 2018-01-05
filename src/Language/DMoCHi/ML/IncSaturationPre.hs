{-# LANGUAGE DeriveGeneric, GeneralizedNewtypeDeriving, MultiParamTypeClasses, UndecidableInstances, RecordWildCards #-}
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


data Context = 
  Context { 
    ctxFlowTbl :: HashTable UniqueKey (S.Set ([IType], BFormula))
  , ctxFlowReg :: HashTable UniqueKey [SomeNode]
  , ctxFlowMap :: FlowMap
  , ctxNodeCounter   :: IORef Int
  , ctxNodeTbl       :: HashTable Int SomeNode
  , ctxNodeDepG      :: HashTable Int [SomeNode]
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

(!) :: (Ord k, Show k) => M.Map k v -> k -> v
(!) f a = case M.lookup a f of
    Just v -> v
    Nothing -> error $ "no assoc found for key: " ++ show a

initContext :: Program -> LoggingT IO Context
initContext prog = do
    flowMap <- flowAnalysis prog
    liftIO $ do
        {-
        (ctxSMTSolver, ctxSMTContext) <- Z3Base.withConfig $ \cfg -> do
            Z3.setOpts cfg Z3.stdOpts
            ctx <- Z3Base.mkContext cfg
            solver <- Z3Base.mkSolver ctx
            return (solver, ctx) -}
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
            , ident      :: !Int
            , types      :: IORef (SatType e)
            , recalcator :: R (SatType e)
            , extractor  :: Extractor e
            , destructor :: R ()
            , pprinter   :: IO Doc
            , alive      :: IORef Bool
            , term       :: e
            } -> Node e

nodeId :: Node e -> Int
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


data UpdateQuery where
     UpdateQuery :: QueryType -> (Node e) -> UpdateQuery

data QueryType = QFlow | QEdge

queryId :: UpdateQuery -> Int
queryId (UpdateQuery _ node) = nodeId node

incrNodeCounter :: R Int
incrNodeCounter = ask >>= \ctx -> liftIO $ do
    v <- readIORef (ctxNodeCounter ctx)
    writeIORef (ctxNodeCounter ctx) $! v+1
    return v

{-
-- Function: calcCondition fml ps 
-- assumption: fml is a satisfiable formula
-- assertion: phi |- fromBFormula ps ret
calcCondition :: HFormula -> [HFormula] -> R BFormula
calcCondition _fml _ps = measureTime CalcCondition $ do
    phi <- go 1 _fml _ps
    {-
    liftIO $ print $ text "calcCondtion" $+$ 
            braces (
                text "assumption:" <+> pPrint _fml $+$
                text "predicates:" <+> (brackets $ hsep $ punctuate comma (map pPrint _ps)) $+$
                text "result:"     <+> text (show phi)
            )
            -}
    return phi
    where
    go _ _ [] = mkBLeaf True
    go i fml (p:ps) = do
        np <- mkUni SNot p
        b1 <- checkSat fml p
        b2 <- checkSat fml np
        v1 <- if b1 then mkBin SAnd fml p >>= \fml' -> go (i + 1) fml' ps 
                    else mkBLeaf False
        v2 <- if b2 then mkBin SAnd fml np >>= \fml' -> go (i + 1) fml' ps 
                    else mkBLeaf False
        mkBNode i v1 v2

fromBFormula :: [HFormula] -> BFormula -> R HFormula
fromBFormula ps fml = 
    case bfmlBody fml of
        BLeaf b -> mkLiteral (CBool b)
        BNode i p1 p2 -> do
            v1 <- fromBFormula ps p1
            v2 <- fromBFormula ps p2
            let x = ps !! (i - 1)
            nx <- mkUni SNot x
            v1 <- mkBin SAnd x  v1
            v2 <- mkBin SAnd nx v2
            mkBin SOr v1 v2
            -}


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

getStatistics :: Context -> IO (Dict IncSat)
getStatistics ctx = do
    nodeSize <- readIORef (ctxNodeCounter ctx)
    {-
    hfmlSize <- readIORef (ctxHFormulaSize ctx)
    bfmlSize <- readIORef (ctxBFormulaSize ctx)
    itypSize <- readIORef (ctxITypeSize ctx)
    itrmSize <- readIORef (ctxITermSize ctx)
    smtCalls <- readIORef (ctxSMTCount ctx)
    smtHits  <- readIORef (ctxSMTCountHit ctx)
    -}
    times <- M.fromList . map (\(a,b) -> (show a, b))<$> H.toList (ctxTimer ctx)
    return $ Dict.empty & access #graph_size ?~ nodeSize
                       {-
                        & access #number_hformula ?~ hfmlSize
                        & access #number_bformula ?~ bfmlSize
                        & access #number_itype    ?~ itypSize
                        & access #number_iterm    ?~ itrmSize
                        & access #number_smt_call ?~ smtCalls
                        & access #number_smt_hit  ?~ smtHits
                        -}
                        & access #time ?~ times

{-
checkSat :: HFormula -> HFormula -> R Bool
checkSat p1 p2 = measureTime CheckSat $ do
    ctx <- ask
    let key = (getIdent p1, getIdent p2)
    res <- liftIO $ H.lookup (ctxCheckSatCache ctx) key
    -- liftIO $ print $ text "checkSat" <+> pPrint key <+> pPrint p1 <+> text "|-" <+> pPrint p2
    case res of
        Just v -> do
            liftIO $ modifyIORef' (ctxSMTCountHit ctx) succ 
            return v
        Nothing -> do 
            liftIO $ modifyIORef' (ctxSMTCount ctx) succ 

            v <- (Z3.local :: R Bool -> R Bool) $ do
                SMT.ASTValue cond <- getIValue <$> mkBin SAnd p1 p2  
                Z3.assert cond
                res <- Z3.check
                case res of
                    Z3.Sat -> return True
                    Z3.Unsat -> return False
                    Z3.Undef -> liftIO $ putStrLn "Undef" >> return True
            liftIO $ H.insert (ctxCheckSatCache ctx) key v
            return v
            -}

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

