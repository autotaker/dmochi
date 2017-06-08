{-# LANGUAGE DeriveGeneric, GeneralizedNewtypeDeriving, MultiParamTypeClasses, UndecidableInstances #-}
module Language.DMoCHi.ML.IncSaturationPre where
import           Language.DMoCHi.ML.Syntax.PNormal hiding(mkBin, mkUni, mkVar, mkLiteral)
import           Language.DMoCHi.ML.Syntax.HFormula
import           Language.DMoCHi.ML.Syntax.PType hiding(ArgType)
import           Language.DMoCHi.Common.Id
import           Language.DMoCHi.ML.Flow
import           Language.DMoCHi.ML.Syntax.IType
-- import qualified Language.DMoCHi.ML.Syntax.PNormal as PNormal

import           GHC.Generics (Generic)
import           Data.Kind(Constraint)
import           Control.Monad.Fix
import           Control.Monad.Reader
import           Control.Monad.Writer hiding((<>))
import           Control.Monad.State.Strict
import qualified Z3.Monad as Z3
import           Data.IORef
import           Data.Time
import           Data.Type.Equality
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.HashTable.IO as H
import           Data.Hashable
import qualified Language.DMoCHi.ML.SMT as SMT
import qualified Data.Sequence as Q
import           Text.PrettyPrint.HughesPJClass
import           Text.Printf

type HFormulaTbl = HashTable HFormula HFormula

data Context = 
  Context { 
    ctxFlowTbl :: HashTable UniqueKey (S.Set ([IType], BFormula))
  , ctxFlowReg :: HashTable UniqueKey [SomeNode]
  , ctxTypeMap :: TypeMap
  , ctxFlowMap :: FlowMap
  , ctxNodeCounter :: IORef Int
  , ctxRtnTypeTbl :: HashTable UniqueKey (PType, [HFormula]) 
  , ctxArgTypeTbl  :: HashTable UniqueKey ([PType], [HFormula]) 
  , ctxHFormulaTbl :: HFormulaTbl
  , ctxHFormulaSize :: IORef Int
  , ctxBFormulaTbl  :: HashTable BFormulaBody BFormula
  , ctxBFormulaSize :: IORef Int
  , ctxITypeTbl     :: HashTable ITypeBody IType
  , ctxITypeSize    :: IORef Int
  , ctxITermTbl     :: HashTable ITermTypeBody ITermType
  , ctxITermSize    :: IORef Int
  , ctxCheckSatCache :: HashTable (Int, Int) Bool
  , ctxUpdated :: IORef Bool
  , ctxSMTCount :: IORef Int
  , ctxSMTCountHit :: IORef Int
  , ctxTimer :: HashTable MeasureKey NominalDiffTime
  , ctxSMTSolver :: Z3.Solver
  , ctxSMTContext :: Z3.Context 
  }

data MeasureKey = CheckSat | CalcCondition | Total | MSaturation | MExtraction
    deriving (Eq, Ord, Show, Generic)

instance Hashable MeasureKey 

newtype R a = R { unR :: ReaderT Context (StateT (Queue UpdateQuery, S.Set Int) IO) a }
    deriving (Monad, Applicative, Functor, MonadFix, MonadIO)

instance MonadReader Context R where
    ask = R ask
    local f a = R (local f $ unR a)

instance MonadState (Queue UpdateQuery, S.Set Int) R where
    get = R get
    put x = R (put x)

instance Z3.MonadZ3 R where
    getSolver = ctxSMTSolver <$> ask
    getContext = ctxSMTContext <$> ask

instance HFormulaFactory R where
    genHFormula generator m_iv = do
        (_, _, v@(HFormula _ _ _ iv key)) <- mfix $ \ ~(ident, iv,_) ->  do
            let key = generator iv ident
            ctx <- ask
            let tbl = ctxHFormulaTbl ctx
            res <- liftIO $ H.lookup tbl key
            case res of
                Just v -> return (getIdent v, getIValue v, v)
                Nothing -> do
                    ident' <- liftIO $ readIORef (ctxHFormulaSize ctx)
                    liftIO $ writeIORef (ctxHFormulaSize ctx) $! (ident'+1)
                    liftIO $ H.insert tbl key key
                    iv' <- m_iv
                    return (ident', iv',key)
        key `seq` iv `seq` return v

instance ITypeFactory R where
    getITypeTable   = ctxITypeTbl <$> ask
    getITypeCounter = ctxITypeSize <$> ask
    getITermTable   = ctxITermTbl <$> ask
    getITermCounter = ctxITermSize <$> ask
    getBFormulaTable   = ctxBFormulaTbl <$> ask
    getBFormulaCounter = ctxBFormulaSize <$> ask

type PEnv = M.Map TId PType
type IEnv = M.Map TId IType

(!) :: (Ord k, Show k) => M.Map k v -> k -> v
(!) f a = case M.lookup a f of
    Just v -> v
    Nothing -> error $ "no assoc found for key: " ++ show a

pprintContext :: Program -> R Doc
pprintContext prog = do
    d_fs <- forM (functions prog) $ \(f,key,xs,e) -> do
        Just (ty_xs, ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxArgTypeTbl ctx) key
        let d_args = vcat $ zipWith (\x ty_x -> parens $ pPrint (name x) 
                                            <+> colon 
                                            <+> pPrint ty_x) xs ty_xs
            d_ps = hsep $ punctuate comma $ map pPrint ps
        d_body <- pprintE e
        return $ text "let" <+> pPrint (name f) <+> (case ps of [] -> d_args <+> text "="
                                                                _  -> d_args $+$ text "|" <+> d_ps <+> text "=")
                            $+$ (nest 4 d_body <> text ";;")
    d_main <- pprintE (mainTerm prog)
    return $ vcat d_fs $+$ d_main 
    where 
    pprintE :: Exp -> R Doc
    pprintE (Exp l arg sty key) = 
        let valueCase :: Value -> R Doc
            valueCase v = do
                d_v <- pprintV 0 v
                Just (ty_r, ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
                return $ comment (ty_r, ps) $+$ d_v
        in case (l, arg) of
            (SLiteral, _) -> valueCase (Value l arg sty key)
            (SVar, _)     -> valueCase (Value l arg sty key)
            (SUnary, _)   -> valueCase (Value l arg sty key)
            (SBinary, _)  -> valueCase (Value l arg sty key)
            (SPair, _)    -> valueCase (Value l arg sty key)
            (SLambda, _)  -> valueCase (Value l arg sty key)
            (SLet, (x, e1@(LExp l1 arg1 sty1 key1), e2)) ->
                let exprCase d_e1 = do
                        Just (ty_x, ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
                        d_e2 <- pprintE e2
                        let d_ps = hsep $ punctuate comma $ map pPrint ps
                        return $ 
                            text "let" <+> pPrint (name x)
                                       <+> (colon <+> pPrint ty_x <+> (case ps of [] -> empty
                                                                                  _  -> text "|" <+> d_ps) $+$
                                            text "=" <+> d_e1) 
                                       <+> text "in" 
                                       $+$ d_e2
                in case l1 of
                    SLiteral -> exprCase (pPrint e1)
                    SVar     -> exprCase (pPrint e1)
                    SUnary   -> exprCase (pPrint e1)
                    SBinary  -> exprCase (pPrint e1)
                    SPair    -> pprintE (Exp l1 arg1 sty1 key1) >>= exprCase
                    SLambda  -> pprintE (Exp l1 arg1 sty1 key1) >>= exprCase
                    SBranch  -> pprintE (Exp l1 arg1 sty1 key1) >>= exprCase
                    SFail    -> pprintE (Exp l1 arg1 sty1 key1) >>= exprCase
                    SOmega   -> pprintE (Exp l1 arg1 sty1 key1) >>= exprCase
                    SApp     -> do
                        let (f, vs) = arg1
                        Just (ty_vs, ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxArgTypeTbl ctx) key
                        vs' <- mapM (pprintV 0) vs
                        let d_e1 = pPrint (name f) <+> (case ps of [] -> d_vs
                                                                   _  -> d_vs $+$ text "|" <+> d_ps)
                            d_vs = vcat $ zipWith (\d_v ty_v -> parens $ d_v
                                                                     <+> text ":" 
                                                                     <+> pPrint ty_v) vs' ty_vs
                            d_ps = hsep $ punctuate comma $ map pPrint ps
                        exprCase d_e1 
                    SRand    -> exprCase (pPrint e1)
            (SLetRec, (fs, e2)) -> do
                d_fs <- forM fs $ \(f,v_f) -> do
                    d_f <- pprintV 0 v_f
                    return $ pPrint (name f) <+> text "=" <+> d_f
                d_e2 <- pprintE e2
                return $
                    text "let rec" <+> 
                        vcat (punctuate (text "and") d_fs)
                        <+> text "in" $+$
                    d_e2
            (SAssume, (cond, e)) -> do
                d_e <- pprintE e
                return $ text "assume" <+> pPrintPrec prettyNormal 9 cond <> text ";" $+$ d_e
            (SBranch, (e1, e2)) -> do
                d_e1 <- pprintE e1
                d_e2 <- pprintE e2
                return $ parens d_e1 <+> text "<>" $+$ parens d_e2
            (SFail, _) -> return $ text "Fail"
            (SOmega, _) -> return $ text "Omega"
    pprintV :: Rational -> Value -> R Doc
    pprintV prec v@(Value l arg _ key) =
        case (l, arg) of
            (SLiteral, _) -> return $ pPrintPrec prettyNormal prec v
            (SVar, _) -> return $  pPrintPrec prettyNormal prec v
            (SBinary, _) -> return $ pPrintPrec prettyNormal prec v
            (SUnary, _) -> return $ pPrintPrec prettyNormal prec v
            (SPair, (v1, v2)) -> do
                d_v1 <- pprintV 0 v1
                d_v2 <- pprintV 0 v2
                return $ parens $ d_v1 <> comma <+> d_v2
            (SLambda, (xs, e)) -> do
                Just (ty_xs, ps) <- do
                    m <- ask >>= \ctx -> liftIO $ H.lookup (ctxArgTypeTbl ctx) key
                    case m of Just v -> return (Just v)
                              Nothing -> error (render (pPrint v))
                d_e <- pprintE e
                let d_args = vcat $ zipWith (\x ty_x -> parens $ pPrint (name x) 
                                                    <+> colon 
                                                    <+> pPrint ty_x) xs ty_xs
                    d_ps = hsep $ punctuate comma $ map pPrint ps
                return $ maybeParens (prec > 0) $ 
                    text "fun" <+> (case ps of 
                                        [] -> d_args <+> text "->"
                                        _  -> d_args $+$ text "|" <+> d_ps <+> text "->") $+$
                        nest 4 d_e

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
    SomeNode :: NonRoot e => Node e -> SomeNode

data Root 

data Node e where
    Node :: (NonRoot e, Eq (SatType e)) => 
            { typeEnv    :: IEnv
            , constraint :: HFormula
            , ident      :: !Int
            , types      :: IORef (SatType e)
            , parent     :: Node e'
            , recalcator :: R (SatType e)
            , extractor  :: Extractor e
            , destructor :: R ()
            , pprinter   :: IO Doc
            , alive      :: IORef Bool
            , term       :: e
            } -> Node e
    RootNode :: { main :: Node Exp } -> Node Root

nodeId :: Node e -> Int
nodeId (Node { ident = ident }) = ident
nodeId (RootNode _) = 0

instance Eq SomeNode where
    (SomeNode n1) == (SomeNode n2) = nodeId n1 == nodeId n2

instance Ord SomeNode where
    compare (SomeNode n1) (SomeNode n2) = compare (nodeId n1) (nodeId n2)

type family NonRoot e :: Constraint where
    NonRoot e = (e == Root) ~ 'False

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

printStatistics :: R ()
printStatistics = do
    ctx <- ask
    liftIO $ do
        nodeSize <- readIORef (ctxNodeCounter ctx)
        hfmlSize <- readIORef (ctxHFormulaSize ctx)
        bfmlSize <- readIORef (ctxBFormulaSize ctx)
        itypSize <- readIORef (ctxITypeSize ctx)
        itrmSize <- readIORef (ctxITermSize ctx)
        smtCalls <- readIORef (ctxSMTCount ctx)
        smtHits  <- readIORef (ctxSMTCountHit ctx)
        printf "Graph size: %7d\n" nodeSize
        printf "#HFormula:  %7d\n" hfmlSize
        printf "#BFormula:  %7d\n" bfmlSize
        printf "#IType:     %7d\n" itypSize
        printf "#ITerm:     %7d\n" itrmSize
        printf "#SMT Calls: %7d\n" smtCalls
        printf "#SMT Hits:  %7d\n" smtHits
        H.mapM_ (\(key, t) ->
            printf "Time %s: %s\n" (show key) (show t)) (ctxTimer ctx)

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
printNode (RootNode _) = putStrLn "ROOT"
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
