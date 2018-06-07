{-# LANGUAGE RecordWildCards #-}

module Language.DMoCHi.ML.IncSaturation(saturate,IncSat) where
import           Language.DMoCHi.ML.Syntax.CEGAR 
import           Language.DMoCHi.ML.Syntax.HFormula(HFormula(..), mkTrue, calcCondition, checkSat, fromBFormula)
import           Language.DMoCHi.ML.Syntax.IType
import           Language.DMoCHi.Common.Id
import           Language.DMoCHi.Common.Util
import           Language.DMoCHi.ML.IncSaturationPre(
    R(..), IncSat,HContext,Node(..), SomeNode(..), UpdateQuery(..), LExpNode, ExpNode, ValueNode,
    CValue(..), CEnv, IEnv, TermExtractor, ValueExtractor, Extractor, SatType, NodeId, HashTable,
    QueryType(..), Context(..),
    getStatistics,  extractTrace,  initContext, runR,
    pushQuery, popQuery,  getNode,  genNode, setParent, getTypes, setTypes,
    extendConstraintVar, extendConstraintCond, genericPrint,  branch, 
    insertTbl, lookupTbl, 
    )

import           Control.Monad.Trans.Maybe(MaybeT(..))
import           Control.Monad.Trans(lift)
import           Control.Monad.Reader(asks)
import           Control.Monad
import           Control.Monad.IO.Class(liftIO)
import           Data.IORef
import           Data.Maybe(isNothing)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.HashTable.IO as H
import           Text.PrettyPrint.HughesPJClass
--import           Debug.Trace
import           Data.PolyDict(Dict)

getFlow :: UniqueKey -> R [([IType], BFormula)]
getFlow i = do
    tbl <- asks ctxFlowTbl 
    S.toList <$> lookupTbl tbl i
    -- liftIO $ print ("getFlow", i, l)

addFlow :: UniqueKey -> ([IType], BFormula) -> R ()
addFlow i v = do
    tbl <- asks ctxFlowTbl
    let cont :: S.Set ([IType], BFormula) -> R ()
        cont !vs' = 
            liftIO (H.insert tbl i vs') >>
            asks ctxFlowReg 
            >>= \reg -> lookupTbl reg i
            >>= mapM_ (pushQuery . UpdateQuery QFlow)
    liftIO (H.lookup tbl i) >>= \case
        Just vs 
            | S.member v vs -> return ()
            | otherwise -> cont (S.insert v vs)
        Nothing -> cont (S.singleton v)
    -- liftIO $ print ("addFlow", i, v)

whenSat :: HFormula -> [HFormula] -> BFormula -> a -> (HFormula -> R a) -> R a
whenSat fml ps phi def cont = do
    cond <- fromBFormula ps phi
    fml' <- extendConstraintCond fml cond
    checkSat fml cond >>= \case
        False -> return def
        True  -> cont fml'

bindTermType :: (IType -> BFormula -> R [ITermType])  -> [ITermType] -> R [ITermType]
bindTermType f tys = fmap concatMerge $ forM tys $ \case
    IFail -> return [mkIFail]
    ITerm ity phi -> f ity phi

calcAtom :: IEnv -> HFormula -> IType
calcAtom env = go
    where
    go (HFormula l arg _ _ _) =
      case (l, arg) of
        (SLiteral, _) -> mkIBase
        (SVar, x) -> env ! x
        (SBinary, _) -> mkIBase
        (SUnary, UniArg op v1) ->
          case (op, go v1) of
            (SFst, IPair i1 _) -> i1
            (SSnd, IPair _ i2) -> i2
            (SFst, _) -> error "calcAtom: unexpected pattern"
            (SSnd, _) -> error "calcAtom: unexpected pattern"
            (SNeg, _) -> mkIBase
            (SNot, _) -> mkIBase

evalAtom :: CEnv -> HFormula -> CValue
evalAtom cenv = go
    where
    go (HFormula l arg _ _ _) =
      case (l, arg) of
        (SLiteral, _) -> CBase
        (SVar, x) -> cenv ! x
        (SBinary, _) -> CBase
        (SUnary, UniArg op v1) ->
          case (op, go v1) of
            (SFst, CPair c1 _) -> c1
            (SSnd, CPair _ c2) -> c2
            (SFst, _) -> error "evalAtom: unexpected pattern"
            (SSnd, _) -> error "evalAtom: unexpected pattern"
            (SNeg, _) -> CBase
            (SNot, _) -> CBase

calcPair :: IEnv -> HFormula -> NodeId -> (Value,Value) -> 
            (R IType -> ValueExtractor -> R () -> R a) -> R a
calcPair env fml pId (v1,v2) cont = do
    node1 <- calcValue env fml v1  >>= setParent pId
    node2 <- calcValue env fml v2  >>= setParent pId
    let recalc = join $ mkIPair <$> getTypes node1 <*> getTypes node2
        extract env = CPair (extractor node1 env) (extractor node2 env)
        destruct = destructor node1 >> destructor node2
    cont recalc extract destruct
    
calcLambda :: IEnv -> HFormula -> NodeId -> UniqueKey -> ([TId], AbstInfo, Exp) -> 
            (R IType -> ValueExtractor -> R () -> R a) -> R a
calcLambda env fml pId key (xs, _abstInfo, e) cont = do
    let ps = abstFormulas _abstInfo
    tbl <- liftIO H.new
    asks ctxFlowReg >>= \tbl -> insertTbl tbl key [pId]
    let recalc = 
            getFlow key 
            >>= mapM child
            >>= mkIFun . mconcat
        child (thetas, phi) = 
            liftIO (H.lookup tbl (thetas,phi)) 
            >>= maybe genBody getTypes 
            >>= pure . map (thetas, phi,)
            where
            genBody = whenSat fml ps phi [] $ \fml' -> do
                let env' = extendEnv env (zip xs thetas)
                node_body <- calcExp env' fml' e >>= setParent pId
                liftIO $ H.insert tbl (thetas,phi) node_body
                getTypes node_body
        extract env = CCls env xs tbl
        destruct = liftIO (H.toList tbl) >>= mapM_ (destructor . snd) 
    cont recalc extract destruct
                
calcBranch :: IEnv -> HFormula -> Int -> (Exp, Exp) -> 
            (R [ITermType] -> TermExtractor -> R () -> R a) -> R a
calcBranch env fml pId (e1, e2) cont = do
    node1 <- calcExp env fml e1 >>= setParent pId
    node2 <- calcExp env fml e2 >>= setParent pId
    let recalc = merge <$> getTypes node1 <*> getTypes node2
        extract cenv iota = do
            tys1 <- getTypes node1
            if any (`subTermTypeOf` iota) tys1
            then branch True  >> extractor node1 cenv iota
            else branch False >> extractor node2 cenv iota
        destruct = destructor node1 >> destructor node2
    cont recalc extract destruct


calcLet :: IEnv -> HFormula -> Int -> (TId, LExp, AbstInfo, Exp)  ->
            (R [ITermType] -> TermExtractor -> R () -> R a) -> R a
calcLet env fml pId  (x, e1, abstInfo, e2) cont = 
    calcLExp env fml x e1 atomCase otherCase
    where
    atomCase ity fml' ev = do
        let env' = M.insert x ity env
        node2 <- calcExp env' fml' e2 >>= setParent pId
        let recalc = getTypes node2 
            extract cenv iota = extractor node2 cenv' iota 
                where cenv' = M.insert x (ev cenv) cenv
        cont recalc extract (destructor node2)
    otherCase node1 = do
        _ <- setParent pId node1
        let ps = abstFormulas abstInfo
        tbl <- liftIO H.new :: R (HashTable (IType, BFormula) ExpNode)
        let child ity phi =
                liftIO (H.lookup tbl (ity, phi))
                >>= maybe doit getTypes
                where
                doit = whenSat fml ps phi [] $ \fml' -> do
                    let env' = M.insert x ity env
                    node2 <- calcExp env' fml' e2  >>= setParent pId
                    liftIO $ H.insert tbl (ity,phi) node2 
                    getTypes node2
            recalc = getTypes node1 >>= bindTermType child
            extract :: TermExtractor
            extract cenv iota = 
                case iota of
                    IFail -> do
                        tys1 <- getTypes node1
                        if any isFail tys1
                        then extractor node1 cenv iota
                        else getTypes node1 >>= go
                    ITerm _ _ -> getTypes node1 >>= go
                where
                go (iota1: tys1) = do
                    r <- runMaybeT $ do 
                        ITerm ity phi <- pure iota1
                        node2 <- MaybeT (liftIO (H.lookup tbl (ity, phi)))
                        tys2 <- lift $ getTypes node2
                        node2 <$ guard (any (`subTermTypeOf` iota) tys2) 
                    case r of
                        Nothing -> go tys1
                        Just node2 -> do
                            cv1 <- extractor node1 cenv iota1
                            extractor node2 (M.insert x cv1 cenv) iota
                go [] = error "unexpected pattern"
            destruct = destructor node1 >>
                liftIO (H.toList tbl) >>= mapM_ (destructor . snd)
        cont recalc extract destruct

calcLetRec :: IEnv -> HFormula -> Int -> ([(TId, Value)], Exp) -> 
            (R [ITermType] -> TermExtractor -> R () -> R a) -> R a
calcLetRec env fml pId (fs, e) cont = do
    top <- mkIFun []
    let env0 = M.fromList [ (f, top) | (f,_) <- fs ]
        env' = M.union env env0
    node_fs <- forM fs $ \(_,v_f) -> do
        node_f <- calcValue env' fml v_f >>= setParent pId
        pushQuery (UpdateQuery QEdge pId)
        return node_f

    -- tys <- getTypes node_e
    {- letRChildren :: IORef [ValueNode]
     - letRHistory :: HashTable (TId, ArgType, ITermType) ValueNode 
     - letREnv  :: IORef IEnv
     - letRCont :: IORef ExpNode
     -}
    letRChildren <- liftIO (newIORef node_fs)
    letREnv      <- liftIO (newIORef env0)
    letRCont     <- 
        calcExp env' fml e 
        >>= setParent pId 
        >>= liftIO . newIORef
    letRHistory  <- liftIO H.new
    let recalc :: R [ITermType]
        recalc = do
            env0  <- liftIO $ readIORef letREnv
            nodes <- liftIO $ readIORef letRChildren
            updated <- liftIO $ newIORef False
            env1 <- M.fromList <$> zipWithM (\node (f,_) -> do
                    ity_cur@(IFun assocs) <- getTypes node 
                    forM_ assocs $ \(thetas, phi, iota) -> liftIO $ do
                        mhist <- H.lookup letRHistory (f, (thetas,phi), iota)
                        when (isNothing mhist) $ do
                            H.insert letRHistory (f, (thetas,phi), iota) node
                            writeIORef updated True
                    (f,) <$> mkIntersection ity_cur (env0 ! f)
                ) nodes fs
            liftIO (readIORef updated) >>= \case
                True -> do
                    let env' = M.union env env1
                    pushQuery (UpdateQuery QEdge pId)
                    node_fs <- forM fs $ \(_, v_f) -> 
                        calcValue env' fml v_f >>= setParent pId
                    liftIO $ writeIORef letREnv env1
                    destruct 
                    liftIO $ writeIORef letRChildren node_fs
                    node_e <- calcExp env' fml e >>= setParent pId
                    liftIO $ writeIORef letRCont node_e 
                    getTypes node_e
                False -> liftIO (readIORef letRCont) >>= getTypes
        extract cenv iota = do
            let cenv' = extendEnv cenv [ (f, CRec cenv' f letRHistory) | (f,_) <- fs ]
            node_e <- liftIO $ readIORef letRCont
            extractor node_e cenv' iota
        destruct = do
            liftIO (readIORef letRCont) >>= destructor
            liftIO (readIORef letRChildren) >>= mapM_ destructor
    cont recalc extract destruct

extractOmega,extractFail :: TermExtractor
extractOmega _ _ = error "diverged"
extractFail _ IFail = mzero
extractFail _ _ = error "extract@SFail_calcExp: fail never returns values"

calcAssume :: IEnv -> HFormula -> NodeId -> (HFormula, Exp) -> 
            (R [ITermType] -> TermExtractor -> R () -> R a) -> R a
calcAssume env fml pId (cond, e) cont = 
    checkSat fml cond >>= \case
        True -> do
            fml' <- extendConstraintCond fml cond
            node_e <- calcExp env fml' e >>= setParent pId
            cont (getTypes node_e) (extractor node_e) (destructor node_e)
        False -> cont (return []) extractOmega (return ())

findTbl :: HashTable k v -> (k -> v -> IO Bool) -> IO v 
findTbl tbl pred = 
    H.foldM (\acc (k,v) -> do
        b <- pred k v 
        if b then return v else return acc) (error "not found") tbl

calcApp :: IEnv -> HFormula -> NodeId -> (TId, AbstInfo, [Value]) -> 
            (R [ITermType] -> TermExtractor -> R () -> R a) -> R a
calcApp env fml pId (f, abstInfo, vs) cont = do
    phi <- calcCondition fml (abstFormulas abstInfo)
    nodes <- forM vs $ calcValue env fml >=> setParent pId
    flow <- asks $ (!f) . ctxFlowMap 
    let ity_f = env ! f
        recalc = do
            thetas <- mapM getTypes nodes
            forM_ flow $ \ident -> addFlow ident (thetas,phi)
            return $ appType ity_f thetas phi
        destruct = forM_ nodes destructor
        extract cenv iota = do
            thetas <- mapM getTypes nodes
            CCls cenv_f xs tbl <- case cenv ! f of
                CRec cenv_f g hist -> do
                    let searchNode = 
                            findTbl hist $ \(g', (thetas', phi'), iota') _ -> pure $
                                g == g' && phi == phi' && 
                                and (zipWith subTypeOf thetas thetas') &&
                                iota' `subTermTypeOf` iota
                    node <- liftIO $ H.lookup hist (g, (thetas, phi), iota) 
                        >>= maybe searchNode return
                    pure $ extractor node cenv_f
                cv_f -> pure cv_f

            let searchNode = 
                    findTbl tbl $ \(thetas',phi') val -> 
                        getTypes val >>= pure . \tys -> 
                            phi == phi' && 
                            and (zipWith subTypeOf thetas thetas') && 
                            any (`subTermTypeOf` iota) tys
                cvs = map (`extractor` cenv) nodes
                cenv_f' = extendEnv cenv_f (zip xs cvs)
            node <- liftIO $ 
                H.lookup tbl (thetas, phi) >>= maybe searchNode pure
            extractor node cenv_f' iota
    cont recalc extract destruct

calcNode :: (Eq (SatType e), Pretty e, Pretty (SatType e)) 
            => IEnv -> HFormula -> NodeId -> e ->
                R (SatType e) -> Extractor e -> R () -> R (Node e)
calcNode typeEnv constraint ident term recalcator extractor destruct = do
    types <- recalcator >>= liftIO . newIORef
    alive <- liftIO $ newIORef True
    let pprinter = genericPrint typeEnv constraint term types ident pPrint pPrint
        destructor = destruct >> liftIO (writeIORef alive False)
    liftIO pprinter >>= logPretty "Fusion" LevelDebug "calcNode" . PPrinted
    return Node{..}

calcValue :: IEnv -> HFormula -> Value -> R ValueNode
calcValue env fml value = genNode $ \nodeIdent -> 
    let cont = calcNode env fml nodeIdent value in
    case valueView value of
        VAtom atom -> cont (return ity) extract (return ())
            where
            extract cenv = evalAtom cenv atom
            ity = calcAtom env atom
        VOther SPair arg -> 
            calcPair env fml nodeIdent arg cont
        VOther SLambda arg -> 
            calcLambda env fml nodeIdent (getUniqueKey value) arg cont

extractValue :: ValueExtractor -> TermExtractor
extractValue extract env (ITerm _ _) = pure (extract env)
extractValue _ _ IFail = error "value never fails"

calcExp :: IEnv -> HFormula -> Exp -> R ExpNode
calcExp env fml exp = genNode $ \nodeIdent -> 
    let cont = calcNode env fml nodeIdent exp in
    case expView exp of
        EValue v info -> do
            phi <- calcCondition fml (abstFormulas info)
            let cont' recalc extract destruct = cont recalc' (extractValue extract) destruct
                    where recalc' = recalc >>= (\theta -> (:[]) <$> mkITerm theta phi)
            case valueView v of
                VAtom atom -> 
                    cont' (pure $ calcAtom env atom) (`evalAtom` atom) (pure ())
                VOther SPair arg -> 
                    calcPair env fml nodeIdent arg cont'
                VOther SLambda arg -> 
                    calcLambda env fml nodeIdent (getUniqueKey exp) arg cont'
        EOther SLet arg -> calcLet env fml nodeIdent arg cont
        EOther SLetRec arg -> calcLetRec env fml nodeIdent arg cont
        EOther SAssume arg -> calcAssume env fml nodeIdent arg cont
        EOther SBranch arg -> calcBranch env fml nodeIdent arg cont
        EOther SFail _ -> cont (return [mkIFail]) extractFail (return ())
        EOther SOmega _ -> cont (return []) extractOmega (return ())

calcLExp :: IEnv -> HFormula -> TId -> LExp -> 
    (IType ->  HFormula ->  (CEnv -> CValue) -> R a) ->
    (LExpNode -> R a) -> R a
calcLExp env fml x lexp atomCase otherCase = 
    let  cont nodeIdent = calcNode env fml nodeIdent lexp in
    case lexpView lexp of
        LAtom atom -> do
            fml' <- extendConstraintVar fml x atom
            let ity = calcAtom env atom
            atomCase ity fml' (`evalAtom` atom)
        LOther SRand _ -> 
            atomCase mkIBase fml (const CBase) 
        LOther SBranch arg -> 
            genNode (\nodeIdent -> 
                calcBranch env fml nodeIdent arg (cont nodeIdent))
                >>= otherCase
        LOther SApp arg -> 
            genNode (\nodeIdent -> 
                calcApp env fml nodeIdent arg (cont nodeIdent))
                >>= otherCase

updateLoop :: R ()
updateLoop = 
    popQuery >>= 
        maybe (return ()) 
              (\(UpdateQuery _ nodeId) -> doit nodeId >> updateLoop)
    where
    doit nodeId = do
        SomeNode node@Node{ident = ident
                          , alive = alive} <- getNode nodeId
        nodeIsAlive <- liftIO (readIORef alive) 
        liftIO (pprinter node) >>= logPretty "Fusion" LevelDebug "updated" . PPrinted
        when nodeIsAlive $ do
            new_ity <- recalcator node
            old_ity <- getTypes node
            setTypes node new_ity
            when (new_ity /= old_ity) $ do
                tbl <- asks ctxNodeDepG
                lookupTbl tbl ident >>= 
                    mapM_ (pushQuery . UpdateQuery QEdge)

saturate :: HContext -> Program -> TracerT (Dict IncSat) (LoggingT IO) (Bool, ([ITermType], Maybe [Bool]))
saturate hctx prog = do
    ctx <- lift $ initContext prog
    res <- lift $ runR hctx ctx $ do
        root <- mkTrue >>= \true -> calcExp M.empty true (mainTerm prog)
        updateLoop
        tys <- getTypes root
        if any isFail tys
        then do
            bs <- extractTrace (extractor root M.empty mkIFail)
            return (True, (tys, Just bs))
        else 
            return (False, (tys, Nothing))
    dict <- liftIO $ getStatistics hctx ctx
    update (id .~ dict)
    return res