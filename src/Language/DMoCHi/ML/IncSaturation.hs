{-# LANGUAGE DeriveGeneric, GeneralizedNewtypeDeriving, RecordWildCards #-}
module Language.DMoCHi.ML.IncSaturation(saturate,IncSat) where
import           Language.DMoCHi.ML.Syntax.CEGAR hiding(mkBin, mkUni, mkVar, mkLiteral)
import           Language.DMoCHi.ML.Syntax.HFormula
import qualified Language.DMoCHi.ML.Syntax.HFormula as HFormula
import           Language.DMoCHi.ML.Syntax.IType
import           Language.DMoCHi.Common.Id
import           Language.DMoCHi.Common.Util
import           Language.DMoCHi.ML.IncSaturationPre
import           Language.DMoCHi.Common.Cache hiding(ident)
import qualified Language.DMoCHi.ML.SMT as SMT
-- import qualified Language.DMoCHi.ML.AbstractSemantics as AbsSemantics

-- import Control.Monad
-- import           Control.Monad.Fix
--import Control.Arrow ((***),second)
import           Control.Monad.Reader
import           Control.Monad.Writer hiding((<>))
import           Control.Monad.State.Strict
-- import Data.List
import           Data.IORef
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.HashTable.IO as H
import           Text.PrettyPrint.HughesPJClass
import           Debug.Trace
import           GHC.Stack
import           Data.PolyDict(Dict)

getFlow :: UniqueKey -> R [([IType], BFormula)]
getFlow i = do
    tbl <- ctxFlowTbl <$> ask
    l <- liftIO (H.lookup tbl i) >>= \case
        Just v -> return (S.toList v)
        Nothing -> return []
    -- liftIO $ print ("getFlow", i, l)
    return l

addFlow :: UniqueKey -> ([IType], BFormula) -> R ()
addFlow i v = do
    tbl <- ctxFlowTbl <$> ask
    reg <- ctxFlowReg <$> ask
    let cont :: S.Set ([IType], BFormula) -> R ()
        cont !vs' = do
            liftIO (H.insert tbl i vs')
            liftIO (lookupTbl reg i) >>= mapM_ (pushQuery . UpdateQuery QFlow)
    liftIO (H.lookup tbl i) >>= \case
        Just vs 
            | S.member v vs -> return ()
            | otherwise -> cont (S.insert v vs)
        Nothing -> cont (S.singleton v)
    -- liftIO $ print ("addFlow", i, v)

whenSat :: HasCallStack => HFormula -> [HFormula] -> BFormula -> a -> (HFormula -> R a) -> R a
whenSat fml ps phi def cont = do
    cond <- fromBFormula ps phi
    fml' <- mkBin SAnd fml cond
    checkSat fml cond >>= \case
        False -> return def
        True  -> cont fml'

calcAtom :: IEnv -> Atom -> IType
calcAtom env = cataAtom $ CataAtom{..}
    where
    literalCase _ = mkIBase
    varCase x = env ! x
    binaryCase _ _ _ = mkIBase
    unaryCase :: Supported op (UniOps Atom) => SUniOp op -> IType -> IType
    unaryCase SFst (IPair i1 _) = i1
    unaryCase SFst _ = error "calcAtom: unexpected pattern"
    unaryCase SSnd (IPair _ i2) = i2
    unaryCase SSnd _ = error "calcAtom: unexpected pattern"
    unaryCase SNeg _ = mkIBase
    unaryCase SNot _ = mkIBase

evalAtom :: CEnv -> Atom -> CValue
evalAtom cenv = cataAtom $ CataAtom {..}
    where
    literalCase _ = CBase
    varCase x = cenv ! x
    binaryCase _ _ _ = CBase
    unaryCase :: Supported op (UniOps Atom) => SUniOp op -> CValue -> CValue
    unaryCase SFst (CPair i1 _) = i1
    unaryCase SFst _ = error "evalAtom: unexpected pattern"
    unaryCase SSnd (CPair _ i2) = i2
    unaryCase SSnd _ = error "evalAtom: unexpected pattern"
    unaryCase SNeg _ = CBase
    unaryCase SNot _ = CBase

calcFromValue :: HFormula -> [HFormula] -> (R IType, ValueExtractor, R ()) 
                 -> R ([ITermType], R [ITermType], TermExtractor, R ())
calcFromValue fml ps (recalc, extract, destruct) = do
    phi <- calcCondition fml ps
    let recalc' = recalc >>= (\theta -> (:[]) <$> mkITerm theta phi)
        extract' env (ITerm _ phi') 
            | phi == phi' = return $ Just (extract env)
            | otherwise = error "extract@calcFromValue: condition mismatch"
        extract' _ _ = error "values never fail"
    tys <- recalc'
    return (tys, recalc', extract', destruct)

calcPair :: IEnv -> HFormula -> NodeId -> (Value,Value) -> R (R IType, ValueExtractor, R ())
calcPair env fml pId (v1,v2) = do
    node1 <- calcValue env fml v1  >>= setParent pId
    node2 <- calcValue env fml v2  >>= setParent pId
    let recalc = join $ mkIPair <$> getTypes node1 <*> getTypes node2
        extract env = CPair (extractor node1 env) (extractor node2 env)
        destruct = destructor node1 >> destructor node2
    return (recalc, extract, destruct)
    
calcLambda :: IEnv -> HFormula -> NodeId -> UniqueKey -> ([TId], AbstInfo, Exp) -> R (R IType, ValueExtractor, R ())
calcLambda env fml pId key (xs, _abstInfo, e) = do
    let ps = abstFormulas _abstInfo
    tbl <- liftIO H.new
    ask >>= \ctx -> liftIO $ insertTbl (ctxFlowReg ctx) key pId
    let recalc = do
            fs <- getFlow key
            ty_assocs <- fmap mconcat $ forM fs $ \(thetas, phi) ->
                liftIO (H.lookup tbl (thetas,phi)) >>= \case
                    Just body -> map (thetas,phi,) <$> getTypes body
                    Nothing -> whenSat fml ps phi [] $ \fml' -> do
                        let env' = extendEnv env (zip xs thetas)
                        node_body <- calcExp env' fml' e >>= setParent pId
                        liftIO $ H.insert tbl (thetas,phi) node_body
                        tys <- getTypes node_body
                        return $ map ((,,) thetas phi) tys
            mkIFun ty_assocs
        extract env = CCls env xs tbl
    let destruct = do
            children <- liftIO $ H.toList tbl
            forM_ children $ \(_,node_body) -> destructor node_body
    return (recalc, extract,destruct)
                
calcBranch :: IEnv -> HFormula -> Int -> (Exp, Exp) -> R ([ITermType] , R [ITermType], TermExtractor, R ())
calcBranch env fml pId (e1, e2) = do
    node1 <- calcExp env fml e1 >>= setParent pId
    node2 <- calcExp env fml e2 >>= setParent pId
    let recalc = merge <$> getTypes node1 <*> getTypes node2
        extract cenv iota = do
            tys1 <- getTypes node1
            if any (flip subTermTypeOf iota) tys1
            then tell [True]  >> extractor node1 cenv iota
            else tell [False] >> extractor node2 cenv iota
        destruct = destructor node1 >> destructor node2
    tys <- recalc
    return (tys, recalc, extract, destruct)

bindTermType :: (IType -> BFormula -> R [ITermType])  -> [ITermType] -> R [ITermType]
bindTermType f tys = fmap concatMerge $ forM tys $ \case
    IFail -> return [mkIFail]
    ITerm ity phi -> f ity phi
    _ -> undefined -- impossible

calcLet :: IEnv -> HFormula -> Int -> (TId, LExp, AbstInfo, Exp) 
            -> R ([ITermType], R [ITermType], TermExtractor, R ())
calcLet env fml pId  (x, e1, _abstInfo, e2) = 
    calcLExp env fml x e1 >>= \case
        Left (ity, fml', ev) -> do
            let env' = M.insert x ity env
            node2 <- calcExp env' fml' e2 >>= setParent pId
            let recalc = getTypes node2 
                extract cenv iota = extractor node2 cenv' iota 
                    where cenv' = M.insert x (ev cenv) cenv
            tys <- recalc
            return (tys,  recalc, extract, destructor node2)
        Right node1 -> do 
            _ <- setParent pId node1
            let ps = abstFormulas _abstInfo
            tbl <- liftIO H.new :: R (HashTable (IType, BFormula) ExpNode)
            let calc :: [ITermType] -> R [ITermType]
                calc = bindTermType $ \ity phi -> -- TODO: あるケースが参照されなくなったらdestructする
                        liftIO (H.lookup tbl (ity,phi)) >>= \case
                            Just node2 -> getTypes node2 
                            Nothing -> whenSat fml ps phi [] $ \fml' -> do
                                let env' = M.insert x ity env
                                node2 <- calcExp env' fml' e2  >>= setParent pId
                                liftIO $ H.insert tbl (ity,phi) node2 
                                getTypes node2
            let recalc = getTypes node1 >>= calc
                extract, extractCont :: TermExtractor
                extract cenv iota@IFail = do
                    tys1 <- getTypes node1
                    if any isFail tys1
                    then extractor node1 cenv iota
                    else extractCont cenv iota
                extract cenv iota = extractCont cenv iota
                extractCont cenv iota = go =<< getTypes node1
                    where
                    go (iota1: tys1) = case iota1 of
                        ITerm ity phi -> liftIO (H.lookup tbl (ity, phi)) >>= \case
                            Nothing -> go tys1 
                            Just node2 -> do
                                tys2 <- getTypes node2
                                if any (flip subTermTypeOf iota) tys2
                                then do
                                    Just cv1 <- extractor node1 cenv iota1
                                    extractor node2 (M.insert x cv1 cenv) iota
                                else go tys1
                        _ -> go tys1
                    go [] = error "unexpected pattern"
                destruct = do
                    destructor node1
                    liftIO (H.toList tbl) >>= mapM_ (destructor . snd)
            tys <- recalc
            return (tys, recalc, extract, destruct)


calcLetRec :: IEnv -> HFormula -> Int -> ([(TId, Value)], Exp) -> R ([ITermType], R [ITermType],TermExtractor, R ())
calcLetRec env fml pId (fs, e) = do
    top <- mkIFun []
    let env0 = M.fromList [ (f, top) | (f,_) <- fs ]
        env' = M.union env env0
    node_fs <- forM fs $ \(_,v_f) -> do
        node_f <- calcValue env' fml v_f >>= setParent pId
        pushQuery (UpdateQuery QEdge pId)
        return node_f

    node_e <- calcExp env' fml e >>= setParent pId
    tys <- getTypes node_e
    {- letRChildren :: IORef [ValueNode]
     - letRHistory :: HashTable (TId, ArgType, ITermType) ValueNode 
     - letREnv  :: IORef IEnv
     - letRCont :: IORef ExpNode
     -}
    letRChildren <- liftIO (newIORef node_fs)
    letREnv      <- liftIO (newIORef env0)
    letRCont     <- liftIO (newIORef node_e)
    letRHistory  <- liftIO H.new
    let recalc :: R [ITermType]
        recalc = do
            env0  <- liftIO $ readIORef letREnv
            nodes <- liftIO $ readIORef letRChildren
            updated <- liftIO $ newIORef False
            env1 <- fmap M.fromList $ zipWithM (\node (f,_) -> do
                    ity_cur <- getTypes node 
                    let assocs = case ity_cur of
                            IFun v -> v
                            _ -> error $ "expect function type: " ++ show ity_cur
                    forM_ assocs $ \(thetas, phi, iota) -> 
                        liftIO $ H.lookup letRHistory (f, (thetas,phi), iota) >>= \case 
                            Just _ -> return ()
                            Nothing -> do
                               H.insert letRHistory (f, (thetas,phi), iota) node
                               writeIORef updated True
                    let ity_old = env0 ! f
                    ity_new <- mkIntersection ity_cur ity_old
                    return (f, ity_new)
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
            node_e <- liftIO $ readIORef letRCont
            destructor node_e
            nodes <- liftIO $ readIORef letRChildren
            forM_ nodes $ \node_f -> destructor node_f
    return (tys, recalc,extract, destruct)

calcAssume :: IEnv -> HFormula -> NodeId -> (Atom, Exp) -> R ([ITermType], R [ITermType], TermExtractor, R ())
calcAssume env fml pId (a, e) = do
    cond <- toHFormula a 
    checkSat fml cond >>= \case
        True -> do
            fml' <- mkBin SAnd fml cond
            node_e <- calcExp env fml' e >>= setParent pId
            let recalc  = getTypes node_e
                extract = extractor node_e
            tys <- recalc
            return (tys, recalc, extract, destructor node_e)
        False -> 
            let extract :: TermExtractor
                extract _ _ = error "assume(false) never returns values" in
            return ([], return [], extract, return ())

calcApp :: IEnv -> HFormula -> NodeId -> (TId, AbstInfo, [Value]) -> R ([ITermType], R [ITermType], TermExtractor, R ())
calcApp env fml pId (f, _abstInfo, vs) = do
    let ity_f = env ! f
    let ps = abstFormulas _abstInfo
    phi <- calcCondition fml ps
    nodes <- forM vs $ \v -> calcValue env fml v >>= setParent pId
    flow <- (!f) . ctxFlowMap <$> ask

    let recalc = do
            thetas <- mapM getTypes nodes
            forM_ flow $ \ident -> addFlow ident (thetas,phi)
            return $ appType ity_f thetas phi
        destruct = forM_ nodes $ destructor
        extract cenv iota = do
            let cvs = map (\node -> extractor node cenv) nodes
            thetas <- mapM getTypes nodes
            let closureCase (CCls cenv_f xs tbl) = do
                    node <- liftIO $ H.lookup tbl (thetas, phi) >>= \case
                        Just node -> return node
                        Nothing -> H.foldM (\acc ((thetas',phi'),val) -> do
                            tys <- getTypes val
                            if phi == phi' && 
                               and (zipWith subTypeOf thetas thetas') && 
                               any (flip subTermTypeOf iota) tys
                            then return val
                            else return acc) (error "no match") tbl
                    let cenv_f' = extendEnv cenv_f (zip xs cvs)
                    extractor node cenv_f' iota
                closureCase _ = error "unexpected pattern"
            
            case cenv ! f of
                CRec cenv_f g hist -> do
                    node <- liftIO $ H.lookup hist (g, (thetas, phi), iota) >>= \case
                        Just node -> return node
                        Nothing -> H.foldM (\acc ((g', (thetas', phi'), iota'), val) -> do
                            if g == g' && phi == phi' && 
                             and (zipWith subTypeOf thetas thetas') &&
                               iota' `subTermTypeOf` iota
                            then return val
                            else return acc) (error "no match") hist
                    closureCase (extractor node cenv_f)
                cv_f -> closureCase cv_f
    tys <- recalc
    return (tys, recalc, extract, destruct)


calcValue :: IEnv -> HFormula -> Value -> R ValueNode
calcValue env fml value = genNode $ \nodeIdent -> do
    (recalc, extract, destruct) <- case valueView value of
        VAtom atom -> do
            let extract cenv = evalAtom cenv atom
                ity = calcAtom env atom
            return (return ity, extract, return ())
        VOther SPair arg -> calcPair env fml nodeIdent arg
        VOther SLambda arg -> calcLambda env fml nodeIdent (getUniqueKey value) arg
    ity <- recalc
    itypeRef <- liftIO $ newIORef ity
    let pp = genericPrint env fml value itypeRef nodeIdent pPrint pPrint
    alive <- liftIO $ newIORef True
    let destruct' = (destruct :: R ()) >> liftIO (writeIORef alive False)
    return $ Node { typeEnv = env
                  , constraint = fml
                  , ident = nodeIdent
                  , term = value
                  , types = itypeRef
                  , recalcator = recalc
                  , extractor  = extract 
                  , destructor = destruct'
                  , alive    = alive
                  , pprinter = pp}

        

calcExp :: IEnv -> HFormula -> Exp -> R ExpNode
calcExp env fml exp = 
    genNode $ \nodeIdent -> do
        (itys,recalc, extract, destruct) <- case expView exp of
            EValue v _info -> 
                let ps = abstFormulas _info in
                case valueView v of
                    VAtom atom -> do
                        let ity = calcAtom env atom
                        calcFromValue fml ps (return ity, flip evalAtom atom, return ())
                    VOther SPair arg -> 
                        calcPair env fml nodeIdent arg
                        >>= calcFromValue fml ps 
                    VOther SLambda arg -> 
                        calcLambda env fml nodeIdent (getUniqueKey exp) arg
                        >>= calcFromValue fml ps
            EOther SLet arg -> calcLet env fml nodeIdent arg
            EOther SLetRec arg -> calcLetRec env fml nodeIdent arg
            EOther SAssume arg -> calcAssume env fml nodeIdent arg
            EOther SBranch arg -> calcBranch env fml nodeIdent arg
            EOther SFail _ -> do
                let extract _ IFail = return Nothing
                    extract _ _ = error "extract@SFail_calcExp: fail never returns values"
                return ([mkIFail], return [mkIFail], extract, return ())
            EOther SOmega _ -> 
                let extract _ _ = error "extract@SOmega_calcExp: omega never returns value nor fails"
                in return ([], return [], extract, return ())
        let extract' cenv iota = do
                {-
                liftIO $ do
                    putStrLn $ "extracting: " ++ show (pPrint iota)
                    putStrLn $ "cenv: " ++ show (M.keys cenv)
                    printNode _node
                    -}
                extract cenv iota
        itypeRef <- liftIO $ newIORef itys
        alive <- liftIO $ newIORef True
        let destruct' = (destruct :: R ()) >> liftIO (writeIORef alive False)
        let pp = genericPrint env fml exp itypeRef nodeIdent pPrint pPrint
        return $ Node { typeEnv = env
                      , constraint = fml
                      , ident = nodeIdent
                      , term = exp
                      , types = itypeRef
                      , recalcator = recalc
                      , extractor = extract'
                      , destructor = destruct'
                      , alive = alive
                      , pprinter = pp }

calcLExp :: IEnv -> HFormula -> TId -> LExp -> R (Either (IType, HFormula, (CEnv -> CValue)) LExpNode)
calcLExp env fml x lexp = -- genNode $ \nodeIdent -> do
    case lexpView lexp of
        LAtom atom -> do
            fml' <- (join $ mkBin SEq <$> mkVar x <*> toHFormula atom) 
                    >>= mkBin SAnd fml
            let ity = calcAtom env atom
            return $ Left (ity, fml', \cenv -> evalAtom cenv atom)
        LOther SRand _ -> return $ Left (mkIBase, fml, \_ -> CBase)
        LOther SBranch arg -> 
            Right <$> genNode (\nodeIdent -> 
                calcBranch env fml nodeIdent arg >>= cont nodeIdent)
        LOther SApp arg -> 
            Right <$> genNode (\nodeIdent -> 
                calcApp env fml nodeIdent arg >>= cont nodeIdent)
    where cont :: NodeId -> ([ITermType], R [ITermType], TermExtractor, R ()) -> R LExpNode
          cont nodeIdent (itys,recalc, extract, destruct) = do
                itypeRef <- liftIO $ newIORef itys
                alive <- liftIO $ newIORef True
                let destruct' = (destruct :: R ()) >> liftIO (writeIORef alive False)
                let extract' cenv iota = do
                        {-
                        liftIO $ do
                            putStrLn $ "extracting: " ++ show (pPrint iota)
                            putStrLn $ "cenv: " ++ show (M.keys cenv)
                            printNode _node
                        -}
                        extract cenv iota
                let pp = genericPrint env fml lexp itypeRef nodeIdent pPrint pPrint
                return $ Node { typeEnv = env
                              , constraint = fml
                              , ident = nodeIdent
                              , term = lexp
                              , types = itypeRef
                              , recalcator = recalc 
                              , extractor = extract'
                              , destructor = destruct'
                              , alive = alive
                              , pprinter = pp}

updateLoop :: R ()
updateLoop = popQuery >>= \case
    Nothing -> return ()
    Just (UpdateQuery _ nodeId) -> do
        SomeNode node <- getNode nodeId
        case node of
            Node {ident = ident, alive = alive} -> do
                liftIO (readIORef alive) >>= \case
                    True -> do
                        new_ity <- recalcator node
                        old_ity <- getTypes node
                        setTypes node new_ity
                        when (new_ity /= old_ity) $ do
                            tbl <- ctxNodeDepG <$> ask
                            liftIO (H.lookup tbl ident) >>= \case
                                Nothing -> pure ()
                                Just ns -> forM_ ns $ pushQuery . UpdateQuery QEdge
                        updateLoop
                    False -> updateLoop

saturate :: HFormula.Context -> Program -> TracerT (Dict IncSat) (LoggingT IO) (Bool, ([ITermType], Maybe [Bool]))
saturate hctx prog = do
    ctx <- lift $ initContext prog
    let doit :: R (Bool, ([ITermType], Maybe [Bool]))
        doit = do
            SMT.initSMTContext
            logPretty "saturate" LevelDebug "Abstraction Annotated Program" (PPrinted (pPrint prog))
            root <- mkLiteral (CBool True) >>= \fml0 -> calcExp M.empty fml0 (mainTerm prog)
            updateLoop
            tys <- getTypes root
            if any isFail tys
            then do
                bs <- execWriterT $ extractor root M.empty mkIFail
                --hcs <- AbsSemantics.genConstraints bs (mainTerm prog)
                -- liftIO $ print hcs
                return (True, (tys, Just bs))
            else do
                return (False, (tys, Nothing))
    res <- lift $ runHFormulaT (evalStateT (runReaderT (unR doit) ctx) (emptyQueue, S.empty)) hctx
    dict <- liftIO $ getStatistics ctx
    update (id .~ dict)
    return res

