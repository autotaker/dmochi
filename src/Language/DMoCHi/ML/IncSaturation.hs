{-# LANGUAGE DeriveGeneric, GeneralizedNewtypeDeriving #-}
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
import           Control.Monad.Fix
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
import           Data.PolyDict(Dict)

{-
setFV :: UniqueKey -> S.Set TId -> R ()
setFV key s = do
    ctx <- ask
    liftIO $ H.insert (ctxFreeVarTbl ctx) key s
getFV :: UniqueKey -> R (S.Set TId)
getFV key = do
    ctx <- ask
    r <- liftIO $ H.lookup (ctxFreeVarTbl ctx) key
    case r of
        Just r -> return r
        Nothing -> error $ "getFV: fv hasn't set yet for key " ++ show key

calcFVV :: Value -> R (S.Set TId)
calcFVV (Value l arg sty key) = do
    let atom a = return $ freeVariables S.empty (cast a)
    fv <- case (l,arg) of
        (SLiteral, _) -> atom (Atom l arg sty)
        (SVar, _)     -> atom (Atom l arg sty)
        (SUnary, _)   -> atom (Atom l arg sty)
        (SBinary, _)  -> atom (Atom l arg sty)
        (SPair, (v1, v2)) -> do
            fv1 <- calcFVV v1
            fv2 <- calcFVV v2
            return (S.union fv1 fv2)
        (SLambda, (xs, e)) -> do
            fv <- calcFVE e
            return $ fv S.\\ S.fromList xs
    setFV key fv
    return fv

calcFVE :: Exp -> R (S.Set TId)
calcFVE (Exp l arg sty key) = do
    let cont fv = fv <$ setFV key fv
    case (l, arg) of
        (SLiteral, _) -> calcFVV (Value l arg sty key)
        (SVar, _) -> calcFVV (Value l arg sty key)
        (SUnary, _) -> calcFVV (Value l arg sty key)
        (SBinary, _) -> calcFVV (Value l arg sty key)
        (SPair, _) -> calcFVV (Value l arg sty key)
        (SLambda, _) -> calcFVV (Value l arg sty key)
        (SLet, (x, e1, e2)) -> do
            fv1 <- calcFVL e1
            fv2 <- calcFVE e2
            cont (fv1 `S.union` (S.delete x fv2))
        (SLetRec, (fs,e2)) -> do
            fvs <- forM fs (\(_,v) -> calcFVV v)
            fv  <- calcFVE e2
            cont $ S.unions (map (\x -> x S.\\ (S.fromList (map fst fs))) (fv:fvs))
        (SAssume, (cond, e)) -> do
            let fv1 = freeVariables S.empty (cast cond)
            fv2 <- calcFVE e
            cont (fv1 `S.union` fv2)
        (SBranch, (e1, e2)) -> do
            fv1 <- calcFVE e1
            fv2 <- calcFVE e2
            cont (fv1 `S.union` fv2)
        (SFail, _) -> cont S.empty
        (SOmega, _) -> cont S.empty

calcFVL :: LExp -> R (S.Set TId)
calcFVL (LExp l arg sty key) = do
    let cont fv = fv <$ setFV key fv
    case (l, arg) of
        (SLiteral, _) -> calcFVV (Value l arg sty key)
        (SVar, _) -> calcFVV (Value l arg sty key)
        (SUnary, _) -> calcFVV (Value l arg sty key)
        (SBinary, _) -> calcFVV (Value l arg sty key)
        (SPair, _) -> calcFVV (Value l arg sty key)
        (SLambda, _) -> calcFVV (Value l arg sty key)
        (SApp, (f,vs)) -> do
            fvs <- forM vs calcFVV
            cont $ S.insert f (S.unions fvs)
        (SBranch, (e1, e2)) -> do
            fv1 <- calcFVE e1
            fv2 <- calcFVE e2
            cont (fv1 `S.union` fv2)
        (SFail, _) -> cont S.empty
        (SOmega, _) -> cont S.empty
        (SRand, _) -> cont S.empty
        -}

{-
calcContextV :: Value  -> R ()
calcContextV v = 
    case valueView v of
        VAtom _ -> return ()
        VOther SPair (v1, v2) -> calcContextV v1 >> calcContextV v2
        VOther SLambda (_, info, e) -> do
            let ps'    = abstPredicates info
                scope_arg = snd (abstTemplate info)
                key = getUniqueKey v
            ctx <- ask
            scope_arg' <- mapM toHFormula scope_arg
            liftIO $ H.insert (ctxArgTypeTbl ctx) key (ps', Scope scope_arg')
            calcContextE e
            -}

{-
-- env scopeEnv |- e : tau [scope]
calcContextE ::  Exp -> R ()
calcContextE e = 
    let key = getUniqueKey e in
    -- scope does not cointain the return variable
    case expView e of
        EValue v info -> do
            let ps' = abstPredicates info
                scope' = snd $ abstTemplate info
            calcContextV v 
            scope' <- mapM toHFormula scope'
            tbl <- ctxRtnTypeTbl <$> ask 
            liftIO (H.insert tbl key (ps', Scope scope'))
        EOther SLet (_, e1, info_ret, e2) -> 
            let key1 = getUniqueKey e1 in
            case lexpView e1 of
                LAtom _ -> do
                    ask >>= \ctx -> liftIO $ H.insert (ctxRtnTypeTbl ctx) key ([], Scope [])
                    calcContextE e2
                LOther SApp (_, info_arg, vs) -> do
                    let ps' = abstPredicates info_arg
                        qs' = abstPredicates info_ret
                        scope_arg = snd (abstTemplate info_arg)
                        scope_ret = snd (abstTemplate info_ret)
                    ctx <- ask
                    forM_ vs calcContextV
                    scope_arg <- mapM toHFormula scope_arg
                    scope_ret <- mapM toHFormula scope_ret
                    liftIO (H.insert (ctxArgTypeTbl ctx) key  (ps', Scope scope_arg))
                    liftIO (H.insert (ctxArgTypeTbl ctx) key1 (ps', Scope scope_arg))
                    liftIO (H.insert (ctxRtnTypeTbl ctx) key  (qs', Scope scope_ret))
                    calcContextE e2
                LOther SRand _   -> do
                    ask >>= \ctx -> liftIO (H.insert (ctxRtnTypeTbl ctx) key ([], Scope[]))
                    calcContextE e2
                LOther SBranch (e_l, e_r) -> do
                    ctx <- ask
                    let ps'   = abstPredicates info_ret
                        scope1  = snd (abstTemplate info_ret)
                    calcContextE e_l
                    calcContextE e_r
                    scope1 <- mapM toHFormula scope1
                    liftIO $ H.insert (ctxRtnTypeTbl ctx) key ( ps', Scope scope1)
                    calcContextE  e2
        EOther SLetRec (fs, e2) -> do
            forM_ fs $ \(_,v_f) -> calcContextV v_f 
            calcContextE e2 
        EOther SAssume (_, e) -> calcContextE e
        EOther SBranch (e1,e2) -> calcContextE e1 >> calcContextE e2
        EOther SFail _ -> return ()
        EOther SOmega _ -> return ()
        -}

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
            liftIO (H.lookup reg i) >>= \case
                Nothing -> return ()
                Just nodes ->
                    forM_ nodes $ ((\(SomeNode node) -> pushQuery (UpdateQuery QFlow node)) :: SomeNode -> R ())
    liftIO (H.lookup tbl i) >>= \case
        Just vs 
            | S.member v vs -> return ()
            | otherwise -> cont (S.insert v vs)
        Nothing -> cont (S.singleton v)
    -- liftIO $ print ("addFlow", i, v)

calcAtom :: IEnv -> Atom -> ITypeBody
calcAtom env (Atom l arg _) = case (l, arg) of
    (SLiteral, CInt _)  -> IBase
    (SLiteral, CBool _) -> IBase
    (SLiteral, CUnit) -> IBase
    (SVar, x) -> body $ env ! x
    (SBinary, BinArg _ _ _) -> IBase
    (SUnary, UniArg op v) -> case op of
        SFst -> (\(IPair i1 _) -> body i1) $ calcAtom env v
        SSnd -> (\(IPair _ i2) -> body i2) $ calcAtom env v
        SNeg -> IBase
        SNot -> IBase

evalAtom :: CEnv -> Atom -> CValue
evalAtom cenv (Atom l arg _) =
    case (l, arg) of
        (SLiteral, _) -> CBase
        (SVar, x) -> cenv ! x
        (SBinary, _) -> CBase
        (SUnary, UniArg op v) ->
            case op of
                SFst -> case evalAtom cenv v of
                    CPair v1 _ -> v1
                    _          -> error "evalAtom: SFst: unexpected pattern"
                SSnd -> case evalAtom cenv v of
                    CPair _ v2 -> v2
                    _          -> error "evalAtom: SFst: unexpected pattern"
                SNeg -> CBase
                SNot -> CBase

calcFromValue :: HFormula -> [HFormula] -> (IType, R IType, ValueExtractor, R ()) 
                 -> R ([ITermType], R [ITermType], TermExtractor, R ())
calcFromValue fml ps (theta, recalc, extract, destruct) = do
    phi <- calcCondition fml ps
    let recalc' = recalc >>= (\theta -> (:[]) <$> mkITerm theta phi)
        extract' env (body -> ITerm _ phi') 
            | phi == phi' = return $ Just (extract env)
            | otherwise = error "extract@calcFromValue: condition mismatch"
        extract' _ _ = error "values never fail"
    tau <- mkITerm theta phi
    return ([tau], recalc', extract', destruct)

calcPair :: IEnv -> HFormula -> Node e -> (Value,Value) -> R (IType, R IType, ValueExtractor, R ())
calcPair env fml _node (v1,v2) = do
    (node1, ty1) <- calcValue env fml v1 
    (node2, ty2) <- calcValue env fml v2
    addDep (ident node1) _node
    addDep (ident node2) _node
    let recalc = do
            ty1 <- liftIO $ readIORef $ types $ node1
            ty2 <- liftIO $ readIORef $ types $ node2
            mkIPair ty1 ty2
        extract env = CPair (extractor node1 env) (extractor node2 env)
        destruct = destructor node1 >> destructor node2
    ity <- mkIPair ty1 ty2
    return (ity, recalc, extract, destruct)
    
calcLambda :: IEnv -> HFormula -> Node e -> UniqueKey -> ([TId], AbstInfo, Exp) -> R (IType, R IType, ValueExtractor, R ())
calcLambda env fml _node key (xs, _abstInfo, e) = do
    let ps = abstPredicates _abstInfo
    tbl <- liftIO H.new
    reg <- ctxFlowReg <$> ask
    liftIO $ H.lookup reg key >>= \case
        Just l  -> H.insert reg key (SomeNode _node:l)
        Nothing -> H.insert reg key [SomeNode _node]
    let recalc = do
            fs <- getFlow key
            ty_assocs <- fmap mconcat $ forM fs $ \(thetas, phi) ->
                liftIO (H.lookup tbl (thetas,phi)) >>= \case
                    Just body -> do
                        tys <- liftIO $ readIORef (types body)
                        return $ map ((,,) thetas phi) tys
                    Nothing -> do
                        cond <- fromBFormula ps phi
                        fml' <- mkBin SAnd fml cond
                        checkSat fml cond >>= \case
                            False -> return []
                            True -> do
                                let env' = foldr (uncurry M.insert) env (zip xs thetas)
                                (node_body,tys) <- calcExp env' fml' e
                                addDep (ident node_body) _node
                                liftIO $ H.insert tbl (thetas,phi) node_body
                                return $ map ((,,) thetas phi) tys
            mkIFun ty_assocs
        extract env = CCls env xs tbl
    ty <- recalc 
    let destruct = do
            children <- liftIO $ H.toList tbl
            forM_ children $ \(_,node_body) -> destructor node_body
    return (ty, recalc, extract,destruct)
                
calcBranch :: IEnv -> HFormula -> Node e -> (Exp, Exp) -> R ([ITermType] , R [ITermType], TermExtractor, R ())
calcBranch env fml _node (e1, e2) = do
    (node1, tys1) <- calcExp env fml e1 
    (node2, tys2) <- calcExp env fml e2 
    addDep (ident node1) _node
    addDep (ident node2) _node
    let recalc = do
            tys1 <- liftIO $ readIORef $ types node1
            tys2 <- liftIO $ readIORef $ types node2
            return $ merge tys1 tys2
        extract cenv iota = do
            tys1 <- liftIO $ readIORef $ types node1
            if any (flip subTermTypeOf iota) tys1
            then tell [True] >> extractor node1 cenv iota
            else tell [False] >> extractor node2 cenv iota
        destruct = destructor node1 >> destructor node2
    return (merge tys1 tys2, recalc, extract, destruct)

calcLet :: IEnv -> HFormula -> ExpNode -> (TId, LExp,AbstInfo, Exp) -> R ([ITermType], R [ITermType], TermExtractor, R ())
calcLet env fml _node  (x, e1, _abstInfo, e2) = 
    (case lexpView e1 of
        LAtom a -> atomCase a
        LOther SRand _ -> do
            env' <- (\ty -> M.insert x ty env) <$> mkIBase
            (node2, tys) <- calcExp env' fml e2 
            addDep (ident node2) _node
            let recalc :: R [ITermType]
                recalc = liftIO $ readIORef $ types node2
                extract cenv iota = extractor node2 cenv' iota 
                    where cenv' = M.insert x CBase cenv
            return (tys,  recalc, extract, destructor node2)
        _        -> genericCase)
    where 
        atomCase :: Atom -> R ([ITermType], R [ITermType], TermExtractor, R ())
        atomCase atom = do
            vx <- mkVar x
            fml' <- toHFormula atom >>= mkBin SEq vx >>= mkBin SAnd fml
            ity <- genIType (calcAtom env atom)
            let env' = M.insert x ity env
            (node2, tys) <- calcExp env' fml' e2
            addDep (ident node2) _node
            let recalc :: R [ITermType]
                recalc = liftIO $ readIORef $ types node2
                extract cenv iota = extractor node2 cenv' iota 
                    where cenv' = M.insert x (evalAtom cenv atom) cenv
            return (tys,  recalc, extract, destructor node2)
        genericCase = do
            --Just (ps, _) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
            let ps = abstPredicates _abstInfo
            tbl <- liftIO H.new :: R (HashTable (IType, BFormula) ExpNode)
            let genericCalc :: [ITermType] -> R [ITermType]
                genericCalc tys1 =  -- TODO: あるケースが参照されなくなったらdestructする
                    fmap concatMerge $ forM tys1 $ \tau -> case body tau of
                        IFail -> (:[]) <$> mkIFail
                        ITerm ity phi -> do
                            liftIO (H.lookup tbl (ity,phi)) >>= \case
                                Just node2 -> liftIO $ readIORef $ types node2
                                Nothing -> do
                                    let env' = M.insert x ity env
                                    cond <- fromBFormula ps phi
                                    fml' <- mkBin SAnd fml cond
                                    checkSat fml cond >>= \case 
                                        False -> return []
                                        True -> do 
                                            (node2, tys) <- calcExp env' fml' e2 
                                            addDep (ident node2) _node
                                            liftIO $ H.insert tbl (ity,phi) node2 
                                            return tys
            (node1, tys1) <- calcLExp env fml e1 
            addDep (ident node1) _node
            tys <- genericCalc tys1
            let recalc = (liftIO $ readIORef $ types node1) >>= genericCalc
                extract, extractCont :: TermExtractor
                extract cenv iota@(body -> IFail) = do
                    tys1 <- liftIO $ readIORef $ types node1
                    if any (\tau -> IFail == body tau) tys1
                    then extractor node1 cenv iota
                    else extractCont cenv iota
                extract cenv iota = extractCont cenv iota
                extractCont cenv iota = go =<< (liftIO $ readIORef $ types node1)
                    where
                    go (iota1: tys1) = case body iota1 of
                        ITerm ity phi -> liftIO (H.lookup tbl (ity, phi)) >>= \case
                            Nothing -> go tys1 
                            Just node2 -> do
                                tys2 <- liftIO $ readIORef $ types node2
                                if any (flip subTermTypeOf iota) tys2
                                then do
                                    Just cv1 <- extractor node1 cenv iota1
                                    let cenv' = M.insert x cv1 cenv
                                    extractor node2 cenv' iota
                                else go tys1
                        IFail -> go tys1
                    go [] = error "unexpected pattern"
                destruct = do
                    destructor node1
                    children <- liftIO $ H.toList tbl
                    forM_ children $ \(_, node_body) -> destructor node_body
            return (tys, recalc, extract, destruct)

calcLetRec :: IEnv -> HFormula -> ExpNode -> ([(TId, Value)], Exp) -> R ([ITermType], R [ITermType],TermExtractor, R ())
calcLetRec env fml _node (fs, e) = do
    top <- mkIFun []
    let env0 = M.fromList [ (f, top) | (f,_) <- fs ]
        env' = M.union env env0
    node_fs <- forM fs $ \(_,v_f) -> do
        (node_f, _) <- calcValue env' fml v_f
        addDep (ident node_f) _node
        pushQuery (UpdateQuery QEdge _node)
        return node_f

    (node_e, tys) <- calcExp env' fml e
    addDep (ident node_e) _node
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
                    ity_cur <- liftIO $ readIORef (types node)
                    let assocs = case body ity_cur of
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
                    node_fs <- forM fs $ \(_, v_f) -> do
                        (node_f, _) <- calcValue env' fml v_f
                        addDep (ident node_f) _node
                        pushQuery (UpdateQuery QEdge _node)
                        return node_f
                    liftIO $ writeIORef letREnv env1
                    destruct 
                    liftIO $ writeIORef letRChildren node_fs
                    (node_e, tys) <- calcExp env' fml e
                    addDep (ident node_e) _node
                    liftIO $ writeIORef letRCont node_e 
                    return tys
                False -> liftIO $ readIORef letRCont >>= readIORef . types 
        extract cenv iota = do
            let cenv' = foldr (uncurry M.insert) cenv [ (f, CRec cenv' f letRHistory) | (f,_) <- fs ]
            node_e <- liftIO $ readIORef letRCont
            extractor node_e cenv' iota
        destruct = do
            node_e <- liftIO $ readIORef letRCont
            destructor node_e
            nodes <- liftIO $ readIORef letRChildren
            forM_ nodes $ \node_f -> destructor node_f
    return (tys, recalc,extract, destruct)

calcAssume :: IEnv -> HFormula -> ExpNode -> (Atom, Exp) -> R ([ITermType], R [ITermType], TermExtractor, R ())
calcAssume env fml _node (a, e) = do
    cond <- toHFormula a 
    checkSat fml cond >>= \case
        True -> do
            fml' <- mkBin SAnd fml cond
            (node_e, tys) <- calcExp env fml' e
            addDep (ident node_e) _node
            let recalc  = liftIO $ readIORef $ types node_e
                extract = extractor node_e
            return (tys, recalc, extract, destructor node_e)
        False -> 
            let extract :: TermExtractor
                extract _ _ = error "assume(false) never returns values" in
            return ([], return [], extract, return ())

calcApp :: IEnv -> HFormula -> LExpNode -> (TId, AbstInfo, [Value]) -> R ([ITermType], R [ITermType], TermExtractor, R ())
calcApp env fml _node (f, _abstInfo, vs) = do
    let ity_f = env ! f
    let ps = abstPredicates _abstInfo
    -- Just (ps, _) <- ask >>= \ctx -> liftIO (H.lookup (ctxArgTypeTbl ctx) key)
    phi <- calcCondition fml ps
    (nodes,thetas) <- fmap unzip $ forM vs $ calcValue env fml 
    forM_ nodes $ \node -> addDep (ident node) _node
    flowMap <- ctxFlowMap <$> ask
    forM_ (flowMap ! f) $ \ident -> addFlow ident (thetas,phi)

    let recalc = do
            thetas <- forM nodes $ liftIO . readIORef . types
            forM_ (flowMap ! f) $ \ident -> addFlow ident (thetas,phi)
            return $ appType ity_f thetas phi
        destruct = do
            forM_ nodes $ destructor
        extract cenv iota = do
            let cvs = map (\node -> extractor node cenv) nodes
            thetas <- forM nodes $ liftIO . readIORef . types
            let closureCase (CCls cenv_f xs tbl) = do
                    node <- liftIO $ H.lookup tbl (thetas, phi) >>= \case
                        Just node -> return node
                        Nothing -> H.foldM (\acc ((thetas',phi'),val) -> do
                            tys <- readIORef $ types val
                            if phi == phi' && 
                               and (zipWith subTypeOf thetas thetas') && 
                               any (flip subTermTypeOf iota) tys
                            then return val
                            else return acc) (error "no match") tbl
                    let cenv_f' = foldr (uncurry M.insert) cenv_f (zip xs cvs)
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
    return (appType ity_f thetas phi, recalc, extract, destruct)

addDep :: Int -> Node e -> R ()
addDep !v node = do
    tbl <- ctxNodeDepG <$> ask 
    liftIO $ 
        H.lookup tbl v >>= \case
            Nothing -> H.insert tbl v [SomeNode node]
            Just l  -> H.insert tbl v (SomeNode node:l)

calcValue :: IEnv -> HFormula -> Value -> R (ValueNode, IType)
calcValue env fml value@(Value l arg sty key) = 
    let fromAtom :: Atom -> R (IType, R IType, ValueExtractor, R ())
        fromAtom atom = do
            ity <- genIType (calcAtom env atom)
            let extract cenv = evalAtom cenv atom
            return (ity, return ity, extract, return ())
    in mfix $ \ ~(_node, _ity) -> do
        (ity,recalc, extract, destruct) <- case l of
            SLiteral -> fromAtom (Atom l arg sty)
            SVar     -> fromAtom (Atom l arg sty)
            SBinary  -> fromAtom (Atom l arg sty)
            SUnary   -> fromAtom (Atom l arg sty)
            SPair    -> calcPair env fml _node arg
            SLambda  -> calcLambda env fml _node key arg
        itypeRef <- liftIO $ newIORef ity
        nodeIdent <- incrNodeCounter
        let pp = genericPrint env fml value itypeRef nodeIdent pPrint pPrint
        alive <- liftIO $ newIORef True
        let destruct' = (destruct :: R ()) >> liftIO (writeIORef alive False)
        let node = Node { typeEnv = env
                        , constraint = fml
                        , ident = nodeIdent
                        , term = value
                        , types = itypeRef
                        , recalcator = recalc
                        , extractor  = extract 
                        , destructor = destruct'
                        , alive    = alive
                        , pprinter = pp}
        {-
        liftIO $ putStrLn "created"
        liftIO $ printNode node
        -}
        return (node, ity)

calcExp :: IEnv -> HFormula -> Exp -> R (ExpNode, [ITermType])
calcExp env fml exp = 
    let fromValue = calcFromValue fml 
        fromAtom ps atom = do
            ity <- genIType (calcAtom env atom)
            calcFromValue fml ps (ity, return ity, flip evalAtom atom, return ())
        key = getUniqueKey exp
    in mfix $ \ ~(_node, _tys) -> do
        (itys,recalc, extract, destruct) <- case expView exp of
            EValue v _info -> 
                let ps = abstPredicates _info in
                case valueView v of
                    VAtom a -> fromAtom ps a
                    VOther SPair arg -> fromValue ps =<< calcPair env fml _node arg
                    VOther SLambda arg -> fromValue ps =<< calcLambda env fml _node key arg
            EOther SLet arg -> calcLet env fml _node arg
            EOther SLetRec arg -> calcLetRec env fml _node arg
            EOther SAssume arg -> calcAssume env fml _node arg
            EOther SBranch arg -> calcBranch env fml _node arg
            EOther SFail _ -> do
                let extract _ (body -> IFail) = return Nothing
                    extract _ _ = error "extract@SFail_calcExp: fail never returns values"
                tfail <- mkIFail
                return ([tfail], return [tfail], extract, return ())
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
        nodeIdent <- incrNodeCounter
        alive <- liftIO $ newIORef True
        let destruct' = (destruct :: R ()) >> liftIO (writeIORef alive False)
        let pp = genericPrint env fml exp itypeRef nodeIdent pPrint pPrint
        let node = Node { typeEnv = env
                        , constraint = fml
                        , ident = nodeIdent
                        , term = exp
                        , types = itypeRef
                        , recalcator = recalc
                        , extractor = extract'
                        , destructor = destruct'
                        , alive = alive
                        , pprinter = pp }
                        {-
        liftIO $ putStrLn "created"
        liftIO $ printNode node
        -}
        return (node, itys)

calcLExp :: IEnv -> HFormula -> LExp -> R (LExpNode, [ITermType])
calcLExp env fml lexp =  
    mfix $ \ ~(_node, _tys) -> do
        (itys,recalc, extract, destruct) <- case lexpView lexp of
            LAtom _ -> error "impossible"
            {-
                do
                    ity <- genIType $ calcAtom env atom
                    calcFromValue fml key (ity, return ity, flip evalAtom atom, return ())
                    -}
            LOther SBranch arg -> calcBranch env fml _node arg
            LOther SApp arg -> calcApp env fml _node arg
            LOther SRand _ -> do
                let extract _ _ = error "extract@SRand_calcExp: should never be called"
                ity <- mkIBase
                btrue <- mkBLeaf True
                ty <- mkITerm ity btrue
                return ([ty], return [ty], extract, return ())
            {-
            SPair    -> fromValue =<< calcPair env fml _node arg
            SLambda  -> fromValue =<< calcLambda env fml _node key arg
            SFail    -> do
                let extract _ (body -> IFail) = return Nothing
                    extract _ _ = error "extract@SFail_calcExp: fail never returns values"
                tfail <- mkIFail
                return ([tfail], return [tfail], extract, return ())
            SOmega   -> 
                let extract _ _ = error "extract@SOmega_calcExp: omega never returns value nor fails"
                in return ([], return [], extract, return ())
                -}
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
        nodeIdent <- incrNodeCounter
        let pp = genericPrint env fml lexp itypeRef nodeIdent pPrint pPrint
        let node = Node { typeEnv = env
                        , constraint = fml
                        , ident = nodeIdent
                        , term = lexp
                        , types = itypeRef
                        , recalcator = recalc 
                        , extractor = extract'
                        , destructor = destruct'
                        , alive = alive
                        , pprinter = pp}
                        {-
        liftIO $ putStrLn "created"
        liftIO $ printNode node
        -}
        return (node, itys)

updateLoop :: R ()
updateLoop = popQuery >>= \case
    Nothing -> return ()
    Just (UpdateQuery _ node) -> do
        -- liftIO $ putStrLn "Updating"
        case node of
            Node {ident = ident, alive = alive} -> do
                liftIO (readIORef alive) >>= \case
                    True -> do
                        new_ity <- recalcator node
                        old_ity <- liftIO $ readIORef (types node) 
                        liftIO $ writeIORef (types node) new_ity
                        {-
                        liftIO $ do
                            putStrLn "recalculated"
                            printNode node
                            -}
                        when (new_ity /= old_ity) $ do
                            tbl <- ctxNodeDepG <$> ask
                            liftIO (H.lookup tbl ident) >>= \case
                                Nothing -> pure ()
                                Just ns -> forM_ ns $ \(SomeNode n) ->
                                    pushQuery (UpdateQuery QEdge n) 
                        updateLoop
                    False -> updateLoop

saturate :: HFormula.Context -> Program -> TracerT (Dict IncSat) (LoggingT IO) (Bool, ([ITermType], Maybe [Bool]))
saturate hctx prog = do
    ctx <- lift $ initContext prog
    let doit :: R (Bool, ([ITermType], Maybe [Bool]))
        doit = do
            SMT.initSMTContext
            -- calcContextE (mainTerm prog) 
            -- _ <- calcFVE (mainTerm prog)
            logPretty "saturate" LevelDebug "Abstraction Annotated Program" (PPrinted (pPrint prog))
            (root, _) <- mkLiteral (CBool True) >>= \fml0 -> calcExp M.empty fml0 (mainTerm prog)
            updateLoop
            tys <- liftIO $ readIORef (types root)
            if any (\iota -> body iota == IFail) tys
            then do
                bs <- mkIFail >>= execWriterT . extractor root M.empty
                --hcs <- AbsSemantics.genConstraints bs (mainTerm prog)
                -- liftIO $ print hcs
                return (True, (tys, Just bs))
            else do
                return (False, (tys, Nothing))
    res <- lift $ runHFormulaT (evalStateT (runReaderT (unR doit) ctx) (emptyQueue, S.empty)) hctx
    dict <- liftIO $ getStatistics ctx
    update (id .~ dict)
    return res

