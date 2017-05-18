{-# LANGUAGE DeriveGeneric, GeneralizedNewtypeDeriving, MultiParamTypeClasses, UndecidableInstances #-}
module Language.DMoCHi.ML.IncSaturation(saturate) where
import           Language.DMoCHi.ML.Syntax.PNormal hiding(mkBin, mkUni, mkVar, mkLiteral)
import           Language.DMoCHi.ML.Syntax.HFormula
import           Language.DMoCHi.ML.Syntax.PType hiding(ArgType)
import           Language.DMoCHi.Common.Id
import           Language.DMoCHi.ML.Flow
import           Language.DMoCHi.ML.IncSaturationPre
import qualified Language.DMoCHi.ML.Syntax.PNormal as PNormal

-- import Control.Monad
import           Control.Monad.Fix
--import Control.Arrow ((***),second)
import           Control.Monad.Reader
import           Control.Monad.Writer hiding((<>))
import           Control.Monad.State.Strict
import qualified Z3.Monad as Z3
import qualified Z3.Base as Z3Base
-- import Data.List
import           Data.IORef
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.HashTable.IO as H
import           Text.PrettyPrint.HughesPJClass
import           Debug.Trace

calcContextV :: M.Map TId PType -> Value -> PType -> R ()
calcContextV env (Value l arg _ key) pty = 
    case (l, arg) of
        (SLiteral, _) -> return ()
        (SVar, _) -> return ()
        (SUnary, _) -> return ()
        (SBinary, _) -> return ()
        (SPair, (v1, v2)) -> do
            let PPair _ pty1 pty2 = pty
            calcContextV env v1 pty1
            calcContextV env v2 pty2
        (SLambda, (xs, e)) -> do
            let PFun _ (ys, ty_ys, ps) tau = pty
                subst = M.fromList (zip ys xs)
                ty_ys' = map (substPType subst) ty_ys
                ps'    = map (substFormula subst) ps
                tau'   = substTermType subst tau
                env'   = foldr (uncurry M.insert) env $ zip xs ty_ys'
            ctx <- ask
            ps' <- mapM toHFormula ps'
            liftIO $ H.insert (ctxArgTypeTbl ctx) key (ty_ys', ps')
            calcContextE env' e tau'

calcContextE :: M.Map TId PType -> Exp -> TermType -> R ()
calcContextE env (Exp l arg sty key) tau =
    let valueCase :: Value -> R () 
        valueCase v = do
            let (r, rty, ps) = tau
            let subst = M.singleton r v
                rty' = substVPType subst rty
                ps' = map (substVFormula subst) ps
            tbl <- ctxRtnTypeTbl <$> ask 
            ps' <- mapM toHFormula ps'
            calcContextV env v rty'
            liftIO (H.insert tbl key (rty', ps'))
    in case (l, arg) of
        (SLiteral, _) -> valueCase (Value l arg sty key)
        (SVar, _)     -> valueCase (Value l arg sty key)
        (SUnary, _)   -> valueCase (Value l arg sty key)
        (SBinary, _)  -> valueCase (Value l arg sty key)
        (SPair, _)    -> valueCase (Value l arg sty key)
        (SLambda, _)  -> valueCase (Value l arg sty key)
        (SLet, (x, LExp l1 arg1 sty1 key1, e2)) -> 
            let atomCase av = do
                    let ty_x = typeOfAtom env av
                    let env' = M.insert x ty_x env
                    ask >>= \ctx -> liftIO $ H.insert (ctxRtnTypeTbl ctx) key (ty_x, [])
                    calcContextE env' e2 tau
                exprCase e1 = do
                    ctx <- ask
                    let Right tau1@(y, ty_y, ps) = ctxTypeMap ctx ! key1
                        subst = M.singleton y x
                        ps'   = map (substFormula subst) ps
                        ty_x  = substPType subst ty_y
                        env'  = M.insert x ty_x env
                    ps' <- mapM toHFormula ps'
                    liftIO $ H.insert (ctxRtnTypeTbl ctx) key (ty_x, ps')
                    calcContextE env e1 tau1
                    calcContextE env' e2 tau
            in case (l1, arg1) of
                (SLiteral, _) -> atomCase (Atom l1 arg1 sty1)
                (SVar, _)     -> atomCase (Atom l1 arg1 sty1)
                (SBinary, _)  -> atomCase (Atom l1 arg1 sty1)
                (SUnary, _)   -> atomCase (Atom l1 arg1 sty1)
                (SApp, (f, vs)) -> do
                    let PFun _ argTy retTy = env ! f
                        (ys, ptys, ps) = argTy
                        subst = M.fromList $ zip ys vs
                        ptys' = map (substVPType subst) ptys
                        ps'   = map (substVFormula subst) ps
                        (r, rty, qs) = retTy
                        subst' = M.insert r (cast (PNormal.mkVar x)) subst
                        qs' = map (substVFormula subst') qs
                        rty' = substVPType subst' rty
                        env' = M.insert x rty' env
                    ctx <- ask
                    ps' <- mapM toHFormula ps'
                    qs' <- mapM toHFormula qs'
                    liftIO (H.insert (ctxArgTypeTbl ctx) key (ptys', ps'))
                    liftIO (H.insert (ctxArgTypeTbl ctx) key1 (ptys', ps'))
                    liftIO (H.insert (ctxRtnTypeTbl ctx) key (rty', qs'))
                    zipWithM_ (\v ty_v -> calcContextV env v ty_v) vs ptys'
                    calcContextE env' e2 tau
                (SPair, _)   -> exprCase (Exp l1 arg1 sty1 key1)
                (SLambda, _) -> exprCase (Exp l1 arg1 sty1 key1)
                (SFail, _)   -> exprCase (Exp l1 arg1 sty1 key1)
                (SOmega, _)  -> exprCase (Exp l1 arg1 sty1 key1)
                (SRand, _)   -> do
                    ask >>= \ctx -> liftIO (H.insert (ctxRtnTypeTbl ctx) key (PInt, []))
                    calcContextE (M.insert x PInt env) e2 tau
                (SBranch, _) -> exprCase (Exp l1 arg1 sty1 key1)
        (SLetRec, (fs, e2)) -> do
            tbl <- ctxTypeMap <$> ask
            let as = [ (f, ty_f) | (f,v_f) <- fs, 
                                   let Left ty_f = tbl ! getUniqueKey v_f ]
                env' = foldr (uncurry M.insert) env as
            forM_ fs $ \(f,v_f) -> calcContextV env' v_f (env' ! f)
            calcContextE env' e2 tau
        (SAssume, (_, e)) -> calcContextE env e tau
        (SBranch, (e1, e2)) -> calcContextE env e1 tau >> calcContextE env e2 tau
        (SFail, _) -> return ()
        (SOmega, _) -> return ()

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

calcAtom :: IEnv -> Atom -> IType
calcAtom env (Atom l arg _) = case (l, arg) of
    (SLiteral, CInt _)  -> IInt
    (SLiteral, CBool _) -> IInt
    (SVar, x) -> env ! x
    (SBinary, BinArg op _ _) -> case op of
        SAdd -> IInt
        SSub -> IInt
        SEq  -> IBool
        SLt  -> IBool
        SLte -> IBool
        SAnd -> IBool
        SOr  -> IBool
    (SUnary, UniArg op v) -> case op of
        SFst -> (\(IPair i1 _) -> i1) $ calcAtom env v
        SSnd -> (\(IPair _ i2) -> i2) $ calcAtom env v
        SNeg -> IInt
        SNot -> IBool

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

calcFromValue :: HFormula -> UniqueKey -> (IType, R IType, ValueExtractor, R ()) 
                 -> R ([ITermType], R [ITermType], TermExtractor, R ())
calcFromValue fml key (theta, recalc, extract, destruct) = do
    Just (_,ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
    phi <- calcCondition fml ps
    let recalc' = (\theta -> [ITerm theta phi]) <$> recalc
        extract' env (ITerm _ phi') 
            | phi == phi' = return $ Just (extract env)
            | otherwise = error "extract@calcFromValue: condition mismatch"
        extract' _ _ = error "values never fail"
    return ([ITerm theta phi], recalc', extract', destruct)

calcPair :: IEnv -> HFormula -> Node e -> (Value,Value) -> R (IType, R IType, ValueExtractor, R ())
calcPair env fml _node (v1,v2) = do
    (node1, ty1) <- calcValue env fml _node v1 
    (node2, ty2) <- calcValue env fml _node v2
    let recalc = do
            ty1 <- liftIO $ readIORef $ types $ node1
            ty2 <- liftIO $ readIORef $ types $ node2
            return $ IPair ty1 ty2
        extract env = CPair (extractor node1 env) (extractor node2 env)
        destruct = destructor node1 >> destructor node2
    return (IPair ty1 ty2, recalc, extract, destruct)
    
calcLambda :: NonRoot e => IEnv -> HFormula -> Node e -> UniqueKey -> ([TId], Exp) -> R (IType, R IType, ValueExtractor, R ())
calcLambda env fml _node key (xs, e) = do
    Just (_, ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxArgTypeTbl ctx) key
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
                                (node_body,tys) <- calcExp env' fml' _node  e
                                liftIO $ H.insert tbl (thetas,phi) node_body
                                return $ map ((,,) thetas phi) tys
            return $ IFun ty_assocs
        extract env = CCls env xs tbl
    ty <- recalc 
    let destruct = do
            children <- liftIO $ H.toList tbl
            forM_ children $ \(_,node_body) -> destructor node_body
    return (ty, recalc, extract,destruct)
                
calcBranch :: IEnv -> HFormula -> Node e -> (Exp, Exp) -> R ([ITermType] , R [ITermType], TermExtractor, R ())
calcBranch env fml _node (e1, e2) = do
    (node1, tys1) <- calcExp env fml _node e1 
    (node2, tys2) <- calcExp env fml _node e2 
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

calcLet :: IEnv -> HFormula -> ExpNode -> UniqueKey -> (TId, LExp, Exp) -> R ([ITermType], R [ITermType], TermExtractor, R ())
calcLet env fml _node key (x, e1@(LExp l1 arg1 sty1 _), e2) = 
    (case l1 of
        SLiteral -> atomCase (Atom l1 arg1 sty1)
        SVar     -> atomCase (Atom l1 arg1 sty1)
        SUnary   -> atomCase (Atom l1 arg1 sty1)
        SBinary  -> atomCase (Atom l1 arg1 sty1)
        SRand    -> do
            let env' = M.insert x IInt env
            (node2, tys) <- calcExp env' fml _node e2 
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
            let ity = calcAtom env atom 
                env' = M.insert x ity env
            (node2, tys) <- calcExp env' fml' _node e2
            let recalc :: R [ITermType]
                recalc = liftIO $ readIORef $ types node2
                extract cenv iota = extractor node2 cenv' iota 
                    where cenv' = M.insert x (evalAtom cenv atom) cenv
            return (tys,  recalc, extract, destructor node2)
        genericCase = do
            Just (_, ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
            tbl <- liftIO H.new :: R (HashTable (IType, BFormula) ExpNode)
            let genericCalc :: [ITermType] -> R [ITermType]
                genericCalc tys1 =  -- TODO: あるケースが参照されなくなったらdestructする
                    fmap concatMerge $ forM tys1 $ \case
                        IFail -> return [IFail]
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
                                            (node2, tys) <- calcExp env' fml' _node e2 
                                            liftIO $ H.insert tbl (ity,phi) node2 
                                            return tys
            (node1, tys1) <- calcLExp env fml _node e1 
            tys <- genericCalc tys1
            let recalc = (liftIO $ readIORef $ types node1) >>= genericCalc
                extract, extractCont :: TermExtractor
                extract cenv IFail = do
                    tys1 <- liftIO $ readIORef $ types node1
                    if IFail `elem` tys1
                    then extractor node1 cenv IFail
                    else extractCont cenv IFail
                extract cenv iota = extractCont cenv iota
                extractCont cenv iota = go =<< (liftIO $ readIORef $ types node1)
                    where
                    go (IFail: tys1) = go tys1
                    go (ITerm ity phi: tys1) = 
                        liftIO (H.lookup tbl (ity, phi)) >>= \case
                            Nothing -> go tys1 
                            Just node2 -> do
                                tys2 <- liftIO $ readIORef $ types node2
                                if any (flip subTermTypeOf iota) tys2
                                then do
                                    Just cv1 <- extractor node1 cenv (ITerm ity phi)
                                    let cenv' = M.insert x cv1 cenv
                                    extractor node2 cenv' iota
                                else go tys1
                    go [] = error "unexpected pattern"
                destruct = do
                    destructor node1
                    children <- liftIO $ H.toList tbl
                    forM_ children $ \(_, node_body) -> destructor node_body
            return (tys, recalc, extract, destruct)

calcLetRec :: IEnv -> HFormula -> ExpNode -> ([(TId, Value)], Exp) -> R ([ITermType], R [ITermType],TermExtractor, R ())
calcLetRec env fml _node (fs, e) = do
    let env0 = M.fromList [ (f, IFun []) | (f,_) <- fs ]
        env' = M.union env env0
    node_fs <- forM fs $ \(_,v_f) -> do
        (node_f@Node { parent = edge_f } , _) <- calcValue env' fml _node v_f
        pushQuery (UpdateQuery QEdge edge_f)
        return node_f

    (node_e, tys) <- calcExp env' fml _node e
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
                    IFun assocs <- liftIO $ readIORef (types node)
                    forM_ assocs $ \(thetas, phi, iota) -> 
                        liftIO $ H.lookup letRHistory (f, (thetas,phi), iota) >>= \case 
                            Just _ -> return ()
                            Nothing -> do
                               H.insert letRHistory (f, (thetas,phi), iota) node
                               writeIORef updated True
                    let IFun assocs' = env0 ! f
                    return (f, IFun (merge assocs assocs'))
                ) nodes fs
            liftIO (readIORef updated) >>= \case
                True -> do
                    let env' = M.union env env1
                    node_fs <- forM fs $ \(_, v_f) -> do
                        (node_f@(Node { parent = parent }), _) <- calcValue env' fml _node v_f
                        pushQuery (UpdateQuery QEdge parent)
                        return node_f
                    liftIO $ writeIORef letREnv env1
                    destruct 
                    liftIO $ writeIORef letRChildren node_fs
                    (node_e, tys) <- calcExp env' fml _node e
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
            (node_e, tys) <- calcExp env fml' _node e
            let recalc  = liftIO $ readIORef $ types node_e
                extract = extractor node_e
            return (tys, recalc, extract, destructor node_e)
        False -> 
            let extract :: TermExtractor
                extract _ _ = error "assume(false) never returns values" in
            return ([], return [], extract, return ())

calcApp :: IEnv -> HFormula -> LExpNode -> UniqueKey -> (TId, [Value]) -> R ([ITermType], R [ITermType], TermExtractor, R ())
calcApp env fml _node key (f, vs) = do
    let IFun assoc = env ! f
    Just (_, ps) <- ask >>= \ctx -> liftIO (H.lookup (ctxArgTypeTbl ctx) key)
    phi <- calcCondition fml ps
    (nodes,thetas) <- fmap unzip $ forM vs $ calcValue env fml _node
    flowMap <- ctxFlowMap <$> ask
    forM_ (flowMap ! f) $ \ident -> addFlow ident (thetas,phi)
    
    let appType thetas = 
            [ iota | (thetas', phi', iota) <- assoc,
                     thetas == thetas' && phi == phi' ]
        recalc = do
            thetas <- forM nodes $ liftIO . readIORef . types
            forM_ (flowMap ! f) $ \ident -> addFlow ident (thetas,phi)
            return $ appType thetas
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
    return (appType thetas, recalc, extract, destruct)

calcValue :: IEnv -> HFormula -> Node e -> Value -> R (ValueNode, IType)
calcValue env fml parent value@(Value l arg sty key) = 
    let fromAtom :: Atom -> (IType, R IType, ValueExtractor, R ())
        fromAtom atom = (ity, return ity, extract, return ())
            where ity = calcAtom env atom
                  extract cenv = evalAtom cenv atom
    in mfix $ \ ~(_node, _ity) -> do
        (ity,recalc, extract, destruct) <- case l of
            SLiteral -> (return $ fromAtom (Atom l arg sty))
            SVar    -> (return $ fromAtom (Atom l arg sty))
            SBinary -> (return $ fromAtom (Atom l arg sty))
            SUnary  -> (return $ fromAtom (Atom l arg sty))
            SPair   -> calcPair env fml _node arg
            SLambda -> calcLambda env fml _node key arg
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
                        , parent = parent
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

calcExp :: IEnv -> HFormula -> Node e -> Exp -> R (ExpNode, [ITermType])
calcExp env fml parent exp@(Exp l arg sty key) = 
    let fromValue :: (IType, R IType, ValueExtractor, R ()) -> R ([ITermType], R [ITermType], TermExtractor, R ())
        fromValue = calcFromValue fml key
        fromAtom atom = do
            let ity = calcAtom env atom
            calcFromValue fml key (ity, return ity, flip evalAtom atom, return ())
    in mfix $ \ ~(_node, _tys) -> do
        (itys,recalc, extract, destruct) <- case l of
            SLiteral -> fromAtom (Atom l arg sty)
            SVar     -> fromAtom (Atom l arg sty)
            SBinary  -> fromAtom (Atom l arg sty)
            SUnary   -> fromAtom (Atom l arg sty)
            SPair    -> fromValue =<< calcPair env fml _node arg
            SLambda  -> fromValue =<< calcLambda env fml _node key arg
            SLet     -> calcLet env fml _node key arg
            SLetRec  -> calcLetRec env fml _node arg
            SAssume  -> calcAssume env fml _node arg
            SBranch  -> calcBranch env fml _node arg
            SFail    -> 
                let extract _ IFail = return Nothing
                    extract _ _ = error "extract@SFail_calcExp: fail never returns values"
                in return ([IFail], return [IFail], extract, return ())
            SOmega   -> 
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
                        , parent = parent
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

calcLExp :: IEnv -> HFormula -> Node e -> LExp -> R (LExpNode, [ITermType])
calcLExp env fml parent lexp@(LExp l arg sty key) =  
    let fromValue :: (IType, R IType, ValueExtractor, R ()) -> R ([ITermType], R [ITermType], TermExtractor, R ())
        fromValue = calcFromValue fml key
        fromAtom atom = do
            let ity = calcAtom env atom
            calcFromValue fml key (ity, return ity, flip evalAtom atom, return ())
    in mfix $ \ ~(_node, _tys) -> do
        (itys,recalc, extract, destruct) <- case l of
            SLiteral -> fromAtom (Atom l arg sty)
            SVar     -> fromAtom (Atom l arg sty)
            SBinary  -> fromAtom (Atom l arg sty)
            SUnary   -> fromAtom (Atom l arg sty)
            SPair    -> fromValue =<< calcPair env fml _node arg
            SLambda  -> fromValue =<< calcLambda env fml _node key arg
            SBranch  -> calcBranch env fml _node arg
            SApp     -> calcApp env fml _node key arg
            SFail    -> 
                let extract _ IFail = return Nothing
                    extract _ _ = error "extract@SFail_calcExp: fail never returns values"
                in return ([IFail], return [IFail], extract, return ())
            SOmega   -> 
                let extract _ _ = error "extract@SOmega_calcExp: omega never returns value nor fails"
                in return ([], return [], extract, return ())
            SRand    -> 
                let extract _ _ = error "extract@SRand_calcExp: should never be called" in
                return ([ITerm IInt (BConst True)], return [ITerm IInt (BConst True)], extract, return ())
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
                        , parent = parent
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
            Node {parent = parent, alive = alive} -> do
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
                        when (new_ity /= old_ity) $ pushQuery (UpdateQuery QEdge parent) 
                        updateLoop
                    False -> updateLoop
            RootNode _main -> do
                -- tys <- liftIO $ readIORef (types main)
                -- unless (IFail `elem` tys) 
                updateLoop

saturate :: TypeMap -> Program -> IO (Bool, ([ITermType], Maybe [Bool]))
saturate typeMap prog = do
    (smtSolver, smtContext) <- Z3Base.withConfig $ \cfg -> do
        Z3.setOpts cfg Z3.stdOpts
        ctx <- Z3Base.mkContext cfg
        solver <- Z3Base.mkSolver ctx
        return (solver, ctx)
    ctx <- Context <$> H.new               -- ctxFlowTbl
                   <*> H.new               -- ctxFlowReg
                   <*> pure typeMap        -- ctxTypeMap
                   <*> flowAnalysis prog   -- ctxFlowMap
                   <*> newIORef 1          -- ctxNodeCounter 
                   <*> H.new               -- ctxRtnTypeTbl
                   <*> H.new               -- ctxArgTypeTbl
                   <*> H.new               -- ctxHFormulaTbl
                   <*> newIORef 0          -- ctxHFormulaSize
                   <*> H.new               -- ctxCheckSatCache
                   <*> newIORef False      -- ctxUpdated
                   <*> newIORef 0          -- ctxSMTCount
                   <*> newIORef 0          -- ctxSMTCountHit
                   <*> H.new               -- ctxTimer
                   <*> return smtSolver    -- ctxSMTSolver
                   <*> return smtContext   -- ctxSMTContext
    let doit :: R (Bool, ([ITermType], Maybe [Bool]))
        doit = do
            calcContextE M.empty (mainTerm prog) (TId TInt (reserved "main"), PInt, [])
            liftIO $ putStrLn "Abstraction Annotated Program"
            pprintContext prog >>= liftIO . print
            RootNode n <- mfix $ \ _root -> do
                fml0 <- mkLiteral (CBool True)
                (node, _) <- calcExp M.empty fml0 _root (mainTerm prog)
                return (RootNode node)
            updateLoop
            tys <- liftIO $ readIORef (types n)
            if IFail `elem` tys
            then do
                bs <- execWriterT (extractor n M.empty IFail)
                return (True, (tys, Just bs))
            else return (False, (tys, Nothing))
    evalStateT (runReaderT (unR doit) ctx) (emptyQueue, S.empty)
