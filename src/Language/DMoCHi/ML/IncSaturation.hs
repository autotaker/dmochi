module Language.DMoCHi.ML.IncSaturation where
import Language.DMoCHi.ML.Syntax.PNormal hiding(mkBin, mkUni, mkVar, mkLiteral)
import Language.DMoCHi.ML.Syntax.HFormula
-- import Control.Monad
import Control.Monad.Fix
import Control.Arrow ((***))
import Control.Monad.Reader
import Data.IORef
import qualified Z3.Monad as Z3
import Data.List
--import qualified Z3.Base as Z3Base
import Language.DMoCHi.Common.Id
import           Data.Time
import qualified Data.Map.Strict as M
import qualified Data.HashTable.IO as H
import qualified Language.DMoCHi.ML.SMT as SMT
import qualified Data.Sequence as Q

type IEnv = M.Map TId IType
type CEnv = ()
type ArgType = ([IType],BFormula)

type Queue a = Q.Seq a
popQueue :: Queue a -> Maybe (a, Queue a)
popQueue queue = case Q.viewl queue of
    Q.EmptyL -> Nothing
    a Q.:< queue' -> Just (a, queue')

pushQueue :: a -> Queue a -> Queue a
pushQueue a queue = queue Q.|> a

data Node e where
    Node :: (Normalized l e arg, Supported l (Labels e)) => 
            { typeEnv    :: IEnv
            , constraint :: HFormula
            , refl   :: NodeProxy e
            , term   :: (SLabel l, arg, Type, UniqueKey)
            , types  :: SatType e
            , parent :: Edge (Node e') (Node e)
            , edges :: Meta l
            } -> Node e

type family SatType e where
    SatType Exp = IORef [ITermType]
    SatType LExp = IORef [ITermType]
    SatType Value = IORef IType
    SatType Atom = IType

type ValueNode = Node Value
type ExpNode = Node Exp
type LExpNode = Node LExp
type AtomNode = Node Atom

data NodeProxy e where
    NodeExp   :: NodeProxy Exp
    NodeLExp  :: NodeProxy LExp
    NodeValue :: NodeProxy Value
    NodeAtom  :: NodeProxy Atom

data EdgeLabel = ELambda ArgType
               | EApp Int
               | ELetC (IType, BFormula)
               | ELetRecD TId
               | EBranch Bool
               | EPair Bool
               | ENone

data Edge fromNode  toNode = 
    Edge { from  :: fromNode
         , to    :: toNode
         , label :: EdgeLabel
         , alive :: IORef Bool
    }

type family Meta (l :: Label) where
   Meta 'Let = MetaLet 
   Meta 'LetRec = MetaLetR
   Meta 'Lambda = MetaLambda
   Meta 'App = MetaApp
   Meta 'Assume = MetaAssume
   Meta 'Pair = MetaPair
   Meta 'Branch = MetaBranch
   Meta l = ()

data MetaLet = 
    MetaLet { letChild :: Edge ExpNode LExpNode
            , letCont  :: IORef [Edge ExpNode ExpNode]
            , letTypeSet :: IORef (M.Map ITermType [Maybe (IType,BFormula)]) }

data MetaLetR = 
    MetaLetR { letRChildren :: IORef [Edge ExpNode ValueNode]
             , letRHistory :: HashTable (TId, ArgType, ITermType) ValueNode 
             , letREnv  :: IORef IEnv
             , letRCont :: IORef (Edge ExpNode ExpNode) }

data MetaLambda where
    MetaLambda :: { lamChildren :: IORef [Edge e ExpNode] } -> MetaLambda

data MetaApp = MetaApp { appArg :: [Edge LExpNode ValueNode], appCond :: BFormula }
newtype MetaAssume = MetaAssume { assumeCont :: Maybe (Edge ExpNode ExpNode) }
data MetaPair where
    MetaPair :: { pairFst :: Edge e ValueNode 
                , pairSnd :: Edge e ValueNode} -> MetaPair
data MetaBranch where
    MetaBranch :: { branchFst :: Edge e ExpNode 
                  , branchSnd :: Edge e ExpNode 
                  , branchTypeSet :: IORef (M.Map ITermType Int) } -> MetaBranch

data UpdateQuery where
    QValue :: Edge (Node e) ValueNode -> IType -> UpdateQuery
    QExp   :: Edge (Node e) ExpNode   -> [ITermType] -> [ITermType] -> UpdateQuery
    QLExp  :: Edge (Node e) LExpNode   -> [ITermType] -> [ITermType] -> UpdateQuery

getFlow :: UniqueKey -> R [([IType], BFormula)]
getFlow = undefined

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
    go _ _ [] = return $ BConst True
    go i fml (p:ps) = do
        np <- mkUni SNot p
        b1 <- checkSat fml p
        b2 <- checkSat fml np
        v1 <- if b1 then mkBin SAnd fml p >>= \fml' -> go (i + 1) fml' ps 
                    else return $ BConst False
        v2 <- if b2 then mkBin SAnd fml np >>= \fml' -> go (i + 1) fml' ps 
                    else return $ BConst False
        if v1 == v2 then
            return v1
        else 
            return $ mkBOr (mkBAnd (BVar i) v1) (mkBAnd (BVar (-i)) v2)


fromBFormula :: [HFormula] -> BFormula -> R HFormula
fromBFormula ps (BVar i) 
    | i < 0     = mkUni SNot (ps !! ((-i) - 1))
    | otherwise = return $ ps !! (i - 1)
fromBFormula _  (BConst b)   = mkLiteral (CBool b)
fromBFormula ps (BOr p1 p2)  = do
    v1 <- fromBFormula ps p1
    v2 <- fromBFormula ps p2
    mkBin SOr  v1 v2
fromBFormula ps (BAnd p1 p2) = do
    v1 <- fromBFormula ps p1
    v2 <- fromBFormula ps p2
    mkBin SAnd v1 v2
merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys) = case compare x y of
    EQ -> x : merge xs ys
    LT -> x : merge xs (y:ys)
    GT -> y : merge (x:xs) ys

concatMerge :: Ord a => [[a]] -> [a]
concatMerge [] = []
concatMerge [x] = x
concatMerge (x:y:xs) = concatMerge (merge x y:xs)

diffTypes :: [ITermType] -> [ITermType] -> ([ITermType], [ITermType])
diffTypes new [] = (new, [])
diffTypes [] old = ([], old)
diffTypes (x:new) (y:old) = case compare x y of
    EQ -> diffTypes new old
    LT -> let (add,sub) = diffTypes new (y:old) in (x:add, sub)
    GT -> let (add,sub) = diffTypes (x:new) old in (add, y:sub)

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

calcAtom :: IEnv -> Atom -> IType
calcAtom env (Atom l arg _) = case (l, arg) of
    (SLiteral, CInt _)  -> IInt
    (SLiteral, CBool _) -> IInt
    (SVar, x) -> env M.! x
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

newEdge :: from -> to -> EdgeLabel -> R (Edge from to)
newEdge from to label = Edge from to label <$> liftIO (newIORef True)

calcPair :: IEnv -> HFormula -> Node e -> (Value,Value) -> R (IType, Meta 'Pair)
calcPair env fml _node (v1,v2) = do
    (ty1,e1) <- mfix $ \(_,_e1) -> do
        (n1,ty1) <- calcValue env fml _e1 v1 
        e1 <- newEdge _node n1 (EPair True)
        return (ty1,e1)
    (ty2,e2) <- mfix $ \(_ ,_e2) -> do
        (n2,ty2) <- calcValue env fml _e2 v2 
        e2 <- newEdge _node n2 (EPair False)
        return (ty2,e2)
    return (IPair ty1 ty2, MetaPair e1 e2)
calcLambda :: IEnv -> HFormula -> Node e -> (UniqueKey, [TId], Exp) -> R (IType, Meta 'Lambda)
calcLambda env fml _node (key, xs, e) = do
    Just (_, ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxArgTypeTbl ctx) key
    fs <- getFlow key
    (ty_assocs, edges) <- fmap mconcat $ forM fs $ \(thetas, phi) -> do
        let env' = foldr (uncurry M.insert) env (zip xs thetas)
        cond <- fromBFormula ps phi
        fml' <- mkBin SAnd fml cond
        b <- checkSat fml cond
        if b
        then do
            (tys,edge) <- mfix $ \(_, _edge) -> do
                (n, tys) <- calcExp env' fml' _edge e
                edge <- newEdge _node n (ELambda (thetas,phi)) 
                return (tys, edge) 
            return (map ((,,) thetas phi) tys,[edge])
        else return ([],[])
    ref <- liftIO $ newIORef edges
    return (IFun ty_assocs, MetaLambda ref)
    
calcValue :: IEnv -> HFormula -> Edge (Node e) ValueNode -> Value -> R (ValueNode, IType)
calcValue env fml pEdge (Value l arg sty key) = 
    mfix $ \(_node, _ity) -> do
        (ity,meta) <- case (l, arg) of
            (SLiteral,_) -> return (calcAtom env (Atom l arg sty), ())
            (SVar, _)    -> return (calcAtom env (Atom l arg sty), ())
            (SBinary, _) -> return (calcAtom env (Atom l arg sty), ())
            (SUnary, _)  -> return (calcAtom env (Atom l arg sty), ())
            (SPair, (v1, v2)) -> calcPair env fml _node (v1,v2)
            (SLambda, (xs,e)) -> calcLambda env fml _node (key, xs, e)
        itypeRef <- liftIO $ newIORef ity
        let node = Node { typeEnv = env
                        , constraint = fml
                        , refl = NodeValue
                        , term = (l, arg, sty, key)
                        , types = itypeRef
                        , parent = pEdge
                        , edges = meta }
        return (node, ity)

popQuery :: R (Maybe UpdateQuery)
popQuery = undefined

pushQuery :: UpdateQuery -> R ()
pushQuery = undefined

updateQValue :: (Edge (Node e) ValueNode) -> IType -> R ()
updateQValue edge _ = case from edge of
    Node _ _ _ (SLiteral, _, _, _) _ _ _ -> error "impossible"
    Node _ _ _ (SVar, _, _, _) _ _ _     -> error "impossible"
    Node _ _ _ (SBinary, _, _, _) _ _ _  -> error "impossible"
    Node _ _ _ (SUnary, _, _, _) _ _ _   -> error "impossible"
    Node _ _ _ (SLambda, _, _, _) _ _ _  -> error "impossible"
    Node _ _ _ (SLet, _, _, _) _ _ _     -> error "impossible"
    Node _ _ _ (SAssume, _, _, _) _ _ _  -> error "impossible"
    Node _ _ _ (SBranch, _, _, _) _ _ _  -> error "impossible"
    Node _ _ _ (SFail, _, _, _) _ _ _    -> error "impossible"
    Node _ _ _ (SOmega, _, _, _) _ _ _   -> error "impossible"
    Node _ _ _ (SRand, _, _, _) _ _ _    -> error "impossible"
    Node _ _ proxy (SPair, _, _, _) tys_ref pEdge (MetaPair e_fst e_snd) ->  do
        ity1 <- liftIO $ readIORef (types (to e_fst))
        ity2 <- liftIO $ readIORef (types (to e_snd))
        let new_ity = IPair ity1 ity2
        case proxy of
            NodeValue -> do
                ity0 <- liftIO $ readIORef tys_ref
                when (ity0 /= new_ity) $ do
                    liftIO $ writeIORef tys_ref new_ity
                    pushQuery (QValue pEdge new_ity)
            NodeExp -> do
                old_tys@[ITerm ity0 phi] <- liftIO $ readIORef tys_ref
                when (ity0 /= new_ity) $ do
                    let new_tys = [ITerm new_ity phi]
                    liftIO $ writeIORef tys_ref new_tys
                    pushQuery (QExp pEdge new_tys old_tys)
            NodeLExp -> do
                old_tys@[ITerm ity0 phi] <- liftIO $ readIORef tys_ref
                when (ity0 /= new_ity) $ do
                    let new_tys = [ITerm new_ity phi]
                    liftIO $ writeIORef tys_ref new_tys
                    pushQuery (QLExp pEdge new_tys old_tys)
    Node env _ NodeLExp (SApp, (f,_), _, _) tys_ref pEdge (MetaApp edges_vs phi) -> do
        let IFun assoc = env M.! f
        thetas <- forM edges_vs $ \edge -> liftIO $ readIORef (types (to edge))
        let new_tys = [ iota | (thetas', phi', iota) <- assoc,
                               thetas == thetas' && phi == phi' ]
        old_tys <- liftIO $ readIORef tys_ref
        let (add,sub) = diffTypes old_tys new_tys
        -- TODO update flow
        unless (null add && null sub) $ do
            liftIO $ writeIORef tys_ref new_tys
            pushQuery (QLExp pEdge add sub)
    node@(Node env fml NodeExp (SLetRec, (fs,e), _, _) tys_ref pEdge meta) -> do
        edges  <- liftIO $ readIORef (letRChildren meta)
        updated <- liftIO $ newIORef False
        thetas <- forM edges $ \edge -> do
            IFun assoc <- liftIO $ readIORef (types (to edge))
            let ELetRecD f = label edge
                IFun old_assoc = typeEnv (to edge) M.! f
            forM_ assoc $ \(ty_args, phi, iota) -> do
                let hist_key = (f, (ty_args, phi), iota) 
                    hist_val = to edge
                v <- liftIO $ H.lookup (letRHistory meta) hist_key
                case v of
                    Just _ -> return ()
                    Nothing -> liftIO $ do
                        H.insert (letRHistory meta) hist_key hist_val
                        writeIORef updated True
            return $ IFun (merge assoc old_assoc)
        updated <- liftIO $ readIORef updated
        when updated $ do
            let new_env = M.fromList $ zip (map fst fs) thetas
                env' = M.union env new_env
            edges_fs <- forM fs $ \(f, v_f) -> do
                (ty_f, edge_f) <- mfix $ \(_, _edge) -> do
                    (n_f, ty_f) <- calcValue env' fml _edge v_f
                    edge_f <- newEdge node n_f (ELetRecD f)
                    return (ty_f, edge_f)
                pushQuery (QValue edge_f ty_f)
                return edge_f
            (new_tys, edge_e) <- mfix $ \(_, _edge) -> do
                (n_e, tys_e) <- calcExp env' fml _edge e
                edge_e <- newEdge node n_e ENone
                return (tys_e, edge_e)
            -- TODO: destruct old edges
            liftIO $ do
                writeIORef (letRChildren meta) edges_fs
                writeIORef (letRCont meta) edge_e
                writeIORef (letREnv meta) new_env
            old_tys <- liftIO $ readIORef tys_ref
            let (add,sub) = diffTypes old_tys new_tys
            unless (null add && null sub) $ do
                liftIO $ writeIORef tys_ref new_tys
                pushQuery (QExp pEdge add sub)

updateQExp :: Edge (Node e) ExpNode -> [ITermType] -> [ITermType] -> R ()
updateQExp edge add_types sub_types = case from edge of
    Node _ _ _ (SLiteral, _, _, _) _ _ _ -> error "impossible"
    Node _ _ _ (SVar, _, _, _) _ _ _     -> error "impossible"
    Node _ _ _ (SBinary, _, _, _) _ _ _  -> error "impossible"
    Node _ _ _ (SUnary, _, _, _) _ _ _   -> error "impossible"
    Node _ _ _ (SFail, _, _, _) _ _ _    -> error "impossible"
    Node _ _ _ (SOmega, _, _, _) _ _ _   -> error "impossible"
    Node _ _ _ (SRand, _, _, _) _ _ _    -> error "impossible"
    Node _ _ _ (SPair, _, _, _) _ _ _    -> error "impossible"
    Node _ _ _ (SApp, _, _, _) _ _ _    -> error "impossible"
    Node _ _ proxy (SLambda, _, _, _) tys_ref pEdge _ -> do
        let ELambda (thetas,phi) = label edge
        let modify_assoc assoc = 
                merge [ (thetas, phi, iota) | iota <- add_types ] $
                filter (\(thetas', phi', iota') -> 
                    thetas' /= thetas || phi' /= phi || 
                    not (elem iota' sub_types)) assoc
        case proxy of
            NodeValue -> do
                IFun assoc <- liftIO $ readIORef tys_ref
                let new_ity = IFun (modify_assoc assoc)
                liftIO $ writeIORef tys_ref new_ity
                pushQuery (QValue pEdge new_ity)
            NodeExp -> do
                old_tys@[ITerm (IFun assoc) phi'] <- liftIO $ readIORef tys_ref
                let new_tys = [ITerm (IFun (modify_assoc assoc)) phi']
                liftIO $ writeIORef tys_ref new_tys
                pushQuery (QExp pEdge new_tys old_tys)
            NodeLExp -> do
                old_tys@[ITerm (IFun assoc) phi'] <- liftIO $ readIORef tys_ref
                let new_tys = [ITerm (IFun (modify_assoc assoc)) phi']
                liftIO $ writeIORef tys_ref new_tys
                pushQuery (QLExp pEdge new_tys old_tys)
    Node _ _ proxy (SBranch, _, _, _) tys_ref pEdge meta  ->
        let doit :: IORef [ITermType] -> MetaBranch -> R ([ITermType], [ITermType])
            doit tys_ref meta = do
                tys <- liftIO $ readIORef tys_ref
                tySet0 <- liftIO $ readIORef (branchTypeSet meta)
                let (tySet1, add_tys') = foldl' (\(tySet, tys) ty -> 
                        if M.member ty tySet
                        then (M.insertWith (+) ty 1 tySet, tys)
                        else (M.insertWith (+) ty 1 tySet, ty:tys)) (tySet0, []) add_types
                    (tySet2, sub_tys') = foldl' (\(tySet, tys) ty ->
                        case M.lookup ty tySet of
                            Just 1 -> (M.delete ty tySet, ty:tys)
                            Just c -> (M.insert ty (c-1) tySet, tys)
                            Nothing -> (tySet, tys)) (tySet1, []) sub_types
                let tys' = merge (tys \\ sub_tys') (reverse add_tys')
                liftIO $ writeIORef (branchTypeSet meta) tySet2
                liftIO $ writeIORef tys_ref tys'
                return (add_tys', sub_tys')
        in case proxy of
            NodeExp -> do
                (add_tys', sub_tys') <- doit tys_ref meta
                pushQuery (QExp pEdge add_tys' sub_tys')
            NodeLExp -> do
                (add_tys', sub_tys') <- doit tys_ref meta
                pushQuery (QLExp pEdge add_tys' sub_tys')
    Node _ _ _ (SLet, _, _, _) _ _ _     -> error "TODO"
    Node _ _ _ (SAssume, _, _, _) _ _ _  -> error "TODO"
    Node _ _ _ (SLetRec, _, _, _) _ _ _  -> error "TODO"
    

updateQLExp :: Edge (Node e) LExpNode -> [ITermType] -> [ITermType] -> R ()
updateQLExp = undefined
    

updateLoop :: R ()
updateLoop = popQuery >>= \case
    Nothing -> return ()
    Just query -> do
        case query of
            QValue edge ity -> do
                b <- liftIO $ readIORef (alive edge)
                when b $ do
                    updateQValue edge ity
                    updateLoop
            QExp edge add sub -> do
                b <- liftIO $ readIORef (alive edge)
                when b $ do
                    updateQExp edge add sub
                    updateLoop
            QLExp edge add sub -> do
                b <- liftIO $ readIORef (alive edge)
                when b $ do
                    updateQLExp edge add sub
                    updateLoop
                
    

calcExp :: IEnv -> HFormula -> Edge (Node e) ExpNode -> Exp -> R (ExpNode, [ITermType])
calcExp env fml pEdge (Exp l arg sty key) = 
    mfix $ \(_node, _tys) -> do
        let fromValue :: (IType, a) -> R ([ITermType], a)
            fromValue (theta, meta) = do
                Just (_,ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
                phi <- calcCondition fml ps
                return ([ITerm theta phi], meta)
        (itys,meta) <- case (l, arg) of
            (SLiteral,_) -> fromValue $ (calcAtom env (Atom l arg sty), ())
            (SVar, _)    -> fromValue $ (calcAtom env (Atom l arg sty), ())
            (SBinary, _) -> fromValue $ (calcAtom env (Atom l arg sty), ())
            (SUnary, _)  -> fromValue $ (calcAtom env (Atom l arg sty), ())
            (SPair, (v1, v2)) -> fromValue =<< calcPair env fml _node (v1,v2)
            (SLambda, (xs,e)) -> fromValue =<< calcLambda env fml _node (key, xs, e)
            (SLet, (x, e1, e2)) -> do
                (tys1, edge1) <- mfix $ \(_, _edge1) -> do
                    (n1, tys1) <- calcLExp env fml _edge1 e1
                    edge1 <- newEdge _node n1 ENone
                    return (tys1,edge1) 
                Just (_, ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
                let f tys = ( concatMerge (map fst tys)
                            , M.fromListWith (++) [ (iota, [x]) | (tys, x) <- tys, iota <- tys])
                ((tys, tySet), edges) <- fmap ((f *** concat).unzip) $ forM tys1 $ \case
                    IFail -> return (([IFail], Nothing), [])
                    ITerm ity phi -> do
                        let env' = M.insert x ity env
                        cond <- fromBFormula ps phi
                        fml' <- mkBin SAnd fml cond
                        b <- checkSat fml cond
                        if b
                        then do
                            (tys2, edge2) <- mfix $ \(_, _edge2) -> do
                                (n2, tys2) <- calcExp env' fml' _edge2 e2
                                edge2 <- newEdge _node n2 (ELetC (ity,phi))
                                return (tys2, edge2)
                            return ((tys2, Just (ity,phi)), [edge2])
                        else return (([], Just (ity,phi)), [])
                ref <- liftIO $ newIORef edges
                ref_tySet <- liftIO $ newIORef tySet 
                return (tys, MetaLet edge1 ref ref_tySet)
            (SLetRec, (fs, e)) -> do
                let env0 = M.fromList [ (f, IFun []) | (f,_) <- fs ]
                    env' = M.union env env0
                edge_fs <- forM fs $ \(f,v_f) -> do
                    (ty_f, edge_f) <- mfix $ \(_, _edge) -> do
                        (n_f, ty_f) <- calcValue env' fml _edge v_f
                        edge_f <- newEdge _node n_f (ELetRecD f)
                        return (ty_f, edge_f)
                    pushQuery (QValue edge_f ty_f)
                    return edge_f
                (tys, edge_e) <- mfix $ \(_, _edge) -> do
                    (n_e, tys_e) <- calcExp env' fml _edge e
                    edge_e <- newEdge _node n_e ENone
                    return (tys_e, edge_e)
                meta <- liftIO $ do
                    history  <-  H.new
                    ref_fs   <- newIORef edge_fs
                    ref_env  <- newIORef env0
                    ref_cont <- newIORef edge_e
                    return $ MetaLetR ref_fs history ref_env ref_cont
                return (tys, meta)
            (SAssume, (a, e)) -> do
                cond <- toHFormula a 
                b <- checkSat fml cond
                if b
                then do
                    fml' <- mkBin SAnd fml cond
                    (tys, edge) <- mfix $ \(_, _edge) ->  do
                        (n, tys) <- calcExp env fml' _edge e
                        edge <- newEdge _node n ENone
                        return (tys, edge)
                    return (tys, MetaAssume (Just edge))
                else return ([], MetaAssume Nothing)
            (SBranch, (e1,e2)) -> do
                (tys1, edge1) <- mfix $ \(_, _edge1) -> do
                    (n1, tys1) <- calcExp env fml _edge1 e1
                    edge1 <- newEdge _node n1 (EBranch True)
                    return (tys1, edge1)
                (tys2, edge2) <- mfix $ \(_, _edge2) -> do
                    (n2, tys2) <- calcExp env fml _edge2 e2
                    edge2 <- newEdge _node n2 (EBranch False)
                    return (tys2, edge2)
                let tySet = M.fromListWith (+) $ map (\ty -> (ty,1)) (tys1 ++ tys2)
                ref <- liftIO $ newIORef tySet
                return (merge tys1 tys2, MetaBranch edge1 edge2 ref)
            (SFail, _) -> return ([IFail], ())
            (SOmega, _) -> return ([], ())
        itypeRef <- liftIO $ newIORef itys
        let node = Node { typeEnv = env
                        , constraint = fml
                        , refl = NodeExp
                        , term = (l, arg, sty, key)
                        , types = itypeRef
                        , parent = pEdge
                        , edges = meta }
        return (node, itys)

calcLExp :: IEnv -> HFormula -> Edge (Node e) LExpNode -> LExp -> R (LExpNode, [ITermType])
calcLExp env fml pEdge (LExp l arg sty key) =  
    mfix $ \(_node, _tys) -> do
        let fromValue :: (IType, a) -> R ([ITermType], a)
            fromValue (theta, meta) = do
                Just (_,ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
                phi <- calcCondition fml ps
                return ([ITerm theta phi], meta)
        (itys,meta) <- case (l, arg) of
            (SLiteral,_) -> fromValue $ (calcAtom env (Atom l arg sty), ())
            (SVar, _)    -> fromValue $ (calcAtom env (Atom l arg sty), ())
            (SBinary, _) -> fromValue $ (calcAtom env (Atom l arg sty), ())
            (SUnary, _)  -> fromValue $ (calcAtom env (Atom l arg sty), ())
            (SPair, (v1, v2)) -> fromValue =<< calcPair env fml _node (v1,v2)
            (SLambda, (xs,e)) -> fromValue =<< calcLambda env fml _node (key, xs, e)
            (SBranch, (e1,e2)) -> do
                (tys1, edge1) <- mfix $ \(_, _edge1) -> do
                    (n1, tys1) <- calcExp env fml _edge1 e1
                    edge1 <- newEdge _node n1 (EBranch True)
                    return (tys1, edge1)
                (tys2, edge2) <- mfix $ \(_, _edge2) -> do
                    (n2, tys2) <- calcExp env fml _edge2 e2
                    edge2 <- newEdge _node n2 (EBranch False)
                    return (tys2, edge2)
                let tySet = M.fromListWith (+) $ map (\ty -> (ty,1)) (tys1 ++ tys2)
                ref <- liftIO $ newIORef tySet
                return (merge tys1 tys2, MetaBranch edge1 edge2 ref)
            (SFail, _) -> return ([IFail], ())
            (SOmega, _) -> return ([], ())
            (SRand, _) -> return ([ITerm IInt (BConst True)], ())
            (SApp, (f, vs)) -> do
                let IFun assoc = env M.! f
                Just (_, ps) <- ask >>= \ctx -> liftIO (H.lookup (ctxArgTypeTbl ctx) key)
                phi <- calcCondition fml ps
                (thetas,edges) <- fmap unzip $ forM (zip [0..] vs) $ \(i,v) -> 
                    mfix $ \(_, _edge) -> do
                        (n, ity) <- calcValue env fml _edge v
                        edge <- newEdge _node n (EApp i)
                        return (ity, edge)
                -- TODO: update flow
                let tys = [ iota | (thetas', phi', iota) <- assoc,
                                   thetas == thetas' && phi == phi' ]
                return (tys, MetaApp edges phi)
        itypeRef <- liftIO $ newIORef itys
        let node = Node { typeEnv = env
                        , constraint = fml
                        , refl = NodeLExp
                        , term = (l, arg, sty, key)
                        , types = itypeRef
                        , parent = pEdge
                        , edges = meta }
        return (node, itys)
        
