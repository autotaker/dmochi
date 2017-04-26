module Language.DMoCHi.ML.IncSaturation where
import Language.DMoCHi.ML.Syntax.PNormal hiding(mkBin, mkUni, mkVar, mkLiteral)
import Language.DMoCHi.ML.Syntax.HFormula
-- import Control.Monad
import Control.Monad.Fix
--import Control.Arrow ((***),second)
import Control.Monad.Reader
import Data.IORef
import qualified Z3.Monad as Z3
-- import Data.List
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
            , types  :: IORef (SatType e)
            , parent :: Edge (Node e') (Node e)
            , edges :: Meta l e
            } -> Node e

type family SatType e where
    SatType Exp = [ITermType]
    SatType LExp = [ITermType]
    SatType Value = IType

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

type family Meta (l :: Label) e where
   Meta 'Let e = MetaLet e
   Meta 'LetRec e = MetaLetR e
   Meta 'Lambda e = MetaLambda e
   Meta 'App e = MetaApp e
   Meta 'Assume e = MetaAssume e
   Meta 'Pair e = MetaPair e
   Meta 'Branch e = MetaBranch e
   Meta l e = ()

data MetaLet e = 
    MetaLet { letChild :: Edge (Node e) LExpNode
            , letCont  :: HashTable (IType,BFormula) (Edge (Node e) ExpNode)
            }

data MetaLetR e = 
    MetaLetR { letRChildren :: IORef [Edge (Node e) ValueNode]
             , letRHistory :: HashTable (TId, ArgType, ITermType) ValueNode 
             , letREnv  :: IORef IEnv
             , letRCont :: IORef (Edge (Node e) ExpNode) }

data MetaLambda e =
    MetaLambda { lamChildren :: HashTable ArgType (Edge (Node e) ExpNode) }

data MetaApp e = MetaApp { appArg :: [Edge (Node e) ValueNode], appCond :: BFormula }
newtype MetaAssume e = MetaAssume { assumeCont :: Maybe (Edge (Node e) ExpNode) }
data MetaPair e =
    MetaPair { pairFst :: Edge (Node e) ValueNode 
             , pairSnd :: Edge (Node e) ValueNode}
data MetaBranch e =
    MetaBranch { branchFst :: Edge (Node e) ExpNode 
               , branchSnd :: Edge (Node e) ExpNode}

data UpdateQuery where
    QValue :: Edge (Node e) ValueNode -> UpdateQuery
    QExp   :: Edge (Node e) ExpNode   -> UpdateQuery
    QLExp  :: Edge (Node e) LExpNode  -> UpdateQuery

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

mkValueEdge :: IEnv -> HFormula -> Node e -> Value -> EdgeLabel -> R (IType, Edge (Node e) ValueNode)
mkValueEdge env fml from v label = mfix $ \(_, _edge) -> do
    (to, ty) <- calcValue env fml _edge v
    edge <- newEdge from to label
    return (ty, edge)

mkExpEdge :: IEnv -> HFormula -> Node e -> Exp -> EdgeLabel -> R ([ITermType], Edge (Node e) ExpNode)
mkExpEdge env fml from e label = mfix $ \(_, _edge) -> do
    (to, tys) <- calcExp env fml _edge e
    edge <- newEdge from to label
    return (tys, edge)

mkLExpEdge :: IEnv -> HFormula -> Node e -> LExp -> EdgeLabel -> R ([ITermType], Edge (Node e) LExpNode)
mkLExpEdge env fml from e label = mfix $ \(_, _edge) -> do
    (to, tys) <- calcLExp env fml _edge e
    edge <- newEdge from to label
    return (tys, edge)

calcFromValue :: HFormula -> UniqueKey -> IType -> R [ITermType]
calcFromValue fml key theta = do
    Just (_,ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
    phi <- calcCondition fml ps
    return [ITerm theta phi]

calcPair :: IEnv -> HFormula -> Node e -> (Value,Value) -> R (IType, Meta 'Pair e)
calcPair env fml _node (v1,v2) = do
    (ty1,e1) <- mkValueEdge env fml _node v1 (EPair True)
    (ty2,e2) <- mkValueEdge env fml _node v2 (EPair False)
    return (IPair ty1 ty2, MetaPair e1 e2)

recalcPair :: Meta 'Pair e -> R IType
recalcPair (MetaPair n1 n2) = do
    ty1 <- liftIO $ readIORef (types $ to n1)
    ty2 <- liftIO $ readIORef (types $ to n2)
    return $ IPair ty1 ty2
    
calcLambda :: IEnv -> HFormula -> Node e -> UniqueKey -> ([TId], Exp) -> R (IType, Meta 'Lambda e)
calcLambda env fml _node key (xs, e) = do
    Just (_, ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxArgTypeTbl ctx) key
    fs <- getFlow key
    tbl <- liftIO H.new
    ty_assocs <- fmap mconcat $ forM fs $ \(thetas, phi) -> do
        let env' = foldr (uncurry M.insert) env (zip xs thetas)
        cond <- fromBFormula ps phi
        fml' <- mkBin SAnd fml cond
        checkSat fml cond >>= \case
            True -> do
                (tys,edge) <- mkExpEdge env' fml' _node e (ELambda (thetas,phi))
                liftIO $ H.insert tbl (thetas,phi) edge
                return (map ((,,) thetas phi) tys)
            False -> return []
    return (IFun ty_assocs, MetaLambda tbl)

recalcLambda :: IEnv -> HFormula -> Meta 'Lambda e -> Node e -> UniqueKey -> ([TId], Exp) -> R IType
recalcLambda env fml meta node key (xs, e) = do
    Just (_, ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxArgTypeTbl ctx) key
    fs <- getFlow key
    ty_assocs <- fmap mconcat $ forM fs $ \(thetas, phi) ->
        liftIO (H.lookup (lamChildren meta) (thetas,phi)) >>= \case
            Just edge -> do
                tys <- liftIO $ readIORef (types (to edge))
                return $ map ((,,) thetas phi) tys
            Nothing -> do
                cond <- fromBFormula ps phi
                fml' <- mkBin SAnd fml cond
                checkSat fml cond >>= \case
                    False -> return []
                    True -> do
                        let env' = foldr (uncurry M.insert) env (zip xs thetas)
                        (tys,edge) <- mkExpEdge env' fml' node e (ELambda (thetas,phi))
                        liftIO $ H.insert (lamChildren meta) (thetas,phi) edge
                        return $ map ((,,) thetas phi) tys
    return (IFun ty_assocs)
                
calcBranch :: IEnv -> HFormula -> Node e -> (Exp, Exp) -> R ([ITermType] , Meta 'Branch e)
calcBranch env fml _node (e1, e2) = do
    (tys1, edge1) <- mkExpEdge env fml _node e1 (EBranch True)
    (tys2, edge2) <- mkExpEdge env fml _node e2 (EBranch False)
    return (merge tys1 tys2, MetaBranch edge1 edge2)

recalcBranch :: MetaBranch e -> R [ITermType]
recalcBranch (MetaBranch n1 n2) = do
    tys1 <- liftIO $ readIORef (types $ to n1)
    tys2 <- liftIO $ readIORef (types $ to n2)
    return $ merge tys1 tys2

calcLet :: IEnv -> HFormula -> ExpNode -> UniqueKey -> (TId, LExp, Exp) -> R ([ITermType], Meta 'Let Exp)
calcLet env fml _node key (x, e1, e2) = do
    (tys1, edge1) <- mkLExpEdge env fml _node e1 ENone
    Just (_, ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
    tbl <- liftIO $ H.new
    tys <- fmap concatMerge $ forM tys1 $ \case
        IFail -> return [IFail]
        ITerm ity phi -> do
            let env' = M.insert x ity env
            cond <- fromBFormula ps phi
            fml' <- mkBin SAnd fml cond
            checkSat fml cond >>= \case 
                False -> return []
                True -> do 
                    (tys, edge) <- mkExpEdge env' fml' _node e2 (ELetC (ity, phi))
                    liftIO $ H.insert tbl (ity,phi) edge
                    return tys
    return (tys, MetaLet edge1 tbl)

recalcLet :: IEnv -> HFormula -> MetaLet Exp -> ExpNode -> UniqueKey -> (TId, LExp, Exp) -> R [ITermType]
recalcLet env fml meta node key (x, _, e2) = do
    tys1 <- liftIO $ readIORef (types $ to $ letChild meta)
    Just (_, ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
    fmap concatMerge $ forM tys1 $ \case
        IFail -> return [IFail]
        ITerm ity phi -> do
            liftIO (H.lookup (letCont meta) (ity,phi)) >>= \case
                Just edge -> liftIO $ readIORef $ types $ to edge
                Nothing -> do
                    let env' = M.insert x ity env
                    cond <- fromBFormula ps phi
                    fml' <- mkBin SAnd fml cond
                    checkSat fml cond >>= \case
                        False -> return []
                        True -> do
                            (tys, edge) <- mkExpEdge env' fml' node e2 (ELetC (ity, phi))
                            liftIO $ H.insert (letCont meta) (ity,phi) edge
                            return tys

calcLetRec :: IEnv -> HFormula -> ExpNode -> ([(TId, Value)], Exp) -> R ([ITermType], Meta 'LetRec Exp)
calcLetRec env fml _node (fs, e) = do
    let env0 = M.fromList [ (f, IFun []) | (f,_) <- fs ]
        env' = M.union env env0
    edge_fs <- forM fs $ \(f,v_f) -> do
        (_, edge_f) <- mkValueEdge env' fml _node v_f (ELetRecD f)
        pushQuery (QValue edge_f)
        return edge_f
    (tys, edge_e) <- mkExpEdge env' fml _node e ENone
    meta <- liftIO $ MetaLetR <$> newIORef edge_fs
                              <*> H.new
                              <*> newIORef env0
                              <*> newIORef edge_e
    return (tys, meta)

recalcLetRec :: IEnv -> HFormula -> MetaLetR Exp -> ExpNode -> ([(TId,Value)], Exp) -> R [ITermType]
recalcLetRec env fml meta node (fs, e) = do
    env0 <- liftIO $ readIORef $ letREnv meta
    edges <- liftIO $ readIORef $ letRChildren meta
    updated <- liftIO $ newIORef False
    env1 <- fmap M.fromList $ forM edges $ \edge -> do
        let ELetRecD f = label edge
        IFun assocs <- liftIO $ readIORef (types $ to edge)
        forM_ assocs $ \(thetas, phi, iota) -> 
            liftIO $ H.lookup (letRHistory meta) (f, (thetas,phi), iota) >>= \case 
                Just _ -> return ()
                Nothing -> do
                   H.insert (letRHistory meta) (f, (thetas,phi), iota) (to edge)
                   writeIORef updated True
        let IFun assocs' = env0 M.! f
        return (f, IFun (merge assocs assocs'))
    liftIO (readIORef updated) >>= \case
        True -> do
            let env' = M.union env env1
            edge_fs <- forM fs $ \(f, v_f) -> do
                (_, edge_f) <- mkValueEdge env' fml node v_f (ELetRecD f)
                pushQuery (QValue edge_f)
                return edge_f
            liftIO $ writeIORef (letREnv meta) env1
            liftIO $ writeIORef (letRChildren meta) edge_fs
            (tys, edge_e) <- mkExpEdge env' fml node e ENone
            liftIO $ writeIORef (letRCont meta) edge_e
            return tys
        False -> liftIO $ readIORef (letRCont meta) >>= readIORef . types . to

calcAssume :: IEnv -> HFormula -> ExpNode -> (Atom, Exp) -> R ([ITermType], Meta 'Assume Exp)
calcAssume env fml _node (a, e) = do
    cond <- toHFormula a 
    checkSat fml cond >>= \case
        True -> do
            fml' <- mkBin SAnd fml cond
            (tys, edge) <- mkExpEdge env fml' _node e ENone
            return (tys, MetaAssume (Just edge))
        False -> return ([], MetaAssume Nothing)

recalcAssume :: MetaAssume e -> R [ITermType]
recalcAssume meta = case assumeCont meta of
    Just edge -> liftIO $ readIORef (types (to edge))
    Nothing -> return []

calcApp :: IEnv -> HFormula -> LExpNode -> UniqueKey -> (TId, [Value]) -> R ([ITermType], Meta 'App LExp)
calcApp env fml _node key (f, vs) = do
    let IFun assoc = env M.! f
    Just (_, ps) <- ask >>= \ctx -> liftIO (H.lookup (ctxArgTypeTbl ctx) key)
    phi <- calcCondition fml ps
    (thetas,edges) <- fmap unzip $ forM (zip [0..] vs) $ \(i,v) -> 
        mkValueEdge env fml _node v (EApp i)
    -- TODO: update flow
    let tys = [ iota | (thetas', phi', iota) <- assoc,
                       thetas == thetas' && phi == phi' ]
    return (tys, MetaApp edges phi)

recalcApp :: IEnv -> MetaApp LExp -> (TId, [Value]) -> R [ITermType]
recalcApp env (MetaApp edges phi) (f,_) = do
    thetas <- forM edges $ liftIO . readIORef . types . to
    let IFun assoc = env M.! f
    let tys = [ iota | (thetas', phi', iota) <- assoc,
                       thetas == thetas' && phi == phi' ]
    return tys
    
calcValue :: IEnv -> HFormula -> Edge (Node e) ValueNode -> Value -> R (ValueNode, IType)
calcValue env fml pEdge (Value l arg sty key) = 
    mfix $ \(_node, _ity) -> do
        (ity,meta) <- case l of
            SLiteral -> return (calcAtom env (Atom l arg sty), ())
            SVar    -> return (calcAtom env (Atom l arg sty), ())
            SBinary -> return (calcAtom env (Atom l arg sty), ())
            SUnary  -> return (calcAtom env (Atom l arg sty), ())
            SPair   -> calcPair env fml _node arg
            SLambda -> calcLambda env fml _node key arg
        itypeRef <- liftIO $ newIORef ity
        let node = Node { typeEnv = env
                        , constraint = fml
                        , refl = NodeValue
                        , term = (l, arg, sty, key)
                        , types = itypeRef
                        , parent = pEdge
                        , edges = meta }
        return (node, ity)

calcExp :: IEnv -> HFormula -> Edge (Node e) ExpNode -> Exp -> R (ExpNode, [ITermType])
calcExp env fml pEdge (Exp l arg sty key) = 
    let fromValue :: (IType, a) -> R ([ITermType], a)
        fromValue (ity, meta) = (\tys -> (tys,meta)) <$> calcFromValue fml key ity
    in mfix $ \(_node, _tys) -> do
        (itys,meta) <- case l of
            SLiteral -> fromValue (calcAtom env (Atom l arg sty), ())
            SVar     -> fromValue (calcAtom env (Atom l arg sty), ())
            SBinary  -> fromValue (calcAtom env (Atom l arg sty), ())
            SUnary   -> fromValue (calcAtom env (Atom l arg sty), ())
            SPair    -> fromValue =<< calcPair env fml _node arg
            SLambda  -> fromValue =<< calcLambda env fml _node key arg
            SLet     -> calcLet env fml _node key arg
            SLetRec  -> calcLetRec env fml _node arg
            SAssume  -> calcAssume env fml _node arg
            SBranch  -> calcBranch env fml _node arg
            SFail    -> return ([IFail], ())
            SOmega   -> return ([], ())
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
    let fromValue :: (IType, a) -> R ([ITermType], a)
        fromValue (ity, meta) = (\tys -> (tys,meta)) <$> calcFromValue fml key ity
    in mfix $ \(_node, _tys) -> do
        (itys,meta) <- case l of
            SLiteral -> fromValue (calcAtom env (Atom l arg sty), ())
            SVar     -> fromValue (calcAtom env (Atom l arg sty), ())
            SBinary  -> fromValue (calcAtom env (Atom l arg sty), ())
            SUnary   -> fromValue (calcAtom env (Atom l arg sty), ())
            SPair    -> fromValue =<< calcPair env fml _node arg
            SLambda  -> fromValue =<< calcLambda env fml _node key arg
            SBranch  -> calcBranch env fml _node arg
            SFail    -> return ([IFail], ())
            SOmega   -> return ([], ())
            SRand    -> return ([ITerm IInt (BConst True)], ())
            SApp     -> calcApp env fml _node key arg
        itypeRef <- liftIO $ newIORef itys
        let node = Node { typeEnv = env
                        , constraint = fml
                        , refl = NodeLExp
                        , term = (l, arg, sty, key)
                        , types = itypeRef
                        , parent = pEdge
                        , edges = meta }
        return (node, itys)

popQuery :: R (Maybe UpdateQuery)
popQuery = undefined

pushQuery :: UpdateQuery -> R ()
pushQuery = undefined

recalcValue :: ValueNode -> R (IType, Bool)
recalcValue node@(Node { typeEnv = env
                       , constraint = fml
                       , term = (l, arg, sty, key)
                       , types = ty_ref
                       , edges = meta }) = do
    new_ity <- case l of
        SLiteral -> return (calcAtom env (Atom l arg sty))
        SVar     -> return (calcAtom env (Atom l arg sty))
        SBinary  -> return (calcAtom env (Atom l arg sty))
        SUnary   -> return (calcAtom env (Atom l arg sty))
        SPair    -> recalcPair meta
        SLambda  -> recalcLambda env fml meta node key arg
    old_ity <- liftIO $ readIORef ty_ref
    liftIO $ writeIORef ty_ref new_ity
    return (new_ity, new_ity /= old_ity)

recalcExp :: ExpNode -> R ([ITermType], Bool)
recalcExp node@(Node { typeEnv = env
                     , constraint = fml
                     , term = (l, arg, sty, key)
                     , types = tys_ref
                     , edges = meta}) = do
    new_itys <- case l of
        SLiteral -> calcFromValue fml key (calcAtom env (Atom l arg sty))
        SVar     -> calcFromValue fml key (calcAtom env (Atom l arg sty))
        SBinary  -> calcFromValue fml key (calcAtom env (Atom l arg sty))
        SUnary   -> calcFromValue fml key (calcAtom env (Atom l arg sty))
        SPair    -> recalcPair meta >>= calcFromValue fml key
        SLambda  -> recalcLambda env fml meta node key arg >>= calcFromValue fml key
        SLet     -> recalcLet env fml meta node key arg
        SLetRec  -> recalcLetRec env fml meta node arg
        SBranch  -> recalcBranch meta
        SAssume  -> recalcAssume meta
        SFail    -> return [IFail]
        SOmega   -> return []
    old_itys <- liftIO $ readIORef tys_ref
    liftIO $ writeIORef tys_ref new_itys
    return (new_itys, new_itys /= old_itys)

recalcLExp :: LExpNode -> R ([ITermType], Bool)
recalcLExp node@(Node { typeEnv = env
                     , constraint = fml
                     , term = (l, arg, sty, key)
                     , types = tys_ref
                     , edges = meta}) = do
    new_itys <- case l of
        SLiteral -> calcFromValue fml key (calcAtom env (Atom l arg sty))
        SVar     -> calcFromValue fml key (calcAtom env (Atom l arg sty))
        SBinary  -> calcFromValue fml key (calcAtom env (Atom l arg sty))
        SUnary   -> calcFromValue fml key (calcAtom env (Atom l arg sty))
        SPair    -> recalcPair meta >>= calcFromValue fml key
        SLambda  -> recalcLambda env fml meta node key arg >>= calcFromValue fml key
        SBranch  -> recalcBranch meta
        SApp     -> recalcApp env meta arg
        SFail    -> return [IFail]
        SOmega   -> return []
        SRand    -> return [ITerm IInt (BConst True)]
    old_itys <- liftIO $ readIORef tys_ref
    liftIO $ writeIORef tys_ref new_itys
    return (new_itys, new_itys /= old_itys)

{-
updateLoop :: R ()
updateLoop = popQuery >>= \case
    Nothing -> return ()
    Just query -> do
        case query of
            QValue edge -> do
                b <- liftIO $ readIORef (alive edge)
                when b $ do
                    updateQValue edge
                    updateLoop
            QExp edge -> do
                b <- liftIO $ readIORef (alive edge)
                when b $ do
                    updateQExp edge
                    updateLoop
            QLExp edge -> do
                b <- liftIO $ readIORef (alive edge)
                when b $ do
                    updateQLExp edge
                    updateLoop
                    -}
