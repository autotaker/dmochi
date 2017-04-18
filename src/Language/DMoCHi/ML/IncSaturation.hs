module Language.DMoCHi.ML.IncSaturation where
import Language.DMoCHi.ML.Syntax.PNormal hiding(mkBin, mkUni, mkVar, mkLiteral)
import Language.DMoCHi.ML.Syntax.HFormula
-- import Control.Monad
import Control.Monad.Fix
import Control.Arrow ((***))
import Control.Monad.Reader
import Data.IORef
import qualified Z3.Monad as Z3
--import qualified Z3.Base as Z3Base
import Language.DMoCHi.Common.Id
import           Data.Time
import qualified Data.Map.Strict as M
import qualified Data.HashTable.IO as H
import qualified Language.DMoCHi.ML.SMT as SMT
type IEnv = M.Map TId IType
type CEnv = ()
type ArgType = ([IType],BFormula)

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
               | ELetRecC TId
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
            , letCont  :: IORef [Edge ExpNode ExpNode] }

data MetaLetR = 
    MetaLetR { letRChildren :: IORef [Edge ExpNode ValueNode]
             , letRHistory :: HashTable (TId, ArgType, ITermType) ExpNode 
             , letREnv  :: IORef IEnv
             , letRCont :: IORef (Edge ExpNode ExpNode) }

data MetaLambda where
    MetaLambda :: { lamChildren :: IORef [Edge e ExpNode] } -> MetaLambda

newtype MetaApp = MetaApp { appArg :: [Edge LExpNode ValueNode] }
newtype MetaAssume = MetaAssume { assumeCont :: Maybe (Edge ExpNode ExpNode) }
data MetaPair where
    MetaPair :: { pairFst :: Edge e ValueNode 
                , pairSnd :: Edge e ValueNode} -> MetaPair
data MetaBranch where
    MetaBranch :: { branchFst :: Edge e ExpNode 
                  , branchSnd :: Edge e ExpNode} -> MetaBranch

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
                (tys, edges) <- fmap ((concatMerge *** concat).unzip) $ forM tys1 $ \case
                    IFail -> return ([IFail], [])
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
                            return (tys2, [edge2])
                        else return ([], [])
                ref <- liftIO$ newIORef edges
                return (tys, MetaLet edge1 ref)
            -- TODO ADD LETREC CASE
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
                return (merge tys1 tys2, MetaBranch edge1 edge2)
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
                return (merge tys1 tys2, MetaBranch edge1 edge2)
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
                return (tys, MetaApp edges)
        itypeRef <- liftIO $ newIORef itys
        let node = Node { typeEnv = env
                        , constraint = fml
                        , refl = NodeLExp
                        , term = (l, arg, sty, key)
                        , types = itypeRef
                        , parent = pEdge
                        , edges = meta }
        return (node, itys)
        
