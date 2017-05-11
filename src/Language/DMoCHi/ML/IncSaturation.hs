{-# LANGUAGE DeriveGeneric, GeneralizedNewtypeDeriving, MultiParamTypeClasses, UndecidableInstances #-}
module Language.DMoCHi.ML.IncSaturation where
import           Language.DMoCHi.ML.Syntax.PNormal hiding(mkBin, mkUni, mkVar, mkLiteral)
import           Language.DMoCHi.ML.Syntax.HFormula
import           Language.DMoCHi.ML.Syntax.PType hiding(ArgType)
import           Language.DMoCHi.Common.Id
import           Language.DMoCHi.ML.Flow
import qualified Language.DMoCHi.ML.Syntax.PNormal as PNormal

-- import Control.Monad
import           GHC.Generics (Generic)
import           Data.Kind(Constraint)
import           Control.Monad.Fix
--import Control.Arrow ((***),second)
import           Control.Monad.Reader
import           Control.Monad.Writer hiding((<>))
import           Control.Monad.State.Strict
import qualified Z3.Monad as Z3
import qualified Z3.Base as Z3Base
-- import Data.List
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
import           Debug.Trace

data Context = Context { ctxFlowTbl :: HashTable UniqueKey (S.Set ([IType], BFormula))
                       , ctxFlowReg :: HashTable UniqueKey [SomeNode]
                       , ctxTypeMap :: TypeMap
                       , ctxFlowMap :: FlowMap
                       , ctxRtnTypeTbl :: HashTable UniqueKey (PType, [HFormula]) 
                       , ctxArgTypeTbl  :: HashTable UniqueKey ([PType], [HFormula]) 
                       , ctxHFormulaTbl :: HFormulaTbl
                       , ctxHFormulaSize :: IORef Int
                       , ctxCheckSatCache :: HashTable (Int, Int) Bool
                       , ctxUpdated :: IORef Bool
                       , ctxSMTCount :: IORef Int
                       , ctxSMTCountHit :: IORef Int
                       , ctxMode  :: IORef TypingMode
                       , ctxTimer :: HashTable MeasureKey NominalDiffTime
                       , ctxSMTSolver :: Z3.Solver
                       , ctxSMTContext :: Z3.Context }

data TypingMode = Saturation 
                | Extraction
          deriving(Show,Ord,Eq)

data MeasureKey = CheckSat | CalcCondition | Total | MSaturation | MExtraction
    deriving (Eq, Ord, Show, Generic)

instance Hashable MeasureKey 

newtype R a = R { unR :: ReaderT Context (StateT (Queue UpdateQuery) IO) a }
    deriving (Monad, Applicative, Functor, MonadFix, MonadIO)

instance MonadReader Context R where
    ask = R ask
    local f a = R (local f $ unR a)

instance MonadState (Queue UpdateQuery) R where
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

type PEnv = M.Map TId PType
type IEnv = M.Map TId IType

(!) :: (Ord k, Show k) => M.Map k v -> k -> v
(!) f a = case M.lookup a f of
    Just v -> v
    Nothing -> error $ "no assoc found for key: " ++ show a

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

data Node e where
    Node :: (NonRoot e, Eq (SatType e)) => 
            { typeEnv    :: IEnv
            , constraint :: HFormula
            , refl   :: NodeProxy e
            , types  :: IORef (SatType e)
            , parent :: Edge (Node e') (Node e)
            , recalcator :: R (SatType e)
            , extractor  :: Extractor e
            , term   :: e
            } -> Node e
    RootNode :: { main :: Node Exp } -> Node Root

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

data Root 

data NodeProxy e where
    NodeExp   :: NodeProxy Exp
    NodeLExp  :: NodeProxy LExp
    NodeValue :: NodeProxy Value

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

data UpdateQuery where
    QEdge :: Edge (Node e) (Node e') -> UpdateQuery
    QFlow :: NonRoot e => Node e -> UpdateQuery

getFlow :: UniqueKey -> R [([IType], BFormula)]
getFlow i = do
    tbl <- ctxFlowTbl <$> ask
    l <- liftIO (H.lookup tbl i) >>= \case
        Just v -> return (S.toList v)
        Nothing -> return []
    liftIO $ print ("getFlow", i, l)
    return l

addFlow :: UniqueKey -> ([IType], BFormula) -> R ()
addFlow i v = do
    tbl <- ctxFlowTbl <$> ask
    reg <- ctxFlowReg <$> ask
    liftIO (H.lookup tbl i) >>= \case
        Just vs 
            | S.member v vs -> return ()
            | otherwise -> do
                let vs' = S.insert v vs
                liftIO (H.insert tbl i $! vs')
                liftIO (H.lookup reg i) >>= \case
                    Nothing -> return ()
                    Just nodes ->
                        forM_ nodes $ ((\(SomeNode node) -> pushQuery (QFlow node)) :: SomeNode -> R ())
        Nothing -> do
            let vs' = S.singleton v
            liftIO (H.insert tbl i $! vs')
            liftIO (H.lookup reg i) >>= \case
                Nothing -> return ()
                Just nodes ->
                    forM_ nodes $ ((\(SomeNode node) -> pushQuery (QFlow node)) :: SomeNode -> R ())
    liftIO $ print ("addFlow", i, v)

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


newEdge :: from -> to -> EdgeLabel -> R (Edge from to)
newEdge from to label = Edge from to label <$> liftIO (newIORef True)

mkValueEdge :: IEnv -> HFormula -> Node e -> Value -> EdgeLabel -> R (IType, Edge (Node e) ValueNode)
mkValueEdge env fml from v label = mfix $ \ ~(_, _edge) -> do
    (to, ty) <- calcValue env fml _edge v
    edge <- newEdge from to label
    return (ty, edge)

mkExpEdge :: IEnv -> HFormula -> Node e -> Exp -> EdgeLabel -> R ([ITermType], Edge (Node e) ExpNode)
mkExpEdge env fml from e label = mfix $ \ ~(_, _edge) -> do
    (to, tys) <- calcExp env fml _edge e
    edge <- newEdge from to label
    return (tys, edge)

mkLExpEdge :: IEnv -> HFormula -> Node e -> LExp -> EdgeLabel -> R ([ITermType], Edge (Node e) LExpNode)
mkLExpEdge env fml from e label = mfix $ \ ~(_, _edge) -> do
    (to, tys) <- calcLExp env fml _edge e
    edge <- newEdge from to label
    return (tys, edge)

calcFromValue :: HFormula -> UniqueKey -> (IType, R IType, ValueExtractor) 
                 -> R ([ITermType], R [ITermType], TermExtractor)
calcFromValue fml key (theta, recalc, extract) = do
    Just (_,ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
    phi <- calcCondition fml ps
    let recalc' = (\theta -> [ITerm theta phi]) <$> recalc
        extract' env (ITerm _ phi') 
            | phi == phi' = return $ Just (extract env)
            | otherwise = error "extract@calcFromValue: condition mismatch"
        extract' _ _ = error "values never fail"
    return ([ITerm theta phi], recalc', extract')

calcPair :: IEnv -> HFormula -> Node e -> (Value,Value) -> R (IType, R IType, ValueExtractor)
calcPair env fml _node (v1,v2) = do
    (ty1,e1) <- mkValueEdge env fml _node v1 (EPair True)
    (ty2,e2) <- mkValueEdge env fml _node v2 (EPair False)
    let recalc = do
            ty1 <- liftIO $ readIORef $ types $ to $ e1
            ty2 <- liftIO $ readIORef $ types $ to $ e2
            return $ IPair ty1 ty2
        extract env = CPair (extractor (to e1) env) (extractor (to e2) env)
    return (IPair ty1 ty2, recalc, extract)
    
calcLambda :: NonRoot e => IEnv -> HFormula -> Node e -> UniqueKey -> ([TId], Exp) -> R (IType, R IType, ValueExtractor)
calcLambda env fml _node key (xs, e) = do
    Just (_, ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxArgTypeTbl ctx) key
    tbl <- liftIO H.new
    reg <- ctxFlowReg <$> ask
    liftIO $ print ("register" :: String,key)
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
                                (tys,edge) <- mkExpEdge env' fml' _node e (ELambda (thetas,phi))
                                liftIO $ H.insert tbl (thetas,phi) (to edge)
                                return $ map ((,,) thetas phi) tys
            return $ IFun ty_assocs
        extract env = CCls env xs tbl
    ty <- recalc 
    return (ty, recalc, extract)
                
calcBranch :: IEnv -> HFormula -> Node e -> (Exp, Exp) -> R ([ITermType] , R [ITermType], TermExtractor)
calcBranch env fml _node (e1, e2) = do
    (tys1, edge1) <- mkExpEdge env fml _node e1 (EBranch True)
    (tys2, edge2) <- mkExpEdge env fml _node e2 (EBranch False)
    let recalc = do
            tys1 <- liftIO $ readIORef $ types $ to $ edge1
            tys2 <- liftIO $ readIORef $ types $ to $ edge2
            return $ merge tys1 tys2
        extract cenv iota = do
            tys1 <- liftIO $ readIORef $ types $ to $ edge1
            if any (flip subTermTypeOf iota) tys1
            then tell [True] >> extractor (to edge1) cenv iota
            else tell [False] >> extractor (to edge2) cenv iota
    return (merge tys1 tys2, recalc, extract)

calcLet :: IEnv -> HFormula -> ExpNode -> UniqueKey -> (TId, LExp, Exp) -> R ([ITermType], R [ITermType], TermExtractor)
calcLet env fml _node key (x, e1@(LExp l1 arg1 sty1 _), e2) = 
    (case l1 of
        SLiteral -> atomCase (Atom l1 arg1 sty1)
        SVar     -> atomCase (Atom l1 arg1 sty1)
        SUnary   -> atomCase (Atom l1 arg1 sty1)
        SBinary  -> atomCase (Atom l1 arg1 sty1)
        SRand    -> do
            let env' = M.insert x IInt env
            (tys,edge2) <- mkExpEdge env' fml _node e2 ENone
            let recalc :: R [ITermType]
                recalc = liftIO $ readIORef $ types $ to $ edge2
                extract cenv iota = extractor (to edge2) cenv' iota 
                    where cenv' = M.insert x CBase cenv
            return (tys,  recalc, extract)
        _        -> genericCase)
    where 
        atomCase :: Atom -> R ([ITermType], R [ITermType], TermExtractor)
        atomCase atom = do
            vx <- mkVar x
            fml' <- toHFormula atom >>= mkBin SEq vx >>= mkBin SAnd fml
            let ity = calcAtom env atom 
                env' = M.insert x ity env
            (tys,edge2) <- mkExpEdge env' fml' _node e2 ENone
            let recalc :: R [ITermType]
                recalc = liftIO $ readIORef $ types $ to $ edge2
                extract cenv iota = extractor (to edge2) cenv' iota 
                    where cenv' = M.insert x (evalAtom cenv atom) cenv
            return (tys,  recalc, extract)
        genericCase = do
            Just (_, ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
            tbl <- liftIO H.new :: R (HashTable (IType, BFormula) ExpNode)
            let genericCalc :: [ITermType] -> R [ITermType]
                genericCalc tys1 = 
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
                                            (tys, edge) <- mkExpEdge env' fml' _node e2 (ELetC (ity, phi))
                                            liftIO $ H.insert tbl (ity,phi) (to edge)
                                            return tys
            (tys1, edge1) <- mkLExpEdge env fml _node e1 ENone
            tys <- genericCalc tys1
            let recalc = (liftIO $ readIORef $ types $ to $ edge1) >>= genericCalc
                extract, extractCont :: TermExtractor
                extract cenv IFail = do
                    tys1 <- liftIO $ readIORef $ types $ to edge1
                    if IFail `elem` tys1
                    then extractor (to edge1) cenv IFail
                    else extractCont cenv IFail
                extract cenv iota = extractCont cenv iota
                extractCont cenv iota = go =<< (liftIO $ readIORef $ types $ to edge1)
                    where
                    go (IFail: tys1) = go tys1
                    go (ITerm ity phi: tys1) = do
                        Just node2 <- liftIO (H.lookup tbl (ity, phi))
                        tys2 <- liftIO $ readIORef $ types node2
                        if any (flip subTermTypeOf iota) tys2
                        then do
                            Just cv1 <- extractor (to edge1) cenv (ITerm ity phi)
                            let cenv' = M.insert x cv1 cenv
                            extractor node2 cenv' iota
                        else go tys1
                    go [] = error "unexpected pattern"
            return (tys, recalc, extract)

calcLetRec :: IEnv -> HFormula -> ExpNode -> ([(TId, Value)], Exp) -> R ([ITermType], R [ITermType],TermExtractor)
calcLetRec env fml _node (fs, e) = do
    let env0 = M.fromList [ (f, IFun []) | (f,_) <- fs ]
        env' = M.union env env0
    edge_fs <- forM fs $ \(f,v_f) -> do
        (_, edge_f) <- mkValueEdge env' fml _node v_f (ELetRecD f)
        pushQuery (QEdge edge_f)
        return edge_f

    (tys, edge_e) <- mkExpEdge env' fml _node e ENone
    {- letRChildren :: IORef [Edge (Node e) ValueNode]
     - letRHistory :: HashTable (TId, ArgType, ITermType) ValueNode 
     - letREnv  :: IORef IEnv
     - letRCont :: IORef (Edge (Node e) ExpNode)
     -}
    letRChildren <- liftIO (newIORef edge_fs)
    letREnv      <- liftIO (newIORef env0)
    letRCont     <- liftIO (newIORef edge_e)
    letRHistory  <- liftIO H.new
    let recalc = do
            env0  <- liftIO $ readIORef letREnv
            edges <- liftIO $ readIORef letRChildren
            updated <- liftIO $ newIORef False
            env1 <- fmap M.fromList $ forM edges $ \edge -> do
                let ELetRecD f = label edge
                IFun assocs <- liftIO $ readIORef (types $ to edge)
                forM_ assocs $ \(thetas, phi, iota) -> 
                    liftIO $ H.lookup letRHistory (f, (thetas,phi), iota) >>= \case 
                        Just _ -> return ()
                        Nothing -> do
                           H.insert letRHistory (f, (thetas,phi), iota) (to edge)
                           writeIORef updated True
                let IFun assocs' = env0 ! f
                return (f, IFun (merge assocs assocs'))
            liftIO (readIORef updated) >>= \case
                True -> do
                    let env' = M.union env env1
                    edge_fs <- forM fs $ \(f, v_f) -> do
                        (_, edge_f) <- mkValueEdge env' fml _node v_f (ELetRecD f)
                        pushQuery (QEdge edge_f)
                        return edge_f
                    liftIO $ writeIORef letREnv env1
                    liftIO $ writeIORef letRChildren edge_fs
                    (tys, edge_e) <- mkExpEdge env' fml _node e ENone
                    liftIO $ writeIORef letRCont edge_e
                    return tys
                False -> liftIO $ readIORef letRCont >>= readIORef . types . to
        extract cenv iota = do
            let cenv' = foldr (uncurry M.insert) cenv [ (f, CRec cenv' f letRHistory) | (f,_) <- fs ]
            edge_e <- liftIO $ readIORef letRCont
            extractor (to edge_e) cenv' iota
    return (tys, recalc,extract)

calcAssume :: IEnv -> HFormula -> ExpNode -> (Atom, Exp) -> R ([ITermType], R [ITermType], TermExtractor)
calcAssume env fml _node (a, e) = do
    cond <- toHFormula a 
    checkSat fml cond >>= \case
        True -> do
            fml' <- mkBin SAnd fml cond
            (tys, edge) <- mkExpEdge env fml' _node e ENone
            let recalc = liftIO $ readIORef $ types $ to edge
                extract = extractor (to edge)
            return (tys, recalc, extract)
        False -> 
            let extract :: TermExtractor
                extract _ _ = error "assume(false) never returns values" in
            return ([], return [], extract)

calcApp :: IEnv -> HFormula -> LExpNode -> UniqueKey -> (TId, [Value]) -> R ([ITermType], R [ITermType], TermExtractor)
calcApp env fml _node key (f, vs) = do
    let IFun assoc = env ! f
    Just (_, ps) <- ask >>= \ctx -> liftIO (H.lookup (ctxArgTypeTbl ctx) key)
    phi <- calcCondition fml ps
    (thetas,edges) <- fmap unzip $ forM (zip [0..] vs) $ \(i,v) -> 
        mkValueEdge env fml _node v (EApp i)

    flowMap <- ctxFlowMap <$> ask
    forM_ (flowMap ! f) $ \ident -> addFlow ident (thetas,phi)
    
    let appType thetas = 
            [ iota | (thetas', phi', iota) <- assoc,
                     thetas == thetas' && phi == phi' ]
        recalc = do
            thetas <- forM edges $ liftIO . readIORef . types . to
            forM_ (flowMap ! f) $ \ident -> addFlow ident (thetas,phi)
            return $ appType thetas
        extract cenv iota = do
            let cvs = map (\edge -> extractor (to edge) cenv) edges
            thetas <- forM edges $ liftIO . readIORef . types . to
            let closureCase (CCls cenv_f xs tbl) = do
                    -- TODO: allow subtyping
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
                    -- TODO: allow subtyping
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
    return (appType thetas, recalc, extract)

calcValue :: IEnv -> HFormula -> Edge (Node e) ValueNode -> Value -> R (ValueNode, IType)
calcValue env fml pEdge value@(Value l arg sty key) = 
    let fromAtom :: Atom -> (IType, R IType, ValueExtractor)
        fromAtom atom = (ity, return ity, extract)
            where ity = calcAtom env atom
                  extract cenv = evalAtom cenv atom
    in mfix $ \ ~(_node, _ity) -> do
        (ity,recalc, extract) <- case l of
            SLiteral -> return $ fromAtom (Atom l arg sty)
            SVar    -> return $ fromAtom (Atom l arg sty)
            SBinary -> return $ fromAtom (Atom l arg sty)
            SUnary  -> return $ fromAtom (Atom l arg sty)
            SPair   -> calcPair env fml _node arg
            SLambda -> calcLambda env fml _node key arg
        itypeRef <- liftIO $ newIORef ity
        let node = Node { typeEnv = env
                        , constraint = fml
                        , refl = NodeValue
                        , term = value
                        , types = itypeRef
                        , parent = pEdge
                        , recalcator = recalc
                        , extractor  = extract }
        liftIO $ putStrLn "created"
        liftIO $ printNode node
        return (node, ity)

calcExp :: IEnv -> HFormula -> Edge (Node e) ExpNode -> Exp -> R (ExpNode, [ITermType])
calcExp env fml pEdge exp@(Exp l arg sty key) = 
    let fromValue :: (IType, R IType, ValueExtractor) -> R ([ITermType], R [ITermType], TermExtractor)
        fromValue = calcFromValue fml key
        fromAtom atom = do
            let ity = calcAtom env atom
            calcFromValue fml key (ity, return ity, flip evalAtom atom)
    in mfix $ \ ~(_node, _tys) -> do
        (itys,recalc, extract) <- case l of
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
                in return ([IFail], return [IFail], extract)
            SOmega   -> 
                let extract _ _ = error "extract@SOmega_calcExp: omega never returns value nor fails"
                in return ([], return [], extract)
        let extract' cenv iota = do
                liftIO $ do
                    putStrLn $ "extracting: " ++ show (pPrint iota)
                    putStrLn $ "    cenv: " ++ show (M.keys cenv)
                    printNode _node
                extract cenv iota
        itypeRef <- liftIO $ newIORef itys
        let node = Node { typeEnv = env
                        , constraint = fml
                        , refl = NodeExp
                        , term = exp
                        , types = itypeRef
                        , parent = pEdge
                        , recalcator = recalc
                        , extractor = extract' }
        liftIO $ putStrLn "created"
        liftIO $ printNode node
        return (node, itys)

calcLExp :: IEnv -> HFormula -> Edge (Node e) LExpNode -> LExp -> R (LExpNode, [ITermType])
calcLExp env fml pEdge lexp@(LExp l arg sty key) =  
    let fromValue :: (IType, R IType, ValueExtractor) -> R ([ITermType], R [ITermType], TermExtractor)
        fromValue = calcFromValue fml key
        fromAtom atom = do
            let ity = calcAtom env atom
            calcFromValue fml key (ity, return ity, flip evalAtom atom)
    in mfix $ \ ~(_node, _tys) -> do
        (itys,recalc, extract) <- case l of
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
                in return ([IFail], return [IFail], extract)
            SOmega   -> 
                let extract _ _ = error "extract@SOmega_calcExp: omega never returns value nor fails"
                in return ([], return [], extract)
            SRand    -> 
                let extract _ _ = error "extract@SRand_calcExp: should never be called" in
                return ([ITerm IInt (BConst True)], return [ITerm IInt (BConst True)], extract)
        itypeRef <- liftIO $ newIORef itys
        let node = Node { typeEnv = env
                        , constraint = fml
                        , refl = NodeLExp
                        , term = lexp
                        , types = itypeRef
                        , parent = pEdge
                        , recalcator = recalc 
                        , extractor = extract}
        liftIO $ putStrLn "created"
        liftIO $ printNode node
        return (node, itys)

genericRecalc :: NonRoot e => Node e -> (SatType e -> SatType e -> R b) -> R b
genericRecalc node cont = do
    new_ity <- recalcator node
    old_ity <- liftIO $ readIORef (types node) 
    liftIO $ writeIORef (types node) new_ity
    liftIO $ do
        putStrLn "recalculated"
        printNode node
    cont new_ity old_ity
    
recalcValue :: ValueNode -> R (IType, Bool)
recalcValue node = genericRecalc node (\new_ity old_ity -> return (new_ity, new_ity /= old_ity))

recalcExp :: ExpNode -> R ([ITermType], Bool)
recalcExp node = genericRecalc node (\new_ity old_ity -> return (new_ity, new_ity /= old_ity))

recalcLExp :: LExpNode -> R ([ITermType], Bool)
recalcLExp node = genericRecalc node (\new_ity old_ity -> return (new_ity, new_ity /= old_ity))

popQuery :: R (Maybe UpdateQuery)
popQuery = state $ \s -> case popQueue s of
                Nothing -> (Nothing, s)
                Just (a,s') -> (Just a, s')

pushQuery :: UpdateQuery -> R ()
pushQuery = modify' . pushQueue

printNode :: Node e -> IO ()
printNode (RootNode _) = putStrLn "ROOT"
printNode (Node { typeEnv = env
                , constraint = fml
                , refl = proxy
                , term = e
                , types = tys_ref }) = 
    let cont :: Doc -> Doc -> IO ()
        cont doc_term doc_ity = print $ text "Node:" $+$ nest 4 doc
            where doc = text "env: " <+> (nest 4 $
                        brackets $ vcat $ [ pPrint (name f) <+> text ":" <+> pPrint ity | (f,ity) <- M.assocs env ])
                    $+$ text "cond: " <+> (pPrint fml)
                    $+$ text "term: " <+> (text (takeWhile (/='\n') $ show doc_term))
                    $+$ text "type:" <+> doc_ity
    in case proxy of
        NodeExp  -> do
            tys <- readIORef tys_ref
            cont (pPrint e) (pPrint tys)
        NodeLExp -> do
            tys <- readIORef tys_ref
            cont (pPrint e) (pPrint tys)
        NodeValue -> do
            tys <- readIORef tys_ref
            cont (pPrint e) (pPrint tys)


updateLoop :: R ()
updateLoop = popQuery >>= \case
    Nothing -> return ()
    Just query -> do
        case query of
            QEdge edge -> do
                b <- liftIO $ readIORef (alive edge)
                liftIO $ putStrLn "Updating edge"
                when b $ 
                    case from edge of
                        n@(Node { parent = parent }) -> do
                            genericRecalc n $ \new_tys old_tys -> do
                                when (new_tys /= old_tys) $ pushQuery (QEdge parent) 
                                updateLoop
                        RootNode main -> do
                            tys <- liftIO $ readIORef (types main)
                            unless (IFail `elem` tys) updateLoop
            QFlow node@(Node {parent = parent}) -> do
                liftIO $ putStrLn "Updating flow"
                genericRecalc node $ \new_tys old_tys ->
                    when (new_tys /= old_tys) $ pushQuery (QEdge parent)
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
                   <*> H.new               -- ctxRtnTypeTbl
                   <*> H.new               -- ctxArgTypeTbl
                   <*> H.new               -- ctxHFormulaTbl
                   <*> newIORef 0          -- ctxHFormulaSize
                   <*> H.new               -- ctxCheckSatCache
                   <*> newIORef False      -- ctxUpdated
                   <*> newIORef 0          -- ctxSMTCount
                   <*> newIORef 0          -- ctxSMTCountHit
                   <*> newIORef Saturation -- ctxMode
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
                (_, edge) <- mkExpEdge M.empty fml0 _root (mainTerm prog) ENone
                return (RootNode (to edge))
            updateLoop
            tys <- liftIO $ readIORef (types n)
            if IFail `elem` tys
            then do
                bs <- execWriterT (extractor n M.empty IFail)
                return (True, (tys, Just bs))
            else return (False, (tys, Nothing))
    evalStateT (runReaderT (unR doit) ctx) emptyQueue
