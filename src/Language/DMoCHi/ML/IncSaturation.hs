{-# LANGUAGE DeriveGeneric, GeneralizedNewtypeDeriving, MultiParamTypeClasses, UndecidableInstances #-}
module Language.DMoCHi.ML.IncSaturation(saturate) where
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
                    let Right tau1@(y, ty_y, ps) = ctxTypeMap ctx M.! key1
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
                    let PFun _ argTy retTy = env M.! f
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
                                   let Left ty_f = tbl M.! getUniqueKey v_f ]
                env' = foldr (uncurry M.insert) env as
            forM_ fs $ \(f,v_f) -> calcContextV env' v_f (env' M.! f)
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
type CEnv = ()
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
    Node :: (NonRoot e, Normalized l e arg, Supported l (Labels e), Eq (SatType e)) => 
            { typeEnv    :: IEnv
            , constraint :: HFormula
            , refl   :: NodeProxy e
            , types  :: IORef (SatType e)
            , parent :: Edge (Node e') (Node e)
            , recalcator :: R (SatType e)
            , edges :: Meta l e
            , term   :: (SLabel l, arg, Type, UniqueKey)
            } -> Node e
    RootNode :: { main :: Node Exp } -> Node Root

type family NonRoot e :: Constraint where
    NonRoot e = (e == Root) ~ 'False

type family SatType e where
    SatType Exp = [ITermType]
    SatType LExp = [ITermType]
    SatType Value = IType

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
  | MetaLetAtom (Edge (Node e) ExpNode)

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

calcFromValue :: HFormula -> UniqueKey -> (IType, a, R IType) -> R ([ITermType], a, R [ITermType])
calcFromValue fml key (theta, meta, recalc) = do
    Just (_,ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
    phi <- calcCondition fml ps
    let recalc' = (\theta -> [ITerm theta phi]) <$> recalc
    return ([ITerm theta phi], meta, recalc')

calcPair :: IEnv -> HFormula -> Node e -> (Value,Value) -> R (IType, MetaPair e, R IType)
calcPair env fml _node (v1,v2) = do
    (ty1,e1) <- mkValueEdge env fml _node v1 (EPair True)
    (ty2,e2) <- mkValueEdge env fml _node v2 (EPair False)
    let recalc = do
            ty1 <- liftIO $ readIORef $ types $ to $ e1
            ty2 <- liftIO $ readIORef $ types $ to $ e2
            return $ IPair ty1 ty2
    return (IPair ty1 ty2, MetaPair e1 e2, recalc)
    
calcLambda :: NonRoot e => IEnv -> HFormula -> Node e -> UniqueKey -> ([TId], Exp) -> R (IType, MetaLambda e, R IType)
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
                                (tys,edge) <- mkExpEdge env' fml' _node e (ELambda (thetas,phi))
                                liftIO $ H.insert tbl (thetas,phi) edge
                                return $ map ((,,) thetas phi) tys
            return $ IFun ty_assocs
    ty <- recalc 
    return (ty, MetaLambda tbl, recalc)
                
calcBranch :: IEnv -> HFormula -> Node e -> (Exp, Exp) -> R ([ITermType] , MetaBranch e, R [ITermType])
calcBranch env fml _node (e1, e2) = do
    (tys1, edge1) <- mkExpEdge env fml _node e1 (EBranch True)
    (tys2, edge2) <- mkExpEdge env fml _node e2 (EBranch False)
    let recalc = do
            tys1 <- liftIO $ readIORef $ types $ to $ edge1
            tys2 <- liftIO $ readIORef $ types $ to $ edge2
            return $ merge tys1 tys2
    return (merge tys1 tys2, MetaBranch edge1 edge2, recalc)

calcLet :: IEnv -> HFormula -> ExpNode -> UniqueKey -> (TId, LExp, Exp) -> R ([ITermType], MetaLet Exp, R [ITermType])
calcLet env fml _node key (x, e1@(LExp l1 arg1 sty1 _), e2) = 
    (case l1 of
        SLiteral -> atomCase (Atom l1 arg1 sty1)
        SVar     -> atomCase (Atom l1 arg1 sty1)
        SUnary   -> atomCase (Atom l1 arg1 sty1)
        SBinary  -> atomCase (Atom l1 arg1 sty1)
        _        -> genericCase)
    where 
        atomCase atom = do
            vx <- mkVar x
            fml' <- toHFormula atom >>= mkBin SEq vx >>= mkBin SAnd fml
            let ity = calcAtom env atom 
                env' = M.insert x ity env
            (tys,edge2) <- mkExpEdge env' fml' _node e2 ENone
            let recalc :: R [ITermType]
                recalc = liftIO $ readIORef $ types $ to $ edge2
            return (tys, MetaLetAtom edge2, recalc)
        genericCase = do
            Just (_, ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
            tbl <- liftIO $ H.new
            let genericCalc :: [ITermType] -> R [ITermType]
                genericCalc tys1 = 
                    fmap concatMerge $ forM tys1 $ \case
                        IFail -> return [IFail]
                        ITerm ity phi -> do
                            liftIO (H.lookup tbl (ity,phi)) >>= \case
                                Just edge -> liftIO $ readIORef $ types $ to edge
                                Nothing -> do
                                    let env' = M.insert x ity env
                                    cond <- fromBFormula ps phi
                                    fml' <- mkBin SAnd fml cond
                                    checkSat fml cond >>= \case 
                                        False -> return []
                                        True -> do 
                                            (tys, edge) <- mkExpEdge env' fml' _node e2 (ELetC (ity, phi))
                                            liftIO $ H.insert tbl (ity,phi) edge
                                            return tys
            (tys1, edge1) <- mkLExpEdge env fml _node e1 ENone
            tys <- genericCalc tys1
            let recalc = (liftIO $ readIORef $ types $ to $ edge1) >>= genericCalc
            return (tys, MetaLet edge1 tbl, recalc)

calcLetRec :: IEnv -> HFormula -> ExpNode -> ([(TId, Value)], Exp) -> R ([ITermType], MetaLetR Exp, R [ITermType])
calcLetRec env fml _node (fs, e) = do
    let env0 = M.fromList [ (f, IFun []) | (f,_) <- fs ]
        env' = M.union env env0
    edge_fs <- forM fs $ \(f,v_f) -> do
        (_, edge_f) <- mkValueEdge env' fml _node v_f (ELetRecD f)
        pushQuery (QEdge edge_f)
        return edge_f
    (tys, edge_e) <- mkExpEdge env' fml _node e ENone
    meta <- liftIO $ MetaLetR <$> newIORef edge_fs
                              <*> H.new
                              <*> newIORef env0
                              <*> newIORef edge_e
    let recalc = do
            env0  <- liftIO $ readIORef $ letREnv meta
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
                        (_, edge_f) <- mkValueEdge env' fml _node v_f (ELetRecD f)
                        pushQuery (QEdge edge_f)
                        return edge_f
                    liftIO $ writeIORef (letREnv meta) env1
                    liftIO $ writeIORef (letRChildren meta) edge_fs
                    (tys, edge_e) <- mkExpEdge env' fml _node e ENone
                    liftIO $ writeIORef (letRCont meta) edge_e
                    return tys
                False -> liftIO $ readIORef (letRCont meta) >>= readIORef . types . to
    return (tys, meta, recalc)

calcAssume :: IEnv -> HFormula -> ExpNode -> (Atom, Exp) -> R ([ITermType], MetaAssume Exp, R [ITermType])
calcAssume env fml _node (a, e) = do
    cond <- toHFormula a 
    checkSat fml cond >>= \case
        True -> do
            fml' <- mkBin SAnd fml cond
            (tys, edge) <- mkExpEdge env fml' _node e ENone
            let recalc = liftIO $ readIORef $ types $ to edge
            return (tys, MetaAssume (Just edge), recalc)
        False -> return ([], MetaAssume Nothing, return [])

calcApp :: IEnv -> HFormula -> LExpNode -> UniqueKey -> (TId, [Value]) -> R ([ITermType], MetaApp LExp, R [ITermType])
calcApp env fml _node key (f, vs) = do
    let IFun assoc = env M.! f
    Just (_, ps) <- ask >>= \ctx -> liftIO (H.lookup (ctxArgTypeTbl ctx) key)
    phi <- calcCondition fml ps
    (thetas,edges) <- fmap unzip $ forM (zip [0..] vs) $ \(i,v) -> 
        mkValueEdge env fml _node v (EApp i)

    flowMap <- ctxFlowMap <$> ask
    forM_ (flowMap M.! f) $ \ident -> addFlow ident (thetas,phi)
    
    let appType thetas = 
            [ iota | (thetas', phi', iota) <- assoc,
                     thetas == thetas' && phi == phi' ]
        recalc = do
            thetas <- forM edges $ liftIO . readIORef . types . to
            forM_ (flowMap M.! f) $ \ident -> addFlow ident (thetas,phi)
            return $ appType thetas

    -- TODO: update flow
    return (appType thetas, MetaApp edges phi, recalc)

calcValue :: IEnv -> HFormula -> Edge (Node e) ValueNode -> Value -> R (ValueNode, IType)
calcValue env fml pEdge (Value l arg sty key) = 
    let fromAtom :: Atom -> (IType, (), R IType)
        fromAtom atom = (ity, (), return ity)
            where ity = calcAtom env atom
    in mfix $ \ ~(_node, _ity) -> do
        (ity,meta, recalc) <- case l of
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
                        , term = (l, arg, sty, key)
                        , types = itypeRef
                        , parent = pEdge
                        , edges = meta
                        , recalcator = recalc }
        return (node, ity)

calcExp :: IEnv -> HFormula -> Edge (Node e) ExpNode -> Exp -> R (ExpNode, [ITermType])
calcExp env fml pEdge (Exp l arg sty key) = 
    let fromValue :: (IType, a, R IType) -> R ([ITermType], a, R [ITermType])
        fromValue = calcFromValue fml key
        fromAtom atom = do
            let ity = calcAtom env atom
            calcFromValue fml key (ity,(), return ity)
    in mfix $ \ ~(_node, _tys) -> do
        (itys,meta,recalc) <- case l of
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
            SFail    -> return ([IFail], (), return [IFail])
            SOmega   -> return ([], (), return [])
        itypeRef <- liftIO $ newIORef itys
        let node = Node { typeEnv = env
                        , constraint = fml
                        , refl = NodeExp
                        , term = (l, arg, sty, key)
                        , types = itypeRef
                        , parent = pEdge
                        , edges = meta
                        , recalcator = recalc }
        liftIO $ printNode node
        return (node, itys)

calcLExp :: IEnv -> HFormula -> Edge (Node e) LExpNode -> LExp -> R (LExpNode, [ITermType])
calcLExp env fml pEdge (LExp l arg sty key) =  
    let fromValue :: (IType, a, R IType) -> R ([ITermType], a, R [ITermType])
        fromValue = calcFromValue fml key
        fromAtom atom = do
            let ity = calcAtom env atom
            calcFromValue fml key (ity,(), return ity)
    in mfix $ \ ~(_node, _tys) -> do
        (itys,meta,recalc) <- case l of
            SLiteral -> fromAtom (Atom l arg sty)
            SVar     -> fromAtom (Atom l arg sty)
            SBinary  -> fromAtom (Atom l arg sty)
            SUnary   -> fromAtom (Atom l arg sty)
            SPair    -> fromValue =<< calcPair env fml _node arg
            SLambda  -> fromValue =<< calcLambda env fml _node key arg
            SBranch  -> calcBranch env fml _node arg
            SApp     -> calcApp env fml _node key arg
            SFail    -> return ([IFail], (), return [IFail])
            SOmega   -> return ([], (), return [])
            SRand    -> return ([ITerm IInt (BConst True)], (), return [ITerm IInt (BConst True)])
        itypeRef <- liftIO $ newIORef itys
        let node = Node { typeEnv = env
                        , constraint = fml
                        , refl = NodeLExp
                        , term = (l, arg, sty, key)
                        , types = itypeRef
                        , parent = pEdge
                        , edges = meta
                        , recalcator = recalc }
        return (node, itys)


genericRecalc :: NonRoot e => Node e -> (SatType e -> SatType e -> R b) -> R b
genericRecalc node cont = do
    new_ity <- recalcator node
    old_ity <- liftIO $ readIORef (types node) 
    liftIO $ writeIORef (types node) new_ity
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
                , term = (l, arg, sty, key)
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
            cont (pPrint (Exp l arg sty key)) (pPrint tys)
        NodeLExp -> do
            tys <- readIORef tys_ref
            cont (pPrint (LExp l arg sty key)) (pPrint tys)
        NodeValue -> do
            tys <- readIORef tys_ref
            cont (pPrint (Value l arg sty key)) (pPrint tys)


updateLoop :: R ()
updateLoop = popQuery >>= \case
    Nothing -> return ()
    Just query -> do
        case query of
            QEdge edge -> do
                b <- liftIO $ readIORef (alive edge)
                liftIO $ putStrLn "Updating edge"
                liftIO $ printNode (from edge)
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
                liftIO $ printNode node 
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
            return (IFail `elem` tys, (tys, Nothing))
    evalStateT (runReaderT (unR doit) ctx) emptyQueue
