{-# LANGUAGE TupleSections, FlexibleContexts #-}
module Language.DMoCHi.Boolean.Type2(saturate,Context(..)) where
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Arrow(second)
import Control.Applicative
import Language.DMoCHi.Boolean.Syntax
import Language.DMoCHi.Boolean.Flow(FlowGraph,Id)
import Language.DMoCHi.Common.Util
import Control.Monad
import Data.Array hiding((!))
import qualified Data.Array as A
import Data.Array.IO
import Data.Maybe
import Data.IORef
import Control.Monad.Reader
import Control.Monad.Writer hiding((<>))
import Control.Monad.State
import Data.List hiding (elem)
import Prelude hiding(elem)
import Data.Function(on)
import Text.PrettyPrint.HughesPJClass
import Text.Printf
import Data.Time
import Language.DMoCHi.Boolean.IType
--import Debug.Trace

incrId :: State Id Id
incrId = do
    i <- get
    put $! i + 1
    return i

assignId' :: Term a -> Term (Id,S.Set String)
assignId' t = evalState (assignId t) 0

assignId :: Term a -> State Id (Term (Id,S.Set String))
assignId (C _ b) = C <$> ((,S.empty) <$> incrId) <*> pure b
assignId (V _ x) = V <$> ((,S.singleton x) <$> incrId) <*> pure x
assignId (Fail _ s) = Fail <$> ((,S.empty) <$> incrId) <*> pure s
assignId (Omega _ s) = Omega <$> ((,S.empty) <$> incrId) <*> pure s
assignId (T _ ts) = do
    ts' <- mapM assignId ts
    let s = S.unions $ map (snd.getValue) ts'
    i <- incrId
    return $ T (i,s) ts'
assignId (TF _) = TF <$> ((,S.empty) <$> incrId)
assignId (Lam _ x t) = do
    t' <- assignId t
    let s = S.delete x $ snd (getValue t')
    i <- incrId
    return $ Lam (i,s) x t'
assignId (Let _ x tx t) = do
    tx' <- assignId tx
    t'  <- assignId t
    let s = S.union (S.delete x (snd $ getValue t')) (snd $ getValue tx')
    i <- incrId
    return $ Let (i,s) x tx' t'
assignId (Proj _ n d t) = do
    t' <- assignId t
    let s = snd $ getValue t'
    i <- incrId
    return $ Proj (i,s) n d t'
assignId (App _ t1 t2) = do
    t1' <- assignId t1
    t2' <- assignId t2
    let s = (snd $ getValue t1') `S.union` (snd $ getValue t2')
    i <- incrId
    return $ App (i,s) t1' t2'
assignId (If _ b t1 t2 t3) = do
    t1' <- assignId t1
    t2' <- assignId t2
    t3' <- assignId t3
    let s = S.unions $ map (snd . getValue) [t1',t2',t3']
    i <- incrId
    return $ If (i,s) b t1' t2' t3'
                                    

type M a = ReaderT Factory IO a

data Context = Context { flowEnv :: M.Map Symbol TTypeList
                       , symEnv  :: M.Map Symbol  VType 
                       , flowTbl :: IOArray Id TTypeList
                       , symHist :: [(M.Map Symbol TTypeList, M.Map Symbol VType)]} deriving(Eq)

saturateFlow ::  (Array Id [Id], M.Map Symbol Id, Array Id (Maybe (Term (Id,S.Set String)))) -> M.Map Symbol VType -> IOArray Id TTypeList -> M (M.Map Symbol TTypeList)
saturateFlow (edgeTbl,symMap,leafTbl) env arr = do
    let terms = [ (i,t) | (i,Just t) <- assocs leafTbl]
        fvarMap = M.fromList $ map (\(i,t) -> (i,freeVariables t \\ M.keys env)) terms
        bvarMap = M.fromList $ map (\(i,t) -> (i,boundVariables t)) terms
    let bb = bounds edgeTbl
    let depTbl :: Array Id [Id]
        depTbl = accumArray (flip (:)) [] bb $
                 [ (t,s) | (s,ts) <- assocs edgeTbl, t <- ts ] ++
                 [ (symMap ! x, s) | (s, Just _) <- assocs leafTbl, 
                                       x <- nub $ fvarMap ! s ++ bvarMap ! s ]
    stat <- liftIO $ (newArray bb (0,0) :: IO (IOArray Id (Int,NominalDiffTime)))
    {-
    nil <- buildTypeList lnil
    arr <- liftIO $ (newArray (bounds leafTbl) nil :: IO (IOArray Id TTypeList))
    -}
    let go s | S.null s = return ()
             | otherwise = do
            let (v,vs) = S.deleteFindMin s
            ty <- liftIO $ readArray arr v
            --liftIO $ printf "updating %s %s..\n" (show (v,fmap getValue (leafTbl ! v))) (take 50 $ show (leafTbl ! v))
            time_st <- liftIO $ getCurrentTime
            ty' <- case leafTbl A.! v of
                Nothing -> do
                    tys <- forM (edgeTbl A.! v) $ liftIO . readArray arr
                    concatTypeList $ ty : tys
                Just (V _ _) -> do
                    tys <- forM (edgeTbl A.! v) $ liftIO . readArray arr
                    r <- concatTypeList $ ty : tys
                    return r
                Just t -> do
                    let fvars = fvarMap ! v
                    let bvars = bvarMap ! v
                    tys <- forM fvars $ liftIO . readArray arr . (symMap !)
                    m <- M.fromList <$> forM bvars (\x -> (x,) <$> liftIO (readArray arr (symMap ! x)))
                    let cands = sequence $ map unfoldV tys
                    ls <- forM cands $ \l -> do
                        let env' = updateEnv env (zip fvars l)
                        res <- saturateTerm m env' t 
                        case res of
                            LFail _ -> buildTypeList lnil
                            tyl -> return tyl
                    concatTypeList ls
            liftIO $ do
                time_ed <- getCurrentTime
                (c,t) <- readArray stat v
                let c1 = c + 1
                    t1 = t+diffUTCTime time_ed time_st
                c1 `seq` t1 `seq` (writeArray stat v $! (c1,t1))
            if ty' === ty 
                then go vs
                else do
                    liftIO (writeArray arr v ty')
                    go (foldr S.insert vs (depTbl A.! v))
    go $ S.fromList $ [ i | (i,Just _) <- assocs leafTbl]
    l <- forM (assocs leafTbl) $ \(v,_) -> liftIO $ do
        (c,t) <- readArray stat v
        return (t,c,v)
    let time = sum [ t | (t,_,_) <- l ]
    let top10 = take 10 $ reverse $ sort l
    liftIO $ do
        printf "time %s\n" $ show time
        printf "top 10:\n"
        forM_ top10 $ \(t,c,v) -> 
            printf "    %4d: %s %d\n" v (show t) c

    fmap M.fromList $ forM (M.assocs symMap) $ \(f,i) -> do
        v <- liftIO $ readArray arr i
        return (f,v)

saturateSym :: M.Map Symbol TTypeList -> M.Map Symbol VType -> [(Symbol,Term (Id,S.Set String))] -> M (M.Map Symbol VType)
saturateSym _flowEnv _symEnv defs = do
    fmap M.fromList $ forM defs $ \(x,t) -> do
        LCons _ ty _  <- saturateTerm _flowEnv _symEnv t
        let VFun _ ty1 = ty
            VFun _ ty2 = _symEnv M.! x
        let mergeFun (VNil _) t2 = return t2
            mergeFun t1 (VNil _) = return t1
            mergeFun t1@(VAnd _ vx1 vt1 t1') t2@(VAnd _ vx2 vt2 t2') 
                | k1 < k2 = do
                    ts <- mergeFun t1 t2'
                    buildFunType (fand vx2 vt2 ts)
                | k1 == k2 = do
                    ts <- mergeFun t1' t2'
                    buildFunType (fand vx1 vt1 ts)
                | otherwise = do
                    ts <- mergeFun t1' t2
                    buildFunType (fand vx1 vt1 ts)
                where k1 = (getId vx1,getId vt1)
                      k2 = (getId vx2,getId vt2)
        ty' <- mergeFun ty1 ty2 >>= buildType . func
        return (x,ty')

updateEnv :: M.Map Symbol VType -> [(Symbol,VType)] -> M.Map Symbol VType
updateEnv = foldl (\acc (x,ty) -> M.insert x ty acc)

saturateTerm :: M.Map Symbol TTypeList -> M.Map Symbol VType -> Term a -> M TTypeList
saturateTerm _flowEnv _env _t = incr termCounter >> go 1 _env _t where
    go c env _t = do
        incr costCounter
        comb <- fmap combCounter ask
        liftIO $ do
            m <- readIORef comb
            writeIORef comb $! max m c
        case _t of
            C _ b -> buildType (bool b) >>= singleton
            V _ x -> singleton (env M.! x)
            Fail _ _ -> buildTypeList lfail
            TF _ ->
              do t1 <- buildType (bool True)  >>= singleton
                 t2 <- buildType (bool False) >>= singleton
                 mergeTypeList t1 t2
            Omega _ _ -> buildTypeList lnil
            Lam _ x t -> do
                let l = unfoldV $ _flowEnv M.! x
                let c' = c * length l
                as <- forM l $ \tyx -> do
                    tl <- go c' (M.insert x tyx env) t
                    return $ (tyx,tl)
                toFunType as >>= buildType . func >>= singleton
            App _ t1 t2 -> do
                ty1 <- go c env t1
                case ty1 of
                    LNil _ -> return ty1
                    LFail _ -> return ty1
                    _ -> do
                        ty2 <- go c env t2
                        applyType ty1 ty2
            If _ _ t1 t2 t3 -> do
                ty1 <- go c env t1
                case ty1 of
                    LFail _ -> return ty1
                    LNil  _ -> return ty1
                    _       -> do
                        xs <- if VT undefined `elem` ty1 then 
                                go c env t2 
                              else buildTypeList lnil
                        ys <- if VF undefined `elem` ty1 then 
                                go c env t3 
                              else buildTypeList lnil
                        mergeTypeList xs ys
            T _ ts -> do
                tys <- forM ts $ go c env 
                let check = foldr (\tyi acc -> 
                                (LFail undefined == tyi) || (LNil undefined /= tyi && acc)) False
                if check tys then
                    {-# SCC buildTypeList443 #-} buildTypeList lfail
                else do
                    let tys' = map unfoldV tys
                    -- can be exponatial
                    tys'' <- forM (sequence tys') $ buildType . tup
                    let sorted = sortBy (compare `on` getId) tys''
                    t0 <- {-# SCC buildTypeList449 #-} buildTypeList lnil
                    foldM (\acc t -> {-# SCC buildTypeList450 #-} buildTypeList $ lcons t acc) t0 sorted
            Let _ x t1 t2 -> do
                ty1 <- go c env t1
                case ty1 of
                    LFail _ -> {-# SCC buildTypeList454 #-} buildTypeList lfail
                    _ -> (forM (unfoldV ty1) $ \tyx -> go c (M.insert x tyx env) t2) >>= concatTypeList
            Proj _ n _ t -> do
                tys <- go c env t
                case tys of
                    LFail _ -> {-# SCC buildTypeList459 #-} buildTypeList lfail
                    _ -> do
                        let tys' = map (\(VTup _ ts) -> ts !! projN n) $ unfoldV tys
                        let sorted = map head $ groupBy (===) $ sortBy (compare `on` getId) tys'
                        t0 <- {-# SCC buildTypeList463 #-} buildTypeList lnil
                        foldM (\acc _t -> {-# SCC buildTypeList464 #-} buildTypeList $ lcons _t acc) t0 sorted

initContext :: (MonadReader Factory m, MonadIO m) => Program -> FlowGraph -> m Context
initContext (Program defs _) (_,mapSym,leafTbl) = do
    nil <- buildTypeList lnil
    ty  <- buildFunType fnil >>= buildType . func
    arr <- liftIO $ (newArray (bounds leafTbl) nil :: IO (IOArray Id TTypeList))
    return $ Context (fmap (const nil) mapSym) (M.fromList (map (second (const ty)) defs)) arr []

data Value = VB Bool | Cls Symbol (Term ()) Env FEnv TEnv | Tup [Value]
type Env = M.Map Symbol Value
type TEnv = M.Map Symbol VType
type FEnv = M.Map Symbol TTypeList

instance Show Value where
    show (VB b) = show b
    show (Cls _ _ _ _ _) = show "<closure>"
    show (Tup vs) = show vs

extractCE :: Program -> M.Map Symbol TTypeList -> TEnv -> [(FEnv,TEnv)] ->  M [Bool]
extractCE prog flowEnv genv hist = 
    let env0 = M.fromList [ (f,Cls x (Omega () "") env0 M.empty M.empty) | (f,Lam _ x _) <- definitions prog ] in
    let f (fenv,genv) env = M.fromList [ (f,Cls x e0 env fenv genv) | (f,Lam _ x e0) <- definitions prog ] in
    let env = foldr f env0 hist in
    execWriterT $ evalFail env flowEnv genv (mainTerm prog)
    where
    evalFail :: Env -> FEnv -> TEnv -> Term () -> WriterT [Bool] (ReaderT Factory IO) ()
    evalFail env fenv tenv e = {- traceShow (e,tenv) $ -} case e of
        T _s es -> 
            let sub [] = error "extractCE: Tuple: there must be an term that fails"
                sub (ei:es') = do
                    tyi <- lift $ saturateTerm fenv tenv ei
                    case tyi of
                        LNil _ -> error "extractCE: Tuple: this term may not diverge" 
                        LFail _ -> evalFail env fenv tenv ei
                        LCons _ etyi _ -> eval env fenv tenv ei etyi >> sub es'
            in sub es 
        Let _ x e1 e2 -> 
            let sub (LFail _) = evalFail env fenv tenv e1 
                sub (LCons _ ty1 ts) = do
                    let tenv' = M.insert x ty1 tenv
                    ty2 <- lift $ saturateTerm fenv tenv' e2
                    if TFail `telem` ty2 then do
                        ex <- eval env fenv tenv e1 ty1
                        evalFail (M.insert x ex env) fenv tenv' e2
                    else
                        sub ts 
                sub (LNil _) = error "evalFail: unexpected pattern" 
            in lift (saturateTerm fenv tenv e1) >>= sub
        Proj _s _n _d e1 -> evalFail env fenv tenv e1
        If _ b e1 e2 e3 -> do
            ty1 <- lift $ saturateTerm fenv tenv e1
            if TFail `telem` ty1 then
                evalFail env fenv tenv e1
            else do
                ty2 <- lift $ saturateTerm fenv tenv e2
                vtrue <- buildType (bool True)
                vfalse <- buildType (bool False)
                if vtrue `elem` ty1 && TFail `telem` ty2 then
                    eval env fenv tenv e1 vtrue >>
                    tell (if b then [True] else []) >> 
                    evalFail env fenv tenv e2
                else 
                    eval env fenv tenv e1 vfalse >>
                    tell (if b then [False] else []) >> 
                    evalFail env fenv tenv e3
        App _ e1 e2 ->  do
            ty1 <- lift (saturateTerm fenv tenv e1)
            if TFail `telem` ty1 then
                evalFail env fenv tenv e1
            else do
                let (LCons _ ty1' _) = ty1 
                ty2 <- lift (saturateTerm fenv tenv e2)
                if TFail `telem` ty2 then do
                    eval env fenv tenv e1 ty1'
                    evalFail env fenv tenv e2
                else do
                    let (ty1',ty2') = head $ do
                            vf@(VFun _ vs) <- unfoldV ty1
                            (a,b) <- unfoldFun vs
                            guard $ b === TFail
                            guard $ a `elem` ty2
                            return (vf,a)
                    (Cls x e0 env' fenv' tenv') <- eval env fenv tenv e1 ty1'
                    v2 <- eval env fenv tenv e2 ty2'
                    evalFail (M.insert x v2 env') fenv' (M.insert x ty2' tenv') e0
        Fail _ _ -> return ()
        C _ _ -> error "evalFail: unexpected pattern"
        V _ _ -> error "evalFail: unexpected pattern"
        TF _ -> error "evalFail: unexpected pattern"V
        Lam _ _ _ -> error "evalFail: unexpected pattern"
        Omega _ _ -> error "evalFail: unexpected pattern"
    eval :: Env -> FEnv -> TEnv -> Term () -> VType -> WriterT [Bool] (ReaderT Factory IO) Value
    eval env fenv tenv e ety = {- traceShow e $ traceShow ("env",env) $ trace ("type: "++ show ety) $ -} case e of
        V _ x -> return $ env M.! x
        C _ b -> return $ VB b
        T _ es -> 
            let VTup _ tys = ety in 
            Tup <$> zipWithM (\ei tyi -> eval env fenv tenv ei tyi) es tys
        TF _ -> case ety of
            VT _ -> return $ VB True
            VF _ -> return $ VB False
            _ -> error "eval: unexpected pattern"
        Lam _ x e1 -> return $ Cls x e1 env fenv tenv
        Let _ x e1 e2 ->
            let sub (LCons _ ty1 ts) = do
                    let tenv' = M.insert x ty1 tenv
                    ty2 <- lift $ saturateTerm fenv tenv' e2
                    if ety `elem` ty2 then do
                        ex <- eval env fenv tenv e1 ty1
                        eval (M.insert x ex env) fenv tenv' e2 ety
                    else
                        sub ts
                sub _ = error "eval: unexpected pattern"
            in lift (saturateTerm fenv tenv e1) >>= sub
        Proj _ n _ e1 -> 
            let sub (LCons _ ty1@(VTup _ tys) ty') 
                    | ety == tys !! projN n = do
                        Tup vs <- eval env fenv tenv e1 ty1
                        return $ vs !! projN n
                    | otherwise = sub ty'
                sub _ = error "eval: unexpected pattern" in
            lift (saturateTerm fenv tenv e1) >>= sub
        App _ e1 e2 -> do
            ty1 <- lift (saturateTerm fenv tenv e1)
            ty2 <- lift (saturateTerm fenv tenv e2)
            let (ty1',ty2') = head $ do
                    vf@(VFun _ vs) <- unfoldV ty1
                    (a,b) <- unfoldFun vs
                    guard $ b === TPrim ety
                    guard $ a `elem` ty2
                    return (vf,a)
            (Cls x e0 env' fenv' tenv') <- eval env fenv tenv e1 ty1'
            v2 <- eval env fenv tenv e2 ty2'
            eval (M.insert x v2 env') fenv' (M.insert x ty2' tenv') e0 ety
        If _ b e1 e2 e3 -> do
            ty1 <- lift $ saturateTerm fenv tenv e1
            ty2 <- lift $ saturateTerm fenv tenv e2
            vtrue <- buildType (bool True)
            vfalse <- buildType (bool False)
            if vtrue `elem` ty1 && ety `elem` ty2 then
                eval env fenv tenv e1 vtrue >>
                tell (if b then [True] else []) >> 
                eval env fenv tenv e2 ety
            else 
                eval env fenv tenv e1 vfalse >>
                tell (if b then [False] else []) >> 
                eval env fenv tenv e3 ety
        Fail _ _ -> error "eval: unexpected pattern"
        Omega _ _ -> error "eval: unexpected pattern"
    telem :: TType -> TTypeList -> Bool
    telem TFail (LFail _) = True
    telem TFail _ = False
    telem (TPrim v) ts = elem v ts


saturate :: Program -> FlowGraph -> LoggingT IO (Maybe [Bool],Context)
saturate p flow = liftIO newFactory >>= runReaderT (loop (0::Int) =<< initContext p flow) where
    t0' = assignId' (mainTerm p)
    ds' = map (second assignId') (definitions p)
    flow' = let (a,b,c) = flow in (a,b,fmap (fmap assignId') c)
    loop i ctx = do
        logInfoNS "saturate" "saturating flow..."
        -- ReaderT IO ~ ReaderT (LoggingT IO)
        env1 <- mapReaderT lift $ saturateFlow flow' (symEnv ctx) (flowTbl ctx)
        logInfoNS "saturate" "updating env..."
        env2 <- mapReaderT lift $ saturateSym env1 (symEnv ctx) ds'
        factory <- ask
        do
            logDebugNS "saturate" "----------ENV----------"
            logPretty "saturate" LevelDebug "environment" $
                PPrinted $ braces $ vcat $ punctuate comma $ 
                    flip map (M.assocs env2) $ \(x,l) -> hang (text x <+> pPrint (getId l) <> colon) 4 (ppV 0 l)
            logPretty "saturate" LevelDebug "Round" i
            liftIO (readIORef (counter      factory)) >>= logPretty "saturate" LevelDebug "Counter"
            liftIO (readIORef (queryCounter factory)) >>= logPretty "saturate" LevelDebug "Queries"
            liftIO (readIORef (mergeCounter factory)) >>= logPretty "saturate" LevelDebug "Merge"
            liftIO (readIORef (applyCounter factory)) >>= logPretty "saturate" LevelDebug "Apply"
            liftIO (readIORef (insertCounter factory))>>= logPretty "saturate" LevelDebug "Insert"
            liftIO (readIORef (singleCounter factory))>>= logPretty "saturate" LevelDebug "Single"
            liftIO (readIORef (termCounter factory))  >>= logPretty "saturate" LevelDebug "Term"
            liftIO (readIORef (costCounter factory))  >>= logPretty "saturate" LevelDebug "Cost"
            liftIO (readIORef (combCounter factory))  >>= logPretty "saturate" LevelDebug "Comb"
        t0 <- mapReaderT lift $ saturateTerm env1 env2 t0'
        let ctx' = Context env1 env2 (flowTbl ctx) ((env1, symEnv ctx):symHist ctx)
        case t0 of
            LFail _ -> do
                logInfoNS "saturate" "extracting a counterexample"
                ws <- mapReaderT lift $ extractCE p env1 env2 (symHist ctx')
                return (Just ws,ctx')
            _ | env2 == symEnv ctx -> return (Nothing,ctx')
              | otherwise          -> loop (i+1) ctx'

