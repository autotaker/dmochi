{-# LANGUAGE TupleSections, FlexibleContexts #-}
module Boolean.Type2(saturate,Context(..)) where
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Arrow(second)
import Control.Applicative
import Boolean.Syntax
import Boolean.Flow(FlowGraph,Id)
import Control.Monad
--import Boolean.Util
import Data.Array
import Data.Array.IO
import Data.Maybe
import Data.IORef
import Control.Monad.Reader
import Control.Monad.State
import Data.List hiding (elem)
import Prelude hiding(elem)
import Data.Function(on)
import Text.PrettyPrint
import Text.Printf
import Data.Time
import Boolean.IType

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
                       , flowTbl :: IOArray Id TTypeList} deriving(Eq)


saturateFlow ::  (Array Id [Id], M.Map Symbol Id, Array Id (Maybe (Term (Id,S.Set String)))) -> M.Map Symbol VType -> IOArray Id TTypeList -> M (M.Map Symbol TTypeList)
saturateFlow (edgeTbl,symMap,leafTbl) env arr = do
    let terms = [ (i,t) | (i,Just t) <- assocs leafTbl]
        fvarMap = M.fromList $ map (\(i,t) -> (i,freeVariables t \\ M.keys env)) terms
        bvarMap = M.fromList $ map (\(i,t) -> (i,boundVariables t)) terms
    let bb = bounds edgeTbl
    let depTbl :: Array Id [Id]
        depTbl = accumArray (flip (:)) [] bb $
                 [ (t,s) | (s,ts) <- assocs edgeTbl, t <- ts ] ++
                 [ (symMap M.! x, s) | (s, Just _) <- assocs leafTbl, 
                                       x <- nub $ fvarMap M.! s ++ bvarMap M.! s ]
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
            ty' <- case leafTbl ! v of
                Nothing -> do
                    tys <- forM (edgeTbl ! v) $ liftIO . readArray arr
                    concatTypeList $ ty : tys
                Just (V _ _) -> do
                    tys <- forM (edgeTbl ! v) $ liftIO . readArray arr
                    r <- concatTypeList $ ty : tys
                    return r
                Just t -> do
                    let fvars = fvarMap M.! v
                    let bvars = bvarMap M.! v
                    tys <- forM fvars $ liftIO . readArray arr . (symMap M.!)
                    m <- M.fromList <$> forM bvars (\x -> (x,) <$> liftIO (readArray arr (symMap M.! x)))
                    let cands = sequence $ map unfoldV tys
                        c = length cands
                    ls <- forM cands $ \l -> do
                        let env' = updateEnv env (zip fvars l)
                        res <- saturateTerm c m env' t 
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
                    go (foldr S.insert vs (depTbl ! v))
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
        LCons _ ty _  <- saturateTerm 1 _flowEnv _symEnv t
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

saturateTerm :: Int -> M.Map Symbol TTypeList -> M.Map Symbol VType -> Term (Id,S.Set String) -> M TTypeList
saturateTerm _c _flowEnv _env _t = incr termCounter >> go _c _env _t where
    go c env _t = {- memo env _t $ -} do
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

initContext :: Program -> FlowGraph -> M Context
initContext (Program defs _) (_,mapSym,leafTbl) = do
    nil <- buildTypeList lnil
    ty  <- buildFunType fnil >>= buildType . func
    arr <- liftIO $ (newArray (bounds leafTbl) nil :: IO (IOArray Id TTypeList))
    return $ Context (fmap (const nil) mapSym) (M.fromList (map (second (const ty)) defs)) arr

saturate :: Program -> FlowGraph -> IO (Bool,Context)
saturate p flow = newFactory >>= runReaderT (loop (0::Int) =<< initContext p flow) where
    t0' = assignId' (mainTerm p)
    ds' = map (second assignId') (definitions p)
    flow' = let (a,b,c) = flow in (a,b,fmap (fmap assignId') c)
    loop i ctx = do
        liftIO $ putStrLn "saturating flow...."
        env1 <- saturateFlow flow' (symEnv ctx) (flowTbl ctx)
        liftIO $ putStrLn "updating env..."
        env2 <- saturateSym env1 (symEnv ctx) ds'
        factory <- ask
        liftIO $ do
            putStrLn "----------ENV----------" 
            forM_ (M.assocs env2) $ \ (x,l) -> do
                putStrLn $ x ++ " " ++ show (getId l) ++ ":" 
                putStrLn $ render $ nest 4 $ ppV 0 l
                putStrLn ""
            printf                                      "Round   :%8d\n" i
            readIORef (counter      factory) >>= printf "Counter :%8d\n"
            readIORef (queryCounter factory) >>= printf "Queries :%8d\n"
            readIORef (mergeCounter factory) >>= printf "Merge   :%8d\n"
            readIORef (applyCounter factory) >>= printf "Apply   :%8d\n"
            readIORef (insertCounter factory)>>= printf "Insert  :%8d\n"
            readIORef (singleCounter factory)>>= printf "Single  :%8d\n"
            readIORef (termCounter factory)  >>= printf "Term    :%8d\n"
            readIORef (costCounter factory)  >>= printf "Cost    :%8d\n"
            readIORef (combCounter factory)  >>= printf "Comb    :%8d\n"
            putStrLn ""
        t0 <- saturateTerm 1 env1 env2 t0'
        let ctx' = Context env1 env2 (flowTbl ctx)
        case t0 of
            LFail _ -> return (False,ctx')
            _ | env2 == symEnv ctx -> return (True,ctx')
              | otherwise          -> loop (i+1) ctx'

