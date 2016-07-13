{-# LANGUAGE FlexibleContexts, LambdaCase #-}
module Language.DMoCHi.Boolean.Type3 where
import Language.DMoCHi.Boolean.IType
import Language.DMoCHi.Boolean.Flow2 hiding(getId,varId,Context)
import Language.DMoCHi.Boolean.PrettyPrint.Typed
import qualified Language.DMoCHi.Boolean.Flow2 as Flow
import Language.DMoCHi.Boolean.Syntax.Typed(Symbol)
import Control.Monad
import Data.Array
import Data.Array.IO
import Data.IORef
import Control.Monad.Reader
import Control.Monad.Writer
import qualified Data.IntMap as IM
import qualified Data.Map as M
import qualified Data.Set as S
import Prelude hiding(elem)
import Data.List(sortBy,groupBy,foldl')
import Data.Function(on)
import qualified Data.Graph as G
import Control.Applicative
import Text.Printf
import Text.PrettyPrint hiding(empty)
import qualified Data.Monoid


type M a = ReaderT Factory IO a
binOp :: (TTypeList -> TTypeList -> M TTypeList) -> M TTypeList -> M TTypeList -> M TTypeList
binOp op mty1 mty2 = do
    ty1 <- mty1
    case ty1 of
        LNil _  -> buildTypeList lnil
        LFail _ -> buildTypeList lfail
        _ -> do
            ty2 <- mty2
            case ty2 of
                LNil  _ -> buildTypeList lnil
                LFail _ -> buildTypeList lfail
                _ -> op ty1 ty2

uniOp :: (TTypeList -> M TTypeList) -> M TTypeList -> M TTypeList
uniOp op mty = do
    ty <- mty
    case ty of
        LNil _ -> buildTypeList lnil
        LFail _ -> buildTypeList lfail
        _ -> op ty

andType,orType :: TTypeList -> TTypeList -> M TTypeList
andType ty1 ty2 = do
    -- assume both of ty1 and ty2 are some non-nil
    x <- if VT undefined `elem` ty1 && VT undefined `elem` ty2 then 
            buildType (bool True) >>= singleton
         else
            buildTypeList lnil
    y <- if VF undefined `elem` ty1 || VF undefined `elem` ty2 then
            buildType (bool False) >>= singleton
         else
            buildTypeList lnil
    mergeTypeList x y
    
orType ty1 ty2 = do
    -- assume both of ty1 and ty2 are some non-nil
    x <- if VF undefined `elem` ty1 && VF undefined `elem` ty2 then 
            buildType (bool False) >>= singleton
         else
            buildTypeList lnil
    y <- if VT undefined `elem` ty1 || VT undefined `elem` ty2 then
            buildType (bool True) >>= singleton
         else
            buildTypeList lnil
    mergeTypeList x y

notType :: TTypeList -> M TTypeList
notType ty = do
    x <- if VT undefined `elem` ty then
            buildType (bool False) >>= singleton
         else
            buildTypeList lnil
    y <- if VF undefined `elem` ty then
            buildType (bool True) >>= singleton
         else
            buildTypeList lnil
    mergeTypeList x y

projType :: Int -> TTypeList -> M TTypeList
projType n tys = do
    let tys' = map (\(VTup _ ts) -> ts !! n) $ unfoldV tys
    let sorted = map head $ groupBy (===) $ sortBy (compare `on` getId) tys'
    t0 <- buildTypeList lnil
    foldM (\acc _t -> buildTypeList $ lcons _t acc) t0 sorted

saturateTerm :: IOArray Id TTypeList -> M.Map VarId TTypeList -> M.Map VarId VType -> FlowTerm -> M (TTypeList,S.Set (Id,TTypeList))
saturateTerm flowTbl flowEnv env0 t0 = do
    updateList <- liftIO $ newIORef $ S.empty
    let go env t = do
            -- liftIO $ printf "go %s\n" (take 30 $ show t)
            tau <- calcTermTypeAux flowEnv go env t
            unless (isFail tau) $ liftIO $ modifyIORef updateList (S.insert (termId t, tau))
            return tau
    tau <- go env0 t0
    l <- liftIO $ readIORef updateList
    return (tau,l)

calcTermType :: FEnv -> TEnv -> FlowTerm -> M TTypeList
calcTermType flowEnv = fix (calcTermTypeAux flowEnv)

calcTermTypeAux :: FEnv -> (TEnv -> FlowTerm -> M TTypeList) -> TEnv -> FlowTerm -> M TTypeList
calcTermTypeAux flowEnv go env _t = case _t of
    C _ b -> buildType (bool b) >>= singleton
    V   x -> singleton (env M.! x)
    Fail _ -> buildTypeList lfail
    Omega _ -> buildTypeList lnil
    Lam _ x t -> do
        let l = unfoldV $ flowEnv M.! x
        as <- forM l $ \tyx -> (,) tyx <$> go (M.insert x tyx env) t
        toFunType as >>= buildType . func >>= singleton
    App _ _ t1 t2 -> binOp applyType (go env t1) (go env t2)
    And _ t1 t2 -> binOp andType (go env t1) (go env t2)
    Or  _ t1 t2 -> binOp orType  (go env t1) (go env t2)
    Not _ t -> uniOp notType (go env t)
    Let _ _ x t1 t2 -> do
        ty1 <- go env t1
        case ty1 of
            LFail _ -> buildTypeList lfail
            _ -> concatTypeList =<< forM (unfoldV ty1) (\tyx -> go (M.insert x tyx env) t2)
    T _ ts -> do
        tys <- mapM (go env) ts
        let check = foldr (\tyi acc -> LFail undefined == tyi || (LNil undefined /= tyi && acc)) False
        if check tys then
            buildTypeList lfail
        else do
            let tys' = map unfoldV tys
            tys'' <- forM (sequence tys') $ buildType . tup
            let sorted = sortBy (compare `on` getId) tys''
            t0 <- buildTypeList lnil
            foldM (\acc t -> buildTypeList $ lcons t acc) t0 sorted
    Proj _ _ n _ t -> uniOp (projType n) (go env t)
    Assume _ _ t1 t2 -> do
        ty1 <- go env t1
        if isFail ty1 then
            buildTypeList lfail
        else if VT undefined `elem` ty1 then
            go env t2
        else
            buildTypeList lnil
    Branch _ _ _ t1 t2 -> do
        ty1 <- go env t1
        ty2 <- go env t2
        mergeTypeList ty1 ty2

propagateFlow :: Array Id [Id] -> Array Id FlowTerm -> IOArray Id TTypeList -> S.Set (Id,TTypeList) -> M [VarId]
propagateFlow cfg_inv termTbl flowTbl = init >=> go []
    where
    init l = do
        let l' = groupBy ((==) `on` fst) $ S.toList l
        nodes <- forM l' $ \vs -> do
            let v = fst $ head vs
            tau <- liftIO $ readArray flowTbl v
            tau' <- concatTypeList $ tau : map snd vs
            if tau === tau' then
                return []
            else do
                liftIO $ writeArray flowTbl v tau'
                return [v]
        return $ S.fromList $ concat nodes
    go updateList s | S.null s = return updateList
                    | otherwise = do
         let (v,s') = S.deleteFindMin s
         tau <- liftIO $ readArray flowTbl v
         updateList' <- case termTbl ! v of
                V x -> return $ x : updateList
                _   -> return $ updateList
         s'' <- foldM (\acc w -> do
             tau' <- liftIO $ readArray flowTbl w
             tau'' <- mergeTypeList tau tau'
             liftIO $ writeArray flowTbl w tau''
             if tau'' === tau' then return acc 
                               else return $ S.insert w acc) s' (cfg_inv ! v)
         go updateList' s''

data Context = Context { symEnv   :: M.Map VarId VType
                       , cfg_inv  :: G.Graph
                       , depGraph :: G.Graph
                       , symbols  :: M.Map VarId SymbolInfo
                       , flowTbl  :: IOArray Id TTypeList
                       , envHist  :: [(M.Map VarId TTypeList, M.Map VarId VType)] }

data SymbolType = Global | Arg | Local
data SymbolInfo = SymbolInfo { symType :: SymbolType
                             , depTerm :: FlowTerm
                             , varId   :: VarId}

initContext :: Program -> M Context
initContext prog = do
    nil <- buildTypeList lnil
    ty <- buildFunType fnil >>= buildType . func
    arr <- liftIO $ newArray (bounds (termTable prog)) nil
    let gather t_body _t = go _t
            where
            go (C _ _) = empty
            go (V _) = empty
            go (T _ ts) = ts >>= go
            go (Lam _ x t) = pure (x, SymbolInfo Arg t_body x) <|> go t
            go (And _ t1 t2) = go t1 <|> go t2
            go (Or  _ t1 t2) = go t1 <|> go t2
            go (Not _ t) = go t
            go (App _ _ t1 t2) = go t1 <|> go t2
            go (Let _ _ x t1 t2) = pure (x, SymbolInfo Local t_body x) <|> go t1 <|> go t2
            go (Assume _ _ t1 t2) = go t1 <|> go t2
            go (Branch _ _ _ t1 t2) = go t1 <|> go t2
            go (Fail _) = empty
            go (Omega _) = empty
            go (Proj _ _ _ _ t) = go t
            go _ = error "symbols: unexpected"
    let symbols = M.fromList $ 
            (definitions prog >>= (\(f,t_body) -> 
                pure (f, SymbolInfo Global t_body f) <|> gather t_body t_body))
            <|> gather (mainTerm prog) (mainTerm prog)
    let depend t_body _t = go _t
            where
            go (C _ _) = empty
            go (V x) = case symType (symbols M.! x) of
                Global -> pure (Flow.getId x, termId t_body)
                _      -> empty
            go (T _ ts) = ts >>= go
            go (Lam _ x t) = go t
            go (And _ t1 t2) = go t1 <|> go t2
            go (Or  _ t1 t2) = go t1 <|> go t2
            go (Not _ t) = go t
            go (App _ _ t1 t2) = go t1 <|> go t2
            go (Let _ _ x t1 t2) = go t1 <|> go  t2
            go (Assume _ _ t1 t2) = go t1 <|> go t2
            go (Branch _ _ _ t1 t2) = go t1 <|> go t2
            go (Fail _) = empty
            go (Omega _) = empty
            go (Proj _ _ _ _ t) = go t
            go _ = error "depend: unexpected"
    let depG :: G.Graph
        depG = G.buildG (bounds (termTable prog)) $ 
               (definitions prog >>= \(_,t_body) -> depend t_body t_body) 
               <|> (depend (mainTerm prog) (mainTerm prog))
    return $ Context { symEnv  = M.fromList $ [ (x,ty) | (x,_) <- definitions prog ]
                     , cfg_inv = G.transposeG (cfg prog)
                     , symbols = symbols
                     , depGraph = depG
                     , flowTbl = arr
                     , envHist = [] }

data Value = VB Bool | Cls VarId FlowTerm VEnv FEnv TEnv | RFun VarId FlowTerm AEnv | Tup [Value]
type VEnv = M.Map VarId Value
type TEnv = M.Map VarId VType 
type AEnv = M.Map FunAssoc (VEnv,TEnv,FEnv)
type FEnv = M.Map VarId TTypeList

newtype FunAssoc = FunAssoc (VType,TType)

instance Eq FunAssoc where
    FunAssoc (a,c) == FunAssoc (b,d) = 
        a === b && c === d

instance Ord FunAssoc where
    compare (FunAssoc (a,c)) (FunAssoc (b,d)) =
        (compare `on` getId) a b Data.Monoid.<> (compare `on` getId) c d

-- (fenv,tenv) \in hist <==> fenv is saturated for tenv
extractCE :: Program -> FEnv -> TEnv -> [(FEnv,TEnv)] -> M [Bool]
extractCE prog flowEnv genv hist = execWriterT $ evalFail env flowEnv genv (mainTerm prog)
    where
    env0 = M.fromList [ (f, RFun f t M.empty) | (f,t) <- definitions prog]
    env = foldr (\((fenv, genv),genv') env -> 
            fmap (\(RFun f t phi) ->
                let tys = case genv' M.! f of VFun _ vf -> unfoldFun vf 
                    phi' = foldl' (\acc ty -> 
                                if M.member (FunAssoc ty) acc 
                                    then acc 
                                    else M.insert (FunAssoc ty) (env,genv,fenv) acc) phi tys
                in RFun f t phi') env
          ) env0 (zip hist (genv:map snd hist))

eval :: VEnv -> FEnv -> TEnv -> FlowTerm -> VType -> WriterT [Bool] (ReaderT Factory IO) Value
eval env fenv tenv _e ety = case _e of
    V x -> return $ env M.! x
    C s b -> return $ VB b
    T s es ->
        let VTup _ tys = ety in
        Tup <$> zipWithM (eval env fenv tenv) es tys
    Lam _ x e1 -> return $ Cls x e1 env fenv tenv
    Let _ _ x e1 e2 ->
        lift (calcTermType fenv tenv e1) >>= 
        fix (\sub (LCons _ ty1 ts) -> do
            let tenv' = M.insert x ty1 tenv
            ty2 <- lift $ calcTermType fenv tenv' e2
            if ety `elem` ty2 then do
                ex <- eval env fenv tenv e1 ty1
                eval (M.insert x ex env) fenv tenv' e2 ety
            else
                sub ts)
    Proj _ _ n d e ->
        lift (calcTermType fenv tenv e) >>=
        fix (\sub (LCons _ ty1@(VTup _ tys) ty') ->
            if ety === (tys !! n) then do
                Tup vs <- eval env fenv tenv e ty1
                return $ vs !! n
            else 
                sub ty')
    App _ _ e1 e2 -> do
        ty1 <- lift $ calcTermType fenv tenv e1
        ty2 <- lift $ calcTermType fenv tenv e2
        let (ty1', ty2') = head $ do
                vf@(VFun _ vs) <- unfoldV ty1
                (a,b) <- unfoldFun vs
                guard $ b === TPrim ety
                guard $ a `elem` ty2
                return (vf,a)
        v1 <- eval env fenv tenv e1 ty1'
        v2 <- eval env fenv tenv e2 ty2'
        case v1 of
            Cls x e0 env' fenv' tenv'  -> 
                eval (M.insert x v2 env') fenv' (M.insert x ty2' tenv') e0 ety
            RFun f (Lam _ x e0) phi -> do
                let (env',tenv',fenv') = phi M.! (FunAssoc (ty2',TPrim ety))
                eval (M.insert x v2 env') fenv' (M.insert x ty2' tenv') e0 ety
    Branch _ _ b e1 e2 -> do
        ty1 <- lift $ calcTermType fenv tenv e1
        ty2 <- lift $ calcTermType fenv tenv e2
        if ety `elem` ty1 then do
            when b $ tell [True]
            eval env fenv tenv e1 ety
        else do
            when b $ tell [False]
            eval env fenv tenv e2 ety
    Assume _ _ e1 e2 -> do
        eval env fenv tenv e1 =<< buildType (bool True)
        eval env fenv tenv e2 ety
    And _ e1 e2 -> 
        case ety of
            VT _ -> do
                vtrue <- buildType (bool True)
                eval env fenv tenv e1 vtrue
                eval env fenv tenv e2 vtrue
            VF _ -> do
                ty1 <- lift $ calcTermType fenv tenv e1
                ty2 <- lift $ calcTermType fenv tenv e2
                vtrue <- buildType (bool True)
                vfalse <- buildType (bool False)
                if vfalse `elem` ty1 then do
                    eval env fenv tenv e1 vfalse
                    eval env fenv tenv e2 (head $ unfoldV ty2)
                    return $ VB False
                else do
                    eval env fenv tenv e1 vtrue
                    eval env fenv tenv e2 vfalse
    Or _ e1 e2 ->
        case ety of
            VT _ -> do
                ty1 <- lift $ calcTermType fenv tenv e1
                ty2 <- lift $ calcTermType fenv tenv e2
                vtrue <- buildType (bool True)
                vfalse <- buildType (bool False)
                if vtrue `elem` ty1 then do
                    eval env fenv tenv e1 vtrue
                    eval env fenv tenv e2 (head $ unfoldV ty2)
                    return $ VB True
                else do
                    eval env fenv tenv e1 vfalse
                    eval env fenv tenv e2 vtrue
            VF _ -> do
                vfalse <- buildType (bool False)
                eval env fenv tenv e1 vfalse
                eval env fenv tenv e2 vfalse
    Not _ e ->
        case ety of
            VT _ -> do
                eval env fenv tenv e =<< buildType (bool False)
                return $ VB True
            VF _ -> do
                eval env fenv tenv e =<< buildType (bool True)
                return $ VB False

evalFail :: VEnv -> FEnv -> TEnv -> FlowTerm -> WriterT [Bool] (ReaderT Factory IO) ()
evalFail env fenv tenv _e = case _e of
    T _ es -> 
        fix (\sub l -> case l of
            [] -> error "extractCE: tuple: there must be a term that fails"
            ei:es' -> do
                tyi <- lift $ calcTermType fenv tenv ei
                case tyi of
                    LNil _ -> error "extractCE: Tuple: this term may not diverge"
                    LFail _ -> evalFail env fenv tenv ei
                    LCons _ etyi _ -> eval env fenv tenv ei etyi >> sub es') es
    Let _ _ x e1 e2 ->
        lift (calcTermType fenv tenv e1) >>=
        fix (\sub l -> case l of
            (LFail _) -> evalFail env fenv tenv e1
            (LCons _ ty1 ts) -> do
                let tenv' = M.insert x ty1 tenv
                ty2 <- lift $ calcTermType fenv tenv' e2
                if isFail ty2 then do
                    ex <- eval env fenv tenv e1 ty1
                    evalFail (M.insert x ex env) fenv tenv' e2
                else
                    sub ts)
    Proj _ _ _ _ e -> evalFail env fenv tenv e
    Branch _ _ b e1 e2 -> do
        ty1 <- lift $ calcTermType fenv tenv e1
        if isFail ty1 then
            when b (tell [True]) >> 
            evalFail env fenv tenv e1
        else
            when b (tell [False]) >> 
            evalFail env fenv tenv e2
    Assume _ _ e1 e2 -> do
        ty1 <- lift $ calcTermType fenv tenv e1
        if isFail ty1 then
            evalFail env fenv tenv e1
        else do
            buildType (bool True) >>= eval env fenv tenv e1
            evalFail env fenv tenv e2
    App _ _ e1 e2 -> do
        ty1 <- lift (calcTermType fenv tenv e1)
        if isFail ty1 then
            evalFail env fenv tenv e1
        else do
            ty2 <- lift $ calcTermType fenv tenv e2
            if isFail ty2 then do
                eval env fenv tenv e1 (head $ unfoldV ty1)
                evalFail env fenv tenv e2
            else do
                let (ty1', ty2') = head $ do
                        vf@(VFun _ vs) <- unfoldV ty1
                        (a,b) <- unfoldFun vs
                        guard $ b === TFail
                        guard $ a `elem` ty2
                        return (vf,a)
                v1 <- eval env fenv tenv e1 ty1'
                v2 <- eval env fenv tenv e2 ty2'
                case v1 of
                    Cls x e0 env' fenv' tenv' ->
                        evalFail (M.insert x v2 env') fenv' (M.insert x ty2' tenv') e0
                    RFun f (Lam _ x e0) phi -> do
                        let (env',tenv',fenv') = phi M.! (FunAssoc (ty2',TFail))
                        evalFail (M.insert x v2 env') fenv' (M.insert x ty2' tenv') e0
    Fail _ -> return ()
    And _ e1 e2 -> do
        ty1 <- lift $ calcTermType fenv tenv e1
        if isFail ty1 then
            evalFail env fenv tenv e1
        else do
            eval env fenv tenv e1 (head $ unfoldV ty1)
            evalFail env fenv tenv e2
    Or _ e1 e2 -> do
        ty1 <- lift $ calcTermType fenv tenv e1
        if isFail ty1 then
            evalFail env fenv tenv e1
        else do
            eval env fenv tenv e1 (head $ unfoldV ty1)
            evalFail env fenv tenv e2
    Not _ e -> evalFail env fenv tenv e

saturate :: Program -> IO (Maybe [Bool])
saturate prog = newFactory >>= runReaderT (initContext prog >>= doit)  where
    q0 = S.singleton (termId (mainTerm prog))
    termTbl = termTable prog
    termNameMap :: M.Map Id (Maybe VarId)
    termNameMap = M.fromList $ (Flow.termId (mainTerm prog), Nothing) : 
                               [ (Flow.termId t, Just f) | (f,t) <- definitions prog ]
    doit ctx = do
        nil <- buildTypeList lnil
        let curFlowEnv = fmap (const nil) (symbols ctx)
        loop 0 q0 curFlowEnv M.empty ctx
    loop :: Int -> S.Set Int -> M.Map VarId TTypeList -> M.Map VarId VType -> Context -> M (Maybe [Bool])
    loop round queue curFlowEnv env_acc ctx 
        | S.null queue = 
            if M.null env_acc then
                -- saturated
                return Nothing
            else do
                let symEnv' = M.union env_acc (symEnv ctx)
                let queue' = S.fromList $ do 
                        f <- M.keys env_acc
                        let f_id = Flow.getId $ varId $ symbols ctx M.! f
                        depGraph ctx ! f_id
                    ctx' = ctx { symEnv  = symEnv'
                               , envHist = (curFlowEnv, symEnv ctx) : envHist ctx }
                loop (round+1) queue' curFlowEnv M.empty ctx'
        | otherwise = do
            let (v,queue') = S.deleteFindMin queue
            let t = termTbl ! v
            liftIO $ printf "Current Round: %d\n" round
            case termNameMap M.! v of
                Just f -> liftIO $ do
                    printf "Updating Function %s(%d)..." (show $ pprintSym $ name f) (Flow.getId f)
                Nothing -> liftIO $ do
                    printf "Updating the main term..."
            (tau,updateNodes) <- saturateTerm (flowTbl ctx) curFlowEnv (symEnv ctx) t
            let k env_acc' = do
                    liftIO $ printf "Propagating flows for nodes ... %d\n" $ S.size updateNodes
                    updateVars <- propagateFlow (cfg_inv ctx) termTbl (flowTbl ctx) updateNodes
                    liftIO $ printf "done.\n"
                    liftIO $ printf "Updated Variables are:\n" -- $ unwords $ map (show . pprintSym . name) updateVars
                    curFlowEnv' <- liftIO $ foldM (\acc x -> do
                        printf "%s(%d):\n" (show $ pprintSym $ name x) (Flow.getId x)
                        tau <- readArray (flowTbl ctx) (Flow.getId x)
                        let doc = nest 4 $ vcat [ ppV 0 ty | ty <- unfoldV tau]
                        print doc
                        return $ M.insert x tau acc) curFlowEnv updateVars
                    let queue'' = foldl' (\acc x -> 
                                            let info = symbols ctx M.! x in
                                            case symType info of
                                                Arg -> S.insert (termId $ depTerm info) acc
                                                _   -> acc) queue' updateVars
                    loop round queue'' curFlowEnv' env_acc' ctx
            liftIO $ putStrLn "done."
            case termNameMap M.! v of
                Just f -> do -- global func
                    let LCons _ ty _ = tau
                    let VFun _ ty1 = ty
                        VFun _ ty2 = symEnv ctx M.! f
                    ty' <- mergeFun ty1 ty2
                    if ty' === ty2 then do
                        liftIO $ printf "No updates\n"
                        k env_acc
                    else do
                        liftIO $ printf "New binding for %s(%d): \n" (show $ pprintSym $ name f) (Flow.getId f)
                        liftIO $ print $ ppF 0 ty'
                        buildType (func ty') >>= k . flip (M.insert f) env_acc
                Nothing -> do -- main term
                    if isFail tau then do
                        liftIO $ putStrLn "Unsafe! extracting a counterexample...\n"
                        ws <- extractCE prog curFlowEnv (symEnv ctx) (envHist ctx)
                        let toi :: Bool -> Int
                            toi True  = 1
                            toi False = 0
                        liftIO $ printf "counterexample is %s\n" (show (map toi ws))
                        return $ Just ws
                    else k env_acc

mergeFun :: VFunType -> VFunType -> M VFunType
mergeFun (VNil _) t2 = return t2
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
    where k1 = (getId vx1, getId vt1)
          k2 = (getId vx2, getId vt2)
         
