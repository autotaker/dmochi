{-# LANGUAGE ScopedTypeVariables, LambdaCase, FlexibleContexts, BangPatterns #-}
module Language.DMoCHi.ML.Refine where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Writer
import           Control.Monad.State.Strict
import           Control.Arrow (first)
import qualified Data.Map as M
import qualified Data.IntMap as IM
import           Data.List(intersperse,nub,foldl',sortBy)
import           Text.PrettyPrint
import           Text.Printf
--import Debug.Trace

import qualified Language.DMoCHi.ML.Syntax.PNormal as ML
import qualified Language.DMoCHi.ML.PrettyPrint.PNormal as ML
import qualified Language.DMoCHi.ML.PredicateAbstraction as PAbst
import qualified Language.DMoCHi.ML.HornClause as Horn
import qualified Language.DMoCHi.ML.SMT as SMT
import           Language.DMoCHi.ML.SymbolicExec
import           Language.DMoCHi.Common.Id
import           Language.DMoCHi.Common.Util


-- Refinement types
data RType = RBool | RInt | RFun !(IM.IntMap RFunAssoc) | RPair !RType !RType deriving(Show)

data RFunAssoc = RFunAssoc { argNames :: ![Id]
                           , argTypes :: ![RType]
                           , preCond :: !LFormula
                           , resType :: !RPostType }
data RPostType = RPostType { posName :: !Id
                           , posType :: !RType
                           , posCond :: !LFormula }
               | RPostTypeFailure
data LFormula = Formula Meta Int CompTreePath [SValue]
data Meta = Meta !String [String]
-- 述語の名前の構造（関数名+アクセサ（事前条件等））

instance Show RFunAssoc where
    show (RFunAssoc xs rtys cond res) = 
        let as = intersperse ", " [ ML.name x ++ " : " ++ show rty | (x,rty) <- zip xs rtys ] in 
        "{" ++ concat as ++ " | " ++ show cond ++ "}" ++ " -> " ++ show res

instance Show RPostType where
    show (RPostType r rty cond) = 
        "{" ++ ML.name r ++ " : " ++ show rty ++ " | " ++ show cond ++ "}"
    show RPostTypeFailure = "_|_"

instance Show LFormula where
    show (Formula (Meta l accessors) i path vs) = 
        let s = concat $ intersperse "," $ map show vs
            smeta = "{" ++ concat (intersperse "." (l : reverse accessors))++ "}" in
        printf "p_%s[%d:%s](%s)" smeta i (show path) s

type RTypeGen m = (String -> [Id] -> Accessor -> m RType,          -- Refinement type generator for values
                   String -> CompTreePath -> [Id] -> Maybe Accessor -> m RPostType -- Refinement type generator for let expressions
                   )

genRTypeFactory :: MonadId m => [CallInfo] -> [ClosureInfo] -> [ReturnInfo] -> RTypeGen m
genRTypeFactory calls closures returns = (genRType, genRPostType)
    where
    clsTbl :: IM.IntMap ClosureInfo
    clsTbl = IM.fromList [ (unClosureId (clsId (closure i)), i) | i <- closures ]
    rtnTbl :: IM.IntMap ReturnInfo
    rtnTbl = IM.fromList [ (unCallId (rcallId i), i) | i <- returns ]
    callTbl :: IM.IntMap CallInfo
    callTbl = IM.fromList [ (unCallId (callId i), i) | i <- calls ]
    clsLookup :: ClosureId -> ClosureInfo
    clsLookup j = clsTbl IM.! unClosureId j
    rtnLookup :: CallId -> ReturnInfo
    rtnLookup j = rtnTbl IM.! unCallId j
    callLookup :: CallId -> CallInfo
    callLookup j = callTbl IM.! unCallId j
    isBase x = case ML.getType x of 
        (ML.TFun _ _) -> False
        _ -> True
    flatten (SVar x) env | isBase x  = (SVar x) : env
                         | otherwise = env
    flatten (P v1 v2) env = flatten v1 (flatten v2 env)
    push = flatten . decompose
    meta_add (Meta i l) s = Meta i (s:l)

    genRType label env = gen (Meta label []) (foldr push [] env)
    genRPostType label path = genPost (Meta label []) path . foldr push []

    gen meta env acsr =
        case ML.getType acsr of
            ML.TBool -> return RBool
            ML.TInt  -> return RInt
            ML.TPair ty1 ty2 -> RPair <$> gen meta env (AFst acsr) <*> gen meta env (ASnd acsr)
            ML.TFun ty_args ty_ret -> do
                let cs = [ info | info <- calls, acsr `elem` callAccessors info ]
                if null cs then
                    return (RFun IM.empty)
                else do
                    let cls = closure (clsLookup (calleeId (head cs)))
                    let xs = ML.args (clsBody cls)
                    let env' = foldl' (flip push) env xs
                    fmap (RFun . IM.fromList) $ forM cs $ \info -> do
                        let j = callId info
                            path = callContext info
                            ReturnInfo _ _ mv = rtnLookup j
                        -- 変数スコープの例
                        -- fの中でxが参照できたり、sの第一要素の中でsの第二要素が参照できることに注意
                        -- { x : int, f : { y : int | P(y,x) } -> { r : int | Q(r,y,x) } | U(x) } -> 
                        --      { s : ({ z : int | R(z,s,x) } -> { t : int | S(t,z,s,z) }) * int | T(x,s) }
                        arg_tys <- forM (zip [(0::Int)..] xs) $ \(i,xi) ->
                            gen (meta_add meta ("pre_" ++ show i)) env' (AVar j xi)
                        p1 <- freshInt
                        let rv = retValue $ rtnLookup j
                        posTy <- genPost (meta_add meta "post") path env' (fmap (const (ARet j ty_ret)) rv)
                        return (unCallId j, RFunAssoc xs arg_tys (Formula (meta_add meta "pre") p1 path env') posTy)
    genPost meta path env Nothing = return RPostTypeFailure
    genPost meta path env (Just acsr) = do
        rj <- ML.Id (ML.getType acsr) <$> freshId "r"
        let env' = push rj env
        pty <- gen meta env' acsr
        p0 <- freshInt
        return $ RPostType rj pty (Formula meta p0 path env')
                                                           

{-
genRTypeFactory :: MonadId m => [CallInfo] -> [ClosureInfo] -> [ReturnInfo] -> RTypeGen m
genRTypeFactory calls closures returns = (genRType, genRPostType)
    where
    genRType :: MonadId m => String -> [Id] -> SValue -> m RType
    genRType label = gen 0 (Meta label []) . foldr push []
    genRPostType :: MonadId m => String -> CompTreePath -> [Id] -> Maybe SValue -> m RPostType
    genRPostType label path = genPost 0 (Meta label []) path . foldr push []
    rtnTbl = IM.fromList [ (unCallId (rcallId info),info) | info <- returns ]
    meta_add (Meta i l) s = Meta i (s:l)
    gen _ _ _ (SVar x) = case ML.getType x of
        ML.TInt -> pure RInt
        ML.TBool -> pure RBool
        ty -> error $ "gen: unexpected type: " ++ show ty
    gen _ _ _ (Int _) = pure RInt
    gen _ _ _ (Bool _) = pure RBool
    gen lim meta env (P v1 v2) = RPair <$> gen lim (meta_add meta "fst") env v1 
                                       <*> gen lim (meta_add meta "snd") env v2
    gen _ _ _ (Add _ _) = pure RInt
    gen _ _ _ (Sub _ _) = pure RInt
    gen _ _ _ (Eq _ _) = pure RBool
    gen _ _ _ (Lt _ _) = pure RBool
    gen _ _ _ (Lte _ _) = pure RBool
    gen _ _ _ (And _ _) = pure RBool
    gen _ _ _ (Or _ _) = pure RBool
    gen _ _ _ (Not _) = pure RBool
    gen lim meta env (C (Cls fdef i _ acsrs)) = do  
        let cs = [ (callId info, callContext info)
                               | info <- calls, 
                                 calleeId info == i,
                                 unCallId (callId info) > lim
                                 ] -- TODO Improve Impl
            xs  = ML.args fdef
            ML.TFun ty_args ty_ret = ML.getType fdef
        as <- forM cs $ \(j,path) -> do
            let ReturnInfo _ arg_vs mv = rtnTbl IM.! (unCallId j)
            let xsj = xs -- [ ML.Id ty_arg (ML.name x) | (x,ty_arg) <- zip xs ty_args ]
            let lim' = unCallId j
            let env' = (foldl' (flip push) env xsj)
            arg_tys <- forM (zip [(0::Int)..] arg_vs) $ \(i,arg_v) -> 
                            gen lim' (meta_add meta ("pre_"++show i)) env' arg_v
            posTy <- genPost lim' (meta_add meta "post") path env' mv
            p1 <- freshInt
            return (unCallId j,RFunAssoc xsj arg_tys (Formula (meta_add meta "pre") p1 path env') posTy)
        return $ RFun $ IM.fromList as
    genPost lim meta path env mv = case mv of
        Just v -> do
            rj <- ML.Id (ML.getType v) <$> freshId "r"
            let env' = push rj env
            pty <- gen lim meta env' v
            p0 <- freshInt
            return $ RPostType rj pty (Formula meta p0 path env')
        Nothing -> return RPostTypeFailure

    isBase x = case ML.getType x of 
        (ML.TFun _ _) -> False
        _ -> True
    flatten (SVar x) env | isBase x  = (SVar x) : env
                         | otherwise = env
    flatten (P v1 v2) env = flatten v1 (flatten v2 env)
    push = flatten . decompose
    -}

{-
evalRType :: M.Map Id (RType,SValue) -> ML.Value -> (RType,SValue)
evalRType env = go where
    go (ML.Atomic v) = evalRTypeA env v
    go (ML.Pair v1 v2) = 
        let (r1,sv1) = go v1 
            (r2,sv2) = go v2 in
        (RPair r1 r2, P sv1 sv2)
    go (ML.Fun fdef) = 
    -}
        
evalRTypeA :: M.Map Id (RType,SValue) -> ML.AValue -> (RType,SValue)
evalRTypeA env = go where
    go (ML.Var x) = env M.! x
    go (ML.CInt i) = (RInt, Int i)
    go (ML.CBool b) = (RBool, Bool b)
    {-
    go (ML.Pair v1 v2) = 
        let (r1,sv1) = go v1 
            (r2,sv2) = go v2 in
        (RPair r1 r2, P sv1 sv2)
    -}
    go (ML.Op (ML.OpAdd v1 v2)) = 
        let (r1,sv1) = go v1 
            (r2,sv2) = go v2 in
        (RInt,Add sv1 sv2)
    go (ML.Op (ML.OpSub v1 v2)) = 
        let (r1,sv1) = go v1 
            (r2,sv2) = go v2 in
        (RInt,Sub sv1 sv2)
    go (ML.Op (ML.OpEq  v1 v2)) = 
        let (r1,sv1) = go v1 
            (r2,sv2) = go v2 in
        (RBool,Eq sv1 sv2)
    go (ML.Op (ML.OpLt  v1 v2)) = 
        let (r1,sv1) = go v1 
            (r2,sv2) = go v2 in
        (RBool,Lt sv1 sv2)
    go (ML.Op (ML.OpLte  v1 v2)) = 
        let (r1,sv1) = go v1 
            (r2,sv2) = go v2 in
        (RBool,Lte sv1 sv2)
    go (ML.Op (ML.OpAnd  v1 v2)) = 
        let (r1,sv1) = go v1 
            (r2,sv2) = go v2 in
        (RBool,And sv1 sv2)
    go (ML.Op (ML.OpOr  v1 v2)) = 
        let (r1,sv1) = go v1 
            (r2,sv2) = go v2 in
        (RBool,Or sv1 sv2)
    go (ML.Op (ML.OpNot v)) = 
        let (r,sv) = go v in (RBool,Not sv)
    go (ML.Op (ML.OpFst _ v)) = let (RPair a _,P sv _) = go v in (a,sv)
    go (ML.Op (ML.OpSnd _ v)) = let (RPair _ b,P _ sv) = go v in (b,sv)

-- input x : Id
-- output v : SValue s.t. 
--        - getType v == getType x
--        - for any free variable x in v, getType v `in` [TBool, TInt, TFun]
decompose :: Id -> SValue
decompose x = case ML.getType x of
    ML.TInt -> SVar x
    ML.TBool -> SVar x
    ML.TPair t1 t2 -> 
        P (decompose (ML.Id t1 (ML.name x ++"_fst"))) 
          (decompose (ML.Id t2 (ML.name x ++"_snd")))
    ML.TFun _ _ -> SVar x

type W m a = WriterT ([(CompTreePath,Horn.Clause)],([(Int,RType)],[(Int,RPostType)])) m a


refineCGen :: forall m.(MonadFix m, MonadId m, MonadIO m) => 
              ML.Program -> FilePath -> Bool -> Int -> Trace -> 
              m (Maybe (Bool,([Horn.Clause],([(Int,RType)],[(Int,RPostType)]))))
refineCGen prog traceFile contextSensitive foolThreshold trace = do
    (genv, (Log consts calls closures returns branches letexps), compTree) <- symbolicExec prog trace
    liftIO $ writeFile traceFile (renderCompTree compTree)
    liftIO $ print consts
    let cs = map fromSValue consts
    isFeasible <- liftIO $ SMT.sat cs
    isFool <- if isFeasible then return False 
                            else fmap not $ liftIO $ SMT.sat (take (length cs - foolThreshold) cs)
    when isFool $ liftIO $ putStrLn "this error trace is fool"
    let sortClauses :: [(CompTreePath,Horn.Clause)] -> [Horn.Clause]
        sortClauses = map snd . sortBy (compare `on` (reverse . fst))
    if isFeasible then
        return Nothing
    else fmap (Just . (,) isFool . first sortClauses) $ execWriterT $ do
        let dump str l = liftIO $ do
                putStrLn $ str ++ ":"
                mapM_ (\v -> putStr "  " >> print v) l
        dump "Calls" calls
        dump "Closures" closures
        dump "Returns" returns
        dump "Branches" branches
        dump "Letexps" letexps
        let (gen,genP) = genRTypeFactory calls closures returns
        let addFuncBinding :: Int -> RType -> W m ()
            addFuncBinding label ty = tell ([],([(label,ty)],[]))
            addExpBinding :: Int -> RPostType -> W m ()
            addExpBinding label ty = tell ([],([],[(label,ty)]))
            addClause :: (CompTreePath,Horn.Clause) -> W m ()
            addClause c = tell ([c],([],[]))

        let callTbl :: M.Map (CallId,Int) CallId
            callTbl = M.fromList [ ((pcallId info,callLabel info),callId info)| info <- calls ]
            closureMap :: M.Map (CallId,Int) ClosureId
            closureMap = M.fromList [ ((cCallId info,label info),clsId $ closure info)| info <- closures ]
            branchMap :: M.Map (CallId,Int) Bool
            branchMap = M.fromList [ ((bCallId info,branchId info),direction info) | info <- branches ]
            letMap :: M.Map (CallId, Int) (CompTreePath, Maybe SValue)
            letMap = M.fromList [ ((lCallId info,lLabel info),(lContext info,evalValue info)) | info <- letexps ]
        genv' <- fmap M.fromList $ forM (M.toList genv) $ \(f,v) -> do
            ty <- gen (ML.name f) [] (AVar (CallId 0) f)
            return (f,(ty,decompose f))
        dump "RefineEnv" (M.assocs genv')

        let showC :: Either SValue LFormula -> String
            showC (Left sv) = show sv
            showC (Right fml) = show fml
            showCs :: [Either SValue LFormula] -> String
            showCs = concat . intersperse ", " . map showC
        let genClause :: Maybe LFormula -> [Either SValue LFormula] -> Horn.Clause
            genClause hd body = Horn.Clause chd cbody
                where
                    f fml@(Formula meta i path svs) 
                        | contextSensitive = fml
                        | otherwise = Formula meta i [] svs
                    chd = case hd of
                        Just fml ->
                            let Horn.Pred s t = termOfFormula (f fml) in
                            Horn.PVar s t
                        Nothing -> Horn.Bot
                    cbody = flip map body $ \case
                        Left sv -> atomOfValue sv
                        Right v -> termOfFormula (f v)

        let check :: M.Map Id (RType,SValue) ->   {- environment -}
                     [Either SValue LFormula] ->  {- accumulator of constraints -}
                     CallId ->                    {- callsite -}
                     ML.Exp ->                    {- checking expr -}
                     RPostType ->                 {- expected type -}
                     W m ()
            check env cs callSite _e tau = case _e of
                ML.Let _ x (ML.LValue v) e -> do
                    let env' = M.insert x (evalRTypeA env v) env
                    check env' cs callSite e tau
                ML.Let _ x (ML.LApp _ i f vs) e -> do
                    let (RFun fassoc,_) = env M.! f
                        j = callTbl M.! (callSite,i)
                        ty_f = fassoc IM.! unCallId j
                    svs <- mapM (genSValue env) vs
                    let subst = M.fromList $ zip (argNames ty_f) svs
                    let tys = map (substRType subst) (argTypes ty_f)
                    svs <- mapM (\(v,sv,theta) -> checkValue env cs callSite v sv theta) $ zip3 vs svs tys
                    clause cs (substLFormula subst (preCond ty_f))
                    case resType ty_f of
                        resTy@(RPostType _ _ _) -> do
                            let x'    = decompose x
                                r     = posName resTy
                                tau_j = substPostType (M.insert r x' subst) $ resTy
                                env'  = M.insert x (posType tau_j,x') env
                                cs'   = Right (posCond tau_j) : cs
                            check env' cs' callSite e tau
                        RPostTypeFailure -> return ()
                ML.Let _ x ML.LRand e -> do
                    let x' = decompose x 
                        env' = M.insert x (RInt,x') env
                    check env' cs callSite e tau
{-
                ML.Let _ f (ML.LFun fdef) e -> do
                    theta <- checkFunDef (ML.name f) env cs callSite fdef Nothing
                    let env' = M.insert f (theta,decompose f) env
                    addFuncBinding (ML.ident fdef) theta
                    check env' cs callSite e tau
-}
                ML.Let _ x (ML.LExp label e') e -> do
                    let (path,letv) = letMap M.! (callSite, label)
                    tau' <- genP (ML.name x ++ "_" ++ show label) path (M.keys env) (fmap (const (AVar callSite x)) letv)
                    addExpBinding label tau'
                    check env cs callSite e' tau'
                    case tau' of
                        RPostType _ _ _ -> do
                            let x'   = decompose x
                                r    = posName tau'
                                tau'' = substPostType (M.singleton r x') tau'
                                env' = M.insert x (posType tau'', x') env
                                cs'  = Right (posCond tau'') : cs
                            check env' cs' callSite e tau
                        RPostTypeFailure -> return ()
                        {- 
                ML.Fun fdef -> do
                    case tau of
                        RPostType _ rty cond -> do
                            checkFunDef "fun" env cs callSite fdef (Just rty)
                            clause cs cond
                        RPostTypeFailure -> do
                            let s = render $ ML.pprintF fdef
                            error $ "This function " ++ s ++ " cannot have the refinement type" ++ show tau
                            -}
                ML.Assume _ v e -> do
                    let (_,sv) = evalRTypeA env v
                    let cs' = Left sv : cs
                    check env cs' callSite e tau
                ML.Branch _ label e1 e2 -> do
                    let b = branchMap M.! (callSite,label)
                    if b then
                        check env cs callSite e1 tau
                    else
                        check env cs callSite e2 tau
                ML.Value v -> 
                    case tau of
                        RPostType _ _ _ -> do
                            sv <- genSValue env v
                            let tau' = substPostType (M.singleton (posName tau) sv) tau
                            sv <- checkValue env cs callSite v sv (posType tau')
                            clause cs (posCond tau')
                        RPostTypeFailure -> do
                            let s = render $ ML.pprintV 0 v
                            error $ "This value "++ s ++ " cannot have the refinement type" ++ show tau
                ML.Fail _ -> 
                    case tau of
                        RPostTypeFailure -> failClause cs
                        _ -> error $ "This failure term cannot have the refinement type" ++ show tau
            checkFunDef fname env cs callSite fdef@(ML.FunDef label xs e0) mtheta = do
                theta@(RFun fassoc) <- case mtheta of 
                    Just it -> return it
                    Nothing -> error "checkFunDef unsupported"
                    {-
                        let clsId = closureMap M.! (callSite,label)
                            meta  = fname++ "_" ++ show label in
                        gen meta (M.keys env) (C (Cls fdef clsId undefined []))
                        -}
                forM_ (IM.assocs fassoc) $ \(j,ty_f) -> do
                    let xsj = argNames ty_f
                        ty_xsj = argTypes ty_f
                        env' = foldr (uncurry M.insert) env (zip xs (zip ty_xsj (map decompose xsj))) 
                        cs' = Right (preCond ty_f) : cs
                    check env' cs' (CallId j) e0 (resType ty_f)
                return theta
            genSValue env = fix $ \go -> \case
                ML.Atomic av -> pure $ snd $ evalRTypeA env av
                ML.Pair v1 v2 -> P <$> go v1 <*> go v2
                ML.Fun fdef -> do
                    f <- freshId "fun"
                    return (SVar (ML.Id (ML.getType fdef) f))
            
            checkValue env cs callSite = go
                where
                go (ML.Atomic av) _ theta = sv <$ subType cs rty theta
                    where
                    (rty, sv) = evalRTypeA env av
                go (ML.Pair v1 v2) (P _sv1 _sv2) (RPair rty1 rty2) =
                    P <$> go v1 _sv1 rty1 <*> go v2 _sv2 rty2
                go (ML.Fun fdef) sv theta = 
                    sv <$ checkFunDef "fun" env cs callSite fdef (Just theta)
                
            clause cs fml = do
                liftIO $ printf "Clause: %s ==> %s\n" (showCs cs) (show fml)
                let Formula _ _ path _ = fml
                addClause (path,genClause (Just fml) cs)
            subType cs ty1 ty2 = do
                liftIO $ printf "SubType: %s |- %s <: %s\n" (showCs cs) (show ty1) (show ty2)
                case (ty1,ty2) of
                    (RInt,RInt) -> return ()
                    (RBool,RBool) -> return ()
                    (RPair t1 t2,RPair t3 t4) -> subType cs t1 t3 >> subType cs t2 t4
                    (RFun fs1,RFun fs2) -> do
                        forM_ (IM.assocs fs2) $ \(i,RFunAssoc xs2 rtys2 cond2 pty2) -> do
                            let RFunAssoc xs1 rtys1 cond1 pty1  = fs1 IM.! i
                            let cs' = Right cond2 : cs
                            let subst = M.fromList $ zip xs1 (map decompose xs2)
                            clause cs' (substLFormula subst cond1)
                            let rtys1' = map (substRType subst) rtys1
                            zipWithM (subType cs') rtys2 rtys1'
                            subTypePost cs' (substPostType subst pty1) pty2
            subTypePost cs (RPostType r1 ty1 cond1) (RPostType r2 ty2 cond2) = do
                let subst = M.singleton r1 (decompose r2)
                let cs' = Right (substLFormula subst cond1) : cs
                clause cs' cond2
                subType cs' (substRType subst ty1) ty2
            subTypePost cs RPostTypeFailure RPostTypeFailure = return ()
            subTypePost cs ty1 ty2 = error $ "subTypePost: unexpected subtyping:" ++ show (cs,ty1,ty2) 
            failClause cs = do
                liftIO $ printf "Clause: %s ==> _|_\n" (showCs cs) 
                addClause ([10],genClause Nothing cs)
        forM_ (ML.functions prog) $ \(f,fdef) -> do
            theta <- checkFunDef (ML.name f) genv' [] (CallId 0) fdef (Just $ fst $ genv' M.! f)
            addFuncBinding (ML.ident fdef) theta
        x <- freshId "main"
        check genv' [] (CallId 0) (ML.mainTerm prog) RPostTypeFailure
        return ()


    
termOfFormula :: LFormula -> Horn.Term
termOfFormula (Formula meta i path vs) = 
    Horn.Pred (printf "p_%s[%d:%d]" smeta i (hashPath path)) ts
    where
    {- 
    annot (SVar x) | ML.getType x == ML.TInt = Add (SVar x) (Int 0)
                   | ML.getType x == ML.TBool = And (SVar x) (Bool True)
                   -}
    annot v = v
    ts = map (termOfValue.annot) vs
    Meta l accessors = meta
    smeta = concat (intersperse "_" (l : reverse accessors))

-- assume that the value has type int/bool
termOfValue :: SValue -> Horn.Term
termOfValue = \case
    SVar x -> Horn.Var x
    Int i -> Horn.Int i
    Bool b -> Horn.Bool b
    Add v1 v2 -> Horn.Add (termOfValue v1) (termOfValue v2)
    Sub v1 v2 -> Horn.Sub (termOfValue v1) (termOfValue v2)
    Eq v1 v2 -> Horn.Eq (termOfValue v1) (termOfValue v2)
    Lt v1 v2 -> Horn.Lt (termOfValue v1) (termOfValue v2)
    Lte v1 v2 -> Horn.Lte (termOfValue v1) (termOfValue v2)
    Not v -> Horn.Not (termOfValue v)
    And v1 v2 -> Horn.And (termOfValue v1) (termOfValue v2)
    Or  v1 v2 -> Horn.Or  (termOfValue v1) (termOfValue v2)
    v -> error $ "termOfValue: unexpected value: " ++ show v

-- assume the value has type bool
atomOfValue :: SValue -> Horn.Term
atomOfValue = \case
    SVar x -> case ML.getType x of
        ML.TBool -> Horn.Var x
        _ -> error $ "atomOfValue: unexpected value: " ++ show x
    Bool b -> Horn.Bool b
    Eq v1 v2 -> Horn.Eq (termOfValue v1) (termOfValue v2)
    Lt v1 v2 -> Horn.Lt (termOfValue v1) (termOfValue v2)
    Lte v1 v2 -> Horn.Lte (termOfValue v1) (termOfValue v2)
    Not v -> Horn.Not (atomOfValue v)
    And v1 v2 -> Horn.And (atomOfValue v1) (atomOfValue v2)
    Or  v1 v2 -> Horn.Or  (atomOfValue v1) (atomOfValue v2)
    v -> error $ "atomOfValue: unexpected value: " ++ show v

-- assume that v is a decomposed value
substPostType :: M.Map Id SValue -> RPostType -> RPostType
substPostType subst (RPostType r rty cond) =
    RPostType r (substRType subst rty) (substLFormula subst cond)
substPostType subst RPostTypeFailure = RPostTypeFailure

-- assume that v is a decomposed value
substRType :: M.Map Id SValue -> RType -> RType
substRType subst = go where
    go (RPair ty1 ty2) = RPair (go ty1) (go ty2)
    go (RFun fassoc) = 
        RFun (fmap (\(RFunAssoc ys rtys cond pos) ->
            RFunAssoc ys (map go rtys) (substLFormula subst cond) (substPostType subst pos)) fassoc)
    go RBool = RBool
    go RInt = RInt

-- assume that x have a base type (int, bool)
substLFormulaBase :: M.Map Id SValue -> LFormula -> LFormula
substLFormulaBase subst (Formula meta i path ws) = Formula meta i path ws' where
    ws' = map (substSValue subst) ws

substLFormula :: M.Map Id SValue -> LFormula -> LFormula
substLFormula subst = substLFormulaBase subst'
    where
    subst' = M.fromList $ 
        M.assocs subst >>= fix (\go p -> case p of
            (SVar x,sv) -> return (x,sv)
            (P x1 x2, P sv1 sv2) -> go (x1,sv1) <|> go (x2,sv2)
            (x,sv) -> error $ "substLFormula: unexpected pattern " ++ show (x,sv)
            ) . first decompose

substSValue :: M.Map Id SValue -> SValue -> SValue
substSValue subst _sv = case _sv of
    SVar y -> case M.lookup y subst of
        Just v -> v
        Nothing -> _sv
    P sv1 sv2   -> P (substSValue subst sv1) (substSValue subst sv2)
    Add sv1 sv2 -> Add (substSValue subst sv1) (substSValue subst sv2)
    Sub sv1 sv2 -> Sub (substSValue subst sv1) (substSValue subst sv2)
    Eq  sv1 sv2 -> Eq  (substSValue subst sv1) (substSValue subst sv2)
    Lt  sv1 sv2 -> Lt  (substSValue subst sv1) (substSValue subst sv2)
    Lte sv1 sv2 -> Lte (substSValue subst sv1) (substSValue subst sv2)
    And sv1 sv2 -> And (substSValue subst sv1) (substSValue subst sv2)
    Or  sv1 sv2 -> Or (substSValue subst sv1) (substSValue subst sv2)
    Not sv1     -> Not (substSValue subst sv1)
    C cls       -> error "substSValue: substituting closure is not supported"
    Int i       -> _sv
    Bool b      -> _sv


-- penv :: i -> (xs,fml) s.t. P_{i} = \xs. fml
-- env : mapping from variables in the formula to values in PType 
refineTermType :: IM.IntMap ([Id], ML.AValue) -> M.Map String ML.AValue -> RPostType -> PAbst.TermType -> PAbst.TermType
refineTermType penv env (RPostType r rty fml) (abst_r, abst_rty, abst_fml) = (abst_r, abst_rty', abst_fml')
    where
    env' = extendEnv r (ML.Var abst_r) env
    abst_rty' = refinePType penv env' rty abst_rty
    phi' = refineLFormula penv env' fml
    abst_fml' = PAbst.updateFormula phi' abst_fml
refineTermType _ _ RPostTypeFailure termType = termType

refinePType :: IM.IntMap ([Id], ML.AValue) -> M.Map String ML.AValue -> RType -> PAbst.PType -> PAbst.PType
refinePType _ _ RBool PAbst.PBool = PAbst.PBool
refinePType _ _ RInt PAbst.PInt = PAbst.PInt
refinePType penv env (RPair rty1 rty2) (PAbst.PPair ty pty1 pty2) = 
    PAbst.PPair ty (refinePType penv env rty1 pty1) (refinePType penv env rty2 pty2)
refinePType penv env (RFun fassoc) (PAbst.PFun ty pty_x0 pty_r0) = pty'
    where
    pty' = uncurry (PAbst.PFun ty) $ foldl' f (pty_x0, pty_r0) (IM.elems fassoc)
    f ((abst_xs, abst_ptys, abst_fml), pty_r) as = pre `seq` abst_ptys' `seq` (pty_x', pty_r')
        where
        env'  = foldr (uncurry extendEnv) env (zip (argNames as) (map ML.Var abst_xs))
        pre   = refineLFormula penv env' (preCond as)
        abst_ptys' = zipWith (refinePType penv env') (argTypes as) abst_ptys
        pty_x' = (abst_xs, abst_ptys', PAbst.updateFormula pre abst_fml)
        pty_r' = refineTermType penv env' (resType as) pty_r

refineLFormula :: IM.IntMap ([Id], ML.AValue) -> M.Map String ML.AValue -> LFormula -> PAbst.Formula
refineLFormula penv env (Formula _ _ _ []) = ML.CBool True  {- this is ad-hoc technique to avoid lookup error: 
                                                             if args is null, penv may not contain the corresponding formula -}
refineLFormula penv env fml = phi' where
    Formula _ i _ args = fml
    (args_phi, phi) = penv IM.! i
    env' = M.union (M.fromList $ zip (map ML.name args_phi) (map recover args)) env
    recover (SVar x) = env M.! (ML.name x)
    phi' = phi & fix (\go -> \case 
        ML.Var x -> case M.lookup (ML.name x) env' of
            Just r -> r
            Nothing -> error $ "Error!:" ++ show (ML.name x, env)
        ML.CInt i -> ML.CInt i
        ML.CBool b -> ML.CBool b
        ML.Op op -> ML.Op $ case op of
            ML.OpAdd a b -> ML.OpAdd (go a) (go b)
            ML.OpSub a b -> ML.OpSub (go a) (go b)
            ML.OpEq  a b -> ML.OpEq  (go a) (go b)
            ML.OpLt  a b -> ML.OpLt  (go a) (go b)
            ML.OpLte a b -> ML.OpLte (go a) (go b)
            ML.OpAnd a b -> ML.OpAnd (go a) (go b)
            ML.OpOr  a b -> ML.OpOr  (go a) (go b)
            ML.OpNot a   -> ML.OpNot (go a)
            ML.OpFst t a -> ML.OpFst t (go a)
            ML.OpSnd t a -> ML.OpSnd t (go a))

extendEnv :: Id -> ML.AValue -> M.Map String ML.AValue -> M.Map String ML.AValue
extendEnv x v env = case ML.getType x of
    ML.TInt -> M.insert (ML.name x) v env
    ML.TBool -> M.insert (ML.name x) v env
    ML.TPair t1 t2 -> extendEnv x1 v1 $ extendEnv x2 v2 env
        where
        x1 = ML.Id t1 (ML.name x ++ "_fst")
        x2 = ML.Id t2 (ML.name x ++ "_snd")
        v1 = ML.Op (ML.OpFst t1 v)
        v2 = ML.Op (ML.OpSnd t2 v)
    ML.TFun _ _ -> env


refine :: IM.IntMap [Id] -> [(Int,RType)] -> [(Int,RPostType)] -> [(Int,[Id],ML.AValue)] -> PAbst.TypeMap -> PAbst.TypeMap
refine fvMap rtyAssoc rpostAssoc subst typeMap = typeMap'' where
    penv = IM.fromList [ (s,(xs,v)) | (s,xs,v) <- subst ]
    typeMap' = foldl' (\acc (i, rty) -> 
                    let Left !pty = acc IM.! i
                        !fv   = fvMap IM.! i
                        !env  = foldl' (\_env x -> extendEnv x (ML.Var x) _env) M.empty fv
                        !pty' = refinePType penv env rty pty
                    in IM.insert i (Left pty') acc
               ) typeMap rtyAssoc
    typeMap'' = foldl' (\acc (i, rpost) ->
                    let Right !termty = acc IM.! i
                        !fv = fvMap IM.! i
                        !env = foldl' (\_env x -> extendEnv x (ML.Var x) _env) M.empty fv
                        !termty' = refineTermType penv env rpost termty
                    in IM.insert i (Right termty') acc
                ) typeMap' rpostAssoc

