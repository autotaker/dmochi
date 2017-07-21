{-# LANGUAGE ScopedTypeVariables, LambdaCase, FlexibleContexts, BangPatterns, GADTs #-}
module Language.DMoCHi.ML.Refine where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Writer
import           Control.Arrow (first)
import qualified Data.Map as M
import qualified Data.IntMap as IM
import           Data.List(intersperse,foldl',sortBy)
import           Text.PrettyPrint.HughesPJClass hiding(first)
import           Text.Printf
import Debug.Trace

import qualified Language.DMoCHi.ML.Syntax.PNormal as ML
-- import qualified Language.DMoCHi.ML.PrettyPrint.PNormal as ML
import qualified Language.DMoCHi.ML.Syntax.PType as PAbst
import qualified Language.DMoCHi.ML.HornClause as Horn
import qualified Language.DMoCHi.ML.SMT as SMT
import           Language.DMoCHi.ML.SymbolicExec
import           Language.DMoCHi.Common.Id hiding( Id)
import qualified Language.DMoCHi.Common.Id as Id
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
        let as = intersperse ", " [ show (ML.name x) ++ " : " ++ show rty | (x,rty) <- zip xs rtys ] in 
        "{" ++ concat as ++ " | " ++ show cond ++ "}" ++ " -> " ++ show res

instance Show RPostType where
    show (RPostType r rty cond) = 
        "{" ++ show (ML.name r) ++ " : " ++ show rty ++ " | " ++ show cond ++ "}"
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
    clsLookup :: ClosureId -> ClosureInfo
    clsLookup j = clsTbl IM.! unClosureId j
    rtnLookup :: CallId -> ReturnInfo
    rtnLookup j = rtnTbl IM.! unCallId j
    isBase x = case ML.getType x of 
        (ML.TFun _ _) -> False
        _ -> True
    flatten (SVar x) env | isBase x  = (SVar x) : env
                         | otherwise = env
    flatten (P v1 v2) env = flatten v1 (flatten v2 env)
    flatten _ _ = error "genRTypeFactor: flatten: unexpected"
    push = flatten . decompose
    meta_add (Meta i l) s = Meta i (s:l)

    genRType label env = gen (Meta label []) (foldr push [] env)
    genRPostType label path = genPost (Meta label []) path . foldr push []

    -- gen meta env acsr
    --  meta :: 述語の名前につけるメタ情報
    --  env  :: 変数スコープ
    --  acsr :: この関数がどのような値として呼ばれているかを表す識別子
    gen meta env acsr =
        case ML.getType acsr of
            ML.TBool -> return RBool
            ML.TInt  -> return RInt
            ML.TPair _ty1 _ty2 -> RPair <$> gen meta env (AFst acsr) <*> gen meta env (ASnd acsr)
            ML.TFun _ty_args ty_ret -> do
                let cs = [ info | info <- calls, acsr `elem` callAccessors info ]
                if null cs then
                    return (RFun IM.empty)
                else do
                    let cls = closure (clsLookup (calleeId (head cs)))
                    let (_,xs',_) = clsBody cls
                    xs <- mapM ML.alphaTId xs' 
                    {- Example:let rec f x =   <- f : { x : int | P_f(x) } -> { r : int | Q_f(x,r) }
                                   let rec g y = f in  <- g : { y : int | P_g(x,y) } -> 
                                                              { ({z : int | P_g1(x,y,z)} -> ... ) | Q_g(x,y) }
                                   let f1 = g 0 in 
                                   f1 (x-1) -}
                    let env' = foldl' (flip push) env xs
                    fmap (RFun . IM.fromList) $ forM cs $ \info -> do
                        let j = callId info
                            path = callContext info
                        -- 変数スコープの例
                        -- fの中でxが参照できたり、sの第一要素の中でsの第二要素が参照できることに注意
                        -- { x : int, f : { y : int | P(y,x) } -> { r : int | Q(r,y,x) } | U(x) } -> 
                        --      { s : ({ z : int | R(z,s.snd,x) } -> { t : int | S(t,z,s.snd,x) }) * int | T(x,s.snd) }
                        arg_tys <- forM (zip [(0::Int)..] xs') $ \(i,xi) -> -- for asscessors, we use unrenamed name
                            gen (meta_add meta ("pre_" ++ show i)) env' (AVar j xi)
                        p1 <- freshInt
                        let rv = retValue $ rtnLookup j
                        posTy <- genPost (meta_add meta "post") path env' (fmap (const (ARet j ty_ret)) rv)
                        return (unCallId j, RFunAssoc xs arg_tys (Formula (meta_add meta "pre") p1 path env') posTy)
    genPost _ _ _ Nothing = return RPostTypeFailure
    genPost meta path env (Just acsr) = do
        rj <- ML.TId (ML.getType acsr) <$> identify "r"
        let env' = push rj env
        pty <- gen meta env' acsr
        p0 <- freshInt
        return $ RPostType rj pty (Formula meta p0 path env')
                                                           
evalRTypeA :: M.Map Id (RType,SValue) -> ML.Atom -> (RType,SValue)
evalRTypeA env = go  where
    go (ML.Atom l arg _) = case (l, arg) of
        (ML.SVar, x) -> env M.! x
        (ML.SLiteral, ML.CInt i) -> (RInt, Int i)
        (ML.SLiteral, ML.CBool b) -> (RBool, Bool b)
        (ML.SLiteral, ML.CUnit) -> error "unexpected pattern"
        (ML.SBinary, ML.BinArg op v1 v2) ->
            let sv1 = snd $ go v1
                sv2 = snd $ go v2
            in case op of
                ML.SAdd -> (RInt, Add sv1 sv2)
                ML.SSub -> (RInt, Sub sv1 sv2)
                ML.SMul -> (RInt, Mul sv1 sv2)
                ML.SDiv -> (RInt, Div sv1 sv2)
                ML.SEq -> (RBool, Eq sv1 sv2)
                ML.SLt -> (RBool, Lt sv1 sv2)
                ML.SLte -> (RBool, Lte sv1 sv2)
                ML.SAnd -> (RBool, And sv1 sv2)
                ML.SOr -> (RBool, Or sv1 sv2)
        (ML.SUnary, ML.UniArg op v1) ->
            let (rty1, sv1) = go v1 in
            case op of
                ML.SNot -> (RBool, Not sv1)
                ML.SNeg -> (RInt, Neg sv1)
                ML.SFst -> let (RPair a _, P sv _) = (rty1, sv1) in (a,sv)
                ML.SSnd -> let (RPair _ b, P _ sv) = (rty1, sv1) in (b,sv)

decomposePairName :: Id -> (Id, Id)
decomposePairName x = (x1, x2)
    where
    x1 = ML.TId t1 (reserved $ show (ML.name x) ++ "_fst")
    x2 = ML.TId t2 (reserved $ show (ML.name x) ++ "_snd")
    ML.TPair t1 t2 = ML.getType x

-- input x : Id
-- output v : SValue s.t. 
--        - getType v == getType x
--        - for any free variable x in v, getType v `in` [TBool, TInt, TFun]
decompose :: Id -> SValue
decompose x = case ML.getType x of
    ML.TInt -> SVar x
    ML.TBool -> SVar x
    ML.TPair _ _ -> 
        let (x1, x2) = decomposePairName x in
        P (decompose x1) (decompose x2)
    ML.TFun _ _ -> SVar x

type W m a = WriterT ([(CompTreePath,Horn.Clause)],([(UniqueKey,RType)],[(UniqueKey,RPostType)])) m a


refineCGen :: forall m.(MonadFix m, MonadId m, MonadIO m, MonadLogger m) => 
              ML.Program -> FilePath -> Bool -> Int -> Trace -> 
              m (Maybe (Bool,([Horn.Clause],([(UniqueKey,RType)],[(UniqueKey,RPostType)]))))
refineCGen prog traceFile contextSensitive foolThreshold trace = do
    (genv, (Log consts calls closures returns branches letexps), compTree) <- symbolicExec prog trace
    liftIO $ writeFile traceFile (renderCompTree compTree)
    logPretty "refine" LevelDebug "constraints" $ map (PPrinted . text . show) consts
    let cs = map fromSValue consts
    isFeasible <- liftIO $ SMT.sat cs
    isFool <- if isFeasible then return False 
                            else fmap not $ liftIO $ SMT.sat (take (length cs - foolThreshold) cs)
    when isFool $ logInfoNS "refine" "this error trace is fool"
    let sortClauses :: [(CompTreePath,Horn.Clause)] -> [Horn.Clause]
        sortClauses = map snd . sortBy (compare `on` (reverse . fst))
    if isFeasible then
        return Nothing
    else fmap (Just . (,) isFool . first sortClauses) $ execWriterT $ do
        let dump str l = logPretty "refine" LevelDebug str (PPrinted doc)
                where doc = vcat $ map (text. show) l
        dump "Calls" calls
        dump "Closures" closures
        dump "Returns" returns
        dump "Branches" branches
        dump "Letexps" letexps
        let (gen,genP) = genRTypeFactory calls closures returns
        let addFuncBinding :: UniqueKey -> RType -> W m ()
            addFuncBinding label ty = tell ([],([(label,ty)],[]))
            addExpBinding :: UniqueKey -> RPostType -> W m ()
            addExpBinding label ty = tell ([],([],[(label,ty)]))
            addClause :: (CompTreePath,Horn.Clause) -> W m ()
            addClause c = tell ([c],([],[]))

        let callTbl :: M.Map (CallId,UniqueKey) CallId
            callTbl = M.fromList [ ((pcallId info,callLabel info),callId info)| info <- calls ]
            branchMap :: M.Map (CallId,UniqueKey) Bool
            branchMap = M.fromList [ ((bCallId info,branchId info),direction info) | info <- branches ]
            letMap :: M.Map (CallId, UniqueKey) (CompTreePath, Maybe SValue)
            letMap = M.fromList [ ((lCallId info,lLabel info),(lContext info,evalValue info)) | info <- letexps ]

        let showC :: Either SValue LFormula -> String
            showC (Left sv) = show sv
            showC (Right fml) = show fml
            showCs :: [Either SValue LFormula] -> String
            showCs = concat . intersperse ", " . map showC
        let genClause :: Maybe LFormula -> [Either SValue LFormula] -> Horn.Clause
            genClause hd body = Horn.Clause chd cbody
                where
                    f fml@(Formula meta i _ svs) 
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
            check env cs callSite _e@(ML.Exp l arg sty key) tau = 
                let valueCase :: ML.Value -> W m ()
                    valueCase v = case tau of
                        RPostType _ _ _ -> do
                            sv <- genSValue env v
                            let tau' = substPostType (M.singleton (posName tau) sv) tau
                            _sv <- checkValue env cs callSite v sv (posType tau')
                            clause cs (posCond tau')
                        RPostTypeFailure -> do
                            let s = render $ pPrint v
                            error $ "This value "++ s ++ " cannot have the refinement type" ++ show tau
                in case (l,arg) of
                    (ML.SLiteral, _) -> valueCase $ ML.Value l arg sty key
                    (ML.SVar, _)     -> valueCase $ ML.Value l arg sty key
                    (ML.SPair, _)    -> valueCase $ ML.Value l arg sty key
                    (ML.SLambda, _)  -> valueCase $ ML.Value l arg sty key
                    (ML.SBinary, _)  -> valueCase $ ML.Value l arg sty key
                    (ML.SUnary, _)   -> valueCase $ ML.Value l arg sty key
                    (ML.SLet, (x, (ML.LExp l1 arg1 sty1 key1), e)) -> 
                        let atomCase v = check (M.insert x (evalRTypeA env v) env) cs callSite e tau
                            exprCase e' = do
                                let (path,letv) = letMap M.! (callSite, key1)
                                tau' <- genP (show (ML.name x) ++ "_" ++ show key1) path (M.keys env) (fmap (const (AVar callSite x)) letv)
                                addExpBinding key1 tau'
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
                        in case (l1, arg1) of
                            (ML.SLiteral, _) -> atomCase (ML.Atom l1 arg1 sty1)
                            (ML.SVar, _)     -> atomCase (ML.Atom l1 arg1 sty1)
                            (ML.SBinary, _)  -> atomCase (ML.Atom l1 arg1 sty1)
                            (ML.SUnary, _)   -> atomCase (ML.Atom l1 arg1 sty1)
                            (ML.SPair, _)   -> exprCase $ ML.Exp l1 arg1 sty1 key1
                            (ML.SLambda, _) -> exprCase $ ML.Exp l1 arg1 sty1 key1
                            (ML.SBranch, _) -> exprCase $ ML.Exp l1 arg1 sty1 key1
                            (ML.SFail, _) -> exprCase $ ML.Exp l1 arg1 sty1 key1
                            (ML.SOmega, _) -> exprCase $ ML.Exp l1 arg1 sty1 key1
                            (ML.SApp, (f, vs)) -> do
                                let (RFun fassoc,_) = env M.! f
                                    j = callTbl M.! (callSite,key1)
                                    Just ty_f = IM.lookup (unCallId j) fassoc
                                svs <- mapM (genSValue env) vs
                                let subst = M.fromList $ zip (argNames ty_f) svs
                                let tys = map (substRType subst) (argTypes ty_f)
                                _svs <- mapM (\(v,sv,theta) -> checkValue env cs callSite v sv theta) $ zip3 vs svs tys
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
                            (ML.SRand, _) -> do
                                let x' = decompose x 
                                    env' = M.insert x (RInt,x') env
                                check env' cs callSite e tau
                    (ML.SLetRec, (fs, e)) -> do
                        as <- forM fs $ \(f,_) -> do
                            ty <- gen (show $ ML.name f)  (M.keys env) (AVar callSite f)
                            return (f, (ty, decompose f))
                        let env' = foldr (uncurry M.insert) env as
                        forM_ fs $ \(f, v) -> do
                            let (key_f,xs,e_f) = case v of
                                    ML.Value ML.SLambda (xs,e_f) _ key_f -> (key_f,xs,e_f)
                                    _ -> error "unexpected"
                            theta <- checkFunDef env' cs callSite (key_f,xs,e_f) (fst $ env' M.! f)
                            addFuncBinding key_f theta
                        check env' cs callSite e tau
                    (ML.SAssume, (v,e)) -> do
                        let (_,sv) = evalRTypeA env v
                        let cs' = Left sv : cs
                        check env cs' callSite e tau
                    (ML.SBranch, (e1, e2)) -> do
                        let b = branchMap M.! (callSite,key)
                        if b 
                        then check env cs callSite e1 tau
                        else check env cs callSite e2 tau
                    (ML.SFail, _) -> case tau of
                        RPostTypeFailure -> failClause cs
                        _ -> error $ "This failure term cannot have the refinement type" ++ show tau
                    (ML.SOmega, _) -> return ()
            checkFunDef env cs _callSite (_,xs,e0) theta = do
                let RFun fassoc = theta 
                forM_ (IM.assocs fassoc) $ \(j,ty_f) -> do
                    let xsj = argNames ty_f
                        ty_xsj = argTypes ty_f
                        env' = foldr (uncurry M.insert) env (zip xs (zip ty_xsj (map decompose xsj))) 
                        cs' = Right (preCond ty_f) : cs
                    check env' cs' (CallId j) e0 (resType ty_f)
                return theta
            genSValue :: M.Map Id (RType, SValue) -> ML.Value -> W m SValue
            genSValue env = fix $ \go (ML.Value l arg sty _) -> 
                case (l, arg) of
                    (ML.SLiteral, _) -> pure $ snd $ evalRTypeA env (ML.Atom l arg sty)
                    (ML.SVar, _)     -> pure $ snd $ evalRTypeA env (ML.Atom l arg sty)
                    (ML.SBinary, _)  -> pure $ snd $ evalRTypeA env (ML.Atom l arg sty)
                    (ML.SUnary, _)   -> pure $ snd $ evalRTypeA env (ML.Atom l arg sty)
                    (ML.SPair, (v1, v2)) -> P <$> go v1 <*> go v2
                    (ML.SLambda, _) -> SVar . ML.TId sty <$> identify "fun"
            checkValue :: M.Map Id (RType, SValue) -> [Either SValue LFormula] -> CallId -> ML.Value -> SValue -> RType -> W m SValue
            checkValue env cs callSite = fix $ \go (ML.Value l arg sty key) sv rty ->
                let atomCase :: ML.Atom -> W m SValue
                    atomCase av = let (rty', sv') = evalRTypeA env av in sv' <$ subType cs rty' rty 
                in case (l, arg, sv, rty) of
                    (ML.SLiteral, _, _, _) -> atomCase (ML.Atom l arg sty)
                    (ML.SVar, _, _, _) -> atomCase (ML.Atom l arg sty)
                    (ML.SBinary, _, _, _) -> atomCase (ML.Atom l arg sty)
                    (ML.SUnary, _, _, _) -> atomCase (ML.Atom l arg sty)
                    (ML.SPair, (v1, v2), P sv1 sv2, RPair rty1 rty2) -> 
                        P <$> go v1 sv1 rty1 <*> go v2 sv2 rty2
                    (ML.SPair, _, _, _) -> error "checkValue: Pair: unexpected pattern"
                    (ML.SLambda, (xs,e),_,_) -> sv <$ checkFunDef env cs callSite (key, xs, e) rty
                
            clause cs fml = do
                -- liftIO $ printf "Clause: %s ==> %s\n" (showCs cs) (show fml)
                let Formula _ _ path _ = fml
                addClause (path,genClause (Just fml) cs)
            subType cs ty1 ty2 = do
                -- liftIO $ printf "SubType: %s |- %s <: %s\n" (showCs cs) (show ty1) (show ty2)
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
                    (_, _) -> error "subType: unexpected pattern"
            subTypePost cs (RPostType r1 ty1 cond1) (RPostType r2 ty2 cond2) = do
                let subst = M.singleton r1 (decompose r2)
                let cs' = Right (substLFormula subst cond1) : cs
                clause cs' cond2
                subType cs' (substRType subst ty1) ty2
            subTypePost _ RPostTypeFailure RPostTypeFailure = return ()
            subTypePost cs ty1 ty2 = error $ "subTypePost: unexpected subtyping:" ++ show (cs,ty1,ty2) 
            failClause cs = do
                -- liftIO $ printf "Clause: %s ==> _|_\n" (showCs cs) 
                addClause ([10],genClause Nothing cs)
        
        genv' <- fmap M.fromList $ forM (M.toList genv) $ \(f,_) -> do
            ty <- gen (show $ ML.name f) [] (AVar (CallId 0) f)
            return (f,(ty,decompose f))
        dump "RefineEnv" (M.assocs genv')
        forM_ (ML.functions prog) $ \(f,key,xs,e) -> do
            theta <- checkFunDef genv' [] (CallId 0) (key,xs,e) (fst $ genv' M.! f)
            addFuncBinding key theta
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
    Neg v -> Horn.Sub (Horn.Int 0) (termOfValue v)
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
substPostType _ RPostTypeFailure = RPostTypeFailure

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
    Mul sv1 sv2 -> Mul (substSValue subst sv1) (substSValue subst sv2)
    Div sv1 sv2 -> Div (substSValue subst sv1) (substSValue subst sv2)
    Eq  sv1 sv2 -> Eq  (substSValue subst sv1) (substSValue subst sv2)
    Lt  sv1 sv2 -> Lt  (substSValue subst sv1) (substSValue subst sv2)
    Lte sv1 sv2 -> Lte (substSValue subst sv1) (substSValue subst sv2)
    And sv1 sv2 -> And (substSValue subst sv1) (substSValue subst sv2)
    Or  sv1 sv2 -> Or (substSValue subst sv1) (substSValue subst sv2)
    Not sv1     -> Not (substSValue subst sv1)
    Neg sv1     -> Neg (substSValue subst sv1)
    C _       -> error "substSValue: substituting closure is not supported"
    Int _       -> _sv
    Bool _      -> _sv


-- penv :: i -> (xs,fml) s.t. P_{i} = \xs. fml
-- env : mapping from variables in the formula to values in PType 
refineTermType :: IM.IntMap ([Id], ML.Atom) -> M.Map (Id.Id String) ML.Atom -> RPostType -> PAbst.TermType -> PAbst.TermType
refineTermType penv env (RPostType r rty fml) (abst_r, abst_rty, abst_fml) = (abst_r, abst_rty', abst_fml')
    where
    env' = extendEnv r (ML.mkVar abst_r) env
    abst_rty' = refinePType penv env' rty abst_rty
    phi' = refineLFormula penv env' fml
    abst_fml' = PAbst.updateFormula phi' abst_fml
refineTermType _ _ RPostTypeFailure termType = termType

refinePType :: IM.IntMap ([Id], ML.Atom) -> M.Map (Id.Id String) ML.Atom -> RType -> PAbst.PType -> PAbst.PType
refinePType _ _ RBool PAbst.PBool = PAbst.PBool
refinePType _ _ RInt PAbst.PInt = PAbst.PInt
refinePType penv env (RPair rty1 rty2) (PAbst.PPair ty pty1 pty2) = 
    PAbst.PPair ty (refinePType penv env rty1 pty1) (refinePType penv env rty2 pty2)

refinePType penv env (RFun fassoc) (PAbst.PFun ty pty_x0 pty_r0) = pty'
    where
    pty' = uncurry (PAbst.PFun ty) $ foldl' f (pty_x0, pty_r0) (IM.elems fassoc)
    f ((abst_xs, abst_ptys, abst_fml), pty_r) as = pre `seq` abst_ptys' `seq` (pty_x', pty_r')
        where
        env'  = foldr (uncurry extendEnv) env (zip (argNames as) (map ML.mkVar abst_xs))
        pre   = refineLFormula penv env' (preCond as)
        abst_ptys' = zipWith (refinePType penv env') (argTypes as) abst_ptys
        pty_x' = (abst_xs, abst_ptys', PAbst.updateFormula pre abst_fml)
        pty_r' = refineTermType penv env' (resType as) pty_r
refinePType _ _ _ _ = error "refinePType: unexpected pattern"

refineLFormula :: IM.IntMap ([Id], ML.Atom) -> M.Map (Id.Id String) ML.Atom -> LFormula -> PAbst.Formula
refineLFormula _ _ (Formula _ _ _ []) = ML.mkLiteral (ML.CBool True)  {- this is ad-hoc technique to avoid lookup error: 
                                                             if args is null, penv may not contain the corresponding formula -}
refineLFormula penv env fml = phi' where
    Formula _ i _ args = fml
    (args_phi, phi) = penv IM.! i
    env' = M.union (M.fromList $ zip (map ML.name args_phi) (map recover args)) env
    recover (SVar x) = env M.! (ML.name x)
    recover _ = error "refineLFormula: recover: unexpected pattern"
    phi' = phi & fix (\go (ML.Atom l arg _) -> case (l,arg) of
        (ML.SVar, x) -> case M.lookup (ML.name x) env' of
            Just r -> r
            Nothing -> error $ "Error!:" ++ show (ML.name x, env)
        (ML.SLiteral, ML.CInt i) -> ML.mkLiteral $ ML.CInt i
        (ML.SLiteral, ML.CBool b) -> ML.mkLiteral $ ML.CBool b
        (ML.SLiteral, ML.CUnit) -> error "unexpected pattern"
        (ML.SBinary, ML.BinArg op a b) -> case op of
            ML.SAdd -> ML.mkBin ML.SAdd (go a) (go b)
            ML.SSub -> ML.mkBin ML.SSub (go a) (go b)
            ML.SMul -> ML.mkBin ML.SMul (go a) (go b)
            ML.SDiv -> ML.mkBin ML.SDiv (go a) (go b)
            ML.SEq  -> ML.mkBin ML.SEq (go a) (go b)
            ML.SLt  -> ML.mkBin ML.SLt (go a) (go b)
            ML.SLte -> ML.mkBin ML.SLte (go a) (go b)
            ML.SAnd -> ML.mkBin ML.SAnd (go a) (go b)
            ML.SOr  -> ML.mkBin ML.SOr  (go a) (go b)
        (ML.SUnary, ML.UniArg op a) -> case op of
            ML.SNot -> ML.mkUni ML.SNot (go a)
            ML.SNeg -> ML.mkUni ML.SNeg (go a)
            ML.SFst -> ML.mkUni ML.SFst (go a)
            ML.SSnd -> ML.mkUni ML.SSnd (go a))

extendEnv :: Id -> ML.Atom -> M.Map (Id.Id String) ML.Atom -> M.Map (Id.Id String) ML.Atom
extendEnv x v env = case ML.getType x of
    ML.TInt -> M.insert (ML.name x) v env
    ML.TBool -> M.insert (ML.name x) v env
    ML.TPair _ _ -> extendEnv x1 v1 $ extendEnv x2 v2 env
        where
        (x1, x2) = decomposePairName x
        v1 = ML.mkUni ML.SFst v
        v2 = ML.mkUni ML.SSnd v
    ML.TFun _ _ -> env


refine :: M.Map UniqueKey [Id] -> [(UniqueKey,RType)] -> [(UniqueKey,RPostType)] -> [(Int,[Id],ML.Atom)] -> PAbst.TypeMap -> PAbst.TypeMap
refine fvMap rtyAssoc rpostAssoc subst typeMap = typeMap'' where
    penv = IM.fromList [ (s,(xs,v)) | (s,xs,v) <- subst ]
    typeMap' = foldl' (\acc (i, rty) -> 
                    let Left !pty = acc M.! i
                        !fv   = fvMap M.! i
                        !env  = foldl' (\_env x -> extendEnv x (ML.mkVar x) _env) M.empty fv
                        !pty' = refinePType penv env rty pty
                    in M.insert i (Left pty') acc
               ) typeMap rtyAssoc
    typeMap'' = foldl' (\acc (i, rpost) ->
                    let Right !termty = acc M.! i
                        !fv = fvMap M.! i
                        !env = foldl' (\_env x -> extendEnv x (ML.mkVar x) _env) M.empty fv
                        !termty' = refineTermType penv env rpost termty
                    in M.insert i (Right termty') acc
                ) typeMap' rpostAssoc

