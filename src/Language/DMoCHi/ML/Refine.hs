{-# LANGUAGE ScopedTypeVariables, LambdaCase, FlexibleContexts, BangPatterns #-}
module Language.DMoCHi.ML.Refine where

import qualified Language.DMoCHi.ML.Syntax.PNormal as ML
import qualified Language.DMoCHi.ML.PrettyPrint.PNormal as ML
import qualified Language.DMoCHi.ML.PredicateAbstraction as PAbst
import qualified Data.Map as M
import qualified Language.DMoCHi.ML.SMT as SMT
import Control.Applicative
import Control.Monad
import Control.Monad.Writer
import Control.Monad.State.Strict
import Control.Arrow (first)
import qualified Data.IntMap as IM
import Language.DMoCHi.Common.Id
import Language.DMoCHi.Common.Util
import Data.List(intersperse,nub,foldl')
import qualified Language.DMoCHi.ML.HornClause as Horn
import Debug.Trace
import Text.PrettyPrint

type Trace = [Bool]
newtype CallId = CallId { unCallId :: Int } deriving (Eq,Ord)
newtype ClosureId = ClosureId { unClosureId :: Int } deriving (Eq,Ord)

instance Show CallId where
    show (CallId x) = show x

instance Show ClosureId where
    show (ClosureId x) = show x

type Constraint = SValue -- must have the sort Bool
data CallInfo = CallInfo { calleeId :: ClosureId   -- 呼び出されたクロージャの識別子
                         , callLabel :: Int     -- 対応する関数呼び出しのラベル
                         , pcallId  :: CallId   -- 親関数呼び出しの識別子
                         , callId   :: CallId   -- 関数呼び出しの識別子
                     } deriving Show

-- クロージャ生成の情報
data ClosureInfo = ClosureInfo { label :: Int -- 対応する関数定義のラベル
                               , closureId :: ClosureId -- 生成されたクロージャの識別子
                               , cCallId :: CallId -- クロージャ生成時の関数呼び出し識別子
                               } deriving Show
-- 関数返り値の情報
data ReturnInfo = ReturnInfo { rcallId :: CallId -- 関数呼び出しの識別子
                             , argValues :: [SValue] -- 引数
                             , retValue :: Maybe SValue -- 返り値(ないときはfailを表す)
                             , retCallId :: CallId -- 関数呼び出し終了時のCallId(exclusive)
                             } deriving Show

-- Let式の評価結果情報
data LetExpInfo = LetExpInfo { lCallId :: CallId -- 評価時の親関数呼び出し識別子
                             , lLabel :: Int -- 呼び出されたlet式のラベル
                             , evalValue :: Maybe SValue -- 評価結果(ないときはfailを表す)
                             } deriving Show

-- 分岐情報
data BranchInfo = BranchInfo { bCallId   :: CallId, 
                               branchId  :: Int,
                               direction :: Bool} deriving Show


-- Symbolic Values
data SValue = SVar Id
            | Int Integer
            | Bool Bool
            | P SValue SValue
            | Add SValue SValue
            | Sub SValue SValue
            | Eq SValue SValue
            | Lt SValue SValue
            | Lte SValue SValue
            | And SValue SValue
            | Or SValue SValue
            | Not SValue
--            | Iff SValue SValue
            | C Closure

instance ML.HasType SValue where
    getType (SVar x)  = ML.getType x
    getType (Int i)   = ML.TInt
    getType (Bool i)  = ML.TBool
    getType (P v1 v2) = ML.TPair (ML.getType v1) (ML.getType v2)
    getType (Add _ _) = ML.TInt
    getType (Sub _ _) = ML.TInt
    getType (Eq _ _)  = ML.TBool
    getType (Lt _ _)  = ML.TBool
    getType (Lte _ _) = ML.TBool
    getType (And _ _) = ML.TBool
    getType (Or  _ _) = ML.TBool
    getType (Not _) = ML.TBool
    getType (C cls)   = ML.getType cls


instance Show SValue where
    showsPrec d (SVar x) = 
        showParen (d >= 3) $ showString (ML.name x) . showString " : " . shows (ML.getType x)
    showsPrec _ (Int i) = shows i
    showsPrec _ (Bool b) = shows b
    showsPrec _ (P v1 v2) = 
        showString "(" .  shows v1 . showString ", " . shows v2 . showString ")"
    showsPrec d (Add v1 v2) =
        showParen (d >= 6) $ (showsPrec 6 v1) . (showString " + ") . (showsPrec 6 v2)
    showsPrec d (Sub v1 v2) = 
        showParen (d >= 6) $ (showsPrec 6 v1) . (showString " - ") . (showsPrec 6 v2)
    showsPrec d (Eq v1 v2) = 
        showParen (d >= 5) $ (showsPrec 5 v1) . (showString " == ") . (showsPrec 5 v2)
    showsPrec d (Lt v1 v2) = 
        showParen (d >= 5) $ (showsPrec 5 v1) . (showString " < ") . (showsPrec 5 v2)
    showsPrec d (Lte v1 v2) = 
        showParen (d >= 5) $ (showsPrec 5 v1) . (showString " <= ") . (showsPrec 5 v2)
    showsPrec d (And v1 v2) = 
        showParen (d >= 4) $ (showsPrec 4 v1) . (showString " && ") . (showsPrec 4 v2)
    showsPrec d (Or v1 v2) = 
        showParen (d >= 3) $ (showsPrec 3 v1) . (showString " || ") . (showsPrec 3 v2)
    showsPrec d (Not v1) = 
        showParen (d >= 8) $ (showString "not ") . showsPrec 8 v1
    showsPrec d (C cls) = showsPrec d cls
                       
data Closure = Cls ML.FunDef ClosureId {- Ident -} Env

instance ML.HasType Closure where
    getType (Cls fdef _ _) = ML.getType fdef

instance Show Closure where
    showsPrec d (Cls i x _) = showParen (d > app_prec) $
        showString "Closure " . showsPrec (app_prec+1) (ML.ident i) . showChar ' ' . showsPrec (app_prec + 1) x
        where
        app_prec = 10
type Env = M.Map Id SValue
type Id = ML.Id

type Log = ([Constraint],[CallInfo],[ClosureInfo],[ReturnInfo],([BranchInfo],[LetExpInfo]))

type M m a = StateT S (WriterT Log m) a
data S = S { callCounter :: !Int
           , clsCounter  :: !Int
           , cTrace      :: !Trace }

incrCall :: S -> S
incrCall (S x y z) = S (x+1) y z

incrCls :: S -> S
incrCls (S x y z) = S x (y+1) z

pop :: S -> S
pop (S x y z) = S x y (tail z)


fromSValue :: SValue -> ML.Value
fromSValue = \case
    SVar x -> ML.Atomic $ ML.Var x
    Int i  -> ML.Atomic $ ML.CInt i
    Bool b -> ML.Atomic $ ML.CBool b
    P v1 v2 -> ML.Pair (fromSValue v1) (fromSValue v2)
    Add v1 v2 -> bin ML.OpAdd v1 v2
    Sub v1 v2 -> bin ML.OpSub v1 v2
    Eq v1 v2 -> bin ML.OpEq v1 v2
    Lt v1 v2 -> bin ML.OpLt v1 v2
    Lte v1 v2 -> bin ML.OpLte v1 v2
    And v1 v2 -> bin ML.OpAnd v1 v2
    Or v1 v2 -> bin ML.OpOr v1 v2
    Not v1 -> unary ML.OpNot v1
    C _ -> error "Cannot convert a closure to a syntactic value"
    where
    bin f v1 v2 = 
        let ML.Atomic !av1 = fromSValue v1 in
        let ML.Atomic !av2 = fromSValue v2 in
        ML.Atomic $ ML.Op (f av1 av2)
    unary f v1 = 
        let ML.Atomic !av1 = fromSValue v1 in
        ML.Atomic $ ML.Op (f av1)
    

symbolicExec :: forall m. (MonadId m, MonadFix m) => ML.Program -> Trace -> m (M.Map Id SValue, Log)
symbolicExec prog trace = 
    runWriterT $ evalStateT (genEnv >>= (\genv -> do
        r <- eval (CallId 0) genv (ML.mainTerm prog)
        case r of
            Just sv -> error "symbolicExec: This error trace cannot reach to any failure!"
            Nothing -> return genv)) (S 1 0 trace)
    where
    -- preprocessing
    genEnv = mfix $ \genv -> do
        es <- forM (ML.functions prog) $ \(f, fdef) -> do
            c <- genClosure (CallId 0) fdef genv
            return (f,C c)
        return $ M.fromList es
    eval :: CallId -> Env -> ML.Exp -> M m (Maybe SValue)
    eval callSite env _e = case _e of
        ML.Value v -> do
            sv <- evalV callSite env v 
            return $ Just sv
        ML.Let _ x lv e -> do
            r <- evalLV callSite env lv
            case r of
                Just sv -> eval callSite (M.insert x sv env) e
                Nothing -> return Nothing
        -- ML.Fun fdef -> Just . C <$> genClosure callSite fdef env
        ML.Assume _ v e -> do
            constrain (evalA env v)
            eval callSite env e
        ML.Fail _ -> return Nothing
        ML.Branch _ i e1 e2 -> do
            b <- consume
            branch (BranchInfo callSite i b)
            if b then
                eval callSite env e1
            else
                eval callSite env e2

    evalV :: CallId -> Env -> ML.Value -> M m SValue
    evalV _ env (ML.Atomic av) = pure $ evalA env av
    evalV callSite env (ML.Pair v1 v2) = P <$> evalV callSite env v1 <*> evalV callSite env v2
    evalV callSite env (ML.Fun fdef) = C <$> genClosure callSite fdef env
    evalA :: Env -> ML.AValue -> SValue
    evalA env = \case
        ML.Var x -> case M.lookup x env of Just v -> v 
                                           Nothing -> error $ "lookup error: key " ++ (show x)
        ML.CInt x -> Int x
        ML.CBool x -> Bool x
        ML.Op op -> case op of
            ML.OpAdd v1 v2 -> Add (evalA env v1) (evalA env v2)
            ML.OpSub v1 v2 -> Sub (evalA env v1) (evalA env v2)
            ML.OpEq  v1 v2  -> Eq (evalA env v1) (evalA env v2)
            ML.OpLt  v1 v2  -> Lt (evalA env v1) (evalA env v2)
            ML.OpLte v1 v2 -> Lte (evalA env v1) (evalA env v2)
            ML.OpAnd v1 v2 -> And (evalA env v1) (evalA env v2)
            ML.OpOr  v1 v2 -> Or (evalA env v1) (evalA env v2)
            ML.OpFst _ v -> 
                let P sv _ = evalA env v in sv
            ML.OpSnd _ v -> 
                let P _ sv = evalA env v in sv
            ML.OpNot v1 -> Not (evalA env v1)
    evalLV :: CallId -> Env -> ML.LetValue -> M m (Maybe SValue)
    evalLV callSite env = \case 
        ML.LValue v -> pure $ Just (evalA env v)
        ML.LApp _ label f vs -> do
            svs <- mapM (evalV callSite env) vs
            let C (Cls fdef clsId env') = env M.! f
            let xs = ML.args fdef
                e0 = ML.body fdef
            j <- newCall label callSite clsId
            let env'' = foldr (uncurry M.insert) env' $ zip xs svs
            r <- eval j env'' e0
            ret_cid <- callCounter <$> get
            retval (ReturnInfo j svs r (CallId ret_cid))
            return r
        -- ML.LFun fdef -> Just . C <$> genClosure callSite fdef env
        ML.LExp label e -> do
            r <- eval callSite env e
            letexp (LetExpInfo callSite label r)
            return r
        ML.LRand -> Just . SVar . ML.Id ML.TInt <$> freshId "rand"

    -- utilities
    constrain :: Constraint -> M m ()
    constrain c = tell ([c],[],[],[],([],[]))
    branch :: BranchInfo -> M m ()
    branch c = tell ([],[],[],[],([c],[]))
    retval :: ReturnInfo -> M m ()
    retval c = tell ([],[],[],[c],([],[]))
    letexp c = tell ([],[],[],[],([],[c]))
    newCall :: Int -> CallId -> ClosureId -> M m CallId
    newCall i pcall clsId = do
        j <- callCounter <$> get
        modify incrCall
        tell ([],[CallInfo clsId i pcall (CallId j)],[],[],([],[]))
        return (CallId j)
    genClosure :: CallId -> ML.FunDef -> Env -> M m Closure
    genClosure callSite fdef env = do
        j <- clsCounter <$> get
        modify incrCls
        tell ([],[],[ClosureInfo (ML.ident fdef) (ClosureId j) callSite],[],([],[]))
        return (Cls fdef (ClosureId j) env)
    consume :: M m Bool
    consume = do
        b <- head . cTrace <$> get
        modify pop
        return b

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
data LFormula = Formula Meta Int [SValue]
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
    show (Formula (Meta l accessors) i vs) = 
        let s = concat $ intersperse "," $ map show vs
            smeta = "{" ++ concat (intersperse "." (l : reverse accessors))++ "}" in
        "P" ++ smeta ++ "_" ++ show i ++ "(" ++ s ++ ")"




type RTypeGen m = (String -> [Id] -> SValue -> m RType,          -- Refinement type generator for values
                   String -> [Id] -> Maybe SValue -> m RPostType -- Refinement type generator for let expressions
                   )

genRTypeFactory :: MonadId m => [CallInfo] -> [ClosureInfo] -> [ReturnInfo] -> RTypeGen m
genRTypeFactory calls closures returns = (genRType, genRPostType)
    where
    genRType :: MonadId m => String -> [Id] -> SValue -> m RType
    genRType label = gen (0,maxBound) (Meta label []) . foldr push []
    genRPostType :: MonadId m => String -> [Id] -> Maybe SValue -> m RPostType
    genRPostType label = genPost (0,maxBound) (Meta label []) . foldr push []
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
    gen lim meta env (C (Cls fdef i _)) = do  
        let cs = [ callId info | info <- calls, 
                                 calleeId info == i,
                                 unCallId (callId info) > fst lim
                                 -- unCallId (callId info) < snd lim
                                 ] -- TODO Improve Impl
            xs  = ML.args fdef
            ML.TFun ty_args ty_ret = ML.getType fdef
        as <- forM cs $ \j -> do
            let ReturnInfo _ arg_vs mv ret_cid = rtnTbl IM.! (unCallId j)
            let xsj = [ ML.Id ty_arg (ML.name x) | (x,ty_arg) <- zip xs ty_args ]
            let lim' = (unCallId j, unCallId ret_cid)
            let env' = (foldl' (flip push) env xsj)
            arg_tys <- forM (zip [(0::Int)..] arg_vs) $ \(i,arg_v) -> 
                            gen lim' (meta_add meta ("pre_"++show i)) env' arg_v
            posTy <- genPost lim' (meta_add meta "post") env' mv
            p1 <- freshInt
            return (unCallId j,RFunAssoc xsj arg_tys (Formula (meta_add meta "pre") p1 env') posTy)
        return $ RFun $ IM.fromList as
    genPost lim meta env mv = case mv of
        Just v -> do
            rj <- ML.Id (ML.getType v) <$> freshId "r"
            let env' = push rj env
            pty <- gen lim meta env' v
            p0 <- freshInt
            return $ RPostType rj pty (Formula meta p0 env')
        Nothing -> return RPostTypeFailure

    isBase x = case ML.getType x of 
        (ML.TFun _ _) -> False
        _ -> True
    flatten (SVar x) env | isBase x  = (SVar x) : env
                         | otherwise = env
    flatten (P v1 v2) env = flatten v1 (flatten v2 env)
    push = flatten . decompose

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

type W m a = WriterT ([Horn.Clause],([(Int,RType)],[(Int,RPostType)])) m a

refineCGen :: forall m.(MonadFix m, MonadId m, MonadIO m) => 
              ML.Program -> Trace -> 
              m (Maybe ([Horn.Clause],([(Int,RType)],[(Int,RPostType)])))
refineCGen prog trace = do
    (genv, (consts,calls,closures,returns,(branches,letexps))) <- symbolicExec prog trace
    liftIO $ print consts
    isFeasible <- liftIO $ SMT.sat (map fromSValue consts)
    if isFeasible then
        return Nothing
    else fmap Just $ execWriterT $ do
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
            addClause :: Horn.Clause -> W m ()
            addClause c = tell ([c],([],[]))

        let callTbl :: M.Map (CallId,Int) CallId
            callTbl = M.fromList [ ((pcallId info,callLabel info),callId info)| info <- calls ]
            closureMap :: M.Map (CallId,Int) ClosureId
            closureMap = M.fromList [ ((cCallId info,label info),closureId info)| info <- closures ]
            branchMap :: M.Map (CallId,Int) Bool
            branchMap = M.fromList [ ((bCallId info,branchId info),direction info) | info <- branches ]
            letMap :: M.Map (CallId, Int) (Maybe SValue)
            letMap = M.fromList [ ((lCallId info,lLabel info),evalValue info) | info <- letexps ]
        genv' <- fmap M.fromList $ forM (M.toList genv) $ \(f,v) -> do
            ty <- gen (ML.name f) [] v
            return (f,(ty,decompose f))
        dump "RefineEnv" (M.assocs genv')

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
                    let letv = letMap M.! (callSite, label)
                    tau' <- genP (ML.name x ++ "_" ++ show label) (M.keys env) letv
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
                    Nothing -> 
                        let clsId = closureMap M.! (callSite,label)
                            meta  = fname++ "_" ++ show label in
                        gen meta (M.keys env) (C (Cls fdef clsId undefined))
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
                liftIO $ putStrLn $ "Clause: " ++ show cs ++ "==>" ++ show fml
                genClause (Just fml) cs >>= addClause
            subType cs ty1 ty2 = do
                liftIO $ putStrLn $ "SubType: " ++ show cs ++ " |- " ++ show ty1 ++ "<:" ++ show ty2
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
                liftIO $ putStrLn $ "Clause: " ++ show cs ++ "==> False" 
                genClause Nothing cs >>= addClause
        forM_ (ML.functions prog) $ \(f,fdef) -> do
            theta <- checkFunDef (ML.name f) genv' [] (CallId 0) fdef (Just $ fst $ genv' M.! f)
            addFuncBinding (ML.ident fdef) theta
        x <- freshId "main"
        check genv' [] (CallId 0) (ML.mainTerm prog) RPostTypeFailure
        return ()

genClause :: MonadId m => Maybe LFormula -> [Either SValue LFormula] -> m Horn.Clause
genClause hd body = do
    ((chd,cbody),extra) <- runWriterT $ do
        chd <- case hd of
            Just fml -> do
                Horn.Pred s t <- termOfFormula fml
                return $ Horn.PVar s t
            Nothing -> return Horn.Bot
        cbody <- forM body $ \case
            Left sv -> atomOfValue sv
            Right v -> termOfFormula v
        return (chd,cbody)
    return $ Horn.Clause chd (cbody ++ extra)
    
termOfFormula :: MonadId m => LFormula -> WriterT [Horn.Term] m Horn.Term
termOfFormula (Formula meta i vs) = do
    ts <- mapM termOfValue vs
    return $ Horn.Pred ("p_"++ smeta ++ "[" ++ show i ++ ":0]") ts
    where
    Meta l accessors = meta
    smeta = concat (intersperse "_" (l : reverse accessors))

-- assume that the value has type int/bool
termOfValue :: MonadId m => SValue -> WriterT [Horn.Term] m Horn.Term
termOfValue = \case
    SVar x -> pure $ Horn.Var (ML.name x)
    Int i -> pure $ Horn.Int i
    Bool b -> pure $ Horn.Bool b
    Add v1 v2 -> liftA2 Horn.Add (termOfValue v1) (termOfValue v2)
    Sub v1 v2 -> liftA2 Horn.Sub (termOfValue v1) (termOfValue v2)
    Eq v1 v2 -> liftA2 Horn.Eq (termOfValue v1) (termOfValue v2)
    Lt v1 v2 -> liftA2 Horn.Lt (termOfValue v1) (termOfValue v2)
    Lte v1 v2 -> liftA2 Horn.Lte (termOfValue v1) (termOfValue v2)
    Not v -> fmap Horn.Not (termOfValue v)
    And v1 v2 -> liftA2 Horn.And (termOfValue v1) (termOfValue v2)
    Or  v1 v2 -> liftA2 Horn.Or  (termOfValue v1) (termOfValue v2)
    v -> error $ "termOfValue: unexpected value: " ++ show v

-- assume the value has type bool
atomOfValue :: MonadId m => SValue -> WriterT [Horn.Term] m Horn.Term
atomOfValue = \case
    SVar x -> case ML.getType x of
        ML.TBool -> pure $ Horn.Var (ML.name x)
        _ -> error $ "atomOfValue: unexpected value: " ++ show x
    Bool b -> pure $ Horn.Bool b
    Eq v1 v2 -> liftA2 Horn.Eq (termOfValue v1) (termOfValue v2)
    Lt v1 v2 -> liftA2 Horn.Lt (termOfValue v1) (termOfValue v2)
    Lte v1 v2 -> liftA2 Horn.Lte (termOfValue v1) (termOfValue v2)
    Not v -> fmap Horn.Not (atomOfValue v)
    And v1 v2 -> liftA2 Horn.And (atomOfValue v1) (atomOfValue v2)
    Or  v1 v2 -> liftA2 Horn.Or  (atomOfValue v1) (atomOfValue v2)
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
substLFormulaBase subst (Formula meta i ws) = Formula meta i ws' where
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

updateFormula :: PAbst.Formula -> [PAbst.Formula] -> [PAbst.Formula]
updateFormula phi fml = case phi of
    ML.CBool _ -> fml
    -- decompose boolean combinations
    ML.Op (ML.OpAnd v1 v2) -> updateFormula v1 (updateFormula v2 fml)
    ML.Op (ML.OpOr v1 v2) -> updateFormula v1 (updateFormula v2 fml)
    _ | phi `elem` fml -> fml
      | otherwise -> phi : fml

-- penv :: i -> (xs,fml) s.t. P_{i} = \xs. fml
-- env : mapping from variables in the formula to values in PType 
refineTermType :: IM.IntMap ([Id], ML.AValue) -> M.Map String ML.AValue -> RPostType -> PAbst.TermType -> PAbst.TermType
refineTermType penv env (RPostType r rty fml) (abst_r, abst_rty, abst_fml) = (abst_r, abst_rty', abst_fml')
    where
    env' = extendEnv r (ML.Var abst_r) env
    abst_rty' = refinePType penv env' rty abst_rty
    phi' = refineLFormula penv env' fml
    abst_fml' = updateFormula phi' abst_fml
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
        pty_x' = (abst_xs, abst_ptys', updateFormula pre abst_fml)
        pty_r' = refineTermType penv env' (resType as) pty_r

refineLFormula :: IM.IntMap ([Id], ML.AValue) -> M.Map String ML.AValue -> LFormula -> PAbst.Formula
refineLFormula penv env (Formula _ _ []) = ML.CBool True  {- this is ad-hoc technique to avoid lookup error: 
                                                             if args is null, penv may not contain the corresponding formula -}
refineLFormula penv env fml = phi' where
    Formula _ i args = fml
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

