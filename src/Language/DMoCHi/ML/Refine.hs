{-# LANGUAGE ScopedTypeVariables, LambdaCase, FlexibleContexts, BangPatterns #-}
module Language.DMoCHi.ML.Refine where

import qualified Language.DMoCHi.ML.Syntax.Typed as ML
import qualified Language.DMoCHi.ML.PrettyPrint.Typed as ML
import qualified Language.DMoCHi.ML.PredicateAbstraction as PAbst
import qualified Data.Map as M
import qualified Language.DMoCHi.ML.SMT as SMT
import Control.Applicative
import Control.Monad
import Control.Monad.Writer
import Control.Monad.State.Strict
import qualified Data.IntMap as IM
import Language.DMoCHi.Common.Id
import Data.List(intersperse,nub,foldl')
import qualified Language.DMoCHi.ML.HornClause as Horn
import Debug.Trace
import Text.PrettyPrint

type Trace = [Bool]
newtype CallId = CallId { unCallId :: Int } deriving (Show,Eq,Ord)
newtype ClosureId = ClosureId { unClosureId :: Int } deriving (Show,Eq,Ord)

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
                             , argValue :: SValue -- 引数(let式の場合は(Int 0))
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
            | Iff SValue SValue
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
    showsPrec d (Iff v1 v2) = 
        showParen (d >= 3) $ (showsPrec 3 v1) . (showString " <=> ") . (showsPrec 3 v2)
    showsPrec d (Not v1) = 
        showParen (d >= 8) $ (showString "not ") . showsPrec 8 v1
    showsPrec d (C cls) = showsPrec d cls
                       
data Closure = Cls ML.FunDef ClosureId {- Ident -} Env

instance ML.HasType Closure where
    getType (Cls fdef _ _) = ML.getType fdef

instance Show Closure where
    show (Cls i x _) = "Closure " ++ show (ML.ident i) ++ " " ++ show x
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

{- needed no longer
closures :: Program -> [Exp]
closures (Program ds t0) = (ds >>= (\(_,_,e) -> go e)) <|> go t0
    where
    go (Value _) = empty
    go (Let _ _ lv e) = sub lv <|> go e
    go (Assume _ _ e) = go e
    go e@(Lambda _ _ _ e1) = pure e <|> go e1
    go (Fail _) = empty
    go (Branch _ _ e1 e2) = go e1 <|> go e2
    sub (LValue _) = empty
    sub (LApp _ _ _ _) = empty
    sub (LExp _ e) = go e
    sub (LRand) = empty
    -}

fromSValue :: SValue -> ML.Value
fromSValue (SVar x) = ML.Var x
fromSValue (Int i)  = ML.CInt i
fromSValue (Bool b) = ML.CBool b
fromSValue (P v1 v2) = ML.Pair (fromSValue v1) (fromSValue v2)
fromSValue (Add v1 v2) = ML.Op (ML.OpAdd (fromSValue v1) (fromSValue v2))
fromSValue (Sub v1 v2) = ML.Op (ML.OpSub (fromSValue v1) (fromSValue v2))
fromSValue (Eq v1 v2) = ML.Op (ML.OpEq (fromSValue v1) (fromSValue v2))
fromSValue (Lt v1 v2) = ML.Op (ML.OpLt (fromSValue v1) (fromSValue v2))
fromSValue (Lte v1 v2) = ML.Op (ML.OpLte (fromSValue v1) (fromSValue v2))
fromSValue (And v1 v2) = ML.Op (ML.OpAnd (fromSValue v1) (fromSValue v2))
fromSValue (Or v1 v2) = ML.Op (ML.OpOr (fromSValue v1) (fromSValue v2))
fromSValue (Not v1) = ML.Op (ML.OpNot (fromSValue v1))
fromSValue (Iff v1 v2) = error "Iff is not supported"
fromSValue (C v1) = error "Cannot convert a closure to a syntactic value"

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
    -- n = length (functions prog)
    eval :: CallId -> Env -> ML.Exp -> M m (Maybe SValue)
    eval callSite env _e = case _e of
        ML.Value v -> do
            let sv = evalV env v 
            -- when isTail (retval (ReturnInfo callSite arg sv))
            return $ Just sv
        ML.Let _ x lv e -> do
            r <- evalLV callSite env lv
            case r of
                Just sv -> eval callSite (M.insert x sv env) e
                Nothing -> return Nothing
        ML.Assume _ v e -> do
            constrain (evalV env v)
            eval callSite env e
        ML.Fail _ -> return Nothing
        ML.Branch _ i e1 e2 -> do
            b <- consume
            branch (BranchInfo callSite i b)
            if b then
                eval callSite env e1
            else
                eval callSite env e2

    evalV :: Env -> ML.Value -> SValue
    evalV env = \case
        ML.Var x -> env M.! x
        ML.CInt x -> Int x
        ML.CBool x -> Bool x
        ML.Pair v1 v2 -> P (evalV env v1) (evalV env v2)
        ML.Op op -> case op of
            ML.OpAdd v1 v2 -> Add (evalV env v1) (evalV env v2)
            ML.OpSub v1 v2 -> Sub (evalV env v1) (evalV env v2)
            ML.OpEq  v1 v2  -> Eq (evalV env v1) (evalV env v2)
            ML.OpLt  v1 v2  -> Lt (evalV env v1) (evalV env v2)
            ML.OpLte v1 v2 -> Lte (evalV env v1) (evalV env v2)
            ML.OpAnd v1 v2 -> And (evalV env v1) (evalV env v2)
            ML.OpOr  v1 v2 -> Or (evalV env v1) (evalV env v2)
            ML.OpFst _ v -> 
                let P sv _ = evalV env v in sv
            ML.OpSnd _ v -> 
                let P _ sv = evalV env v in sv
            ML.OpNot v1 -> Not (evalV env v1)
    evalLV :: CallId -> Env -> ML.LetValue -> M m (Maybe SValue)
    evalLV callSite env = \case 
        ML.LValue v -> pure $ Just (evalV env v)
        ML.LApp _ label f v -> do
            let sv = evalV env v
            let C (Cls fdef clsId env') = env M.! f
            let x  = ML.arg fdef
                e0 = ML.body fdef
            j <- newCall label callSite clsId
            r <- eval j (M.insert x sv env') e0
            ret_cid <- callCounter <$> get
            retval (ReturnInfo j sv r (CallId ret_cid))
            return r
        ML.LFun fdef -> Just . C <$> genClosure callSite fdef env
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

data RFunAssoc = RFunAssoc { argName :: !Id
                           , argType :: !RType
                           , preCond :: !LFormula
                           , resType :: !RPostType }
data RPostType = RPostType { posName :: !Id
                           , posType :: !RType
                           , posCond :: !LFormula }
               | RPostTypeFailure
data LFormula = Formula Meta Int [SValue]
data Meta = Meta !String [String]
-- この定義だと{(int,int -> {int | P1})|P2}でP1からタプルの第一要素が参照できない。

instance Show RFunAssoc where
    show (RFunAssoc x rty cond res) = 
        "{" ++ ML.name x ++ " : " ++ show rty ++ " | " ++ show cond ++ "}" ++ " -> " ++ show res

instance Show RPostType where
    show (RPostType r rty cond) = 
        "{" ++ ML.name r ++ " : " ++ show rty ++ " | " ++ show cond ++ "}"
    show RPostTypeFailure = "_|_"

instance Show LFormula where
    show (Formula (Meta l accessors) i vs) = 
        let s = concat $ intersperse "," $ map show vs
            smeta = "{" ++ concat (intersperse "." (l : reverse accessors))++ "}" in
        "P" ++ smeta ++ "_" ++ show i ++ "(" ++ s ++ ")"

{-
pprintFormula :: LFormula -> String
pprintFormula x = go M.empty x "" where
    go env (Formula i []) = showString "P_" . shows i . showString "()"
    go env (Formula i xs) =
        showString "P_" . shows i . showChar '(' .
        foldr1 (\a b -> a . showChar ',' . b) (map (\x ->
            case M.lookup x env of
                Just sv -> shows sv
                Nothing -> showString $ ML.name x ++ " : " ++ show (ML.getType x)) xs)
        . showChar ')'
    go env (Subst theta fml) =
        let env' = foldr (\(x,sv) -> M.insert x sv) env theta in
        go env' fml
        -}

termOfFormula :: LFormula -> Horn.Term
termOfFormula (Formula meta i vs) = Horn.Pred ("P"++ smeta ++ show i) (map termOfValue vs)
    where
    Meta l accessors = meta
    smeta = "{" ++ concat (intersperse "." (l : reverse accessors)) ++ "}"


-- assume that the value has type int
termOfValue :: SValue -> Horn.Term
termOfValue = \case
    SVar x -> Horn.Var (ML.name x)
    Int i -> Horn.Int i
--    P v1 v2  -> Horn.Pair (termOfValue v1) (termOfValue v2)
    Add v1 v2 -> Horn.Add (termOfValue v1) (termOfValue v2)
    Sub v1 v2 -> Horn.Sub (termOfValue v1) (termOfValue v2)
    v -> error $ "termOfValue: unexpected value: " ++ show v
--    Eq v1 v2 -> Horn.Eq (termOfValue v1) (termOfValue v2)
--    Lt v1 v2 -> Horn.Lt (termOfValue v1) (termOfValue v2)
--    Lte v1 v2 -> Horn.Lte (termOfValue v1) (termOfValue v2)
{-
    Not v -> case v of
        Bool b -> Horn.Bool (not b)
        Eq v1 v2 -> Horn.NEq (termOfValue v1) (termOfValue v2)
        Lt v1 v2 -> Horn.Gte (termOfValue v1) (termOfValue v2)
        Lte v1 v2 -> Horn.Gt (termOfValue v1) (termOfValue v2)
        Not v -> termOfValue v
        C _ -> error "termOfValue: unexpected closure"
        _ -> error "termOfValue: negation of Boolean combination is not supported"
    C _ -> error "termOfValue: unexpected closure"
-}

-- assume the value has type bool
atomOfValue :: SValue -> Horn.Term
atomOfValue = \case
    SVar x -> case ML.getType x of
        ML.TBool -> Horn.Var (ML.name x) `Horn.Eq` Horn.Int 1
    Bool b -> Horn.Bool b
    Eq v1 v2 -> Horn.Eq (termOfValue v1) (termOfValue v2)
    Lt v1 v2 -> Horn.Lt (termOfValue v1) (termOfValue v2)
    Lte v1 v2 -> Horn.Lte (termOfValue v1) (termOfValue v2)
    Not v -> Horn.Not (atomOfValue v)
    And v1 v2 -> Horn.And (atomOfValue v1) (atomOfValue v2)
    Iff v1 v2 -> Horn.Iff (atomOfValue v1) (atomOfValue v2)
    Or  v1 v2 -> Horn.Or  (atomOfValue v1) (atomOfValue v2)
    v -> error $ "atomOfValue: unexpected value: " ++ show v


type RTypeGen m = (String -> [Id] -> SValue -> m RType, String -> [Id] -> Maybe SValue -> m RPostType)

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
    gen lim meta env (C (Cls fdef i _)) = do  -- 
        let cs = [ callId info | info <- calls, 
                                 calleeId info == i,
                                 unCallId (callId info) > fst lim
                                 -- unCallId (callId info) < snd lim
                                 ] -- TODO Improve Impl
            x  = ML.arg fdef
            ML.TFun ty_arg ty_ret = ML.getType fdef
        as <- forM cs $ \j -> do
            let ReturnInfo _ arg_v mv ret_cid = rtnTbl IM.! (unCallId j)
            let xj = ML.Id ty_arg (ML.name x)
            let lim' = (unCallId j, unCallId ret_cid)
            arg_ty <- gen lim' (meta_add meta "pre") env arg_v
            posTy <- genPost lim' (meta_add meta "post") (push xj env) mv
            p1 <- freshInt
            return (unCallId j,RFunAssoc xj arg_ty (Formula (meta_add meta "pre") p1 (push xj env)) posTy)
        return $ RFun $ IM.fromList as
    genPost lim meta env mv = case mv of
        Just v -> do
            pty <- gen lim meta env v
            let rj = ML.Id (ML.getType v) "r"
            p0 <- freshInt
            return $ RPostType rj pty (Formula meta p0 (push rj env))
        Nothing -> return RPostTypeFailure

    isBase x = case ML.getType x of 
        (ML.TFun _ _) -> False
        _ -> True
    flatten (SVar x) env | isBase x  = (SVar x) : env
                         | otherwise = env
    flatten (P v1 v2) env = flatten v1 (flatten v2 env)
    push = flatten . decompose

evalRType :: M.Map Id (RType,SValue) -> ML.Value -> (RType,SValue)
evalRType env = go where
    go (ML.Var x) = env M.! x
    go (ML.CInt i) = (RInt, Int i)
    go (ML.CBool b) = (RBool, Bool b)
    go (ML.Pair v1 v2) = 
        let (r1,sv1) = go v1 
            (r2,sv2) = go v2 in
        (RPair r1 r2, P sv1 sv2)
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

decompose :: Id -> SValue
decompose x = case ML.getType x of
    ML.TInt -> SVar x
    ML.TBool -> SVar x
    ML.TPair t1 t2 -> 
        P (decompose (ML.Id t1 (ML.name x ++"$fst"))) 
          (decompose (ML.Id t2 (ML.name x ++"$snd")))
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
        liftIO $ print calls
        liftIO $ print closures
        liftIO $ print returns
        liftIO $ print branches
        liftIO $ print letexps
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
        liftIO $ print genv'

        let check :: M.Map Id (RType,SValue) ->   {- environment -}
                     [Either SValue LFormula] ->  {- accumulator of constraints -}
                     CallId ->                    {- callsite -}
                     ML.Exp ->                    {- checking expr -}
                     RPostType ->                 {- expected type -}
                     W m ()
            check env cs callSite _e tau = case _e of
                ML.Let _ x (ML.LValue v) e -> do
                    let env' = M.insert x (evalRType env v) env
                    check env' cs callSite e tau
                ML.Let _ x (ML.LApp _ i f v) e -> do
                    let (RFun fassoc,_) = env M.! f
                        (ty_v,sv) = evalRType env v
                        j = callTbl M.! (callSite,i)
                        ty_f = fassoc IM.! unCallId j
                    clause cs (substLFormula (argName ty_f) sv (preCond ty_f))
                    subType cs ty_v (argType ty_f)
                    case resType ty_f of
                        RPostType _ _ _ -> do
                            let x'    = decompose x
                                tau_j = substPostType (argName ty_f) sv $ resType ty_f
                                env'  = M.insert x (posType tau_j,x') env
                                cs'   = Right (substLFormula (posName tau_j) x' (posCond tau_j)) : cs
                            check env' cs' callSite e tau
                        RPostTypeFailure -> return ()
                ML.Let _ x ML.LRand e -> do
                    let x' = decompose x 
                        env' = M.insert x (RInt,x') env
                    check env' cs callSite e tau
                ML.Let _ f (ML.LFun fdef) e -> do
                    theta <- checkFunDef (ML.name f) env cs callSite fdef Nothing
                    let env' = M.insert f (theta,decompose f) env
                    addFuncBinding (ML.ident fdef) theta
                    check env' cs callSite e tau
                ML.Let _ x (ML.LExp label e') e -> do
                    let letv = letMap M.! (callSite, label)
                    tau' <- genP (ML.name x ++ "_" ++ show label) (M.keys env) letv
                    addExpBinding label tau'
                    check env cs callSite e' tau'
                    case tau' of
                        RPostType _ _ _ -> do
                            let x'   = decompose x
                                env' = M.insert x (posType tau', x') env
                                cs'  = Right (substLFormula (posName tau') x' (posCond tau')) : cs
                            check env' cs' callSite e tau
                        RPostTypeFailure -> return ()
                ML.Assume _ v e -> do
                    let (_,sv) = evalRType env v
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
                            let (rty,sv) = evalRType env v
                            clause cs (substLFormula (posName tau) sv (posCond tau))
                            subType cs rty (posType tau)
                        RPostTypeFailure -> do
                            let s = render $ ML.pprintV 0 v
                            error $ "This value "++ s ++ " cannot have the refinement type" ++ show tau
                ML.Fail _ -> 
                    case tau of
                        RPostTypeFailure -> failClause cs
                        _ -> error $ "This failure term cannot have the refinement type" ++ show tau
            checkFunDef fname env cs callSite fdef@(ML.FunDef label x e0) mtheta = do
                theta@(RFun fassoc) <- case mtheta of 
                    Just it -> return it
                    Nothing -> 
                        let clsId = closureMap M.! (callSite,label)
                            meta  = fname++ "_" ++ show label in
                        gen meta (M.keys env) (C (Cls fdef clsId undefined))
                forM_ (IM.assocs fassoc) $ \(j,ty_f) -> do
                    let xj = argName ty_f
                        ty_xj = argType ty_f
                        env' = M.insert x (ty_xj,decompose xj) env
                        cs' = Right (preCond ty_f) : cs
                    check env' cs' (CallId j) e0 (resType ty_f)
                return theta
            clause cs fml = do
                liftIO $ putStrLn $ "Clause: " ++ show cs ++ "==>" ++ show fml
                {-
                (fml,cs) <- deBooleanize fml cs
                liftIO $ putStrLn $ "debooleanized Clause: " ++ show cs ++ "==>" ++ show fml
                -}
                let hd = case termOfFormula fml of
                        Horn.Pred x ts  -> Horn.PVar x ts
                    body = map f cs
                    f (Left sv) = atomOfValue sv
                    f (Right v) = termOfFormula v
                addClause $ Horn.Clause hd body
            subType cs ty1 ty2 = do
                liftIO $ putStrLn $ "SubType: " ++ show cs ++ " |- " ++ show ty1 ++ "<:" ++ show ty2
                case (ty1,ty2) of
                    (RInt,RInt) -> return ()
                    (RBool,RBool) -> return ()
                    (RPair t1 t2,RPair t3 t4) -> subType cs t1 t3 >> subType cs t2 t4
                    (RFun fs1,RFun fs2) -> do
                        forM_ (IM.assocs fs2) $ \(i,RFunAssoc x2 rty2 cond2 pty2) -> do
                            let RFunAssoc x1 rty1 cond1 pty1  = fs1 IM.! i
                            let cs' = Right cond2 : cs
                            clause cs' (substLFormula x1 (decompose x2) cond1)
                            subType cs rty2 rty1
                            subTypePost cs' (substPostType x1 (decompose x2) pty1) pty2
            subTypePost cs (RPostType r1 ty1 cond1) (RPostType r2 ty2 cond2) = do
                let cs' = Right (substLFormula r1 (decompose r2) cond1) : cs
                clause cs' cond2
                subType cs' ty1 ty2
            subTypePost cs RPostTypeFailure RPostTypeFailure = return ()
            subTypePost cs ty1 ty2 = error $ "subTypePost: unexpected subtyping:" ++ show (cs,ty1,ty2) 
            failClause cs = do
                liftIO $ putStrLn $ "Clause: " ++ show cs ++ "==> False" 
                {-
                let dummy = Formula 0 []
                (_,cs) <- deBooleanize dummy cs
                liftIO $ putStrLn $ "debooleanized Clause: " ++ show cs ++ "==> False"
                -}
                let body = map f cs
                    f (Left sv) = atomOfValue sv
                    f (Right v) = termOfFormula v
                addClause $ Horn.Clause Horn.Bot body
        forM_ (ML.functions prog) $ \(f,fdef) -> do
            theta <- checkFunDef (ML.name f) genv' [] (CallId 0) fdef (Just $ fst $ genv' M.! f)
            addFuncBinding (ML.ident fdef) theta
        x <- freshId "main"
        check genv' [] (CallId 0) (ML.mainTerm prog) RPostTypeFailure
        return ()

-- assume that v is a decomposed value
substPostType :: Id -> SValue -> RPostType -> RPostType
substPostType x v (RPostType r rty cond) =
    RPostType r (substRType x v rty) (substLFormula x v cond)
substPostType x v RPostTypeFailure = RPostTypeFailure

-- assume that v is a decomposed value
substRType :: Id -> SValue -> RType -> RType
substRType x v = go where
    go (RPair ty1 ty2) = RPair (go ty1) (go ty2)
    go (RFun fassoc) = 
        RFun (fmap (\(RFunAssoc y rty cond pos) ->
            RFunAssoc y (go rty) (substLFormula x v cond) (substPostType x v pos)) fassoc)
    go RBool = RBool
    go RInt = RInt

-- assume that x have a base type (int, bool)
substLFormulaBase :: Id -> SValue -> LFormula -> LFormula
substLFormulaBase x sv (Formula meta i ws) = Formula meta i ws' where
    ws' = map (substSValue x sv) ws

substLFormula :: Id -> SValue -> LFormula -> LFormula
substLFormula = go . decompose
    where
    go (SVar x) sv = substLFormulaBase x sv
    go (P x1 x2) (P sv1 sv2) = go x1 sv1 . go x2 sv2
    go x sv = error $ "substLFormula: unexpected pattern " ++ show (x,sv)

substSValue :: Id -> SValue -> SValue -> SValue
substSValue x v _sv = case _sv of
    SVar y | y == x -> v
           | otherwise -> _sv
    P sv1 sv2   -> P (substSValue x v sv1) (substSValue x v sv2)
    Add sv1 sv2 -> Add (substSValue x v sv1) (substSValue x v sv2)
    Sub sv1 sv2 -> Sub (substSValue x v sv1) (substSValue x v sv2)
    Eq  sv1 sv2 -> Eq  (substSValue x v sv1) (substSValue x v sv2)
    Lt  sv1 sv2 -> Lt  (substSValue x v sv1) (substSValue x v sv2)
    Lte sv1 sv2 -> Lte (substSValue x v sv1) (substSValue x v sv2)
    And sv1 sv2 -> And (substSValue x v sv1) (substSValue x v sv2)
    Or  sv1 sv2 -> Or (substSValue x v sv1) (substSValue x v sv2)
    Not sv1     -> Not (substSValue x v sv1)
    C cls       -> error "substSValue: substituting closure is not supported"
    Int i       -> _sv
    Bool b      -> _sv

updateFormula :: PAbst.Formula -> [PAbst.Formula] -> [PAbst.Formula]
updateFormula phi fml = case phi of
    ML.CBool _ -> fml
    _ | phi `elem` fml -> fml
      | otherwise -> phi : fml

refineTermType :: IM.IntMap ([Id], ML.Value) -> M.Map String ML.Value -> RPostType -> PAbst.TermType -> PAbst.TermType
refineTermType penv env (RPostType r rty fml) (abst_r, abst_rty, abst_fml) = (abst_r, abst_rty', abst_fml')
    where
    abst_rty' = refinePType penv env rty abst_rty
    phi' = refineLFormula penv (extendEnv r (ML.Var abst_r) env) fml
    abst_fml' = updateFormula phi' abst_fml
refineTermType _ _ RPostTypeFailure termType = termType

refinePType :: IM.IntMap ([Id], ML.Value) -> M.Map String ML.Value -> RType -> PAbst.PType -> PAbst.PType
refinePType _ _ RBool PAbst.PBool = PAbst.PBool
refinePType _ _ RInt PAbst.PInt = PAbst.PInt
refinePType penv env (RPair rty1 rty2) (PAbst.PPair ty pty1 pty2) = 
    PAbst.PPair ty (refinePType penv env rty1 pty1) (refinePType penv env rty2 pty2)
refinePType penv env (RFun fassoc) (PAbst.PFun ty pty_x0 pty_r0) = pty'
    where
    pty' = uncurry (PAbst.PFun ty) $ foldl' f (pty_x0, pty_r0) (IM.elems fassoc)
    f ((abst_x, abst_pty, abst_fml), pty_r) as = pre `seq` abst_pty' `seq` (pty_x', pty_r')
        where
        env'  = extendEnv (argName as) (ML.Var abst_x) env
        pre   = refineLFormula penv env' (preCond as)
        abst_pty' = refinePType penv env (argType as) abst_pty
        pty_x' = (abst_x, abst_pty', updateFormula pre abst_fml)
        pty_r' = refineTermType penv env' (resType as) pty_r

refineLFormula :: IM.IntMap ([Id], ML.Value) -> M.Map String ML.Value -> LFormula -> PAbst.Formula
refineLFormula penv env fml = phi' where
    Formula _ i args = fml
    (args_phi, phi) = penv IM.! i
    env' = M.union (M.fromList $ zip (map ML.name args_phi) (map recover args)) env
    recover (SVar x) = env M.! (ML.name x)
    phi' = ML.evalV env' phi
        
extendEnv :: Id -> ML.Value -> M.Map String ML.Value -> M.Map String ML.Value
extendEnv x v env = case ML.getType x of
    ML.TInt -> M.insert (ML.name x) v env
    ML.TBool -> M.insert (ML.name x) v env
    ML.TPair t1 t2 -> extendEnv x1 v1 $ extendEnv x2 v2 env
        where
        x1 = ML.Id t1 (ML.name x ++ "$fst")
        x2 = ML.Id t2 (ML.name x ++ "$snd")
        v1 = ML.Op (ML.OpFst t1 v)
        v2 = ML.Op (ML.OpSnd t2 v)
    ML.TFun _ _ -> env

refine :: IM.IntMap [Id] -> [(Int,RType)] -> [(Int,RPostType)] -> [(Int,[Id],ML.Value)] -> PAbst.TypeMap -> PAbst.TypeMap
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

{-
deBooleanizeF :: MonadId m => SValue -> LFormula -> m (LFormula, SValue)
deBooleanizeF fml0 (Formula i vs) = do
    (fml,ws) <- foldM f (fml0, []) (reverse vs)
    return (Formula i ws, fml)
    where
    f (fml,ws) v = case v of
        SVar x     -> case ML.getType x of
            ML.TInt -> return (fml, v : ws)
            ML.TBool -> return (fml, SVar (ML.Id ML.TInt (ML.name x)) : ws)
            _ -> error "deBooleanizeF: variable of unexpected type" 
        Bool True  -> return (fml, Int 1 : ws)
        Bool False -> return (fml, Int 0 : ws)
        P _ _ -> error "deBooleanizeF: unexpected tuple"
        C _ -> error "deBooleanizeF: unexpected closure"

        Int i      -> return (fml, v : ws)
        _ -> case ML.getType v of
            ML.TInt -> return (fml, v : ws)
            ML.TBool -> do
                b <- ML.Id ML.TInt <$> freshId "b"
                let fml' = (SVar b `Eq` Int 1) `Iff` v
                return (fml' `And` fml, SVar b : ws)

deBooleanizeA :: SValue -> SValue
deBooleanizeA (And v1 v2) = And (deBooleanizeA v1) (deBooleanizeA v2)
deBooleanizeA (Or  v1 v2) = Or  (deBooleanizeA v1) (deBooleanizeA v2)
deBooleanizeA (Not v1) = Not (deBooleanizeA v1)
deBooleanizeA (SVar x) = 
    let y = SVar (ML.Id ML.TInt (ML.name x)) in
    Eq y (Int 1)
deBooleanizeA (Iff _ _) = error "deBooleanizeA: unexpected iff"
deBooleanizeA v = v

deBooleanize :: MonadId m => LFormula -> [Either SValue LFormula] -> m (LFormula, [Either SValue LFormula])
deBooleanize hd cs = do
    (hd',fml) <- deBooleanizeF (Bool True) hd
    (fml',cs') <- foldM f (fml, []) (reverse cs)
    return (hd',Left fml': cs')
    where
    f (fml, ds) _v = case _v of
        Left sv -> return (fml, Left (deBooleanizeA sv) : ds)
        Right p -> do
            (p', fml') <- deBooleanizeF fml p
            return (fml', Right p' : ds)
            -}

{-
substValue :: M.Map Id Value -> Value -> Value
substValue env = go where
    go (Var y) = case M.lookup y env of
        Just v -> v
        Nothing -> Var y
    go (Op op) = Op $ case op of
        OpAdd a b -> OpAdd (go a) (go b)
        OpSub a b -> OpSub (go a) (go b)
        OpEq  a b -> OpEq  (go a) (go b)
        OpLt  a b -> OpLt  (go a) (go b)
        OpLte a b -> OpLte (go a) (go b)
        OpAnd a b -> OpAnd (go a) (go b)
        OpOr  a b -> OpOr  (go a) (go b)
        OpNot a   -> OpNot (go a)
        OpFst t a -> OpFst t (go a)
        OpSnd t a -> OpSnd t (go a)
    go w = w
    -}
