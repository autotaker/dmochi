{-# LANGUAGE ScopedTypeVariables, FlexibleContexts, LambdaCase, BangPatterns #-}
module Language.DMoCHi.ML.SymbolicExec where

import           Control.Applicative
import           Control.Monad.Writer
import           Control.Monad.State.Strict
import qualified Data.Map as M
import qualified Language.Dot as Dot
import           Text.Printf
import           Data.List(intersperse,foldl')
import           Data.Int
import           Data.Bits

import qualified Language.DMoCHi.ML.Syntax.PNormal as ML
import qualified Language.DMoCHi.ML.PrettyPrint.PNormal as ML
import qualified Language.DMoCHi.ML.SMT as SMT
import           Language.DMoCHi.Common.Id
import           Language.DMoCHi.Common.Util

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
                         , callContext :: CompTreePath -- 関数呼び出しの計算木での位置
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
                             , lContext :: CompTreePath
                             } deriving Show

-- 分岐情報
data BranchInfo = BranchInfo { bCallId   :: CallId, 
                               branchId  :: Int,
                               direction :: Bool} deriving Show

type CompTreePath = [Int]

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
            | C Closure

data Closure = Cls ML.FunDef ClosureId {- Ident -} Env

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
    showsPrec d (SVar x) | d >= 3 = showString (ML.name x)
                         | otherwise = showString (ML.name x) . showString " : " . shows (ML.getType x)
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
                       

instance ML.HasType Closure where
    getType (Cls fdef _ _) = ML.getType fdef

instance Show Closure where
    showsPrec d (Cls i x _) = showParen (d > app_prec) $
        showString "Cls " . showsPrec (app_prec+1) (ML.ident i) . showChar ' ' . showsPrec (app_prec + 1) x
        where
        app_prec = 10

data CompTree = CompTree { expr :: ML.Exp
                         , subTrees :: [(Int,CompTreeInfo,CompTree)] }
data CompTreeInfo = InfoBind [(Id,SValue)]
                  | InfoAssume SValue
                  | InfoNone

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
    

leaf :: ML.Exp -> CompTree
leaf e = CompTree e []

symbolicExec :: forall m. (MonadId m, MonadFix m) => ML.Program -> Trace -> m (M.Map Id SValue, Log, CompTree)
symbolicExec prog trace = do
    ((m,tree),log) <- runWriterT $ evalStateT (genEnv >>= (\genv -> do
        (t,r) <- eval (CallId 0) genv [] (ML.mainTerm prog)
        case r of
            Just sv -> error "symbolicExec: This error trace cannot reach to any failure!"
            Nothing -> return (genv,t))) (S 1 0 trace)
    return (m,log,tree)
    where
    genEnv = mfix $ \genv -> do
        es <- forM (ML.functions prog) $ \(f, fdef) -> do
            c <- genClosure (CallId 0) fdef genv
            return (f,C c)
        return $ M.fromList es
    eval :: CallId -> Env -> CompTreePath -> ML.Exp -> M m (CompTree, Maybe SValue)
    eval callSite env path _e = case _e of
        ML.Value v -> do
            sv <- evalV callSite env v 
            return $ (leaf _e, Just sv)
        ML.Let _ x lv e -> do
            (info,t1,r) <- evalLV callSite env (1:path) lv
            case r of
                Just sv -> do
                    (t2,r) <- eval callSite (M.insert x sv env) (2:path) e
                    let t = CompTree _e [(1,info,t1),(2,InfoBind [(x,sv)],t2)]
                    return (t,r)
                Nothing -> do
                    let t = CompTree _e [(1,info,t1)]
                    return (t, Nothing)
        ML.Assume _ v e -> do
            let phi = evalA env v
            constrain phi
            (t,r) <- eval callSite env (1:path) e
            return (CompTree _e [(1,InfoAssume phi,t)],r)
        ML.Fail _ -> return (leaf _e,Nothing)
        ML.Branch _ i e1 e2 -> do
            b <- consume
            branch (BranchInfo callSite i b)
            if b then do
                (t,r) <- eval callSite env (1:path) e1
                return (CompTree _e [(1,InfoNone,t)],r)
            else do
                (t,r) <- eval callSite env (2:path) e2
                return (CompTree _e [(2,InfoNone,t)],r)

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
    evalLV :: CallId -> Env -> CompTreePath -> ML.LetValue -> M m (CompTreeInfo, CompTree,Maybe SValue)
    evalLV callSite env path = \case 
        ML.LValue v -> pure $ (InfoNone, leaf (ML.Value (ML.Atomic v)), Just (evalA env v))
        ML.LApp _ label f vs -> do
            svs <- mapM (evalV callSite env) vs
            let C (Cls fdef clsId env') = env M.! f
            let xs = ML.args fdef
                e0 = ML.body fdef
            j <- newCall label callSite path clsId
            let env'' = foldr (uncurry M.insert) env' $ zip xs svs
            let info = InfoBind (zip xs svs ++ M.toList env')
            (t,r) <- eval j env'' path e0
            ret_cid <- callCounter <$> get
            retval (ReturnInfo j svs r (CallId ret_cid))
            return (info,t,r)
        -- ML.LFun fdef -> Just . C <$> genClosure callSite fdef env
        ML.LExp label e -> do
            (t,r) <- eval callSite env path e
            letexp (LetExpInfo callSite label r path)
            return (InfoNone,t,r)
        ML.LRand -> do
            r <- Just . SVar . ML.Id ML.TInt <$> freshId "rand"
            return (InfoNone,leaf (ML.Value (ML.Atomic (ML.Var (ML.Id ML.TInt "*")))), r)

    -- utilities
    constrain :: Constraint -> M m ()
    constrain c = tell ([c],[],[],[],([],[]))
    branch :: BranchInfo -> M m ()
    branch c = tell ([],[],[],[],([c],[]))
    retval :: ReturnInfo -> M m ()
    retval c = tell ([],[],[],[c],([],[]))
    letexp c = tell ([],[],[],[],([],[c]))
    newCall :: Int -> CallId -> CompTreePath -> ClosureId -> M m CallId
    newCall i pcall path clsId = do
        j <- callCounter <$> get
        modify incrCall
        tell ([],[CallInfo clsId i pcall (CallId j) path],[],[],([],[]))
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

renderCompTree :: CompTree -> String
renderCompTree t = Dot.renderDot $ Dot.Graph Dot.StrictGraph Dot.DirectedGraph Nothing stmts
    where
    stmts = execWriter (evalStateT (doit t) 0)
    name s = Dot.NameId s
    doit = fix (\go t -> do
        let e = expr t
            ts = subTrees t
        i <- get
        put (i + 1)
        let nodeId = Dot.NodeId (Dot.IntegerId i) Nothing
            value = Dot.StringId $ takeWhile (/='\n') $ show $ ML.pprintE e
            shape = name $ if null ts then "ellipse" else "box"
            attrs = [Dot.AttributeSetValue (name "label") value
                    ,Dot.AttributeSetValue (name "shape") shape]
        tell [Dot.NodeStatement nodeId attrs]

        forM_ ts $ \(i,info,ti) -> do
            vi <- go ti
            let nodeId' = Dot.NodeId (Dot.IntegerId vi) Nothing
            let edge = [Dot.ENodeId Dot.NoEdge nodeId
                       ,Dot.ENodeId Dot.DirectedEdge nodeId']
                attrs = case info of
                        InfoBind binds -> 
                            let s = "{ " ++ concat (intersperse "; " [ 
                                        printf "%s = %s" (ML.name x) (show sv) | (x,sv) <- binds ]) ++ " }" in
                            [Dot.AttributeSetValue (name "label") (Dot.StringId (show i ++ ", " ++ s))]
                        InfoAssume sv -> 
                            [Dot.AttributeSetValue (name "label") (Dot.StringId (show i ++ ", " ++ show sv))]
                        InfoNone -> 
                            [Dot.AttributeSetValue (name "label") (Dot.StringId (show i))]
            tell [Dot.EdgeStatement edge attrs]
        return i)

hashPath :: CompTreePath -> Int32
hashPath path = fromIntegral (h .&. 0x7fffffff)
    where
    h :: Int64
    h = foldl' (\cur x -> cur * 3 + (fromIntegral x)) 0 path

