{-# LANGUAGE ScopedTypeVariables, LambdaCase #-}
module ML.Refine where

import ML.Syntax.Typed
import qualified Data.Map as M
import Control.Applicative
import Control.Monad
import Control.Monad.Writer
import Control.Monad.State.Strict
import qualified Data.IntMap as IM
import Id

type Trace = [Bool]
newtype CallId = CallId { unCallId :: Int } deriving Show
newtype ClosureId = ClosureId { unClosureId :: Int } deriving Show


type Constraint = SValue -- must have the sort Bool
data CallInfo = CallInfo { calleeId :: ClosureId   -- 呼び出されたクロージャの識別子
                         , callId   :: CallId   -- 関数呼び出しの識別子
                     } deriving Show

-- クロージャ生成の情報
data ClosureInfo = ClosureInfo { label :: Int -- 対応する関数定義のラベル
                               , closureId :: ClosureId -- 生成されたクロージャの識別子
                               } deriving Show
-- 関数返り値の情報
data ReturnInfo = ReturnInfo { rcallId :: CallId -- 関数呼び出しの識別子
                             , retValue :: SValue -- 返り値
                             } deriving Show

-- 分岐情報
data BranchInfo = BranchInfo { bcallId   :: CallId, 
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
            | C Closure
            deriving Show

data Closure = Cls Int {- Label -} ClosureId {- Ident -}  Env

instance Show Closure where
    show (Cls i x _) = "Closure " ++ show i ++ " " ++ show x
type Env = M.Map Id SValue

type Log = ([Constraint],[CallInfo],[ClosureInfo],[ReturnInfo],[BranchInfo])

type M m a = StateT S (WriterT Log m) a
data S = S { callCounter :: !Int, clsCounter :: !Int, cTrace :: !Trace }

incrCall :: S -> S
incrCall (S x y z) = S (x+1) y z

incrCls :: S -> S
incrCls (S x y z) = S x (y+1) z

pop :: S -> S
pop (S x y z) = S x y (tail z)

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
    sub (LApp _ _ _) = empty
    sub (LExp _ e) = go e

symbolicExec :: forall m. (MonadFix m) => Program -> Trace -> m Log
symbolicExec prog trace = execWriterT (evalStateT (genEnv >>= (\genv -> evalFail genv (mainTerm prog))) (S 1 0 trace)) 
    where
    clsTbl :: IM.IntMap Exp
    clsTbl = IM.fromList $ map (\t@(Lambda _ i _ _) -> (i,t)) $ closures prog
    genEnv = mfix $ \genv -> do
        es <- forM (functions prog) $ \(f, _, Lambda _ i _ _) -> do
            c <- genClosure i genv
            return (f,C c)
        return $ M.fromList es
    n = length (functions prog)
    evalFail :: Env -> Exp -> M m ()
    evalFail env = \case
        Let _ x lv e -> do
            r <- evalLV (CallId 0) env lv
            evalFail (M.insert x r env) e
        Assume _ v e -> do
            constrain (evalV env v)
            evalFail env e
        Fail _ -> return ()
        Branch _ i e1 e2 -> do
            b <- consume
            branch (BranchInfo (CallId 0) i b)
            if b then
                evalFail env e1
            else
                evalFail env e2
    evalV :: Env -> Value -> SValue
    evalV env = \case
        Var x -> env M.! x
        CInt x -> Int x
        CBool x -> Bool x
        Pair v1 v2 -> P (evalV env v1) (evalV env v2)
        Op op -> case op of
            OpAdd v1 v2 -> Add (evalV env v1) (evalV env v2)
            OpSub v1 v2 -> Sub (evalV env v1) (evalV env v2)
            OpLt v1 v2 -> Lt (evalV env v1) (evalV env v2)
            OpLte v1 v2 -> Lte (evalV env v1) (evalV env v2)
            OpAnd v1 v2 -> And (evalV env v1) (evalV env v2)
            OpOr  v1 v2 -> Or (evalV env v1) (evalV env v2)
            OpFst _ v -> 
                let P sv _ = evalV env v in sv
            OpSnd _ v -> 
                let P _ sv = evalV env v in sv
            OpNot v1 -> Not (evalV env v1)
    evalLV :: CallId -> Env -> LetValue -> M m SValue
    evalLV callSite env = \case 
        LValue v -> pure $ evalV env v
        LApp _ f vs -> 
            let svs = map (evalV env) vs in
            foldM (\(C (Cls i clsId env')) sv -> do
                let Lambda _ _ x e0 = clsTbl IM.! i
                j <- newCall clsId
                eval True j (M.insert x sv env') e0) (env M.! f) svs
        LExp _ e -> eval False callSite env e
    eval :: Bool -> CallId -> Env -> Exp -> M m SValue
    eval isTail callSite env _e = case _e of
        Value v -> do
            let sv = evalV env v 
            when isTail (retval (ReturnInfo callSite sv))
            return sv
        Lambda _ i _ _ -> do
            sv <- C <$> genClosure i env
            when isTail (retval (ReturnInfo callSite sv))
            return sv
        Let _ x lv e -> do
            r <- evalLV callSite env lv
            eval isTail callSite (M.insert x r env) e
        Assume _ v e -> do
            constrain (evalV env v)
            eval isTail callSite env e
        Branch _ i e1 e2 -> do
            b <- consume
            branch (BranchInfo callSite i b)
            if b then
                eval isTail callSite env e1
            else
                eval isTail callSite env e2

    constrain :: Constraint -> M m ()
    constrain c = tell ([c],[],[],[],[])
    branch :: BranchInfo -> M m ()
    branch c = tell ([],[],[],[],[c])
    retval :: ReturnInfo -> M m ()
    retval c = tell ([],[],[],[c],[])
    newCall :: ClosureId -> M m CallId
    newCall clsId = do
        j <- callCounter <$> get
        modify incrCall
        tell ([],[CallInfo clsId (CallId j)],[],[],[])
        return (CallId j)
    genClosure :: Int -> Env -> M m Closure
    genClosure label env = do
        j <- clsCounter <$> get
        modify incrCls
        tell ([],[],[ClosureInfo label (ClosureId j)],[],[])
        return (Cls label (ClosureId j) env)
    consume :: M m Bool
    consume = do
        b <- head . cTrace <$> get
        modify pop
        return b
-- Refinement types
data RType = RBool | RFun !(IM.IntMap RFunAssoc) | RPair !RType !RType
data RFunAssoc = RFunAssoc { argName :: !Id
                           , argType :: !RType
                           , preCond :: !LFormula
                           , resType :: !RPostType }
data RPostType = RPostType { posName :: !Id
                           , posType :: !RType
                           , posCond :: !LFormula }
data LFormula = Formula [Id] | Subst ![(Id,SValue)] !LFormula

{-
genFunType :: (MonadId m) -> [CallInfo] -> [Int] -> Int -> Type -> m RType
genFunType calls hist cId (TFun targ tres) = undefined
    where
        next = [  | info <- calls, closureId info == cId, callHist info == hist ]

-}

