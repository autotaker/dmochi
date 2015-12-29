{-# LANGUAGE ScopedTypeVariables, LambdaCase #-}
module ML.Refine where

import ML.Syntax.Typed
import qualified Data.Map as M
import Control.Applicative
import Control.Monad
import Control.Monad.Writer
import Control.Monad.State.Strict
import qualified Data.IntMap as IM

type Trace = [Bool]

type Constraint = SValue -- must have the sort Bool
data CallInfo = CallInfo { closureId :: Int   -- the ident of called closure
                         , callId    :: Int   -- the closure is called at this Id
                         , callHist  :: [Int] -- how the closure is generated }
                     } deriving Show

-- Symbolic Values
data SValue = Int Integer
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

data Closure = Cls Int [Int] {- history -} Env deriving Show
type Env = M.Map Id SValue

type M m a = StateT S (WriterT ([Constraint], [CallInfo]) m) a
data S = S { counter :: !Int, cTrace :: !Trace }

incr :: S -> S
incr (S x y) = S (x+1) y

pop :: S -> S
pop (S x y) = S x (tail y)

closures :: Program -> [Exp]
closures (Program ds t0) = (ds >>= (\(_,_,e) -> go e)) <|> go t0
    where
    go (Value _) = empty
    go (Let _ _ lv e) = sub lv <|> go e
    go (Assume _ _ e) = go e
    go e@(Lambda _ _ _ e1) = pure e <|> go e1
    go (Fail _) = empty
    go (Branch _ e1 e2) = go e1 <|> go e2
    sub (LValue _) = empty
    sub (LApp _ _ _) = empty
    sub (LExp _ e) = go e

symbolicExec :: forall m. (Monad m) => Program -> Trace -> m ([Constraint], [CallInfo])
symbolicExec prog trace = execWriterT (evalStateT (evalFail genv (mainTerm prog)) (S 0 trace)) 
    where
    clsTbl :: IM.IntMap Exp
    clsTbl = IM.fromList $ map (\t@(Lambda _ i _ _) -> (i,t)) $ closures prog
    genv = M.fromList [ (f, C (Cls i [] genv)) | (f, _, Lambda _ i _ _) <- functions prog ]
    evalFail :: Env -> Exp -> M m ()
    evalFail env = \case
        Let _ x lv e -> do
            r <- evalLV [] env lv
            evalFail (M.insert x r env) e
        Assume _ v e -> do
            constrain (evalV env v)
            evalFail env e
        Fail _ -> return ()
        Branch _ e1 e2 -> do
            b <- consume
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
    evalLV :: [Int] -> Env -> LetValue -> M m SValue
    evalLV hist env = \case 
        LValue v -> pure $ evalV env v
        LApp _ f vs -> 
            let svs = map (evalV env) vs in
            foldM (\(C (Cls i hist' env')) sv -> do
                let Lambda _ _ x e0 = clsTbl IM.! i
                j <- newCall i hist
                eval (j:hist') (M.insert x sv env') e0) (env M.! f) svs
        LExp _ e -> eval hist env e
    eval :: [Int] -> Env -> Exp -> M m SValue
    eval hist env _e = case _e of
        Value v -> pure (evalV env v)
        Let _ x lv e -> do
            r <- evalLV hist env lv
            eval hist (M.insert x r env) e
        Assume _ v e -> do
            constrain (evalV env v)
            eval hist env e
        Lambda _ i x e0 -> do
            pure $ C (Cls i hist env)
        Branch _ e1 e2 -> do
            b <- consume
            if b then
                eval hist env e1
            else
                eval hist env e2

    constrain :: Constraint -> M m ()
    constrain c = tell ([c],[])
    newCall :: Int -> [Int] -> M m Int
    newCall i hist = do
        j <- counter <$> get
        modify incr
        tell ([],[CallInfo i j hist])
        return j
    consume :: M m Bool
    consume = do
        b <- head . cTrace <$> get
        modify pop
        return b

