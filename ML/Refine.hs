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
import Data.List(intersperse)
import qualified ML.HornClause as Horn

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
                             , argValue :: SValue -- 引数
                             , retValue :: SValue -- 返り値
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
            | C Closure

instance Show SValue where
    showsPrec d (SVar x) = 
        showParen (d >= 3) $ showString (name x) . showString " : " . shows (getType x)
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
    sub (LApp _ _ _ _) = empty
    sub (LExp _ e) = go e

symbolicExec :: forall m. (MonadFix m) => Program -> Trace -> m (M.Map Id SValue, Log)
symbolicExec prog trace = runWriterT (evalStateT (genEnv >>= (\genv -> evalFail genv (mainTerm prog) >> return genv)) (S 1 0 trace)) 
    where
    clsTbl :: IM.IntMap Exp
    clsTbl = IM.fromList $ map (\t@(Lambda _ i _ _) -> (i,t)) $ closures prog
    genEnv = mfix $ \genv -> do
        es <- forM (functions prog) $ \(f, _, Lambda _ i _ _) -> do
            c <- genClosure (CallId 0) i genv
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
        LApp _ label f v -> do
            let sv = evalV env v
            let C (Cls i clsId env') = env M.! f
            let Lambda _ _ x e0 = clsTbl IM.! i
            j <- newCall label callSite clsId
            eval True sv j (M.insert x sv env') e0
        LExp _ e -> eval False (Int 0) callSite env e
    eval :: Bool -> SValue -> CallId -> Env -> Exp -> M m SValue
    eval isTail arg callSite env _e = case _e of
        Value v -> do
            let sv = evalV env v 
            when isTail (retval (ReturnInfo callSite arg sv))
            return sv
        Lambda _ i _ _ -> do
            sv <- C <$> genClosure callSite i env
            when isTail (retval (ReturnInfo callSite arg sv))
            return sv
        Let _ x lv e -> do
            r <- evalLV callSite env lv
            eval isTail arg callSite (M.insert x r env) e
        Assume _ v e -> do
            constrain (evalV env v)
            eval isTail arg callSite env e
        Branch _ i e1 e2 -> do
            b <- consume
            branch (BranchInfo callSite i b)
            if b then
                eval isTail arg callSite env e1
            else
                eval isTail arg callSite env e2

    constrain :: Constraint -> M m ()
    constrain c = tell ([c],[],[],[],[])
    branch :: BranchInfo -> M m ()
    branch c = tell ([],[],[],[],[c])
    retval :: ReturnInfo -> M m ()
    retval c = tell ([],[],[],[c],[])
    newCall :: Int -> CallId -> ClosureId -> M m CallId
    newCall i pcall clsId = do
        j <- callCounter <$> get
        modify incrCall
        tell ([],[CallInfo clsId i pcall (CallId j)],[],[],[])
        return (CallId j)
    genClosure :: CallId -> Int -> Env -> M m Closure
    genClosure callSite label env = do
        j <- clsCounter <$> get
        modify incrCls
        tell ([],[],[ClosureInfo label (ClosureId j) callSite],[],[])
        return (Cls label (ClosureId j) env)
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
data LFormula = Formula Int [Id] | Subst ![(Id,SValue)] !LFormula
-- この定義だと{(int,int -> {int | P1})|P2}でP1からタプルの第一要素が参照できない。

instance Show RFunAssoc where
    show (RFunAssoc x rty cond res) = 
        "{" ++ name x ++ " : " ++ show rty ++ " | " ++ show cond ++ "}" ++ " -> " ++ show res

instance Show RPostType where
    show (RPostType r rty cond) = 
        "{" ++ name r ++ " : " ++ show rty ++ " | " ++ show cond ++ "}"

instance Show LFormula where
    show = pprintFormula
    {-
    show (Formula i xs) =
        "P_" ++ show i ++ "(" ++
        concat (intersperse "," [ name x ++ " : " ++ show (getType x) | x <- xs ])
        ++ ")"
    show (Subst theta fml) =
        "[" ++ 
            concat (intersperse "," [ show sv ++ "/" ++ name x  | (x,sv) <- theta ])
        ++ "]" ++ show fml
        -}

pprintFormula :: LFormula -> String
pprintFormula x = go M.empty x "" where
    go env (Formula i []) = showString "P_" . shows i . showString "()"
    go env (Formula i xs) =
        showString "P_" . shows i . showChar '(' .
        foldr1 (\a b -> a . showChar ',' . b) (map (\x ->
            case M.lookup x env of
                Just sv -> shows sv
                Nothing -> showString $ name x ++ " : " ++ show (getType x)) xs)
        . showChar ')'
    go env (Subst theta fml) =
        let env' = foldr (\(x,sv) -> M.insert x sv) env theta in
        go env' fml

termOfFormula :: LFormula -> Horn.Term
termOfFormula = go M.empty where
    go env (Formula i xs) = Horn.Pred ("P"++show i) (map f xs)
        where
        f x = case M.lookup x env of
            Just sv -> termOfValue sv
            Nothing -> Horn.Var (filter (/='_') $ name x)
    go env (Subst theta fml) =
        let env' = foldr (\(x,sv) -> M.insert x sv) env theta in
        go env' fml

termOfValue :: SValue -> Horn.Term
termOfValue = \case
    SVar x -> Horn.Var (filter (/='_') $ name x)
    Int i -> Horn.Int i
    Bool b -> Horn.Bool b
    P _ _ -> error "termOfValue: pairs are not supported"
    Add v1 v2 -> Horn.Add (termOfValue v1) (termOfValue v2)
    Sub v1 v2 -> Horn.Sub (termOfValue v1) (termOfValue v2)
    Eq v1 v2 -> Horn.Eq (termOfValue v1) (termOfValue v2)
    Lt v1 v2 -> Horn.Lt (termOfValue v1) (termOfValue v2)
    Lte v1 v2 -> Horn.Lte (termOfValue v1) (termOfValue v2)
    Not v -> case v of
        Bool b -> Horn.Bool (not b)
        Eq v1 v2 -> Horn.NEq (termOfValue v1) (termOfValue v2)
        Lt v1 v2 -> Horn.Gte (termOfValue v1) (termOfValue v2)
        Lte v1 v2 -> Horn.Gt (termOfValue v1) (termOfValue v2)
        Not v -> termOfValue v
        C _ -> error "termOfValue: unexpected closure"
        _ -> error "termOfValue: negation of Boolean combination is not supported"
    C _ -> error "termOfValue: unexpected closure"

genRType :: MonadId m => [CallInfo] -> [ClosureInfo] -> [ReturnInfo] -> IM.IntMap Exp -> [Id] -> SValue -> m RType
genRType calls closures returns clsTbl = gen 0 . filter (isBase) where
    rtnTbl = IM.fromList [ (unCallId (rcallId info),info) | info <- returns ]
    gen _ _ (SVar x) = case getType x of
        TInt -> pure RInt
        TBool -> pure RBool
    gen _ _ (Int _) = pure RInt
    gen _ _ (Bool _) = pure RBool
    gen lim env (P v1 v2) = RPair <$> gen lim env v1 <*> gen lim env v2
    gen _ _ (Add _ _) = pure RInt
    gen _ _ (Sub _ _) = pure RInt
    gen _ _ (Eq _ _) = pure RBool
    gen _ _ (Lt _ _) = pure RBool
    gen _ _ (And _ _) = pure RBool
    gen _ _ (Or _ _) = pure RBool
    gen _ _ (Not _) = pure RBool
    gen lim env (C (Cls l i _)) = do
        let cs = [ callId info | info <- calls, 
                                 calleeId info == i, 
                                 unCallId (callId info) > lim ] -- TODO Improve Impl
            e@(Lambda ty _ x _) = clsTbl IM.! l
            TFun ty_arg ty_ret = ty
        as <- forM cs $ \j -> do
            let ReturnInfo _ arg_v v = rtnTbl IM.! (unCallId j)
            let xj = Id ty_arg (name x)
            arg_ty <- gen (unCallId j) env arg_v
            pty <- gen (unCallId j) ([xj | isBase xj] ++ env) v
            let rj = Id ty_ret "r"
            p0 <- freshInt
            p1 <- freshInt
            let posTy = RPostType rj pty (Formula p0 ([rj | isBase rj] ++ [xj | isBase xj] ++ env))
            return $ (unCallId j,RFunAssoc xj arg_ty (Formula p1 ([xj | isBase xj]++env)) posTy)
        return $ RFun $ IM.fromList as
    isBase x = case getType x of 
        (TFun _ _) -> False
        _ -> True

evalRType :: M.Map Id (RType,SValue) -> Value -> (RType,SValue)
evalRType env = go where
    go (Var x) = env M.! x
    go (CInt i) = (RInt, Int i)
    go (CBool b) = (RBool, Bool b)
    go (Pair v1 v2) = 
        let (r1,sv1) = go v1 
            (r2,sv2) = go v2 in
        (RPair r1 r2, P sv1 sv2)
    go (Op (OpAdd v1 v2)) = 
        let (r1,sv1) = go v1 
            (r2,sv2) = go v2 in
        (RInt,Add sv1 sv2)
    go (Op (OpSub v1 v2)) = 
        let (r1,sv1) = go v1 
            (r2,sv2) = go v2 in
        (RInt,Sub sv1 sv2)
    go (Op (OpEq  v1 v2)) = 
        let (r1,sv1) = go v1 
            (r2,sv2) = go v2 in
        (RBool,Eq sv1 sv2)
    go (Op (OpLt  v1 v2)) = 
        let (r1,sv1) = go v1 
            (r2,sv2) = go v2 in
        (RBool,Lt sv1 sv2)
    go (Op (OpLte  v1 v2)) = 
        let (r1,sv1) = go v1 
            (r2,sv2) = go v2 in
        (RBool,Lte sv1 sv2)
    go (Op (OpAnd  v1 v2)) = 
        let (r1,sv1) = go v1 
            (r2,sv2) = go v2 in
        (RBool,And sv1 sv2)
    go (Op (OpOr  v1 v2)) = 
        let (r1,sv1) = go v1 
            (r2,sv2) = go v2 in
        (RBool,Or sv1 sv2)
    go (Op (OpNot v)) = 
        let (r,sv) = go v in (RBool,Not sv)
    go (Op (OpFst _ v)) = let (RPair a _,P sv _) = go v in (a,sv)
    go (Op (OpSnd _ v)) = let (RPair _ b,P _ sv) = go v in (b,sv)

decompose :: Id -> SValue
decompose x = case getType x of
    TInt -> SVar x
    TBool -> SVar x
    TPair t1 t2 -> P (decompose (Id t1 (name x ++".fst")))
                     (decompose (Id t2 (name x ++".snd")))
    TFun _ _ -> SVar x

refineCGen :: forall m.(MonadFix m, MonadId m, MonadIO m) => Program -> Trace -> m ([Horn.Clause],[(Id,RType)])
refineCGen prog trace = execWriterT $ do
    let clsTbl = IM.fromList $ map (\t@(Lambda _ i _ _) -> (i,t)) $ closures prog
    (genv, (consts,calls,closures,returns,branches)) <- symbolicExec prog trace
    liftIO $ print consts
    liftIO $ print calls
    liftIO $ print closures
    liftIO $ print returns
    liftIO $ print branches
    let gen = genRType calls closures returns clsTbl
    let addBinding :: Id -> RType -> WriterT ([Horn.Clause],[(Id,RType)]) m ()
        addBinding f ty = tell ([],[(f,ty)])
    let addClause :: Horn.Clause -> WriterT ([Horn.Clause],[(Id,RType)]) m () 
        addClause c = tell ([c],[])
    let callTbl :: M.Map (CallId,Int) CallId
        callTbl = M.fromList [ ((pcallId info,callLabel info),callId info)| info <- calls ]
        closureMap :: M.Map (CallId,Int) ClosureId
        closureMap = M.fromList [ ((cCallId info,label info),closureId info)| info <- closures ]
        branchMap :: M.Map (CallId,Int) Bool
        branchMap = M.fromList [ ((bCallId info,branchId info),direction info) | info <- branches ]
    genv' <- fmap M.fromList $ forM (M.toList genv) $ \(f,v) -> do
        ty <- gen [] v
        addBinding f ty
        return (f,(ty,decompose f))
    let check :: M.Map Id (RType,SValue) -> 
                 [Either SValue LFormula] -> 
                 CallId -> Exp -> RPostType -> WriterT ([Horn.Clause],[(Id,RType)]) m ()
        check env cs callSite _e tau = case _e of
            Let _ x (LValue v) e -> do
                let env' = M.insert x (evalRType env v) env
                check env' cs callSite e tau
            Let _ x (LApp _ i f v) e -> do
                let (RFun fassoc,_) = env M.! f
                    (ty_v,sv) = evalRType env v
                    j = callTbl M.! (callSite,i)
                    ty_f = fassoc IM.! unCallId j
                    tau_j = substPostType (argName ty_f) sv $ resType ty_f
                clause cs (Subst [(argName ty_f,sv)] (preCond ty_f))
                subType cs ty_v (argType ty_f)
                let x' = decompose x
                    env' = M.insert x (posType tau_j,x') env
                    cs' = Right (Subst [(posName tau_j,x')] (posCond tau_j)) : cs
                check env' cs' callSite e tau
            Let _ f (LExp _ (Lambda _ label x e0)) e -> do
                let clsId = closureMap M.! (callSite,label)
                theta@(RFun fassoc) <- gen (M.keys env) (C (Cls label clsId undefined))
                forM_ (IM.assocs fassoc) $ \(j,ty_f) -> do
                    let xj = argName ty_f
                        ty_xj = argType ty_f
                        env' = M.insert x (ty_xj,decompose xj) env
                        cs' = Right (preCond ty_f) : cs
                    check env' cs' (CallId j) e0 (resType ty_f)
                let env' = M.insert f (theta,decompose f) env
                addBinding f theta
                check env' cs callSite e tau
            Assume _ v e -> do
                let (_,sv) = evalRType env v
                let cs' = Left sv : cs
                check env cs' callSite e tau
            Branch _ label e1 e2 -> do
                let b = branchMap M.! (callSite,label)
                if b then
                    check env cs callSite e1 tau
                else
                    check env cs callSite e2 tau
            Value v -> do
                let (rty,sv) = evalRType env v
                clause cs (Subst [(posName tau,sv)] (posCond tau))
                subType cs rty (posType tau)
            Lambda _ label x e -> do
                let clsId = closureMap M.! (callSite,label)
                theta@(RFun fassoc) <- gen (M.keys env) (C (Cls label clsId undefined))
                forM_ (IM.assocs fassoc) $ \(j,ty_f) -> do
                    let xj = argName ty_f
                        ty_xj = argType ty_f
                        env' = M.insert x (ty_xj,decompose xj) env
                        cs' = Right (preCond ty_f) : cs
                    check env' cs' (CallId j) e (resType ty_f)
                clause cs (posCond tau) -- 返り値は関数型なので述語には出現しない。
                subType cs theta (posType tau)
            Fail _ -> do
                failClause cs
        clause cs fml = do
            liftIO $ putStrLn $ "Clause: " ++ show cs ++ "==>" ++ show fml
            let hd = case termOfFormula fml of
                    Horn.Pred x ts  -> Horn.PVar x ts
                body = map f cs
                f (Left sv) = termOfValue sv
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
                        clause cs' (Subst [(x1,decompose x2)] cond1)
                        subType cs rty2 rty1
                        subTypePost cs' (substPostType x1 (decompose x2) pty1) pty2
        subTypePost cs (RPostType r1 ty1 cond1) (RPostType r2 ty2 cond2) = do
            let cs' = Right (Subst [(r1,decompose r2)] cond1) : cs
            clause cs' cond2
            subType cs' ty1 ty2
        failClause cs = do
            liftIO $ putStrLn $ "Clause: " ++ show cs ++ "==> False" 
            let body = map f cs
                f (Left sv) = termOfValue sv
                f (Right v) = termOfFormula v
            addClause $ Horn.Clause Horn.Bot body
    forM (functions prog) $ \(f,_,e) -> do
        i <- freshInt
        check genv' [] (CallId 0) e (RPostType f (fst $ genv' M.! f) (Formula i []))
    x <- freshId "main"
    let ty = getType (mainTerm prog)
    let rty = case ty of
            TInt -> RInt
            TBool -> RBool
    i <- freshInt
    check genv' [] (CallId 0) (mainTerm prog) (RPostType (Id ty x) rty (Formula i []))
    return ()

substPostType :: Id -> SValue -> RPostType -> RPostType
substPostType x v (RPostType r rty cond) =
    RPostType r (substRType x v rty) (Subst [(x,v)] cond)

substRType :: Id -> SValue -> RType -> RType
substRType x v = go where
    go (RPair ty1 ty2) = RPair (go ty1) (go ty2)
    go (RFun fassoc) = 
        RFun (fmap (\(RFunAssoc y rty cond pos) ->
            RFunAssoc y (go rty) (Subst [(x,v)] cond) (substPostType x v pos)) fassoc)
    go RBool = RBool
    go RInt = RInt

refine :: Program -> [(Id,RType)] -> [(String,[Id],Value)] -> Program
refine prog tassoc subst = prog' where
    genv :: M.Map Id [RType]
    genv = M.fromListWith (++) $ map (\(x,y) -> (x,[y])) tassoc
    penv = M.fromList [ (s,(xs,v)) | (s,xs,v) <- subst ]

    prog' = Program ds' t0'
    ds' = [ (f,toPType (refinePType (head $ genv M.! f) (fromPType pty)),refineTerm e) | (f,pty,e) <- functions prog ]
    t0' = refineTerm (mainTerm prog)

    refinePType :: RType -> PType' -> PType'
    refinePType RInt _ = PInt'
    refinePType RBool _ = PBool'
    refinePType (RFun fassoc) (PFun' ty ty_x ty_r) = PFun' ty ty_x' ty_r'
        where
        ty_x' = foldl (\(x,pty_x,ps_x) (RFunAssoc y rty1 cond1 _) ->
                    let p = substCond cond1 in
                    (x,refinePType rty1 pty_x,(y,p):ps_x)) ty_x (IM.elems fassoc)
        (x0,_,_) = ty_x
        ty_r' = foldl (\(pty_r,ps_r) (RFunAssoc y _ _ tau) ->
                    let RPostType r rty2 cond2 = tau in
                    let p = substCond (Subst [(y,decompose x0)] cond2) in
                    let pty_r' = refinePType (substRType y (decompose x0) rty2) pty_r in
                    (pty_r',(r,p):ps_r)) ty_r (IM.elems fassoc)

    refineTerm :: Exp -> Exp
    refineTerm (Value v) = Value v
    refineTerm (Let ty f (LExp pty (Lambda ty0 label x e0)) e) = 
        Let ty f (LExp (toPType pty') (Lambda ty0 label x e0')) e' 
            where
            rtys = case M.lookup f genv of
                Just l -> l
                Nothing -> []
            pty' = foldr refinePType (fromPType pty) rtys
            e0' = refineTerm e0'
            e' = refineTerm e'
    refineTerm (Let ty f (LValue v) e) = Let ty f (LValue v) (refineTerm e)
    refineTerm (Let ty f (LApp ty0 label x v) e) = Let ty f (LApp ty0 label x v) (refineTerm e)
    refineTerm (Assume ty v e) = Assume ty v (refineTerm e)
    refineTerm (Lambda ty l x e) = Lambda ty l x (refineTerm e)
    refineTerm (Fail ty) = Fail ty
    refineTerm (Branch ty l e1 e2) = Branch ty l (refineTerm e1) (refineTerm e2)
        
    substCond :: LFormula -> Value
    substCond (Formula i xs) =
        let (ys,v) = penv M.! ("P"++show i) in
        let env = M.fromList $ zip ys (map Var xs) in
        substValue env v
    substCond (Subst theta fml) =
        let env = M.fromList $ map (\(x,v) -> (x,toValue v)) theta in
        substValue env (substCond fml)
    toValue (SVar x) = Var x
    toValue (Int i) = CInt i
    toValue (Bool b) = CBool b
    toValue (P v1 v2) = Pair (toValue v1) (toValue v2)
    toValue (Add v1 v2) = Op (OpAdd (toValue v1) (toValue v2))
    toValue (Sub v1 v2) = Op (OpSub (toValue v1) (toValue v2))
    toValue (Eq v1 v2) = Op (OpEq (toValue v1) (toValue v2))
    toValue (Lt v1 v2) = Op (OpLt (toValue v1) (toValue v2))
    toValue (Lte v1 v2) = Op (OpLte (toValue v1) (toValue v2))
    toValue (And v1 v2) = Op (OpAnd (toValue v1) (toValue v2))
    toValue (Or v1 v2) = Op (OpOr (toValue v1) (toValue v2))
    toValue (Not v1) = Op (OpNot (toValue v1))

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
