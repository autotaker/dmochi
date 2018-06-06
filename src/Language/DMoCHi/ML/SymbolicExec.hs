module Language.DMoCHi.ML.SymbolicExec where

import           Control.Monad.Writer
import           Control.Monad.State.Strict
import qualified Data.Map as M
import qualified Language.Dot as Dot
import           Text.Printf
import           Data.List(intersperse,foldl')
import           Data.Int
import           Data.Bits
import           Text.PrettyPrint.HughesPJClass hiding((<>))

import qualified Language.DMoCHi.ML.Syntax.PNormal as ML
-- import qualified Language.DMoCHi.ML.PrettyPrint.PNormal as ML
import           Language.DMoCHi.Common.Id hiding(Id)

type Trace = [Bool]
newtype CallId = CallId { unCallId :: Int } deriving (Eq,Ord)
newtype ClosureId = ClosureId { unClosureId :: Int } deriving (Eq,Ord)

instance Show CallId where
    show (CallId x) = show x

instance Show ClosureId where
    show (ClosureId x) = show x

type Constraint = SValue -- must have the sort Bool
data CallInfo = CallInfo { calleeId :: ClosureId   -- 呼び出されたクロージャの識別子
                         , callLabel :: UniqueKey     -- 対応する関数呼び出しのラベル
                         , pcallId  :: CallId   -- 親関数呼び出しの識別子
                         , callId   :: CallId   -- 関数呼び出しの識別子
                         , callContext :: CompTreePath -- 関数呼び出しの計算木での位置
                         , callAccessors :: [Accessor] -- accessors affected by the call  
                     } deriving Show

-- クロージャ生成の情報
data ClosureInfo = ClosureInfo { label :: UniqueKey -- 対応する関数定義のラベル
                               , closure :: Closure -- 生成されたクロージャ
                               , cCallId :: CallId -- クロージャ生成時の関数呼び出し識別子
                               } deriving Show
-- 関数返り値の情報
data ReturnInfo = ReturnInfo { rcallId :: CallId -- 関数呼び出しの識別子
                             , argValues :: [SValue] -- 引数
                             , retValue :: Maybe SValue -- 返り値(ないときはfailを表す)
                             } deriving Show

-- Let式の評価結果情報
data LetExpInfo = LetExpInfo { lCallId :: CallId -- 評価時の親関数呼び出し識別子
                             , lLabel :: UniqueKey -- 呼び出されたlet式のラベル
                             , evalValue :: Maybe SValue -- 評価結果(ないときはfailを表す)
                             , lContext :: CompTreePath  -- let式の計算木での位置
                             } deriving Show

-- 分岐情報
data BranchInfo = BranchInfo { bCallId   :: CallId, 
                               branchId  :: UniqueKey,
                               direction :: Bool} deriving Show

type CompTreePath = [Int]

-- Symbolic Values
data SValue = SVar Id
            | Int Integer
            | Bool Bool
            | P SValue SValue
            | Add SValue SValue
            | Sub SValue SValue
            | Mul SValue SValue
            | Div SValue SValue
            | Eq SValue SValue
            | Lt SValue SValue
            | Lte SValue SValue
            | And SValue SValue
            | Or SValue SValue
            | Not SValue
            | Neg SValue
            | C Closure

data Closure = Cls { clsBody :: (UniqueKey, [ML.TId], ML.Exp)
                   , clsId :: ClosureId {- Ident -} 
                   , clsEnv :: Env 
                   , clsAccessors :: [Accessor] }

data Accessor = AVar CallId Id 
              | ARet CallId ML.Type
              | AFst Accessor
              | ASnd Accessor
              deriving Eq

instance Show Accessor where
    show (AVar j x) = printf "%s[%d]" (show $ ML.name x) (unCallId j)
    show (ARet j _) = printf "<ret>[%d]" (unCallId j)
    show (AFst v)   = show v ++ ".fst"
    show (ASnd v)   = show v ++ ".snd"

instance ML.HasType Accessor where
    getType (AVar _ x) = ML.getType x
    getType (ARet _ ty) = ty
    getType (AFst v) = 
        let ML.TPair a _ = ML.getType v in a
    getType (ASnd v) = 
        let ML.TPair _ b = ML.getType v in b

instance ML.HasType SValue where
    getType (SVar x)  = ML.getType x
    getType (Int _)   = ML.TInt
    getType (Bool _)  = ML.TBool
    getType (P v1 v2) = ML.TPair (ML.getType v1) (ML.getType v2)
    getType (Add _ _) = ML.TInt
    getType (Sub _ _) = ML.TInt
    getType (Mul _ _) = ML.TInt
    getType (Div _ _) = ML.TInt
    getType (Eq _ _)  = ML.TBool
    getType (Lt _ _)  = ML.TBool
    getType (Lte _ _) = ML.TBool
    getType (And _ _) = ML.TBool
    getType (Or  _ _) = ML.TBool
    getType (Not _) = ML.TBool
    getType (Neg _) = ML.TInt
    getType (C cls)   = ML.getType cls

instance Show SValue where
    showsPrec d (SVar x) | d >= 3 = showString (show $ ML.name x)
                         | otherwise = showString (show $ ML.name x) . showString " : " . shows (ML.getType x)
    showsPrec _ (Int i) = shows i
    showsPrec _ (Bool b) = shows b
    showsPrec _ (P v1 v2) = 
        showString "(" .  shows v1 . showString ", " . shows v2 . showString ")"
    showsPrec d (Add v1 v2) =
        showParen (d >= 6) $ (showsPrec 6 v1) . (showString " + ") . (showsPrec 6 v2)
    showsPrec d (Sub v1 v2) = 
        showParen (d >= 6) $ (showsPrec 6 v1) . (showString " - ") . (showsPrec 6 v2)
    showsPrec d (Mul v1 v2) = 
        showParen (d >= 7) $ (showsPrec 7 v1) . (showString " * ") . (showsPrec 7 v2)
    showsPrec d (Div v1 v2) = 
        showParen (d >= 7) $ (showsPrec 7 v1) . (showString " / ") . (showsPrec 7 v2)
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
    showsPrec d (Neg v1) = 
        showParen (d >= 8) $ (showString "- ") . showsPrec 8 v1
    showsPrec d (C cls) = showsPrec d cls
                       

instance ML.HasType Closure where
    getType cls = ML.TFun (map ML.getType xs) (ML.getType e0)
        where
        (_, xs, e0) = clsBody cls

instance Show Closure where
    showsPrec d (Cls (i,_,_) x _ _) = showParen (d > app_prec) $
        showString "Cls " . showsPrec (app_prec+1) (show i) . showChar ' ' . showsPrec (app_prec + 1) x
        where
        app_prec = 10

data CompTree = CompTree { expr :: ML.Exp
                         , subTrees :: [(Int,CompTreeInfo,CompTree)] }
data CompTreeInfo = InfoBind [(Id,SValue)]
                  | InfoAssume SValue
                  | InfoNone

type Env = M.Map Id SValue
type Id = ML.TId

-- type Log = ([Constraint],[CallInfo],[ClosureInfo],[ReturnInfo],([BranchInfo],[LetExpInfo]))
data Log = Log { logCnstr :: [Constraint]
               , logCall :: [CallInfo]
               , logClosure :: [ClosureInfo]
               , logReturn :: [ReturnInfo]
               , logBranch  :: [BranchInfo]
               , logLetExp :: [LetExpInfo] }
               deriving (Show)

instance Monoid Log where
    mappend (Log a1 a2 a3 a4 a5 a6) (Log b1 b2 b3 b4 b5 b6) = 
        Log (a1 <> b1) (a2 <> b2) (a3 <> b3) (a4 <> b4) (a5 <> b5) (a6 <> b6)
    mempty = Log [] [] [] [] [] []

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
    SVar x -> ML.cast $ ML.mkVar x
    Int i  -> ML.cast $ ML.mkLiteral $ ML.CInt i
    Bool b -> ML.cast $ ML.mkLiteral $ ML.CBool b
    P v1 v2 -> ML.mkPair (fromSValue v1) (fromSValue v2) reservedKey
    Add v1 v2 -> bin (ML.mkBin ML.SAdd) v1 v2
    Sub v1 v2 -> bin (ML.mkBin ML.SSub) v1 v2
    Mul v1 v2 -> bin (ML.mkBin ML.SMul) v1 v2
    Div v1 v2 -> bin (ML.mkBin ML.SDiv) v1 v2
    Eq v1 v2 -> bin (ML.mkBin ML.SEq) v1 v2
    Lt v1 v2 -> bin (ML.mkBin ML.SLt) v1 v2
    Lte v1 v2 -> bin (ML.mkBin ML.SLte) v1 v2
    And v1 v2 -> bin (ML.mkBin ML.SAnd) v1 v2
    Or v1 v2 -> bin (ML.mkBin ML.SOr) v1 v2
    Not v1 -> unary (ML.mkUni ML.SNot) v1
    Neg v1 -> unary (ML.mkUni ML.SNeg) v1
    C _ -> error "Cannot convert a closure to a syntactic value"
    where
    bin :: (ML.Atom -> ML.Atom -> ML.Atom) -> SValue -> SValue -> ML.Value
    bin f v1 v2 = 
        case (ML.valueView (fromSValue v1), ML.valueView (fromSValue v2)) of
            (ML.VAtom av1, ML.VAtom av2) -> ML.cast $ f av1 av2
            _ -> error "fromSValue: unexpected pattern"
    unary :: (ML.Atom -> ML.Atom) -> SValue -> ML.Value
    unary f v1 = 
        case ML.valueView (fromSValue v1) of
            ML.VAtom av1 -> ML.cast $ f av1
            _ -> error "fromSValue : unexpected pattern"
    

leaf :: ML.Exp -> CompTree
leaf e = CompTree e []

bindCls :: CallId -> Id -> SValue -> SValue
bindCls callId = bindClsA . AVar callId

bindClsR :: CallId -> SValue -> SValue
bindClsR j sv = bindClsA (ARet j (ML.getType sv)) sv

bindClsA :: Accessor -> SValue -> SValue
bindClsA acsr (C cls) = C cls{ clsAccessors = acsr : clsAccessors cls }
bindClsA acsr (P v1 v2) = P (bindClsA (AFst acsr) v1) (bindClsA (ASnd acsr) v2)
bindClsA _acsr v = v

symbolicExec :: forall m. (MonadId m, MonadFix m) => ML.Program -> Trace -> m (M.Map Id SValue, Log, CompTree)
symbolicExec prog trace = do
    ((m,tree),log) <- runWriterT $ evalStateT (genEnv >>= (\genv -> do
        (t,_) <- eval (CallId 0) genv [] (ML.mainTerm prog)
        return (genv,t))) (S 1 0 trace)
    return (m,log,tree)
    where
    genEnv = mfix $ \genv -> do
        es <- forM (ML.functions prog) $ \(f, key, xs, e) -> do
            c <- genClosure (CallId 0) (key,xs,e) genv
            return (f,bindCls (CallId 0) f (C c))
        return $ M.fromList es
    eval :: CallId -> Env -> CompTreePath -> ML.Exp -> M m (CompTree, Maybe SValue)
    eval callSite env path _e@(ML.Exp l arg sty key) = 
        let valueCase v = evalV callSite env v >>= \sv -> return (leaf _e, Just sv)
        in case (l,arg) of
            (ML.SLiteral, _) -> valueCase (ML.Value l arg sty key)
            (ML.SVar, _)     -> valueCase (ML.Value l arg sty key)
            (ML.SBinary,_)   -> valueCase (ML.Value l arg sty key)
            (ML.SUnary,_)    -> valueCase (ML.Value l arg sty key)
            (ML.SPair,_)     -> valueCase (ML.Value l arg sty key)
            (ML.SLambda,_)   -> valueCase (ML.Value l arg sty key)
            (ML.SLet, (x, lv, e)) -> do
                (info,t1,r) <- evalLV callSite env (1:path) lv
                case fmap (bindCls callSite x) r of
                    Just sv -> do
                        (t2,r) <- eval callSite (M.insert x sv env) (2:path) e
                        let t = CompTree _e [(1,info,t1),(2,InfoBind [(x,sv)],t2)]
                        return (t,r)
                    Nothing -> do
                        let t = CompTree _e [(1,info,t1)]
                        return (t, Nothing)
            (ML.SLetRec, (fs,e)) -> do
                env' <- mfix $ \genv -> do
                    es <- forM fs $ \(f,v) -> do
                        let (key,xs,e) = case v of
                                ML.Value ML.SLambda (xs,e) _ key -> (key,xs,e)
                                _ -> error "unexpected"
                        c <- genClosure callSite (key,xs,e) genv
                        return (f, bindCls callSite f (C c))
                    return $ foldr (uncurry M.insert) env es
                (t2,r) <- eval callSite env' (1:path) e
                let binds = [(f, env' M.! f) | (f,_) <- fs ]
                return (CompTree _e [(1,InfoBind binds, t2)], r)
            (ML.SAssume, (v, e)) -> do
                let phi = evalA env v
                constrain phi
                (t,r) <- eval callSite env (1:path) e
                return (CompTree _e [(1,InfoAssume phi,t)],r)
            (ML.SFail, _) -> return (leaf _e,Nothing)
            (ML.SOmega, _) -> return (leaf _e,Nothing)
            (ML.SBranch, (e1, e2)) -> do
                let i = key
                mb <- consume
                case mb of
                    Just b -> do
                        branch (BranchInfo callSite i b)
                        if b then do
                            (t,r) <- eval callSite env (1:path) e1
                            return (CompTree _e [(1,InfoNone,t)],r)
                        else do
                            (t,r) <- eval callSite env (2:path) e2
                            return (CompTree _e [(2,InfoNone,t)],r)
                    Nothing -> return (CompTree _e [], Nothing)

    evalV :: CallId -> Env -> ML.Value -> M m SValue
    evalV callSite env (ML.Value l arg sty key) =
        case l of
            ML.SLiteral -> pure $ evalA env (ML.Atom l arg sty)
            ML.SVar     -> pure $ evalA env (ML.Atom l arg sty)
            ML.SBinary  -> pure $ evalA env (ML.Atom l arg sty)
            ML.SUnary   -> pure $ evalA env (ML.Atom l arg sty)
            ML.SPair    -> 
                let (v1,v2) = arg in
                P <$> evalV callSite env v1 <*> evalV callSite env v2
            ML.SLambda  -> C <$> genClosure callSite (key,fst arg, snd arg) env
    evalA :: Env -> ML.Atom -> SValue
    evalA env (ML.Atom l arg _) = case (l,arg) of
        (ML.SVar, x) -> case M.lookup x env of Just v -> v 
                                               Nothing -> error $ "lookup error: key " ++ (show x)
        (ML.SLiteral, ML.CInt x) -> Int x
        (ML.SLiteral, ML.CBool x) -> Bool x
        (ML.SLiteral, _) -> error "unexpected unit"
        (ML.SBinary, ML.BinArg op v1 v2) -> case op of
            ML.SAdd -> Add (evalA env v1) (evalA env v2)
            ML.SSub -> Sub (evalA env v1) (evalA env v2)
            ML.SMul -> Mul (evalA env v1) (evalA env v2)
            ML.SDiv -> Div (evalA env v1) (evalA env v2)
            ML.SEq  -> Eq  (evalA env v1) (evalA env v2)
            ML.SLt  -> Lt  (evalA env v1) (evalA env v2)
            ML.SLte -> Lte (evalA env v1) (evalA env v2)
            ML.SAnd -> And (evalA env v1) (evalA env v2)
            ML.SOr  -> Or  (evalA env v1) (evalA env v2)
        (ML.SUnary, ML.UniArg op v1) -> case op of
            ML.SFst -> let P sv _ = evalA env v1 in sv
            ML.SSnd -> let P _ sv = evalA env v1 in sv
            ML.SNot -> Not (evalA env v1)
            ML.SNeg -> Neg (evalA env v1)
    evalLV :: CallId -> Env -> CompTreePath -> ML.LExp -> M m (CompTreeInfo, CompTree,Maybe SValue)
    evalLV callSite env path (ML.LExp l arg sty key) = 
        let atomCase :: ML.Atom -> M m (CompTreeInfo, CompTree, Maybe SValue)
            atomCase v = pure $ (InfoNone, leaf (ML.castWith key v), Just (evalA env v))
            exprCase e = do
                (t,r) <- eval callSite env path e
                letexp (LetExpInfo callSite key r path)
                return (InfoNone,t,r)
        in case (l, arg) of
            (ML.SLiteral, _) -> atomCase $ ML.Atom l arg sty
            (ML.SVar, _)     -> atomCase $ ML.Atom l arg sty
            (ML.SBinary, _)  -> atomCase $ ML.Atom l arg sty
            (ML.SUnary, _)   -> atomCase $ ML.Atom l arg sty
            (ML.SPair, _)    -> exprCase $ ML.Exp l arg sty key
            (ML.SLambda, _)  -> exprCase $ ML.Exp l arg sty key
            (ML.SBranch, _)  -> exprCase $ ML.Exp l arg sty key
            (ML.SFail, _)    -> exprCase $ ML.Exp l arg sty key
            (ML.SOmega, _)    -> exprCase $ ML.Exp l arg sty key
            (ML.SApp, (f,vs)) -> do
                svs <- mapM (evalV callSite env) vs
                let C (Cls (_, xs, e0) clsId env' acsrs) = env M.! f
                j <- newCall key callSite path clsId acsrs
                let as = [ (x, bindCls j x sv) | (x,sv) <- zip xs svs ]
                let env'' = foldr (uncurry M.insert) env' as
                let info = InfoBind (zip xs svs ++ M.toList env')
                (t,r) <- eval j env'' path e0
                let r' = fmap (bindClsR j) r
                retval (ReturnInfo j svs r')
                return (info,t,r')
            -- ML.LFun fdef -> Just . C <$> genClosure callSite fdef env
            (ML.SRand, _) -> do
                r <- Just . SVar . ML.TId ML.TInt <$> identify "rand"
                return (InfoNone,leaf (ML.cast (ML.mkVar (ML.TId ML.TInt (reserved "*")))), r)

    -- utilities
    constrain :: Constraint -> M m ()
    constrain c = tell (Log [c] [] [] [] [] [])
    branch :: BranchInfo -> M m ()
    branch c = tell (Log [] [] [] [] [c] [])
    retval :: ReturnInfo -> M m ()
    retval c = tell (Log [] [] [] [c] [] [])
    letexp c = tell (Log [] [] [] [] [] [c])
    newCall :: UniqueKey -> CallId -> CompTreePath -> ClosureId -> [Accessor] -> M m CallId
    newCall i pcall path clsId acsrs = do
        j <- callCounter <$> get
        modify incrCall
        tell (Log [] [CallInfo clsId i pcall (CallId j) path acsrs] [] [] [] [])
        return (CallId j)
    genClosure :: CallId -> (UniqueKey, [ML.TId], ML.Exp) -> Env -> M m Closure
    genClosure callSite fdef@(key,_,_) env = do
        j <- clsCounter <$> get
        modify incrCls
        let cls = (Cls fdef (ClosureId j) env [])
        tell (Log [] [] [ClosureInfo key cls callSite] [] [] [])
        return cls
    consume :: M m (Maybe Bool)
    consume = do
        l <- cTrace <$> get
        case l of
            (b:_) -> modify pop >> return (Just b)
            [] -> return Nothing

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
            value = Dot.StringId $ takeWhile (/='\n') $ show $ pPrint e
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
                                        printf "%s = %s" (show $ ML.name x) (show sv) | (x,sv) <- binds ]) ++ " }" in
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

