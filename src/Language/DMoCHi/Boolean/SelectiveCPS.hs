{-# LANGUAGE LambdaCase, FlexibleContexts #-}
module Language.DMoCHi.Boolean.SelectiveCPS where

import qualified Language.DMoCHi.Boolean.Syntax.Typed as B
import Language.DMoCHi.Boolean.Syntax.Typed(Size,Index)
import Control.Monad
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Except
import qualified Data.Map as M
import qualified Data.Set as S
import Language.DMoCHi.Common.Id
import Data.DList hiding(map,head,foldr,concat)
import Data.List(sort,groupBy)
import Data.Function(on)

type SLabel = String
data SSort = SX | SBool | STuple [SSort] | SFun SSort SSort SLabel 
             deriving(Eq,Ord,Show)
data Symbol = Symbol { _sort :: SSort, name :: String } deriving(Show)

instance Eq Symbol where
    (==) a b = name a == name b

instance Ord Symbol where
    compare a b = name a `compare` name b

type Def = (Symbol,Term)
data Term = C Bool
          | V Symbol
          | T SLabel [Term]
          | Lam SLabel Symbol Term
          | App SLabel SSort Term Term
          | Proj SLabel SSort Index Size Term
          | Assume SSort Term Term
          | Branch SSort Term Term
          | And SLabel Term Term
          | Or  SLabel Term Term
          | Not SLabel Term
          | Fail SSort 
          | Omega SSort deriving(Ord,Eq,Show)

-- CPSTerm should has sort s ::= X | Bool | t -> s 
--                         t ::= s | [t_1..t_k]
-- CPSApp t x := t is either CPSApp of CPSAtom
--
type CPSProgram = ([(B.Symbol,CPSTerm)],CPSTerm)
data CPSTerm = CPSTrue
             | CPSFalse
             | CPSVar B.Symbol
             | CPSLam B.Symbol CPSTerm
             | CPSApp B.Sort CPSTerm CPSTerm
             | CPSOmega                      -- X
             | CPSFail                       -- X
             | CPSBranch CPSTerm CPSTerm     -- X -> X -> X
             | CPSIf CPSTerm CPSTerm CPSTerm 
             | CPSAnd CPSTerm CPSTerm
             | CPSOr  CPSTerm CPSTerm
             | CPSNot CPSTerm
             | CPSTuple [CPSTerm]
             | CPSProj B.Sort Index Size CPSTerm
             deriving(Show) -- Bool -> X -> X -> X


instance B.HasSort CPSTerm where
    getSort CPSTrue = B.Bool
    getSort CPSFalse = B.Bool
    getSort (CPSVar x) = B.getSort x
    getSort (CPSLam x t) = B.getSort x B.:-> B.getSort t
    getSort (CPSApp s _ _) = s
    getSort CPSOmega = B.X
    getSort CPSFail = B.X
    getSort (CPSBranch _ _)= B.X
    getSort (CPSIf _ _ _) = B.X
    getSort (CPSAnd _ _) = B.Bool
    getSort (CPSOr _ _) = B.Bool
    getSort (CPSNot _) = B.Bool
    getSort (CPSTuple ts) = B.Tuple $ map B.getSort ts
    getSort (CPSProj s _ _ _) = s

f_cpsapp :: CPSTerm -> CPSTerm -> CPSTerm
f_cpsapp t1 t2 =
    let _ B.:-> s2 = B.getSort t1 in
    CPSApp s2 t1 t2

f_cpsproj :: Index -> Size -> CPSTerm -> CPSTerm
f_cpsproj idx size t =
    let B.Tuple ss = B.getSort t in
    CPSProj (ss !! idx) idx size t

data Program = Program { definitions :: [Def]
                       , mainTerm :: Term }

class HasSSort m where
    getSSort :: m -> SSort

instance HasSSort Symbol where
    getSSort = _sort

instance HasSSort Term where
    getSSort (C _) = SBool
    getSSort (V x) = getSSort x
    getSSort (T _ ts) = STuple $ map getSSort ts
    getSSort (Lam l x t) = SFun (getSSort x) (getSSort t) l
    getSSort (App _ s _ _)   = s
    getSSort (Proj _ s _ _ _) = s
    getSSort (Assume s _ _) = s
    getSSort (Branch s _ _) = s
    getSSort (And _ _ _) = SBool
    getSSort (Or _ _ _)  = SBool
    getSSort (Not _ _)   = SBool
    getSSort (Fail s) = s
    getSSort (Omega s) = s

-- insert labels
convert :: (MonadId m, Applicative m) => B.Program -> m Program
convert (B.Program ds t0) = do
    env <- M.fromList <$> buildEnv ds
    ds' <- forM ds $ \(f,t) -> 
        let s = env ! (B.name f) in
        (,) (Symbol s (B.name f)) <$> convertT env t
    t0' <- convertT env t0
    return $ Program ds' t0'

buildEnv :: (MonadId m, Applicative m) => [B.Def] -> m [(String,SSort)]
buildEnv = mapM $ \(f,_) -> (,) (B.name f) <$> convertS (B.getSort f)

(!) :: M.Map String a -> String -> a
env ! x = case M.lookup x env of
    Just v -> v
    Nothing -> error $ "no key :"++x
    
convertS :: (MonadId m, Applicative m) => B.Sort -> m SSort
convertS = \case
    B.X -> pure SX
    B.Bool -> pure SBool
    B.Tuple ts -> STuple <$> mapM convertS ts
    t1 B.:-> t2 -> do
        t1' <- convertS t1
        t2' <- convertS t2
        SFun t1' t2' <$> freshId "l"

convertT :: (MonadId m, Applicative m) => M.Map String SSort -> B.Term -> m Term
convertT env = \case
    B.C b -> pure $ C b
    B.V x -> pure $ V $ Symbol (env ! (B.name x)) (B.name x)
    B.T ts -> T <$> freshId "l" <*> mapM (convertT env) ts
    B.Lam x t -> do
        sx <- convertS $ B.getSort x 
        t' <- convertT (M.insert (B.name x) sx env) t
        label <- freshId "l"
        return $ Lam label (Symbol sx (B.name x)) t'
    B.Let _ x tx t -> 
        convertT env (B.App (B.getSort t) (B.Lam x t) tx)
    B.App _ t1 t2 -> do
        t1' <- convertT env t1
        t2' <- convertT env t2
        let SFun _ s _ = getSSort t1'
        label <- freshId "l"
        return $ App label s t1' t2'
    B.Proj _ idx size t -> do
        t' <- convertT env t
        label <- freshId "l"
        let s = (\(STuple l) -> l !! idx) $ getSSort t'
        return $ Proj label s idx size t'
    B.Assume _ t1 t2 -> do
        t1' <- convertT env t1
        t2' <- convertT env t2
        return $ Assume (getSSort t2') t1' t2'
    B.Branch _ _ t1 t2 -> do
        t1' <- convertT env t1
        t2' <- convertT env t2
        return $ Branch (getSSort t1') t1' t2'
    B.Fail x -> do
        sx <- convertS $ B.getSort x
        return $ Fail sx
    B.Omega x -> do
        sx <- convertS $ B.getSort x
        return $ Omega sx
    B.And t1 t2 -> And <$> freshId "l" <*> convertT env t1 <*> convertT env t2
    B.Or t1 t2 -> Or <$> freshId "l" <*> convertT env t1 <*> convertT env t2
    B.Not t -> Not <$> freshId "l" <*> convertT env t


-- solve constraints
type Constraint = (SLabel, LValue)
data LValue = Cont | Maximum (S.Set SLabel)

instance Monoid LValue where
    mempty = Maximum S.empty
    mappend Cont _ = Cont
    mappend _ Cont = Cont
    mappend (Maximum s1) (Maximum s2) = Maximum (S.union s1 s2)

eqLabel :: SLabel -> SLabel -> DList Constraint
eqLabel l1 l2 = 
    pure (l1,Maximum (S.singleton l2)) <>
    pure (l2,Maximum (S.singleton l1))

eqSort :: SSort -> SSort -> DList Constraint
eqSort (SFun s1 s2 l1) (SFun s3 s4 l2) = 
    eqLabel l1 l2 <> eqSort s1 s3 <> eqSort s2 s4
eqSort (STuple l1) (STuple l2) = mconcat $ zipWith eqSort l1 l2
eqSort _ _ = mempty

eqFun :: SSort -> Term -> DList Constraint
eqFun (SFun s1 s2 l1) (Lam l2 x t) =
    eqSort s1 (getSSort x) <> eqLabel l1 l2 <> case t of
            Lam _ _ _ -> eqFun s2 t
            _ -> eqSort s2 (getSSort t) <> pure (l1,Cont)
eqFun _ _ = error "unexpected pattern for eqFun"


gatherT :: Term -> Writer (DList Constraint) LValue
gatherT = \case
    C _ -> pure mempty
    V _ -> pure mempty
    T l ts -> do
        v <- mconcat <$> mapM gatherT ts 
        tell $ pure (l,v)
        return v
    Lam l x t -> do
        v <- gatherT t
        tell (pure (l,v))
        case getSSort t of
            STuple _ -> tell $ pure (l,Cont)
            _ -> return ()
        let go (SFun s1 s2 l') = do
                go s1 >> go s2
                case s2 of
                    STuple _ -> tell $ pure (l',Cont)
                    _ -> return ()
            go (STuple ts) = mapM_ go ts
            go SX = return ()
            go SBool = return ()
        go (getSSort x)
        go (getSSort t)
        pure mempty
    App l _ t1 t2 -> do
        let SFun s1 _ l1 = getSSort t1
        let s1' = getSSort t2
        tell $ eqSort s1 s1'
        v1 <- gatherT t1
        v2 <- gatherT t2
        let v = v1 <> v2 <> (Maximum (S.singleton l1))
        tell (pure (l,v))
        return v
    Proj l _ _ _ t -> do
        v <- gatherT t
        tell $ pure (l,v)
        return v
    Assume _ t1 t2 -> Cont <$ gatherT t1 <* gatherT t2 
    Branch _ t1 t2 -> Cont <$ gatherT t1 
                           <* gatherT t2 
                           <* tell (eqSort (getSSort t1) (getSSort t2))
    And l t1 t2 -> do
        v <- mappend <$> gatherT t1 <*> gatherT t2
        tell $ pure (l,v)
        return v
    Or l t1 t2 -> do
        v <- mappend <$> gatherT t1 <*> gatherT t2
        tell $ pure (l,v)
        return v
    Not l t -> do
        v <- gatherT t
        tell $ pure (l,v)
        return v
    Fail _ -> pure Cont
    Omega _ -> pure Cont

gatherP :: Program -> [Constraint]
gatherP (Program ds t0) = toList $ execWriter doit where
    doit = do
        forM_ ds $ \(f,t) -> do
            void $ gatherT t
            tell $ eqFun (getSSort f) t
        void $ gatherT t0

solve :: [Constraint] -> S.Set SLabel
solve cs = execState doit S.empty where
    conts :: [SLabel]
    conts = [ x | (x,Cont) <- cs ]
    edges :: [(SLabel,SLabel)]
    edges = do
        (x,v) <- cs
        case v of
            Cont -> mzero
            Maximum s -> do
                y <- S.toList s
                return (y,x)
    graph :: M.Map SLabel [SLabel]
    graph = M.fromList $ map (\l -> (fst $ head l, map snd l)) 
                       $ groupBy ((==) `on` fst) 
                       $ sort edges
    doit = mapM_ dfs conts
    dfs v = do
        s <- get
        when (S.notMember v s) $ do
            modify (S.insert v)
            let vs = case M.lookup v graph of
                        Just l -> l
                        Nothing -> []
            mapM_ dfs vs

-- cps transformation follows from the solution to the constraints.
transformV :: S.Set SLabel -> Symbol -> B.Symbol
transformV env x = B.Symbol (transformS env $ getSSort x) (name x)

transformS :: S.Set SLabel -> SSort -> B.Sort
transformS env = \case
    SX -> B.X 
    SBool -> B.Bool
    STuple l -> B.Tuple (map (transformS env) l)
    SFun s1 s2 label ->
        let s1' = transformS env s1
            s2' = transformS env s2 in
        if S.member label env then
            s1' B.:-> (s2' B.:-> B.X) B.:-> B.X
        else
            s1' B.:-> s2'

cps :: (MonadId m, Applicative m) => S.Set SLabel -> Term -> CPSTerm -> m CPSTerm
cps env t k =
    if requireCont env t then
        cpsC env t k
    else
        f_cpsapp k <$> cpsN env t

requireCont :: S.Set SLabel -> Term -> Bool
requireCont env = \case 
    C _ -> False
    V _ -> False
    T l _ -> S.member l env
    Lam _ _ _ -> False
    App l _ _ _ -> S.member l env
    Proj l _ _ _ _ -> S.member l env
    Assume _ _ _ -> True
    Branch _ _ _ -> True
    And l _ _ -> S.member l env
    Or  l _ _ -> S.member l env
    Not l _ -> S.member l env
    Fail _ -> True
    Omega _ -> True


cpsN :: (MonadId m, Applicative m) => S.Set SLabel -> Term -> m CPSTerm
cpsN env = \case
    C b -> pure $ if b then CPSTrue else CPSFalse
    V x -> pure $ CPSVar $ transformV env x
    T s ts | S.notMember s env -> CPSTuple <$> mapM (cpsN env) ts
    Lam l x t ->
        if S.member l env then do
            let x' = transformV env x
            k  <- freshSym "k" (transformS env (getSSort t) B.:-> B.X)
            lam x' . lam k <$> cps env t (CPSVar k)
        else do
            let x' = transformV env x
            lam x' <$> cpsN env t
    App l _ t1 t2 | S.notMember l env -> 
        f_cpsapp <$> cpsN env t1 <*> cpsN env t2
    Proj l _ idx size t | S.notMember l env -> do
        f_cpsproj idx size <$> cpsN env t
    And l t1 t2 | S.notMember l env ->
        CPSAnd <$> cpsN env t1 <*> cpsN env t2
    Or l t1 t2 | S.notMember l env ->
        CPSOr <$> cpsN env t1 <*> cpsN env t2
    Not l t | S.notMember l env -> CPSNot <$> cpsN env t
    _ -> error "unexpected pattern for cpsN"

app :: Bool -> CPSTerm -> CPSTerm -> CPSTerm
app True t k = f_cpsapp t k
app False t k = f_cpsapp k t

lam :: B.Symbol -> CPSTerm -> CPSTerm
lam x t = CPSLam x t

cpsC :: (MonadId m, Applicative m) => S.Set SLabel -> Term -> CPSTerm -> m CPSTerm
cpsC env _t k = case _t of
    App l _ t1 t2 | S.member l env -> do
        f <- freshSym "f" (transformS env (getSSort t1))
        x <- freshSym "x" (transformS env (getSSort t2))
        let SFun _ _ l' = getSSort t1
        let b = S.member l' env
        cps env t1 =<< (lam f <$>
            cps env t2 (lam x $
                app b (f_cpsapp (CPSVar f) (CPSVar x)) k))
    And l t1 t2 | S.member l env -> do
        x1 <- freshSym "and_fst" (transformS env SBool)
        x2 <- freshSym "and_snd" (transformS env SBool)
        cps env t1 =<< (lam x1 <$>
            cps env t2 (lam x2 $ f_cpsapp k (CPSAnd (CPSVar x1) (CPSVar x2))))
    Or l t1 t2 | S.member l env -> do
        x1 <- freshSym "or_fst" (transformS env SBool)
        x2 <- freshSym "or_snd" (transformS env SBool)
        cps env t1 =<< (lam x1 <$>
            cps env t2 (lam x2 $ f_cpsapp k (CPSOr (CPSVar x1) (CPSVar x2))))
    Not l t | S.member l env -> do
        x <- freshSym "not" (transformS env SBool)
        cps env t (lam x $ f_cpsapp k (CPSNot (CPSVar x)))
    T l ts | S.member l env -> do
        xs <- mapM (\t -> freshSym "x" $ transformS env (getSSort t)) ts
        let t0 = f_cpsapp k (CPSTuple $ map CPSVar xs)
        foldM (\t (ti,xi) -> cps env ti (lam xi t)) t0 (reverse $ zip ts xs)
    Proj l _ idx size t | S.member l env -> do
        x <- freshSym "proj" (transformS env (getSSort t))
        cps env t (lam x $ f_cpsapp k (f_cpsproj idx size (CPSVar x)))
    Assume _ t1 t2 -> do
        b <- freshSym "assume_pred" (transformS env SBool)
        cps env t1 =<< (lam b <$> 
            (CPSIf (CPSVar b) <$> (cps env t2 k) <*> pure CPSOmega))
    Fail _ -> pure CPSFail
    Omega _ -> pure CPSOmega
    Branch _ t1 t2 -> do
        k' <- freshSym "k" (transformS env (getSSort t1) B.:-> B.X)
        t' <- CPSBranch <$> cps env t1 (CPSVar k') <*> cps env t2 (CPSVar k')
        return $ f_cpsapp (lam k' t') k
    _ -> error "unexpected pattern for cpsC"

freshSym :: MonadId m => String -> B.Sort -> m B.Symbol
freshSym _name s = freshId _name >>= \x -> return (B.Symbol s x)

selectiveCPS :: (MonadId m,Applicative m) => B.Program -> m ([(B.Symbol,CPSTerm)],CPSTerm)
selectiveCPS p = do
    sp@(Program ds t0) <- convert p
    let cs = gatherP sp
    let env = solve cs
    ds' <- forM ds $ \(f,t) -> 
        (,) (transformV env f) <$> cpsN env t
    k <- freshSym "k" (transformS env (getSSort t0))
    t0' <- cps env t0 (lam k CPSOmega)
    return $ (ds',t0')


-- 
--
-- tuple elimination
-- resulting terms are consistent to the following syntax
--  sort s := o | bool | s1 -> s2
--  term
--  t_o := t1_(s -> o) t2_s
--      | omega | fail
--      | if t_bool t1_o t2_o
--      | branch t1_o t2_o
--      | x_o
--  t_bool := true | false
--         |  x_bool 
--         |  t1_(s -> bool) t2_s
--         |  t_bool && t_bool
--         |  t_bool || t_bool
--         |  not t_bool
--  t_(s1 -> s2) := fun (x:s1) -> t_s2
--               | t1_(s -> s1 -> s2) t2_s
--  program
--   p := let rec { fi_s = t_(s1 -> ... -> sk -> o)  | i <- [1..l] } in t_o
--
--
--
data Tree a = Node [Tree a] | Leaf a deriving(Show)

instance Functor Tree where
    fmap f (Leaf a) = Leaf (f a)
    fmap f (Node ts) = Node (map (fmap f) ts)

iterTree :: (Monad m,Functor m) => Tree a -> (a -> m b) -> m (Tree b)
iterTree _t f = go _t where
    go (Node ts) = Node <$> mapM go ts
    go (Leaf x) = Leaf <$> f x

flatten :: Tree a -> [a]
flatten (Node ts) = concatMap flatten ts
flatten (Leaf x) = return x

elimTupleSort :: B.Sort -> B.Sort
elimTupleSort (t1 B.:-> t2) = foldr (B.:->) (elimTupleSort t2) $ flatten (currySort t1)
elimTupleSort B.X = B.X
elimTupleSort B.Bool = B.Bool
elimTupleSort x = error $ "elimTupleSort " ++ show x

currySort :: B.Sort -> Tree B.Sort
currySort (B.Tuple ss) = Node $ map currySort ss
currySort t = Leaf $ elimTupleSort t

elimTuple :: (MonadId m,Applicative m) => M.Map B.Symbol (Tree CPSTerm) -> CPSTerm -> m CPSTerm
elimTuple env (CPSLam x t) = do
    ys <- do
        let ss = currySort (B.getSort x)
        iterTree ss (\s -> freshSym (B.name x) s)
    let env' = M.insert x (fmap CPSVar ys) env
    t' <- elimTuple env' t
    return $ foldr lam t' (flatten ys)
elimTuple env (CPSApp _ t1 t2) = do
    t1' <- elimTuple env t1
    t2' <- elimTupleT env t2
    let ts2 = flatten t2'
    return $ foldl (f_cpsapp) t1' ts2
elimTuple _ CPSTrue = return CPSTrue
elimTuple _ CPSFalse = return CPSFalse
elimTuple env (CPSBranch t1 t2) = CPSBranch <$> elimTuple env t1 <*> elimTuple env t2
elimTuple _ CPSFail = return CPSFail
elimTuple _ CPSOmega = return CPSOmega
elimTuple env (CPSIf b t1 t2) = CPSIf <$> elimTuple env b <*> elimTuple env t1 <*> elimTuple env t2
elimTuple env (CPSAnd t1 t2) = CPSAnd <$> elimTuple env t1 <*> elimTuple env t2
elimTuple env (CPSOr t1 t2) = CPSOr <$> elimTuple env t1 <*> elimTuple env t2
elimTuple env (CPSNot t) = CPSNot <$> elimTuple env t
elimTuple env (CPSVar x) = 
    let x' = case env M.! x of
            Leaf a -> a
            xs  -> error $ "unexpected tuple" ++ show (x,xs) in
    return x'
elimTuple env (CPSProj _ idx _ t) = do
    Node ts <- elimTupleT env t
    let Leaf v = ts !! idx
    return v
elimTuple _ (CPSTuple _) = error "unexpected tuple constructor for elimTuple"

elimTupleT :: (MonadId m, Applicative m) => M.Map B.Symbol (Tree CPSTerm) -> CPSTerm -> m (Tree CPSTerm)
elimTupleT env (CPSProj _ idx _ t) = (\(Node ts) -> ts !! idx) <$> elimTupleT env t
elimTupleT env (CPSTuple ts) = Node <$> mapM (elimTupleT env) ts
elimTupleT env (CPSVar x) = return $ env M.! x
elimTupleT env t = Leaf <$> elimTuple env t

elimTupleP :: (MonadId m,Applicative m) => ([(B.Symbol,CPSTerm)],CPSTerm) -> m ([(B.Symbol,CPSTerm)],CPSTerm) 
elimTupleP (ds,t0) = do
    let ds1 = map (\(x,t) -> (B.modifySort elimTupleSort x,t)) ds
    let env = M.fromList $ [ (y,Leaf $ CPSVar y) | (y,_) <- ds1 ]
    ds' <- forM ds1 $ \(y,t) -> do
        t' <- elimTuple env t
        return (y,t')
    t0' <- elimTuple env t0
    return (ds',t0')


tCheck :: (Monad m,Applicative m) => 
          ([(B.Symbol,CPSTerm)],CPSTerm) -> ExceptT (B.Sort,B.Sort,String) m ()
tCheck (ds,t0) = doit where
    check str s1 s2 = when (s1 /= s2) $ throwError (s1,s2,str)
    doit = do
        forM_ ds $ \(x,t) -> do
            check "let rec" (B.getSort x) =<< go t
        check "main" B.X =<< go t0
    go = \case
        CPSTrue -> return B.Bool
        CPSFalse -> return B.Bool
        CPSVar x -> return $ B.getSort x
        CPSFail -> return B.X
        CPSOmega -> return B.X
        CPSTuple _ -> error "tCheck: cannot be a tuple"
        CPSProj _ _ _ _ -> error "tCheck: cannot be a projection"
        CPSBranch t1 t2 -> do
            check "branch fst" B.X =<< go t1
            check "branch snd" B.X =<< go t2
            return B.X
        CPSLam x v -> (B.:->) (B.getSort x) <$> go v
        CPSApp _ t1 t2 -> do
            s1 <- go t1
            s2 <- go t2
            case s1 of
                s2' B.:-> s3 -> check "app arg" s2 s2' >> return s3
                _ -> throwError (s1,s1,"app fun")
        CPSIf t1 t2 t3 -> do
            check "if pred" B.Bool =<< go t1
            check "if then" B.X =<< go t2
            check "if else" B.X =<< go t3
            return B.X
        CPSAnd t1 t2 -> do
            check "opAnd fst" B.Bool =<< go t1
            check "opAnd snd" B.Bool =<< go t2
            return B.Bool
        CPSOr t1 t2 -> do
            check "opOr fst" B.Bool =<< go t1
            check "opOr snd" B.Bool =<< go t2
            return B.Bool
        CPSNot t1 -> do
             check "opNot arg" B.Bool =<< go t1
             return B.Bool


-- Boolean elimination
-- resulting terms are consistent to the following syntax
--  sort s := o | (bool == o -> o -> o) | s1 -> s2
--  term
--  t_o := t1_(s -> o) t2_s
--      | omega | fail
--      | if t_bool t1_o t2_o
--      | branch t1_o t2_o
--      | x_o
--  t_bool := true | false
--         |  x_bool 
--         |  t1_(s -> bool) t2_s
--  t_(s1 -> s2) := fun (x:s1) -> t_s2
--               | t1_(s -> s1 -> s2) t2_s
--  program
--   p := let rec { fi_s = t_(s1 -> ... -> sk -> o)  | i <- [1..l] } in t_o
--  
elimBoolSort :: B.Sort -> B.Sort
elimBoolSort (t1 B.:-> t2) = elimBoolSort t1 B.:-> elimBoolSort t2
elimBoolSort B.Bool = B.X B.:-> B.X B.:-> B.X
elimBoolSort B.X = B.X
elimBoolSort x = error $ "elimBoolSort" ++ show x


elimBoolEnv :: (MonadId m, Applicative m) => m [(String,(B.Symbol,CPSTerm))]
elimBoolEnv = do
    let tbool = elimBoolSort B.Bool
        tbase = B.X
    c_true <- freshSym "true" tbool
    t_true <- do
        x <- freshSym "x" B.X
        y <- freshSym "y" B.X
        return $ CPSLam x $ CPSLam y $ CPSVar x

    c_false <- freshSym "false" tbool
    t_false <- do
        x <- freshSym "x" B.X
        y <- freshSym "y" B.X
        return $ CPSLam x $ CPSLam y $ CPSVar y

    c_and <- freshSym "and" (tbool B.:-> tbool B.:-> tbool)
    t_and <- do
        x <- freshSym "x" tbool
        y <- freshSym "y" tbool
        z <- freshSym "z" tbase
        w <- freshSym "w" tbase
        return $ CPSLam x $ CPSLam y $ CPSLam z $ CPSLam w $
            CPSVar x `f_cpsapp` (CPSVar y `f_cpsapp` CPSVar z `f_cpsapp` CPSVar w)
                     `f_cpsapp` CPSVar w
    
    c_or <- freshSym "or" (tbool B.:-> tbool B.:-> tbool)
    t_or <- do
        x <- freshSym "x" tbool
        y <- freshSym "y" tbool
        z <- freshSym "z" tbase
        w <- freshSym "w" tbase
        return $ CPSLam x $ CPSLam y $ CPSLam z $ CPSLam w $
            CPSVar x `f_cpsapp` CPSVar z 
                     `f_cpsapp` (CPSVar y `f_cpsapp` CPSVar z `f_cpsapp` CPSVar w)

    c_not <- freshSym "not" (tbool B.:-> tbool)
    t_not <- do
        x <- freshSym "x" tbool
        y <- freshSym "y" tbase
        z <- freshSym "z" tbase
        return $ CPSLam x $ CPSLam y $ CPSLam z $
            CPSVar x `f_cpsapp` CPSVar z
                     `f_cpsapp` CPSVar y

    c_if <- freshSym "if" (tbool B.:-> tbool)
    t_if <- do
        x <- freshSym "x" tbool
        y <- freshSym "y" tbase
        z <- freshSym "z" tbase
        return $ CPSLam x $ CPSLam y $ CPSLam z $
            CPSVar x `f_cpsapp` CPSVar y
                     `f_cpsapp` CPSVar z
    
    return [("true",(c_true,t_true))
           ,("false",(c_false,t_false))
           ,("and",(c_and,t_and))
           ,("or",(c_or,t_or))
           ,("not",(c_not,t_not))
           ,("if",(c_if,t_if))]

elimBoolP :: (MonadId m,Applicative m) => ([(B.Symbol,CPSTerm)], CPSTerm) -> m ([(B.Symbol,CPSTerm)],CPSTerm)
elimBoolP (ds,t0) = do
    env <- elimBoolEnv
    let env' = M.fromList [ (x,CPSVar x') | (x,(x',_)) <- env ]
    let ds' = map (\(x,t) -> (B.modifySort elimBoolSort x, elimBool env' t)) ds
    let t0' = elimBool env' t0
    return (map snd env++ds',t0')

elimBool :: M.Map String CPSTerm -> CPSTerm -> CPSTerm
elimBool env CPSTrue = env M.! "true"
elimBool env CPSFalse = env M.! "false"
elimBool _ (CPSVar x) = CPSVar (B.modifySort elimBoolSort x)
elimBool _ (CPSTuple _) = error "elimBool: unexpected projection"
elimBool _ (CPSProj _ _ _ _) = error "elimBool: unexpected projection"
elimBool env (CPSIf b t1 t2) =
    (env M.! "if") `f_cpsapp` elimBool env b
                   `f_cpsapp` elimBool env t1
                   `f_cpsapp` elimBool env t2
elimBool env (CPSAnd t1 t2) = 
    (env M.! "and") `f_cpsapp` elimBool env t1
                    `f_cpsapp` elimBool env t2
elimBool env (CPSOr t1 t2) =
    (env M.! "or") `f_cpsapp` elimBool env t1
                   `f_cpsapp` elimBool env t2
elimBool env (CPSNot t) =
    (env M.! "not") `f_cpsapp` elimBool env t
elimBool env (CPSLam x t) = CPSLam (B.modifySort elimBoolSort x) (elimBool env t)
elimBool env (CPSApp _ t1 t2) = f_cpsapp (elimBool env t1) (elimBool env t2)
elimBool _ (CPSOmega) = CPSOmega
elimBool _ (CPSFail) = CPSFail
elimBool env (CPSBranch t1 t2) = CPSBranch (elimBool env t1) (elimBool env t2)

