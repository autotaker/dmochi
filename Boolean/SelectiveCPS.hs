{-# LANGUAGE LambdaCase #-}
module Boolean.SelectiveCPS where

import qualified Boolean.Syntax.Typed as B
import Boolean.Syntax.Typed(Size,Index)
import Control.Monad
import Control.Monad.Writer
import Control.Monad.State
import Control.Applicative
import Control.Monad.Except
import qualified Data.Map as M
import qualified Data.Set as S
import Id
import Data.DList hiding(map,head,foldr,concat)
import Data.List(sort,groupBy)
import Data.Function(on)
import Data.Either

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
          | Fail Symbol deriving(Ord,Eq,Show)

-- CPSTerm should has sort s ::= X | Bool | t -> s 
--                         t ::= s | [t_1..t_k]
-- CPSApp t x := t is either CPSApp of CPSAtom
--
type CPSProgram = ([(B.Symbol,CPSTerm)],CPSTerm)
data CPSTerm = CPSTrue
             | CPSFalse
             | CPSVar B.Symbol
             | CPSLam [B.Symbol] CPSTerm
             | CPSApp B.Sort CPSTerm CPSTerm
             | CPSOmega                      -- X
             | CPSFail                       -- X
             | CPSBranch CPSTerm CPSTerm     -- X -> X -> X
             | CPSIf CPSTerm CPSTerm CPSTerm 
             | CPSAnd CPSTerm CPSTerm
             | CPSOr  CPSTerm CPSTerm
             | CPSNot CPSTerm
             | CPSTuple [CPSTerm]
             deriving(Show) -- Bool -> X -> X -> X


instance B.HasSort CPSTerm where
    getSort CPSTrue = B.Bool
    getSort CPSFalse = B.Bool
    getSort (CPSVar x) = B.getSort x
    getSort (CPSLam [x] t) = B.getSort x B.:-> B.getSort t
    getSort (CPSApp s _ _) = s
    getSort CPSOmega = B.X
    getSort CPSFail = B.X
    getSort (CPSBranch _ _)= B.X
    getSort (CPSIf _ _ _) = B.X
    getSort (CPSAnd _ _) = B.Bool
    getSort (CPSOr _ _) = B.Bool
    getSort (CPSNot _) = B.Bool
    getSort (CPSTuple ts) = B.Tuple $ map B.getSort ts
    getSort _ = error "getSort"

f_cpsapp t1 t2 =
    let _ B.:-> s2 = B.getSort t1 in
    CPSApp s2 t1 t2

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
    getSSort (Fail x) = getSSort x

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
    B.Branch _ t1 t2 -> do
        t1' <- convertT env t1
        t2' <- convertT env t2
        return $ Branch (getSSort t1') t1' t2'
    B.Fail x -> do
        sx <- convertS $ B.getSort x
        return $ Fail $ Symbol sx (B.name x)
    B.And t1 t2 -> And <$> freshId "l" <*> convertT env t1 <*> convertT env t2
    B.Or t1 t2 -> Or <$> freshId "l" <*> convertT env t1 <*> convertT env t2
    B.Not t -> Not <$> freshId "l" <*> convertT env t

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
    Proj l _ idx _ t | S.notMember l env -> do
        let B.Tuple ss = transformS env (getSSort t)
        xs <- mapM (freshSym "proj") ss
        f_cpsapp (CPSLam xs (CPSVar (xs !! idx))) <$> cpsN env t
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
lam x t = CPSLam [x] t

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
    Proj l _ idx _ t | S.member l env -> do
        let B.Tuple ss = transformS env (getSSort t)
        xs <- mapM (freshSym "proj") ss
        cps env t (CPSLam xs $ f_cpsapp k (CPSVar (xs !! idx)))
    Assume _ t1 t2 -> do
        b <- freshSym "assume_pred" (transformS env SBool)
        cps env t1 =<< (lam b <$> 
            (CPSIf (CPSVar b) <$> (cps env t2 k) <*> pure CPSOmega))
    Fail _ -> pure CPSFail
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

elimTupleSort :: B.Sort -> B.Sort
elimTupleSort (t1 B.:-> t2) = foldr (B.:->) (elimTupleSort t2) $ currySort t1 [] 
elimTupleSort B.X = B.X
elimTupleSort B.Bool = B.Bool
elimTupleSort x = error $ "elimTupleSort " ++ show x

currySort :: B.Sort -> [B.Sort] -> [B.Sort]
currySort (B.Tuple xs) acc = foldr currySort acc xs
currySort t acc = elimTupleSort t : acc

elimTuple :: (MonadId m,Applicative m) => M.Map B.Symbol [B.Symbol] -> CPSTerm -> m CPSTerm
elimTuple env (CPSLam xs t) = do
    args <- forM xs $ \xi -> do
        let ss = currySort (B.getSort xi) [] 
        ys <- forM ss (\s -> freshSym (B.name xi) s)
        return (xi,ys)
    let env' = foldr (uncurry M.insert) env args
    let ys = concat $ map snd args
    t' <- elimTuple env' t
    return $ foldr lam t' ys
elimTuple env (CPSApp _ t1 t2) = do
    t1' <- elimTuple env t1
    let go (CPSTuple ts) = concat <$> mapM go ts
        go (CPSVar x) = return $ map CPSVar (env M.! x)
        go t = return <$> elimTuple env t
    ts2 <- go t2
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
    let [x'] = env M.! x in
    return $ CPSVar x'
elimTuple _ (CPSTuple _) = error "unexpected tuple constructor for elimTuple"

elimTupleP :: (MonadId m,Applicative m) => ([(B.Symbol,CPSTerm)],CPSTerm) -> m ([(B.Symbol,CPSTerm)],CPSTerm) 
elimTupleP (ds,t0) = do
    let ds1 = map (\(x,t) -> (B.modifySort elimTupleSort x,t)) ds
    let env = M.fromList $ [ (y,[y]) | (y,_) <- ds1 ]
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
        CPSBranch t1 t2 -> do
            check "branch fst" B.X =<< go t1
            check "branch snd" B.X =<< go t2
            return B.X
        CPSLam [x] v -> (B.:->) (B.getSort x) <$> go v
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
{-
app :: Either CPSTerm CPSArg -> CPSCont -> CPSTerm
app (Left t) k = CPSAppCont t k
app (Right v) k = CPSReturn k v

{-
f_if :: B.Term -> B.Term -> B.Term -> B.Term
f_if tb tthen telse = 
    B.f_branch (B.f_assume tb tthen) (B.f_assume (B.Not tb) telse)
    -}
fromRight :: Either a b -> b
fromRight (Right x) = x
fromRight _ = error "fromRight: pattern match failure"

fromLeft :: Either a b -> a
fromLeft (Left x) = x
fromLeft _ = error "fromLeft: pattern match failure"

fromLeaf :: Tree a -> a
fromLeaf (Leaf x) = x
fromLeaf _ = error "fromLeaf: pattern match failure"

var :: B.Symbol -> CPSAtom
var = CPSVar []

transformT :: (MonadId m,Applicative m) => 
              S.Set SLabel -> Term -> m (Either (CPSCont -> CPSTerm) CPSArg)
transformT env = \case
    C b -> return $ Right $ Leaf $ if b then CPSTrue else CPSFalse
    V x -> return $ Right $ Leaf $ var (transformV env x)
    T ts -> do
        ts' <- mapM (transformT env) ts
        if any isLeft ts' then do
            -- insert cont
            let n = length ts'
            k <- freshSym "k" (transformS env (getSSort (T ts)) B.:-> B.X)
            xs <- forM (zip [1..n] ts) $ \(i,ti) -> 
                let s = transformS env (getSSort ti) in
                freshSym ("x_"++show i) s
            let t' = foldr (\(ti',xi) acc -> 
                        app ti' (CPSLam xi acc)) t0 (zip ts' xs)
            return $ Left $ \k ->
                let t0 = CPSReturn k $ Node $ map (Leaf . var) xs in
                let t' = foldr (\(ti',xi) acc -> 
                            app ti' (CPSLam xi acc)) t0 (zip ts' xs)
                CPSAtom $ CPSLam k t'
        else return $ Right $ Node $ rights ts'
    Lam s x t -> do
        let l = (\(SFun _ _ _l) -> _l) s
        t' <- transformT env t
        let x' = transformV env x
        if S.member l env then do
            -- insert cont
            k <- freshSym "k" (transformS env (getSSort t) B.:-> B.X)
            return $ Right $ Leaf $ CPSLam x' $ CPSAtom $ CPSLam k $ app t' (var k)
        else
            return $ Right $ Leaf $ CPSLam x' $ CPSAtom $ fromLeaf $ fromRight t'
    App s t0 t1 -> do
        t0' <- transformT env t0
        t1' <- transformT env t1
        let b0 = isLeft t0'
            b1 = isLeft t1'
            b2 = S.member ((\(SFun _ _ _l) -> _l) $ getSSort t0) env
        if b0 || b1 || b2 then do
            k <- freshSym "k" (transformS env s B.:-> B.X)
            f <- freshSym "f" (transformS env (getSSort t0))
            x <- freshSym "x" (transformS env (getSSort t1))
            return $ Left (CPSLam k $ 
                    app t0' (CPSLam f $
                        app t1' (CPSLam x $
                            if b2 then
                                CPSAtom (var f) `CPSApp` Leaf (var x) `CPSApp` Leaf (var k)
                            else
                                CPSAtom (var k) `CPSApp` 
                                Leaf (CPSAtom (var f) `CPSApp` (Leaf (var x)))
                            )))
        else do
            let v0 = fromLeaf $ fromRight t0'
                v1 = fromRight t1'
            return $ Right $ Leaf $ CPSApp (CPSAtom v0) v1
        {-
    Proj s idx size t -> do
        t' <- transformT env t
        if isLeft t' then do
            k <- freshSym "k" (transformS env s B.:-> B.X)
            x <- freshSym "x" (transformS env (getSSort t))
            return $ Left $ CPSLam k $ 
                app t' (CPSLam x $ 
                    CPSApp (CPSVar k) (CPSPrim $ CPSProj idx size (CPSPrim $ CPSVar x)))
        else 
            return $ Right $ CPSPrim $ CPSProj idx size $ fromRight t'
    Assume s t0 t1 -> do
        t0' <- transformT env t0
        t1' <- transformT env t1
        k <- freshSym "k" (transformS env s B.:-> B.X)
        x <- freshSym "x" (transformS env SBool)
        return $ Left $ CPSLam k $
            app t0' (CPSLam x $
                CPSIf (CPSVar x) (app t1' (CPSVar k)) CPSOmega)
    Branch s t0 t1 -> do
        t0' <- transformT env t0
        t1' <- transformT env t1
        k <- freshSym "k" (transformS env s B.:-> B.X)
        return $ Left $ CPSLam k $
            CPSBranch (app t0' (CPSVar k)) (app t1' (CPSVar k))
    Fail x -> do
        k <- freshSym "k" (transformS env (getSSort x) B.:-> B.X)
        return $ Left $ CPSLam k CPSFail
    And t0 t1 -> do
        t0' <- transformT env t0
        t1' <- transformT env t1
        k <- freshSym "k" (transformS env SBool B.:-> B.X)
        if isLeft t0' || isLeft t1' then do
            x0 <- freshSym "x0" (transformS env SBool)
            x1 <- freshSym "x1" (transformS env SBool)
            return $ Left $ CPSLam k $ 
                app t0' $ CPSLam x0 $
                    app t1' $ CPSLam x1 $
                        CPSApp (CPSVar k) (CPSAnd (CPSPrim $ CPSVar x0) 
                                                  (CPSPrim $ CPSVar x1))
        else 
            return $ Right $ CPSAnd (fromRight t0') (fromRight t1')
    Or t0 t1 -> do
        t0' <- transformT env t0
        t1' <- transformT env t1
        k <- freshSym "k" (transformS env SBool B.:-> B.X)
        if isLeft t0' || isLeft t1' then do
            x0 <- freshSym "x0" (transformS env SBool)
            x1 <- freshSym "x1" (transformS env SBool)
            return $ Left $ CPSLam k $ 
                app t0' $ CPSLam x0 $
                    app t1' $ CPSLam x1 $
                        CPSApp (CPSVar k) (CPSOr  (CPSPrim $ CPSVar x0) 
                                                  (CPSPrim $ CPSVar x1))
        else 
            return $ Right $ CPSOr (fromRight t0') (fromRight t1')
    Not t -> do
        t' <- transformT env t
        if isLeft t' then do
            k <- freshSym "k" (transformS env SBool B.:-> B.X)
            x <- freshSym "x" (transformS env SBool)
            return $ Left $ (CPSLam k $ 
                app t' (CPSLam x $
                    CPSApp (CPSVar k) (CPSNot (CPSPrim $ CPSVar x))))
        else
            return $ Right $ CPSNot $ fromRight t'
            

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
        CPSBranch t1 t2 -> do
            check "branch fst" B.X =<< go t1
            check "branch snd" B.X =<< go t2
            return B.X
        CPSLam x v -> (B.:->) (B.getSort x) <$> go v
        CPSProj idx size t -> do
            s <- goV t
            ss <- case s of B.Tuple xs -> return xs
                            _ -> throwError (s,s,"tuple expected")
            when (length ss /= size) $ throwError (s,s,"tuple length mismatch")
            return (ss !! idx)
        CPSApp t1 t2 -> do
            s1 <- go t1
            s2 <- goV t2
            case s1 of
                s2' B.:-> s3 -> check "app arg" s2 s2' >> return s3
                _ -> throwError (s1,s1,"app fun")
        CPSIf t1 t2 t3 -> do
            check "if pred" B.Bool =<< go t1
            check "if then" B.X =<< go t2
            check "if else" B.X =<< go t3
            return B.X
    goV = \case
       CPSPrim t -> go t 
       CPSTuple ts -> B.Tuple <$> mapM goV ts
       CPSAnd t1 t2 -> do
           check "opAnd fst" B.Bool =<< goV t1
           check "opAnd snd" B.Bool =<< goV t2
           return B.Bool
       CPSOr t1 t2 -> do
           check "opOr fst" B.Bool =<< goV t1
           check "opOr snd" B.Bool =<< goV t2
           return B.Bool
       CPSNot t1 -> do
            check "opNot arg" B.Bool =<< goV t1
            return B.Bool
{-

elimTupleSort :: B.Sort -> B.Sort
elimTupleSort = undefined
{-
elimTupleSort (t1 B.:-> t2) = foldr (B.:->) (elimTupleSort t2) $ currySort t1 [] 
elimTupleSort B.X = B.X
elimTupleSort _ = error "elimTupleSort"
-}

currySort :: B.Sort -> Tree B.Sort
currySort = undefined
{-
currySort (B.Tuple xs) acc = foldr currySort acc xs
currySort t acc = elimTupleSort t : acc
-}

elimTuple :: (MonadId m,Applicative m) => M.Map B.Symbol [B.Symbol] -> CPSTerm -> m CPSTerm
elimTuple env = \case
    CPSTrue -> return CPSTrue
    CPSFalse -> return CPSFalse
    CPSOmega -> return CPSOmega
    CPSFail -> return CPSFail
    CPSBranch t1 t2 -> CPSBranch <$> elimTuple env t1 <*> elimTuple env t2
    CPSVar x -> return $ CPSVar $ B.modifySort elimTupleSort x
    CPSLam x t -> do
        let ss = flattenTree $ currySort (B.getSort x)
        xs <- mapM (freshSym (B.name x)) ss
        let env' = M.insert x xs env
        t' <- elimTuple env' t
        return $ foldr CPSLam t' xs
    CPSApp t0 t1 -> do
        t0' <- elimTuple env t0
        t1s <- flattenTree <$> elimTupleV env t1
        return $ foldl CPSApp t0' t1s
    CPSProj idx size t -> do
        t' <- elimTupleV env t
        let ti = (\(Node l) -> l !! idx) t'
        return $ (\(Leaf ) -> x) ti

data Tree a = Node [Tree a] 
            | Leaf a

flattenTree :: Tree a -> [a]
flattenTree (Node xs) = concatMap flattenTree xs
flattenTree (Leaf x) = pure x

elimTupleV :: (MonadId m,Applicative m) => M.Map B.Symbol [B.Symbol] -> CPSValue -> m (Tree CPSValue)
elimTupleV = undefined
        

-}
-}
-}
