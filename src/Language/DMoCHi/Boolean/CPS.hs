{-# LANGUAGE FlexibleInstances, FlexibleContexts, StandaloneDeriving #-}
    
module Language.DMoCHi.Boolean.CPS where
import Language.DMoCHi.Boolean.Syntax.Typed hiding(f_app)
import Control.Monad.Except hiding(mapM_,forM_,mapM,forM)
import Control.Applicative
import qualified Data.Map as M
import Language.DMoCHi.Common.Id
import Prelude hiding(foldl,foldr,sum,mapM_,concat,mapM)
import Data.Foldable
import Data.Traversable
import Data.Monoid

data Tuple t = One t | Many [t] 
instance Show t => Show (Tuple t) where
    showsPrec x (One t) = showsPrec x t
    showsPrec x (Many t) = showsPrec x t 

newtype Simple t = Simple t 
instance Show t => Show (Simple t) where
    showsPrec x (Simple t) = showsPrec x t

instance Functor Tuple where
    fmap f (One t) = One (f t)
    fmap f (Many ts) = Many (map f ts)

instance Functor Simple where
    fmap f (Simple t) = Simple (f t)

instance Foldable Tuple where
    foldMap f (One t) = f t
    foldMap f (Many ts) = mconcat $ map f ts

instance Foldable Simple where
    foldMap f (Simple t) = f t

instance Traversable Simple where
    traverse f (Simple x) = Simple <$> f x

data STerm f = SV Symbol
           | SLam (f Symbol) (STerm f)
           | SApp Sort (STerm f) (f (STerm f))
           | STrue
           | SFalse
           | SBranch
           | SFail
           | SOmega 

deriving instance Show (STerm Tuple) 
deriving instance Show (STerm Simple)

f_app :: HasSort (STerm f) => STerm f -> (f (STerm f)) -> STerm f
--f_app (SLam (One x) t) (One t2) = substSTerm (M.fromList [(x,t2)]) t
--f_app (SLam (Many xs) t) (Many ts) = substSTerm (M.fromList $ zip xs ts) t
f_app t1 t2 = 
    let _ :-> s2 = getSort t1 in
    SApp s2 t1 t2

{-
substSTerm :: M.Map Symbol (STerm Tuple) -> STerm Tuple -> STerm Tuple
substSTerm env _t = case _t of
    SV x -> case M.lookup x env of
        Just t -> t
        Nothing -> _t
    SLam x' t -> SLam x' (substSTerm env t)
    SApp s t1 t2 -> SApp s (substSTerm env t1) (fmap (substSTerm env) t2)
    _ -> _t
    -}

instance HasSort a => HasSort (Tuple a) where
    getSort (One t) = getSort t
    getSort (Many t) = Tuple $ map getSort t

instance HasSort a => HasSort (Simple a) where
    getSort (Simple t) = getSort t

instance HasSort (STerm Tuple) where
    getSort (SV x) = getSort x
    getSort (SLam x t) = getSort x :-> getSort t
    getSort (SApp s _ _) = s
    getSort STrue = X :-> (X :-> X)
    getSort SFalse = X :-> (X :-> X)
    getSort SBranch = X :-> (X :-> X)
    getSort SFail = X
    getSort SOmega = X

instance HasSort (STerm Simple) where
    getSort (SV x) = getSort x
    getSort (SLam x t) = getSort x :-> getSort t
    getSort (SApp s _ _) = s
    getSort STrue = X :-> (X :-> X)
    getSort SFalse = X :-> (X :-> X)
    getSort SBranch = X :-> (X :-> X)
    getSort SFail = X
    getSort SOmega = X

type P f = ([(Symbol,STerm f)], STerm f)

tCheck1 :: (HasSort (STerm f),Foldable f,HasSort (f (STerm f))) => P f -> Except (Sort,Sort,String,[STerm f]) ()
tCheck1 (ds,t0) = doit where
    check s1 s2 str ctx = when (s1 /= s2) $ throwError (s1,s2,str,ctx)
    doit = do
        forM_ ds $ \(x,t) -> do
            go [] t
            check (getSort x) (getSort t) "let rec" [t]
        go [] t0
        check (getSort t0) X "main" [t0]
    go ctx _t = let ctx' = _t:ctx in case _t of
        STrue -> return ()
        SFalse -> return ()
        SV _ -> return ()
        SFail -> return ()
        SOmega -> return ()
        SBranch -> return ()
        SLam _ t -> go ctx' t
        SApp s t1 t2 -> do
            go ctx' t1
            forM_ t2 (go ctx')
            case getSort t1 of
                s1 :-> s2 -> check s1 (getSort t2) "app arg" ctx' >> 
                             check s s2 "app result" ctx'
                s' -> throwError (s',X,"app fun",ctx')

size1 :: (Foldable f, Functor f) => P f -> Int
size1 (ds,t0) = sum (map (\(_,t) -> go t+1) ds) + go t0 where
    go STrue = 1
    go SFalse = 1
    go (SV _) = 1
    go SFail = 1
    go SOmega = 1
    go SBranch = 1
    go (SLam x t) = go t + sum (fmap (const 1) x)
    go (SApp _ t1 t2) = 1 + go t1 + sum (fmap go t2)
        
isAtomic :: Term -> Bool
isAtomic (C _) = True
isAtomic (Lam _ _) = True
isAtomic (V _) = True
isAtomic _ = False

cpsSort :: Sort -> Sort
cpsSort Bool = X :-> (X :-> X)
cpsSort (Tuple ts) = Tuple (map cpsSort ts)
cpsSort (s1 :-> s2) = cpsSort s1 :-> ((cpsSort s2 :-> X) :-> X)
cpsSort X = undefined


cps :: (MonadId m,Applicative m) => Program -> m ([(Symbol,STerm Tuple)], STerm Tuple)
cps p = do
    ds' <- forM (definitions p) $ \(f,t) -> (,) (modifySort cpsSort f) <$> cpsM t
    x <- freshSym "x" (cpsSort $ getSort (mainTerm p))
    t'  <- cpsT (mainTerm p) (SLam (One x) SOmega)
    return $ (ds', t')

cpsM :: (MonadId m,Applicative m) => Term -> m (STerm Tuple)
cpsM (C True)  = pure STrue
cpsM (C False) = pure SFalse
cpsM (V x)     = pure $ SV $ modifySort cpsSort x
cpsM (Lam x t) = 
    let x' = modifySort cpsSort x in
    freshSym "k" (cpsSort (getSort t) :-> X) >>= \k -> 
        SLam (One x') . SLam (One k) <$> cpsT t (SV k)
cpsM _ = error $ "atomic term is expected"

cpsT :: (MonadId m,Applicative m) => Term -> (STerm Tuple) -> m (STerm Tuple)
cpsT e k | isAtomic e = f_app k . One <$> cpsM e
cpsT (App _ t1 t2) k = do
    x1 <- freshSym "x1" $ cpsSort (getSort t1)
    x2 <- freshSym "x2" $ cpsSort (getSort t2)
    cpsT t1 =<< (SLam (One x1) <$> cpsT t2 (SLam (One x2) (SV x1 `f_app` (One $ SV x2) `f_app` (One k))))
cpsT (T ts) k = do
    let n = length ts
    xs <- forM (zip ts [1..n]) $ \(ti,i) -> freshSym ("x_"++show i) (cpsSort $ getSort ti)
    let t0 = f_app k (Many $ map SV xs)
    foldM (\acc (ti,xi) -> cpsT ti $ SLam (One xi) acc) t0 $ reverse $ zip ts xs
cpsT (Proj _ idx size t) k = cpsT t =<< do
    let Tuple ss = getSort t
    xs <- forM (zip ss [0..size-1]) $ \(si,i) -> freshSym ("x_"++show i) (cpsSort si)
    pure $ SLam (Many xs) (f_app k (One $ SV $ xs !! idx))
cpsT (Fail _) _ = pure SFail
cpsT (Let _ x e1 e2) k = cpsT (App (getSort e2) (Lam x e2) e1) k
cpsT (Branch _ _ t1 t2) k = do
    k' <- freshSym "k" (getSort k)
    let f t1' t2' = SLam (One k') (SBranch `f_app` One t1' `f_app` One t2') `f_app` One k
    f <$> cpsT t1 (SV k') <*> cpsT t2 (SV k')
cpsT (Assume _ p t) k = do
    b <- freshSym "b" (cpsSort Bool)
    let f t2' = SLam (One b) $ SV b `f_app` One t2' `f_app` One SOmega
    cpsT p =<< f <$> cpsT t k
cpsT (And t1 t2) k = do
    k' <- freshSym "k" (getSort k)
    f_app <$> (SLam (One k') <$> do
        b <- freshSym "and" (cpsSort Bool)
        let f t2' = SLam (One b) $ SV b `f_app` One t2' `f_app` One (SV k' `f_app` One SFalse)
        cpsT t1 =<< f <$> cpsT t2 (SV k')
        ) <*> pure (One k)
cpsT (Or t1 t2) k = do
    k' <- freshSym "k" (getSort k)
    f_app <$> (SLam (One k') <$> do
        b <- freshSym "and" (cpsSort Bool)
        let f t2' = SLam (One b) $ SV b `f_app` One ((SV k') `f_app` One STrue) `f_app` One t2'
        cpsT t1 =<< f <$> cpsT t2 (SV k')
        ) <*> pure (One k)
cpsT (Not t) k = do
    b <- freshSym "not" (cpsSort Bool)
    x <- freshSym "not_x" X
    y <- freshSym "not_y" X
    let k' = SLam (One b) $ k `f_app` One (SLam (One x) (SLam (One y) (SV b `f_app` One (SV y) `f_app` One (SV x))))
    cpsT t k'
cpsT _ _ = error "unexpected pattern match failure"
{-
cpsT (If e1 e2 e3) k = cpsT e1 =<< do
    b <- freshId "b"
    SLam (One b) <$> liftA2 SApp (SApp (SV b) . One <$> cpsT e2 k) (One <$> cpsT e3 k)
    -}

elimTupleSort :: Sort -> Sort
elimTupleSort (t1 :-> t2) = foldr (:->) (elimTupleSort t2) $ currySort t1 [] 
elimTupleSort X = X
elimTupleSort _ = error "elimTupleSort"

currySort :: Sort -> [Sort] -> [Sort]
currySort (Tuple xs) acc = foldr currySort acc xs
currySort t acc = elimTupleSort t : acc

elimTupleP :: (MonadId m,Applicative m) => P Tuple -> m (P Simple)
elimTupleP (ds,t0) = do
    let ds1 = map (\(x,t) -> (modifySort elimTupleSort x,t)) ds
    let env = M.fromList $ [ (y,[y]) | (y,_) <- ds1 ]
    ds' <- forM ds1 $ \(y,t) -> do
        t' <- elimTuple env t
        return (y,t')
    t0' <- elimTuple env t0
    return (ds',t0')

elimTuple :: (MonadId m,Applicative m) => M.Map Symbol [Symbol] -> STerm Tuple -> m (STerm Simple)
elimTuple env (SLam x t) = do
    let xs = case x of One x' -> [x']
                       Many xs' -> xs'
    args <- forM xs $ \xi -> do
        let ss = currySort (getSort xi) [] 
        ys <- forM ss (\s -> freshSym (name xi) s)
        return (xi,ys)
    let env' = foldr (uncurry M.insert) env args
    let ys = concat $ map snd args
    t' <- elimTuple env' t
    return $ foldr (SLam . Simple) t' ys
elimTuple env (SApp _ t1 t2) = do
    t1' <- elimTuple env t1
    let go (One t) = case getSort t of
            Tuple _ ->
                let SV x = t in
                let ys = env M.! x in
                return $ map SV ys
            _ -> return <$> elimTuple env t
        go (Many ts) = concat <$> mapM (go.One) ts
    ts2 <- go t2
    return $ foldl (\acc -> f_app acc . Simple) t1' ts2
elimTuple _ STrue = return STrue
elimTuple _ SFalse = return SFalse
elimTuple _ SBranch = return SBranch
elimTuple _ SFail = return SFail
elimTuple _ SOmega = return SOmega
elimTuple env (SV x) = 
    let [x'] = env M.! x in
    return $ SV x'
    


{-
cpsE :: Term -> M Term
cpsE (C True)  = pure $ Lam "k" (App (V "k") (V "TRUE"))
cpsE (C False) = pure $ Lam "k" (App (V "k") (V "FALSE"))
cpsE TF        = pure $ Lam "k" (App (V "k") (V "BRANCH"))
cpsE (V x) = genFresh >>= \k -> pure (Lam k (App (V k) (V x)))
cpsE (T ts) = do
    xs <- replicateM (length ts) genFresh
    ts' <- mapM cpsE ts
    k  <- genFresh
    p  <- genFresh
    let ps = zip ts' xs
    let t0 = App (V k) $ Lam p $ foldl (\acc xi -> App acc (V xi)) (V p) xs
    let t = foldr (\(ti,xi) acc -> App ti (Lam xi acc)) t0 ps
    return  $ Lam k t
cpsE (Fail s) = pure $ Lam "k" (Fail s)
cpsE (Omega s) = pure $ Lam "k" (Omega s)
cpsE (Proj i d t) = do
    k <- genFresh 
    t' <- cpsE t
    xs <- replicateM (projD d) genFresh
    p <- genFresh
    let xi = xs !! projN i
    let proj = Lam p (App (V p) (foldr Lam (App (V k) (V xi)) xs))
    pure $ Lam k (App t' proj)
cpsE (App t1 t2) = do
    k <- genFresh
    t1' <- cpsE t1
    t2' <- cpsE t2
    f <- genFresh
    x <- genFresh
    pure $ Lam k (App t1' (Lam f (App t2' (Lam x (App (App (V f) (V x)) (V k))))))
cpsE (Lam x t) = do
    k <- genFresh
    Lam k . App (V k) . Lam x  <$> cpsE t
cpsE (If e1 e2 e3) = do
    k <- genFresh
    b <- genFresh 
    e1' <- cpsE e1
    e2' <- cpsE e2
    e3' <- cpsE e3
    pure $ Lam k $ App e1' (Lam b $ App (App (V b) (App e2' (V k))) (App e3' (V k)))
cpsE (Let x e1 e2) = cpsE (App (Lam x e2) e1)

simplify :: Term -> Term
simplify (T ts) = T $ map simplify ts
simplify (Proj i d t) = Proj i d $ simplify t
simplify (App t1 t2) =
    let t1' = simplify t1 in
    let t2' = simplify t2 in
    if isValue t2' then
        case t1' of
            Lam x t -> simplify $ reduce x t2' t
            _ -> App t1' t2'
    else
        App t1' t2'
simplify (If t1 t2 t3) = If (simplify t1) (simplify t2) (simplify t3)
simplify (Let x t1 t2) = Let x (simplify t1) (simplify t2)
simplify (Lam x t) = Lam x (simplify t)
simplify t = t

isValue :: Term -> Bool
isValue (Lam _ _) = True
isValue (C _) = True
isValue (V _) = True
isValue (T ts) = all isValue ts
isValue (Proj _ _ t) = isValue t
isValue _ = False

reduce :: String -> Term -> Term -> Term
reduce x t (Lam y t') = if x == y then Lam y t' else Lam y (reduce x t t')
reduce x t (T ts) = T $ map (reduce x t) ts
reduce x t (Let y t1 t2) = Let y (reduce x t t1) (if x == y then t2 else reduce x t t2)
reduce x t (Proj i d t') = Proj i d (reduce x t t')
reduce x t (App t1 t2) = App (reduce x t t1) (reduce x t t2)
reduce x t (If t1 t2 t3) = If (reduce x t t1) (reduce x t t2) (reduce x t t3)
reduce x t (V y) = if x == y then t else V y
reduce _ _ t' = t'

-}

