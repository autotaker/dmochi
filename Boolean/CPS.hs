module Boolean.CPS where
import Boolean.Syntax
import Control.Monad
import Control.Applicative
import Id


data STerm = SV Symbol
           | SLam Symbol STerm
           | SApp STerm STerm
           | STrue
           | SFalse
           | SBranch
           | SFail
           | SOmega deriving(Ord,Eq)

cps :: (MonadId m,Applicative m) => Program -> m ([(String,STerm)], STerm)
cps p = do
    ds' <- forM (definitions p) $ \(f,t) -> (,) f <$> cpsM t
    x <- freshId "x"
    t'  <- cpsT (mainTerm p) (SLam x SOmega)
    return $ (ds', t')

isAtomic :: Term -> Bool
isAtomic (C _) = True
isAtomic (Lam _ _) = True
isAtomic TF = True
isAtomic (V _) = True
isAtomic _ = False

cpsM :: (MonadId m,Applicative m) => Term -> m STerm
cpsM (C True)  = pure STrue
cpsM (C False) = pure SFalse
cpsM TF        = pure SBranch
cpsM (V x)     = pure $ SV x
cpsM (Lam x t) = freshId "k" >>= \k -> SLam x . SLam k <$> cpsT t (SV k)
cpsM _ = error $ "atomic term is expected"

cpsT :: (MonadId m,Applicative m) => Term -> STerm -> m STerm
cpsT e k | isAtomic e = SApp k <$> cpsM e
cpsT (App t1 t2) k = do
    x1 <- freshId "x1"
    x2 <- freshId "x2"
    cpsT t1 =<< (SLam x1 <$> cpsT t2 (SLam x2 (SV x1 `SApp` SV x2 `SApp` k)))
cpsT (T ts) k = do
    let n = length ts
    xs <- forM [1..n] (freshId . ("x_"++) . show)
    p <- freshId "p"
    let t0 = SApp k (SLam p (foldl (\acc xi -> acc `SApp` SV xi) (SV p) xs))
    foldM (\acc (ti,xi) -> cpsT ti $ SLam xi acc) t0 $ reverse $ zip ts xs
cpsT (Proj n d t) k = cpsT t =<< do
    c <- freshId "c"
    xs <- forM [1..projD d] (freshId . ("x_"++) . show)
    pure $ SLam c $ SApp (SV c) $ foldr SLam (SApp k (SV $ xs !! projN n)) xs
cpsT (If e1 e2 e3) k = cpsT e1 =<< do
    b <- freshId "b"
    SLam b <$> liftA2 SApp (SApp (SV b) <$> cpsT e2 k) (cpsT e3 k)
cpsT (Fail _) _ = pure SFail
cpsT (Omega _) _ = pure SOmega
cpsT (Let x e1 e2) k = cpsT (App (Lam x e2) e1) k
cpsT _ _ = error "unexpected pattern match failure"


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

