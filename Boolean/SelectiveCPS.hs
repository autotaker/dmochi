{-# LANGUAGE LambdaCase #-}
module Boolean.SelectiveCPS where

import qualified Boolean.Syntax.Typed as B
import Boolean.Syntax.Typed(Size,Index)
import Control.Monad
import Control.Monad.Writer
import Control.Monad.State
import Control.Applicative
import qualified Data.Map as M
import qualified Data.Set as S
import Id
import Data.DList hiding(map,head,foldr)
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
          | T [Term]
          | Lam SSort Symbol Term
          | Let SSort Symbol Term Term
          | App SSort Term Term
          | Proj SSort Index Size  Term
          | Assume SSort Term Term
          | Branch SSort Term Term
          | And Term Term
          | Or  Term Term
          | Not Term
          | Fail Symbol deriving(Ord,Eq,Show)

data Program = Program { definitions :: [Def]
                       , mainTerm :: Term }

class HasSSort m where
    getSSort :: m -> SSort

instance HasSSort Symbol where
    getSSort = _sort

instance HasSSort Term where
    getSSort (C _) = SBool
    getSSort (V x) = getSSort x
    getSSort (T ts) = STuple $ map getSSort ts
    getSSort (Lam s _ _) = s
    getSSort (Let s _ _ _) = s
    getSSort (App s _ _)   = s
    getSSort (Proj s _ _ _) = s
    getSSort (Assume s _ _) = s
    getSSort (Branch s _ _) = s
    getSSort (And _ _) = SBool
    getSSort (Or _ _)  = SBool
    getSSort (Not _)   = SBool
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
    B.T ts -> T <$> mapM (convertT env) ts
    B.Lam x t -> do
        sx <- convertS $ B.getSort x 
        t' <- convertT (M.insert (B.name x) sx env) t
        label <- freshId "l"
        let s = SFun sx (getSSort t') label
        return $ Lam s (Symbol sx (B.name x)) t'
    B.Let _ x tx t -> 
        convertT env (B.App (B.getSort t) (B.Lam x t) tx)
    B.App _ t1 t2 -> do
        t1' <- convertT env t1
        t2' <- convertT env t2
        let SFun _ s _ = getSSort t1'
        return $ App s t1' t2'
    B.Proj _ idx size t -> do
        t' <- convertT env t
        let s = (\(STuple l) -> l !! idx) (getSSort t')
        return $ Proj s idx size t'
    B.Assume _ t1 t2 -> do
        t1' <- convertT env t1
        t2' <- convertT env t2
        return $ Assume (getSSort t2') t1' t2'
    B.Branch _ t1 t2 -> do
        t1' <- convertT env t1
        t2' <- convertT env t2
        return $ Branch (getSSort t2') t1' t2'
    B.Fail x -> do
        sx <- convertS $ B.getSort x
        return $ Fail $ Symbol sx (B.name x)
    B.And t1 t2 -> And <$> convertT env t1 <*> convertT env t2
    B.Or t1 t2 -> Or <$> convertT env t1 <*> convertT env t2
    B.Not t -> Not <$> convertT env t

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
eqFun (SFun s1 s2 l1) (Lam (SFun s3 s4 l2) _ t) =
    eqSort s1 s3 <> eqLabel l1 l2 <> case t of
            Lam _ _ _ -> eqFun s2 t
            _ -> eqSort s2 s4 <> pure (l1,Cont)
eqFun _ _ = error "unexpected pattern for eqFun"


gatherT :: Term -> Writer (DList Constraint) LValue
gatherT = \case
    C _ -> pure mempty
    V _ -> pure mempty
    T ts -> mconcat <$> mapM gatherT ts 
    Lam s _ t -> do
        v <- gatherT t
        let l = (\(SFun _ _ x) -> x) s
        tell (pure (l,v))
        case getSSort t of
            STuple _ -> tell $ pure (l,Cont)
            _ -> return ()
        pure mempty
    Let _ _ _ _ -> error "unexpected pattern for gatherT"
    App _ t1 t2 -> do
        let SFun s1 _ l = getSSort t1
        let s1' = getSSort t2
        tell $ eqSort s1 s1'
        v1 <- gatherT t1
        v2 <- gatherT t2
        return $ v1 <> v2 <> (Maximum (S.singleton l))
    Proj _ _ _ t -> gatherT t
    Assume _ t1 t2 -> Cont <$ gatherT t1 <* gatherT t2 
    Branch _ t1 t2 -> Cont <$ gatherT t1 
                           <* gatherT t2 
                           <* tell (eqSort (getSSort t1) (getSSort t2))
    And t1 t2 -> mappend <$> gatherT t1 <*> gatherT t2
    Or t1 t2 -> mappend <$> gatherT t1 <*> gatherT t2
    Not t -> gatherT t
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

freshSym :: MonadId m => String -> B.Sort -> m B.Symbol
freshSym _name s = freshId _name >>= \x -> return (B.Symbol s x)

app :: Bool -> B.Term -> B.Term -> B.Term
app True t k = B.f_app t k
app False t k = B.f_app k t

f_if :: B.Term -> B.Term -> B.Term -> B.Term
f_if tb tthen telse = 
    B.f_branch (B.f_assume tb tthen) (B.f_assume (B.Not tb) telse)

selectiveCPS :: (MonadId m,Applicative m) => B.Program -> m B.Program
selectiveCPS p = do
    sp@(Program ds t0) <- convert p
    let cs = gatherP sp
    let env = solve cs
    ds' <- forM ds $ \(f,t) -> (,) (transformV env f).fst <$> transformT env t
    (t0',b) <- transformT env t0
    k <- freshSym "k" (transformS env (getSSort t0))
    omega <- B.f_assume (B.C False) . B.Fail <$> freshSym "fail" B.X
    let t0'' = app b t0' (B.Lam k omega)
    return $ B.Program ds' t0''

transformT :: (MonadId m,Applicative m) => S.Set SLabel -> Term -> m (B.Term,Bool)
transformT env = \case
    C b -> return (B.C b,False)
    V x -> return (B.V (transformV env x),False)
    T ts -> do
        (ts',l) <- unzip <$> mapM (transformT env) ts
        if or l then do
            -- insert cont
            let n = length l
            k <- freshSym "k" (transformS env (getSSort (T ts)) B.:-> B.X)
            xs <- forM (zip [1..n] ts) $ \(i,ti) -> 
                let s = transformS env (getSSort ti) in
                freshSym ("x_"++show i) s
            let t0 = B.f_app (B.V k) $ B.T $ map B.V xs
            let t' = foldr (\(ti',xi,b) acc -> 
                        app b ti' (B.Lam xi acc)) t0 (zip3 ts' xs l)
            return (B.Lam k t',True)
        else return (B.T ts',False)
    Lam s x t -> do
        let l = (\(SFun _ _ _l) -> _l) s
        (t',b) <- transformT env t
        let x' = transformV env x
        if S.member l env then do
            -- insert cont
            k <- freshSym "k" (transformS env (getSSort t) B.:-> B.X)
            return (B.Lam x' $ B.Lam k $ app b t' (B.V k),False)
        else
            return (B.Lam x' t',False)
    Let _ _ _ _ -> error "unexpected pattern for transformT"
    App s t0 t1 -> do
        (t0',b0) <- transformT env t0
        (t1',b1) <- transformT env t1
        let b2 = S.member ((\(SFun _ _ _l) -> _l) $ getSSort t0) env
        if b0 || b1 || b2 then do
            k <- freshSym "k" (transformS env s B.:-> B.X)
            f <- freshSym "f" (transformS env (getSSort t0))
            x <- freshSym "f" (transformS env (getSSort t1))
            return (B.Lam k $ 
                    if b0 then 
                        B.f_app t0' (B.Lam f $ 
                            if b1 then
                                B.f_app t1' (B.Lam x $ 
                                    app b2 (B.V f `B.f_app` B.V x) (B.V k))
                            else
                                app b2 (B.f_app (B.V f) t1') (B.V k))
                    else
                        if b1 then
                            B.f_app t1' (B.Lam x $ 
                                app b2 (t0' `B.f_app` B.V x) (B.V k))
                        else
                            app b2 (B.f_app t0' t1') (B.V k)
                   ,True)
        else return (B.f_app t0' t1',False)
    Proj s idx size t -> do
        (t',b) <- transformT env t
        t'' <- if b then do
                k <- freshSym "k" (transformS env s B.:-> B.X)
                x <- freshSym "x" (transformS env (getSSort t))
                return $ B.Lam k $ B.f_app t' (B.Lam x $ 
                    B.f_app (B.V k) (B.f_proj idx size (B.V x)))
            else return $ B.f_proj idx size t'
        return (t'',b)
    Assume s t0 t1 -> do
        (t0',b0) <- transformT env t0
        (t1',b1) <- transformT env t1
        k <- freshSym "k" (transformS env s B.:-> B.X)
        t <- B.Lam k <$> 
            if b0 then do
                x <- freshSym "x" (transformS env SBool)
                return $ B.f_app t0' (B.Lam x $ 
                    B.f_assume (B.V x) (app b1 t1' (B.V k)))
            else
                return $ B.f_assume t0' (app b1 t1' (B.V k))
        return (t,True)
    Branch s t0 t1 -> do
        (t0',b0) <- transformT env t0
        (t1',b1) <- transformT env t1
        k <- freshSym "k" (transformS env s B.:-> B.X)
        let t = B.Lam k $ B.f_branch (app b0 t0' (B.V k)) (app b1 t1' (B.V k))
        return (t,True)
    Fail x -> do
        x' <- freshSym "fail" B.X
        k <- freshSym "k" (transformS env (getSSort x) B.:-> B.X)
        return (B.Lam k (B.Fail x'),True)
    And t0 t1 -> do
        (t0',b0) <- transformT env t0
        (t1',b1) <- transformT env t1
        k <- freshSym "k" (transformS env SBool B.:-> B.X)
        if b0 then do
            x0 <- freshSym "x0" (transformS env SBool)
            return (B.Lam k $ 
                B.f_app t0' $ B.Lam x0 $
                    f_if (B.V x0) (app b1 t1' (B.V k))
                                  (B.f_app (B.V k) (B.C False)),True)
        else if b1 then do
            return (B.Lam k $
                f_if t0' (app b1 t1' (B.V k))
                         (B.f_app (B.V k) (B.C False)),True)
        else
            return (f_if t0' t1' (B.C False),False)
    Or t0 t1 -> do
        (t0',b0) <- transformT env t0
        (t1',b1) <- transformT env t1
        k <- freshSym "k" (transformS env SBool B.:-> B.X)
        if b0 then do
            x0 <- freshSym "x0" (transformS env SBool)
            return (B.Lam k $ 
                B.f_app t0' $ B.Lam x0 $
                    f_if (B.V x0) 
                         (B.f_app (B.V k) (B.C True))
                         (app b1 t1' (B.V k)),True)
        else if b1 then do
            return (B.Lam k $
                f_if t0' (B.f_app (B.V k) (B.C True))
                         (app b1 t1' (B.V k)),True)
        else
            return (f_if t0' t1' (B.C False),False)
    Not t -> do
        (t',b) <- transformT env t
        if b then do
            k <- freshSym "k" (transformS env SBool B.:-> B.X)
            x <- freshSym "x" (transformS env SBool)
            return (B.Lam k $
                B.f_app t' (B.Lam x $ (B.V k) `B.f_app` (B.Not (B.V x))),True)
        else
            return (B.Not t',False)
