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
import Data.DList hiding(map,head,foldr)
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
          | T [Term]
          | Lam SSort Symbol Term
          | App SSort Term Term
          | Proj SSort Index Size  Term
          | Assume SSort Term Term
          | Branch SSort Term Term
          | And Term Term
          | Or  Term Term
          | Not Term
          | Fail Symbol deriving(Ord,Eq,Show)

-- CPSTerm should has sort s ::= X | t -> s 
--                         t ::= s | [t_1..t_k]
data CPSTerm = CPSTrue                       -- X -> X -> X
             | CPSFalse                      -- X -> X -> X
             | CPSOmega                      -- X
             | CPSFail                       -- X
             | CPSBranch CPSTerm CPSTerm     -- X -> X -> X
             | CPSVar B.Symbol               
             | CPSLam B.Symbol CPSTerm      
             | CPSProj Index Size CPSValue  
             | CPSApp CPSTerm CPSValue      
             | CPSIf CPSTerm CPSTerm CPSTerm deriving(Show)-- (X -> X -> X) -> X -> X -> X
                                              -- -> (X-> X -> X) -> X -> X -> X
                                              

data CPSValue = CPSTuple [CPSValue]
              | CPSPrim  CPSTerm
              | CPSAnd CPSValue CPSValue
              | CPSOr  CPSValue CPSValue
              | CPSNot CPSValue deriving(Show)

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

app :: Either CPSTerm CPSValue -> CPSTerm -> CPSTerm
app (Left t) k = CPSApp t (CPSPrim k)
app (Right v) k = CPSApp k v

f_if :: B.Term -> B.Term -> B.Term -> B.Term
f_if tb tthen telse = 
    B.f_branch (B.f_assume tb tthen) (B.f_assume (B.Not tb) telse)

selectiveCPS :: (MonadId m,Applicative m) => B.Program -> m ([(B.Symbol,CPSTerm)],CPSTerm)
selectiveCPS p = do
    sp@(Program ds t0) <- convert p
    let cs = gatherP sp
    let env = solve cs
    ds' <- forM ds $ \(f,t) -> 
        (,) (transformV env f).fromPrim . fromRight <$> transformT env t
    t0' <- transformT env t0
    k <- freshSym "k" (transformS env (getSSort t0))
    let t0'' = app t0' (CPSLam k CPSOmega)
    return $ (ds',t0'')

fromRight :: Either a b -> b
fromRight (Right x) = x
fromRight _ = error "fromRight: pattern match failure"

fromLeft :: Either a b -> a
fromLeft (Left x) = x
fromLeft _ = error "fromLeft: pattern match failure"

fromPrim :: CPSValue -> CPSTerm
fromPrim (CPSPrim x) = x
fromPrim _ = error "fromPrim: pattern match failure"

transformT :: (MonadId m,Applicative m) => 
              S.Set SLabel -> Term -> m (Either CPSTerm CPSValue)
transformT env = \case
    C b -> return $ Right $ CPSPrim (if b then CPSTrue else CPSFalse)
    V x -> return $ Right $ CPSPrim (CPSVar (transformV env x))
    T ts -> do
        ts' <- mapM (transformT env) ts
        if any isLeft ts' then do
            -- insert cont
            let n = length ts'
            k <- freshSym "k" (transformS env (getSSort (T ts)) B.:-> B.X)
            xs <- forM (zip [1..n] ts) $ \(i,ti) -> 
                let s = transformS env (getSSort ti) in
                freshSym ("x_"++show i) s
            let t0 = CPSApp (CPSVar k) $ CPSTuple $ map (CPSPrim . CPSVar) xs
            let t' = foldr (\(ti',xi) acc -> 
                        app ti' (CPSLam xi acc)) t0 (zip ts' xs)
            return $ Left $ CPSLam k t'
        else return $ Right $ CPSTuple $ rights ts'
    Lam s x t -> do
        let l = (\(SFun _ _ _l) -> _l) s
        t' <- transformT env t
        let x' = transformV env x
        if S.member l env then do
            -- insert cont
            k <- freshSym "k" (transformS env (getSSort t) B.:-> B.X)
            return $ Right $ CPSPrim $ CPSLam x' $ CPSLam k $ app t' (CPSVar k)
        else
            return $ Right $ CPSPrim $ CPSLam x' (fromPrim $ fromRight t')
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
                                CPSVar f `CPSApp` CPSPrim (CPSVar x)
                                         `CPSApp` CPSPrim (CPSVar k)
                            else
                                CPSVar k `CPSApp` 
                                CPSPrim (CPSVar f `CPSApp` (CPSPrim (CPSVar x)))
                            )))
        else do
            let v0 = fromPrim $ fromRight t0'
                v1 = fromRight t1'
            return $ Right $ CPSPrim (CPSApp v0 v1)
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




        


