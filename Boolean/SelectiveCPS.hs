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
import Data.DList hiding(map)

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
        let sort = env M.! (B.name f) in
        (,) (Symbol sort (B.name f)) <$> convertT env t
    t0' <- convertT env t0
    return $ Program ds' t0'

buildEnv :: (MonadId m, Applicative m) => [B.Def] -> m [(String,SSort)]
buildEnv = mapM $ \(f,_) -> (,) (B.name f) <$> convertS (B.getSort f)
    
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
    B.V x -> pure $ V $ Symbol (env M.! (B.name x)) (B.name x)
    B.T ts -> T <$> mapM (convertT env) ts
    B.Lam x t -> do
        sx <- convertS $ B.getSort x 
        t' <- convertT (M.insert (B.name x) sx env) t
        label <- freshId "l"
        let s = SFun sx (getSSort t') label
        return $ Lam s (Symbol sx (B.name x)) t'
    B.Let _ x tx t -> do
        tx' <- convertT env tx
        let x' = Symbol (getSSort tx') (B.name x)
        let env' = M.insert (B.name x) (getSSort tx') env
        t' <- convertT env' t
        return $ Let (getSSort t') x' tx' t'
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

-- (x,Left l) <=> x >= maximum l
-- (x,Right b) <=> x >= b
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
        pure mempty
    Let _ _ tx t -> mappend <$> gatherT tx <*> gatherT t
    App _ t1 t2 -> do
        let SFun s1 _ l = getSSort t1
        let s1' = getSSort t2
        tell $ eqSort s1 s1'
        v1 <- gatherT t1
        v2 <- gatherT t2
        return $ v1 <> v2 <> (Maximum (S.singleton l))
    Proj _ _ _ t -> gatherT t
    Assume _ t1 t2 -> Cont <$ gatherT t1 <* gatherT t2 
    Branch _ t1 t2 -> Cont <$ gatherT t1 <* gatherT t2
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
    

