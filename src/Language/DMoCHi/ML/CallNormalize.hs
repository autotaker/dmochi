module Language.DMoCHi.ML.CallNormalize (normalize) where


import Language.DMoCHi.ML.Syntax.UnTyped
import Language.DMoCHi.Common.Id
import Control.Monad
import Control.Monad.Cont
import Control.Monad.Trans
import Control.Applicative

normalize :: MonadId m => Program -> m Program
normalize (Program fs syns e) = liftA2 (flip Program syns) (mapM normalizeF fs) (normalizeE e)

normalizeF :: MonadId m => (Id,Type,Exp) -> m (Id,Type,Exp)
normalizeF (x,ty,e) = (,,) x ty <$> normalizeE e

normalizeE :: MonadId m => Exp -> m Exp
normalizeE (Value v) = runContT (normalizeV v) (pure.Value)
normalizeE (Let x lv e) = case lv of 
    LValue v -> 
        runContT (normalizeVLet v) (\lv -> Let x lv <$> normalizeE e)
    LExp ty ex -> do
        ex' <- normalizeE ex
        Let x (LExp ty ex') <$> normalizeE e
    LRand -> Let x LRand <$> normalizeE e
normalizeE (Assume v e) =
    runContT (normalizeV v) (\v' -> Assume v' <$> normalizeE e)
normalizeE (Lambda xs e) =
    Lambda xs <$> normalizeE e
normalizeE Fail = pure Fail
normalizeE (Branch e1 e2) = liftA2 Branch (normalizeE e1) (normalizeE e2)

normalizeVLet :: MonadId m => Value -> ContT Exp m LetValue
normalizeVLet (App f vs) = LApp f <$> mapM normalizeV vs
normalizeVLet v = LValue <$> normalizeV v

normalizeV :: MonadId m => Value -> ContT Exp m Value
normalizeV (Var x) = pure (Var x)
normalizeV (CInt i) = pure (CInt i)
normalizeV (CBool b) = pure (CBool b)
normalizeV (Pair v1 v2) = liftA2 Pair (normalizeV v1) (normalizeV v2)
normalizeV (App f vs) = do
    vs' <- mapM normalizeV vs
    r <- lift $ freshId "tmp"
    ContT $ \cont -> Let r (LApp f vs') <$> (cont (Var r))
normalizeV (Op op) = fmap Op $ case op of
    OpAdd v1 v2 -> liftA2 OpAdd (normalizeV v1) (normalizeV v2)
    OpSub v1 v2 -> liftA2 OpSub (normalizeV v1) (normalizeV v2)
    OpNeg v1 -> OpNeg <$> normalizeV v1
    OpEq v1 v2 -> liftA2 OpEq (normalizeV v1) (normalizeV v2)
    OpLt v1 v2 -> liftA2 OpLt (normalizeV v1) (normalizeV v2)
    OpGt v1 v2 -> liftA2 OpGt (normalizeV v1) (normalizeV v2)
    OpLte v1 v2 -> liftA2 OpLte (normalizeV v1) (normalizeV v2)
    OpGte v1 v2 -> liftA2 OpGte (normalizeV v1) (normalizeV v2)
    OpAnd v1 v2 -> liftA2 OpAnd (normalizeV v1) (normalizeV v2)
    OpOr v1 v2 -> liftA2 OpOr (normalizeV v1) (normalizeV v2)
    OpFst v -> OpFst <$> normalizeV v
    OpSnd v -> OpSnd <$> normalizeV v
    OpNot v -> OpNot <$> normalizeV v
    

