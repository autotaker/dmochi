module Language.DMoCHi.Boolean.LiftRec where
import Language.DMoCHi.Common.Id
import Language.DMoCHi.Boolean.Syntax.Typed
import Control.Monad.State.Strict
import qualified Data.Set as S
import qualified Data.Map as M

liftRec :: forall m. MonadId m => Program -> m Program
liftRec (Program ds t0) = 
    runStateT doit [] >>= \(t0',ds') -> 
        return (Program (reverse ds') t0')
    where                             
    doit :: StateT [Def] m Term
    doit = do
        forM_ ds $ \(f, t_f) -> do
            t_f' <- go M.empty t_f
            add (f, t_f')
        go M.empty t0
    add def = modify' (def:)
    rename env f = case M.lookup f env of
        Just t -> t
        Nothing -> V f
    go _   (C b) = pure (C b)
    go env (V f) = pure (rename env f)
    go env (T ts) = T <$> mapM (go env) ts
    go env (Lam x t) = Lam x <$> go env t
    go env (Let s x t1 t2) = 
        Let s x <$> go env t1 <*> go env t2
    go env (LetRec _ fs t2) = do
        let (names, values) = unzip fs
        let fvs = S.toList $ S.unions (map freeVariables values) `S.difference` S.fromList names
            g ty = Tuple (map getSort fvs) :-> ty
            as  = [ (f, f_app (V (modifySort g f)) (T (map (rename env) fvs))) | f <- names ]
        let env' = foldr (uncurry M.insert) env as 
        forM_ fs $ \(f,t_f) -> do
            arg <- freshSym "arg" (Tuple (map getSort fvs))
            xs <- mapM (\x -> freshSym (name x) (getSort x)) fvs
            let env' = M.fromList $ [ (f, f_app (V (modifySort g f)) (V arg)) | f <- names ]
                                 ++ zip fvs (map V xs)
            t_f' <- go env' t_f
            let n = length fvs
            let t = Lam arg (foldr (\(x,i) t -> 
                        f_let x (f_proj i n (V arg)) t) t_f' (zip xs [0..]))
            add (modifySort g f, t)
        go env' t2
    go env (App s t1 t2) = App s <$> go env t1 <*> go env t2
    go env (Proj s i n t) = Proj s i n <$> go env t
    go env (Assume s t1 t2) = Assume s <$> go env t1 <*> go env t2
    go env (Branch s b t1 t2) = Branch s b <$> go env t1 <*> go env t2
    go env (And t1 t2) = And <$> go env t1 <*> go env t2
    go env (Or  t1 t2) = Or  <$> go env t1 <*> go env t2
    go env (Not t1) = Not <$> go env t1
    go _ (Fail s) = pure (Fail s)
    go _ (Omega s) = pure (Omega s)
        
