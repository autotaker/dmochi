module Language.DMoCHi.ML.ElimCast(elimCast) where

import Control.Monad
import Language.DMoCHi.ML.Syntax.PNormal
import Language.DMoCHi.Common.Id

import Language.DMoCHi.ML.Syntax.PType
import qualified Data.Map as M
import qualified Data.IntMap as IM

{- Eliminate abstraction type casting by eta-expansion.
 -
 - Assume av :: AValue is a function value with type sigma :: PType and 
 - required to have type sigma' :: PType - where sigma /= sigma'.
 - This type casting is eliminated by replacing av with 
 - (fun x1 .. xn -> let f = av in ElimCast(f x1 .. xn)) :: Value
 -}
elimCastFunDef :: MonadId m => TypeMap -> Env -> FunDef -> PType -> m FunDef
elimCastFunDef tbl env (FunDef ident ys e) sigma = 
    FunDef ident ys <$> elimCastTerm tbl env' e retTy'
        where
        PFun _ (xs,ty_xs,_) retTy = sigma 
        subst = M.fromList $ zip xs ys
        ty_ys = map (substPType subst) ty_xs
        env' = foldr (uncurry M.insert) env (zip ys ty_ys)
        retTy' = substTermType subst retTy

elimCastValue :: MonadId m => TypeMap -> Env -> Value -> PType -> m Value
elimCastValue tbl env _v sigma = case _v of
    Atomic av | sigma == typeOfAValue env av -> return $ Atomic av
              | otherwise -> case sigma of
                PFun ty@(TFun _ ty_r) (xs,_,_) _ -> do
                    (f, cnstr_f) <- case av of
                        Var g -> return (g, id)
                        _ -> do g <- Id ty <$> freshId "f"
                                return (g, Let ty_r g (LValue av))
                    ys <- mapM alphaId xs
                    e <- cnstr_f <$> do
                        j <- freshInt
                        r <- Id ty_r <$> freshId "r"
                        return $ Let ty_r r (LApp ty_r j f (map (Atomic . Var) ys)) $ 
                                 Value (Atomic (Var r))
                    i <- freshInt
                    Fun <$> elimCastFunDef tbl env (FunDef i ys e) sigma
                PPair (TPair ty1 ty2) sigma1 sigma2 -> 
                    Pair <$> elimCastValue tbl env (Atomic (Op (OpFst ty1 av))) sigma1
                         <*> elimCastValue tbl env (Atomic (Op (OpSnd ty2 av))) sigma2
                _ -> error "elimCastValue: Impossible"
    Fun fdef -> Fun <$> elimCastFunDef tbl env fdef sigma
    Pair v1 v2 -> 
        let PPair _ sigma1 sigma2 = sigma in
        Pair <$> elimCastValue tbl env v1 sigma1 
             <*> elimCastValue tbl env v2 sigma2

elimCastTerm :: MonadId m => TypeMap -> Env -> Exp -> TermType -> m Exp
elimCastTerm tbl env _e tau = case _e of
    Value v -> 
        let (r, r_ty, _) = tau 
            r_ty' = substVPType (M.singleton r v) r_ty
        in
        Value <$> elimCastValue tbl env v r_ty'
    Let s x (LValue av) e -> do
        let x_ty = typeOfAValue env av
            env' = M.insert x x_ty env
        Let s x (LValue av) <$> elimCastTerm tbl env' e tau
    Let s x (LApp ty ident f vs) e -> do
        let PFun _ (ys, ys_ty, _) (r, r_ty, _) = env M.! f
            subst = M.fromList $ zip ys vs
            ys_ty' = map (substVPType subst) ys_ty
        vs' <- zipWithM (elimCastValue tbl env) vs ys_ty' 
        let subst' = M.insert r (Atomic (Var x)) subst
            r_ty' = substVPType subst' r_ty
            env' = M.insert x r_ty' env
        Let s x (LApp ty ident f vs') <$> elimCastTerm tbl env' e tau
    Let s x (LExp ident e1) e -> do
        let Right tau1@(r, r_ty, _) = tbl IM.! ident
        e1' <- elimCastTerm tbl env e1 tau1
        let subst = M.singleton r x
            r_ty' = substPType subst r_ty
            env' = M.insert x r_ty' env
        Let s x (LExp ident e1') <$> elimCastTerm tbl env' e tau
    Let s x LRand e -> 
        let env' = M.insert x PInt env in
        Let s x LRand <$> elimCastTerm tbl env' e tau
    Assume s p e -> Assume s p <$> elimCastTerm tbl env e tau
    Fail ty -> return $ Fail ty
    Branch ty l e1 e2 -> Branch ty l <$> elimCastTerm tbl env e1 tau 
                                     <*> elimCastTerm tbl env e2 tau
        
elimCast :: MonadId m => TypeMap -> Program -> m Program
elimCast tbl prog = do
    let env = M.fromList [ (f, ty) | (f, func) <- functions prog, 
                                     let Left ty = tbl IM.! ident func ]
    fs <- forM (functions prog) $ \(f, fdef) -> (,) f <$> elimCastFunDef tbl env fdef (env M.! f)
    r <- Id TInt <$> freshId "main"
    e <- elimCastTerm tbl env (mainTerm prog) (r, PInt, [])
    return $ Program fs e
    

