{-# LANGUAGE GADTs #-}
module Language.DMoCHi.ML.ElimCast(elimCast) where

import Control.Monad
import Language.DMoCHi.ML.Syntax.PNormal
import Language.DMoCHi.Common.Id
import Language.DMoCHi.ML.Syntax.Type
import Language.DMoCHi.ML.Syntax.Base

import Language.DMoCHi.ML.Syntax.PType
import qualified Data.Map as M

{- Eliminate abstraction type casting by eta-expansion.
 -
 - Assume av :: AValue is a function value with type sigma :: PType and 
 - required to have type sigma' :: PType - where sigma /= sigma'.
 - This type casting is eliminated by replacing av with 
 - (fun x1 .. xn -> let f = av in ElimCast(f x1 .. xn)) :: Value
 -}
elimCastFunDef :: MonadId m => TypeMap -> Env -> (UniqueKey, [SId], Exp) -> PType -> m (UniqueKey, [SId], Exp)
elimCastFunDef tbl env (ident,ys,e) sigma = 
    (,,) ident ys <$> elimCastTerm tbl env' e retTy'
        where
        PFun _ (xs,ty_xs,_) retTy = sigma 
        subst = M.fromList $ zip xs ys
        ty_ys = map (substPType subst) ty_xs
        env' = foldr (uncurry M.insert) env (zip ys ty_ys)
        retTy' = substTermType subst retTy

elimCastValue :: MonadId m => TypeMap -> Env -> Value -> PType -> m Value
elimCastValue tbl env v@(Value l arg sty key) sigma = case (l,arg) of
    (SLambda, (xs, e)) -> do
        (_, _, e') <- elimCastFunDef tbl env (key,xs,e) sigma
        return $ Value l (xs,e') sty key
    (SPair, (v1,v2)) -> do
        let PPair _ sigma1 sigma2 = sigma 
        v1' <- elimCastValue tbl env v1 sigma1 
        v2' <- elimCastValue tbl env v2 sigma2 
        return $ mkPair v1' v2' key
    _ -> case atomOfValue v of
        Nothing -> error "elimCastValue: impossible"
        Just av -> case sigma of
                PInt -> return v
                PBool -> return v
                _ | sigma == typeOfAValue env av -> return v
                PFun ty@(STFun _ ty_r) (xs,_,_) _ -> do
                    (f, cnstr_f) <- case l of
                        SVar -> return (arg, id)
                        _ -> do g <- SId ty <$> identify "f"
                                key' <- freshKey
                                return (g, (\e -> mkLet g (cast v) e key'))
                    ys <- mapM alphaSId xs
                    e <- cnstr_f <$> do
                        j <- freshKey
                        r <- SId ty_r <$> identify "r"
                        kr <- freshKey 
                        vs <- mapM (\y -> freshKey >>= (\k -> return $ castWith k (mkVar y))) ys
                        mkLet r (mkApp f vs j) (castWith kr (mkVar r)) <$> freshKey
                    i <- freshKey
                    (_, _, e') <- elimCastFunDef tbl env (i,ys, e) sigma
                    return $ mkLambda ys e' i
                PPair _ sigma1 sigma2 -> do
                    v1 <- freshKey >>= (\k -> return $ castWith k $ mkUni SFst av)
                    v2 <- freshKey >>= (\k -> return $ castWith k $ mkUni SSnd av)
                    v1' <- elimCastValue tbl env v1 sigma1
                    v2' <- elimCastValue tbl env v2 sigma2
                    return $ mkPair v1' v2' key

elimCastTerm :: MonadId m => TypeMap -> Env -> Exp -> TermType -> m Exp
elimCastTerm tbl env (Exp l arg sty key) tau = case (l,arg) of
    (SLiteral, _) -> do
        let (r, r_ty, _) = tau 
            v = Value l arg sty key
            r_ty' = substVPType (M.singleton r v) r_ty
        cast <$> elimCastValue tbl env v r_ty'
    (SVar, _) -> do
        let (r, r_ty, _) = tau 
            v = Value l arg sty key
            r_ty' = substVPType (M.singleton r v) r_ty
        cast <$> elimCastValue tbl env (Value l arg sty key) r_ty'
    (SBinary, _) -> do
        let (r, r_ty, _) = tau 
            v = Value l arg sty key
            r_ty' = substVPType (M.singleton r v) r_ty
        cast <$> elimCastValue tbl env (Value l arg sty key) r_ty'
    (SUnary, _) -> do
        let (r, r_ty, _) = tau 
            v = Value l arg sty key
            r_ty' = substVPType (M.singleton r v) r_ty
        cast <$> elimCastValue tbl env (Value l arg sty key) r_ty'
    (SPair, _) -> do
        let (r, r_ty, _) = tau 
            v = Value l arg sty key
            r_ty' = substVPType (M.singleton r v) r_ty
        cast <$> elimCastValue tbl env (Value l arg sty key) r_ty'
    (SLambda, _) -> do
        let (r, r_ty, _) = tau 
            v = Value l arg sty key
            r_ty' = substVPType (M.singleton r v) r_ty
        cast <$> elimCastValue tbl env (Value l arg sty key) r_ty'
    (SLet, (x, e1@(Exp l1 arg1 _ key1), e2)) -> case valueOfExp e1 >>= atomOfValue of
        Just av -> do
            let x_ty = typeOfAValue env av
                env' = M.insert x x_ty env
            e2' <- elimCastTerm tbl env' e2 tau
            return $ mkLet x e1 e2' key
        Nothing -> case (l1,arg1) of
            (SApp, (f,vs)) -> do
                let PFun _ (ys, ys_ty, _) (r, r_ty, _) = env M.! f
                    subst = M.fromList $ zip ys vs
                    ys_ty' = map (substVPType subst) ys_ty
                vs' <- zipWithM (elimCastValue tbl env) vs ys_ty' 
                let subst' = M.insert r (cast (mkVar x)) subst
                    r_ty' = substVPType subst' r_ty
                    env' = M.insert x r_ty' env
                e2' <- elimCastTerm tbl env' e2 tau
                return $ mkLet x (mkApp f vs' key1) e2' key
            (SRand, ()) -> do
                let env' = M.insert x PInt env 
                e2' <- elimCastTerm tbl env' e2 tau
                return $ mkLet x (mkRand key1) e2' key
            _ -> do
                let Right tau1@(r, r_ty, _) = tbl M.! key
                e1' <- elimCastTerm tbl env e1 tau1
                let subst = M.singleton r x
                    r_ty' = substPType subst r_ty
                    env' = M.insert x r_ty' env
                e2' <- elimCastTerm tbl env' e2 tau
                return $ mkLet x e1' e2' key
    (SAssume, (p, e1)) -> do
        e1' <- elimCastTerm tbl env e1 tau
        return $ mkAssume p e1' key
    (SFail,_) -> return $ mkFail sty key
    (SOmega,_) -> return $ mkOmega sty key
    (SRand,_) -> return $ mkRand key
    (SApp, (f, vs)) -> do
        key1 <- freshKey
        key2 <- freshKey
        r <- SId sty <$> identify "r"
        let e' = mkLet r (mkApp f vs key) (castWith key1 $ mkVar r) key2
        elimCastTerm tbl env e' tau
    (SBranch, (e1, e2)) -> do
        e1' <- elimCastTerm tbl env e1 tau
        e2' <- elimCastTerm tbl env e2 tau
        return $ mkBranch e1' e2' key
        
elimCast :: MonadId m => TypeMap -> Program -> m Program
elimCast tbl prog = do
    let env = M.fromList [ (f, ty) | (f, key, _, _) <- functions prog, let Left ty = tbl M.! key ]
    fs <- forM (functions prog) $ \(f, key, xs, e) -> do
                    (_,_,e') <- elimCastFunDef tbl env (key,xs,e) (env M.! f)
                    return (f, key, xs, e')
    r <- SId STInt <$> identify "main"
    e <- elimCastTerm tbl env (mainTerm prog) (r, PInt, [])
    return $ Program fs e
    

