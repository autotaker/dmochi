{-# LANGUAGE GADTs #-}
module Language.DMoCHi.ML.ElimCast(elimCast) where

import Control.Monad
import Language.DMoCHi.ML.Syntax.PNormal
import Language.DMoCHi.Common.Id
import Language.DMoCHi.Common.Util

import Language.DMoCHi.ML.Syntax.PType
import qualified Data.Map as M

{- Eliminate abstraction type casting by eta-expansion.
 -
 - Assume av :: AValue is a function value with type sigma :: PType and 
 - required to have type sigma' :: PType - where sigma /= sigma'.
 - This type casting is eliminated by replacing av with 
 - (fun x1 .. xn -> let f = av in ElimCast(f x1 .. xn)) :: Value
 -}
elimCastFunDef :: TypeMap -> Env -> (UniqueKey, [TId], Exp) -> PType -> FreshIO c (UniqueKey, [TId], Exp)
elimCastFunDef tbl env (ident,ys,e) sigma = 
    (,,) ident ys <$> elimCastTerm tbl env' e retTy'
        where
        PFun _ (xs,ty_xs,_,_) retTy = sigma 
        subst = M.fromList $ zip xs ys
        ty_ys = map (substPType subst) ty_xs
        env' = foldr (uncurry M.insert) env (zip ys ty_ys)
        retTy' = substTermType subst retTy

elimCastValue :: TypeMap -> Env -> Value -> PType -> FreshIO c Value
elimCastValue tbl env v sigma 
    | let sty = getType v
          key = getUniqueKey v = 
    case valueView v of
        VOther SLambda (xs, e) -> do
            (_, _, e') <- elimCastFunDef tbl env (key,xs,e) sigma
            return $ Value SLambda (xs,e') sty key
        VOther SPair (v1, v2) -> do
            let PPair _ sigma1 sigma2 = sigma 
            v1' <- elimCastValue tbl env v1 sigma1 
            v2' <- elimCastValue tbl env v2 sigma2 
            return $ mkPair v1' v2' key
        VAtom av@(Atom l arg _) -> case sigma of
            PInt -> return v
            PBool -> return v
            _ | sigma == typeOfAtom env av -> return v
            PFun ty (xs,_,_,_) _ -> do
                let TFun _ ty_r = ty
                (f, cnstr_f) <- case l of
                    SVar -> return (arg, id)
                    _ -> do g <- TId ty <$> identify "f"
                            key' <- freshKey
                            return (g, (\e -> mkLet g (cast v) e key'))
                ys <- mapM alphaTId xs
                e <- cnstr_f <$> do
                    j <- freshKey
                    r <- TId ty_r <$> identify "r"
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

{-
extendEnvByLet :: TypeMap -> Env -> TId -> LExp -> Env
extendEnvByLet tbl env x e = M.insert x r_ty' env
    where
    r_ty' = case lexpView e1 of
        LValue v 
          | VAtom av <- valueView v -> typeOfAtom env 
          | otherwise -> substVPType (M.singleton r v) r_ty
        LOther SRand _ -> PInt
        LOther SApp (f, vs) -> substVPType subst' r_ty
          where
          PFun _ (ys, ys_ty, _,_) (r, r_ty, _,_) = env M.! f
          subst = M.fromList $ zip ys vs
          ys_ty' = map (substVPType subst) ys_ty
          subst' = M.insert r (cast (mkVar x)) subst
        LOther SFail _ -> 
          exprCase
          -}
        


elimCastLet :: TypeMap -> Env -> TId -> LExp -> Exp -> UniqueKey -> TermType -> FreshIO c Exp
elimCastLet tbl env x e1 e2 key tau 
    | let key1 = getUniqueKey e1
          Right tau1@(r, r_ty, _,_) = case M.lookup key1 tbl of 
            Nothing -> error $ show key1
            Just v -> v
          exprCase :: LExp -> FreshIO c (LExp, Env)
          exprCase e1' = return (e1', env')
            where
              subst = M.singleton r x
              r_ty' = substPType subst r_ty
              env' = M.insert x r_ty' env
      = do
          (e1', env') <- case lexpView e1 of
              LValue v 
                | VAtom av <- valueView v -> do
                  let x_ty = typeOfAtom env av
                      env' = M.insert x x_ty env
                  return (e1,env')
                | otherwise -> do
                  let r_ty' = substVPType (M.singleton r v) r_ty
                      env' = M.insert x r_ty' env
                  e1' <- cast <$> elimCastValue tbl env v r_ty'
                  return (e1', env')
              LOther SRand _ -> do
                  let env' = M.insert x PInt env
                  return (e1,env')
              LOther SApp (f, vs) -> do
                  let PFun _ (ys, ys_ty, _,_) (r, r_ty, _,_) = env M.! f
                      subst = M.fromList $ zip ys vs
                      ys_ty' = map (substVPType subst) ys_ty
                  vs' <- zipWithM (elimCastValue tbl env) vs ys_ty' 
                  let subst' = M.insert r (cast (mkVar x)) subst
                      r_ty' = substVPType subst' r_ty
                      env' = M.insert x r_ty' env
                  return (mkApp f vs' key1, env')
              LOther SBranch (e3, e4) -> do
                  e3' <- elimCastTerm tbl env e3 tau1
                  e4' <- elimCastTerm tbl env e4 tau1
                  exprCase (mkBranchL e3' e4' key1)
              LOther SFail _ -> exprCase e1
              LOther SOmega _ -> exprCase e1
          e2' <- elimCastTerm tbl env' e2 tau
          return $ mkLet x e1' e2' key 
        

elimCastTerm :: TypeMap -> Env -> Exp -> TermType -> FreshIO c Exp
elimCastTerm tbl env e tau 
    | let sty = getType e
          key = getUniqueKey e = 
    case expView e of
        EValue v -> cast <$> elimCastValue tbl env v r_ty'
            where
            (r, r_ty, _, _) = tau 
            r_ty' = substVPType (M.singleton r v) r_ty
        EOther SLet (x, e1, e2) -> elimCastLet tbl env x e1 e2 key tau
        EOther SLetRec (fs, e2) -> do
            let as = map (\(f,v_f) -> 
                        let Left ty_f = tbl M.! (getUniqueKey v_f) in 
                        (f, ty_f)) fs
            let env' = foldr (uncurry M.insert) env as 
            fs' <- forM fs $ \(f, v_f) -> do
                let key_f = getUniqueKey v_f
                    Left ty_f = tbl M.! key_f
                v_f' <- elimCastValue tbl env' v_f ty_f
                return (f, v_f')
            mkLetRec fs' <$> elimCastTerm tbl env' e2 tau <*> pure key
        EOther SAssume (p, e1) -> do
            e1' <- elimCastTerm tbl env e1 tau
            return $ mkAssume p e1' key
        EOther SFail _ -> return $ mkFail sty key
        EOther SOmega _ -> return $ mkOmega sty key
        EOther SBranch (e1, e2) -> do
            e1' <- elimCastTerm tbl env e1 tau
            e2' <- elimCastTerm tbl env e2 tau
            return $ mkBranch e1' e2' key
        
elimCast :: TypeMap -> Program -> FreshIO c Program
elimCast tbl prog = do
    let env = M.fromList [ (f, ty) | (f, key, _, _) <- functions prog, let Left ty = tbl M.! key ]
    fs <- forM (functions prog) $ \(f, key, xs, e) -> do
                    (_,_,e') <- elimCastFunDef tbl env (key,xs,e) (env M.! f)
                    return (f, key, xs, e')
    r <- TId TInt <$> identify "main"
    e <- elimCastTerm tbl env (mainTerm prog) (r, PInt, [], undefined)
    return $ Program fs e
    

