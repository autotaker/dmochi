module Language.DMoCHi.ML.ToCEGAR(convert) where

import qualified Language.DMoCHi.ML.Syntax.PNormal as From
import qualified Language.DMoCHi.ML.Syntax.CEGAR   as To
import           Language.DMoCHi.ML.Syntax.Base
import           Language.DMoCHi.ML.Syntax.PType
import           Language.DMoCHi.ML.Syntax.PNormal(Castable(..))
import           Language.DMoCHi.ML.Syntax.Type
import           Language.DMoCHi.Common.Id
import qualified Data.Map as M

convert :: TypeMap -> From.Program -> To.Program
convert typeMap prog = To.Program (convertE typeMap M.empty (From.mainTerm prog) tau)
    where
    tau = (TId TInt (reserved "main"), PInt, [], dummyPredTemplate)

convertV :: TypeMap -> M.Map TId PType -> From.Value -> PType -> To.Value
convertV typeMap env v sigma = 
    let key = getUniqueKey v in
    case From.valueView v of
        From.VAtom a -> castWith key a
        From.VOther SLambda (xs, e) -> 
            To.mkLambda xs info e' key
            where
            PFun _ (ys, ptys_ys, ps, pred_tmpl_ys) tau = sigma
            subst = M.fromList $ zip ys xs
            ptys_xs = map (substPType subst) ptys_ys
            ps' = map (substFormula subst) ps
            pred_tmpl_xs = substPredTemplate subst pred_tmpl_ys
            info = To.AbstInfo ps' pred_tmpl_xs
            env' = foldr (uncurry M.insert) env (zip xs ptys_xs)
            tau' = substTermType subst tau
            e' = convertE typeMap env' e tau'
        From.VOther SPair (v1, v2) ->
            To.mkPair v1' v2' key
            where
            PPair _ sigma1 sigma2 = sigma
            v1' = convertV typeMap env v1 sigma1
            v2' = convertV typeMap env v2 sigma2

-- env scopeEnv |- e : tau 
convertE :: TypeMap -> M.Map TId PType -> From.Exp -> TermType -> To.Exp
convertE typeMap env e tau =
    let key = getUniqueKey e in
    case From.expView e of
        From.EValue v -> castWith info v'
            where
            v' = convertV typeMap env v rty' 
            (r, rty, ps, pred_tmpl) = tau
            subst = M.singleton r v
            rty' = substVPType subst rty
            ps' = map (substVFormula subst) ps
            pred_tmpl' = substVPredTemplate subst pred_tmpl
            info = To.AbstInfo ps' pred_tmpl'
        From.EOther SLetRec (fs, e2) -> To.mkLetRec fs' e2' key
            where
            as = [ (f, pty_f)  | (f, v_f) <- fs, let Left pty_f = typeMap M.! getUniqueKey v_f ]
            env' = foldr (uncurry M.insert) env as
            fs' = [ (f, convertV typeMap env' v_f (env' M.! f)) | (f, v_f) <- fs ]
            e2' = convertE typeMap env' e2 tau
        From.EOther SAssume (cond, e2) -> To.mkAssume cond e2' key
            where e2' = convertE typeMap env e2 tau
        From.EOther SBranch (e1, e2) -> 
            To.mkBranch e1' e2' key
            where
            e1' = convertE typeMap env e1 tau
            e2' = convertE typeMap env e2 tau
        From.EOther SFail () -> To.mkFail (getType e) key
        From.EOther SOmega () -> To.mkOmega (getType e) key
        From.EOther SLet (x, e1, e2) -> 
            case From.lexpView e1 of
                From.LValue (From.valueView -> From.VAtom a) ->
                    To.mkLet x (castWith (getUniqueKey e1) a) info e2' key
                    where 
                    info = To.AbstInfo [] dummyPredTemplate
                    pty_x = typeOfAtom env a
                    e2' = convertE typeMap (M.insert x pty_x env) e2 tau
                From.LValue _ -> error "RHS of let-binding must not be a pair nor a lambda-abst"
                From.LOther SApp (f, vs) ->
                    To.mkLet x e1' info_ret e2' key
                    where
                    PFun _ argTy retTy = env M.! f
                    (ys, ptys, ps, pred_tmpl_arg) = argTy
                    subst = M.fromList $ zip ys vs
                    ps' = map (substVFormula subst) ps
                    pred_tmpl_arg' = substVPredTemplate  subst pred_tmpl_arg
                    ptys_vs = map (substVPType subst) ptys
                    (r, pty_r, qs, pred_tmpl_ret) = retTy
                    subst' = M.insert r (cast (From.mkVar x)) subst
                    qs' = map (substVFormula subst') qs
                    pred_tmpl_ret' = substVPredTemplate  subst' pred_tmpl_ret
                    info_arg = To.AbstInfo ps' pred_tmpl_arg'
                    info_ret = To.AbstInfo qs' pred_tmpl_ret'
                    pty_x = substVPType subst' pty_r
                    vs' = zipWith (convertV typeMap env) vs ptys_vs
                    e1' = To.mkApp f info_arg vs' (getUniqueKey e1)
                    e2' = convertE typeMap (M.insert x pty_x env) e2 tau
                From.LOther SRand () ->
                    To.mkLet x (To.mkRand (getUniqueKey e1)) info e2' key
                    where
                    info = To.AbstInfo [] dummyPredTemplate
                    e2' = convertE typeMap (M.insert x PInt env) e2 tau
                From.LOther SBranch (e_l, e_r) ->
                    To.mkLet x (To.mkBranchL e_l' e_r' key1) info e2' key
                    where
                    key1 = getUniqueKey e1
                    e_l' = convertE typeMap env e_l tau1
                    e_r' = convertE typeMap env e_r tau1
                    subst = M.singleton y x
                    pty_x = substPType subst pty_y
                    pred_tmpl_x = substPredTemplate subst pred_tmpl_y
                    ps' = map (substFormula subst) ps
                    Right tau1@(y, pty_y, ps, pred_tmpl_y) = typeMap M.! key1
                    e2' = convertE typeMap (M.insert x pty_x env) e2 tau
                    info = To.AbstInfo ps' pred_tmpl_x
                From.LOther SOmega _ -> To.mkOmega (getType e) key
                From.LOther SFail  _ -> To.mkFail  (getType e) key
                    
