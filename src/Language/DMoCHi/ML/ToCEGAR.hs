module Language.DMoCHi.ML.ToCEGAR(convert) where

import qualified Language.DMoCHi.ML.Syntax.PNormal as From
import qualified Language.DMoCHi.ML.Syntax.CEGAR   as To
import           Language.DMoCHi.ML.Syntax.HFormula(HFormulaFactory(..), toHFormula, runHFormulaT, Context)
import           Language.DMoCHi.ML.Syntax.Base
import           Language.DMoCHi.ML.Syntax.PType
import           Language.DMoCHi.ML.Syntax.PNormal(Castable(..))
import           Language.DMoCHi.ML.Syntax.Type
import           Language.DMoCHi.Common.Id
import           Control.Monad
import qualified Data.Map as M

convert :: Context -> TypeMap -> From.Program -> IO To.Program
convert ctx typeMap prog = runHFormulaT (To.Program <$> (convertE typeMap M.empty (From.mainTerm prog) tau)) ctx
    where
    tau = (TId TInt (reserved "main"), PInt, [], dummyPredTemplate)

convertV :: HFormulaFactory m => TypeMap -> M.Map TId PType -> From.Value -> PType -> m To.Value
convertV typeMap env v sigma = 
    let key = getUniqueKey v in
    case From.valueView v of
        From.VAtom a -> return $ castWith key a
        From.VOther SLambda (xs, e) -> do
                e' <- convertE typeMap env' e tau'
                info <- mapM toHFormula ps' >>= \ps' -> return $ To.AbstInfo ps' pred_tmpl_xs
                return $ To.mkLambda xs info e' key
            where
            PFun _ (ys, ptys_ys, ps, pred_tmpl_ys) tau = sigma
            subst = M.fromList $ zip ys xs
            ptys_xs = map (substPType subst) ptys_ys
            pred_tmpl_xs = substPredTemplate subst pred_tmpl_ys
            ps' = map (substFormula subst) ps
            env' = foldr (uncurry M.insert) env (zip xs ptys_xs)
            tau' = substTermType subst tau
        From.VOther SPair (v1, v2) -> do
                v1' <- convertV typeMap env v1 sigma1
                v2' <- convertV typeMap env v2 sigma2
                return $ To.mkPair v1' v2' key
            where
            PPair _ sigma1 sigma2 = sigma

-- env scopeEnv |- e : tau 
convertE :: HFormulaFactory m => TypeMap -> M.Map TId PType -> From.Exp -> TermType -> m To.Exp
convertE typeMap env e tau =
    let key = getUniqueKey e in
    case From.expView e of
        From.EValue v -> do
                v' <- convertV typeMap env v rty' 
                info <- mapM toHFormula ps' >>= \ps' -> return $ To.AbstInfo ps' pred_tmpl'
                return $ castWith info v'
            where
            (r, rty, ps, pred_tmpl) = tau
            subst = M.singleton r v
            rty' = substVPType subst rty
            ps' = map (substVFormula subst) ps
            pred_tmpl' = substVPredTemplate subst pred_tmpl
        From.EOther SLetRec (fs, e2) -> do
                fs' <- forM fs $ \(f, v_f) -> (f,) <$> convertV typeMap env' v_f (env' M.! f)
                e2' <- convertE typeMap env' e2 tau
                return $ To.mkLetRec fs' e2' key
            where
            as = [ (f, pty_f)  | (f, v_f) <- fs, let Left pty_f = typeMap M.! getUniqueKey v_f ]
            env' = foldr (uncurry M.insert) env as
        From.EOther SAssume (cond, e2) -> do
                e2' <- convertE typeMap env e2 tau
                return $ To.mkAssume cond e2' key
        From.EOther SBranch (e1, e2) -> do
            e1' <- convertE typeMap env e1 tau
            e2' <- convertE typeMap env e2 tau
            return $ To.mkBranch e1' e2' key
        From.EOther SFail () -> return $ To.mkFail (getType e) key
        From.EOther SOmega () -> return $ To.mkOmega (getType e) key
        From.EOther SLet (x, e1, e2) -> 
            case From.lexpView e1 of
                From.LValue (From.valueView -> From.VAtom a) -> do
                        e2' <- convertE typeMap (M.insert x pty_x env) e2 tau
                        return $ To.mkLet x (castWith (getUniqueKey e1) a) info e2' key
                    where 
                    info = To.AbstInfo [] dummyPredTemplate
                    pty_x = typeOfAtom env a
                From.LValue _ -> error "RHS of let-binding must not be a pair nor a lambda-abst"
                From.LOther SApp (f, vs) -> do
                        vs' <- zipWithM (convertV typeMap env) vs ptys_vs
                        info_arg <- mapM toHFormula ps' >>= \ps' -> return $ To.AbstInfo ps' pred_tmpl_arg'
                        let e1' = To.mkApp f info_arg vs' (getUniqueKey e1)
                        e2' <- convertE typeMap (M.insert x pty_x env) e2 tau
                        info_ret <- mapM toHFormula qs' >>= \qs' -> return $ To.AbstInfo qs' pred_tmpl_ret'
                        return $ To.mkLet x e1' info_ret e2' key
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
                    pty_x = substVPType subst' pty_r
                From.LOther SRand () -> do
                        e2' <- convertE typeMap (M.insert x PInt env) e2 tau
                        return $ To.mkLet x (To.mkRand (getUniqueKey e1)) info e2' key
                    where
                    info = To.AbstInfo [] dummyPredTemplate
                From.LOther SBranch (e_l, e_r) -> do
                        e_l' <- convertE typeMap env e_l tau1
                        e_r' <- convertE typeMap env e_r tau1
                        e2' <- convertE typeMap (M.insert x pty_x env) e2 tau
                        info <-  mapM toHFormula ps' >>= \ps' -> return $ To.AbstInfo ps' pred_tmpl_x
                        return $ To.mkLet x (To.mkBranchL e_l' e_r' key1) info e2' key
                    where
                    key1 = getUniqueKey e1
                    subst = M.singleton y x
                    pty_x = substPType subst pty_y
                    pred_tmpl_x = substPredTemplate subst pred_tmpl_y
                    ps' = map (substFormula subst) ps
                    Right tau1@(y, pty_y, ps, pred_tmpl_y) = typeMap M.! key1
                From.LOther SOmega _ -> return $ To.mkOmega (getType e) key
                From.LOther SFail  _ -> return $ To.mkFail  (getType e) key
                    
