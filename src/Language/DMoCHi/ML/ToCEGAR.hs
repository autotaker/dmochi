module Language.DMoCHi.ML.ToCEGAR(convert) where

import qualified Language.DMoCHi.ML.Syntax.PNormal as From
import qualified Language.DMoCHi.ML.Syntax.CEGAR   as To
import           Language.DMoCHi.ML.Syntax.HFormula(HFormulaFactory(..), runHFormulaT, Context)
import           Language.DMoCHi.ML.Syntax.Base
import           Language.DMoCHi.ML.Syntax.PType
import           Language.DMoCHi.ML.Syntax.PNormal(Castable(..))
import           Language.DMoCHi.ML.Syntax.Type
import           Language.DMoCHi.Common.Id
import           Language.DMoCHi.Common.Util
import           Control.Monad
import qualified Data.Map as M

convert :: Context -> TypeMap -> From.Program -> IO To.Program
convert ctx typeMap prog = 
    runHFormulaT (To.Program <$> convertE typeMap M.empty (From.mainTerm prog) tau) ctx
    where
    tau = (TId TInt (reserved "main"), PInt, [], dummyPredTemplate)

convertV :: HFormulaFactory m => TypeMap -> M.Map TId PType -> From.Value -> PType -> m To.Value
convertV typeMap env v sigma = 
    let key = getUniqueKey v in
    case From.valueView v of
        From.VAtom a -> return $ castWith key a
        From.VOther SLambda (xs, e) -> do
            let PFun _ (_, ptys_xs, ps, pred_tmpl_xs) tau = alphaConvFun xs sigma
                env' = extendEnv env (zip xs ptys_xs)
            e' <- convertE typeMap env' e tau
            info <- To.mkAbstInfo ps pred_tmpl_xs
            return $ To.mkLambda xs info e' key
        From.VOther SPair (v1, v2) -> do
            let PPair _ sigma1 sigma2 = sigma
            v1' <- convertV typeMap env v1 sigma1
            v2' <- convertV typeMap env v2 sigma2
            return $ To.mkPair v1' v2' key

-- env scopeEnv |- e : tau 
convertE :: HFormulaFactory m => TypeMap -> M.Map TId PType -> From.Exp -> TermType -> m To.Exp
convertE typeMap env e tau =
    let key = getUniqueKey e in
    case From.expView e of
        From.EValue v -> do
            let (rty, ps, pred_tmpl) = betaConv v tau
            v' <- convertV typeMap env v rty 
            info <- To.mkAbstInfo ps pred_tmpl
            return $ castWith info v'
        From.EOther SLetRec (fs, e2) -> do
            let as = [ (f, pty_f)  | (f, v_f) <- fs, 
                                     let Left pty_f = typeMap M.! getUniqueKey v_f ]
                env' = foldr (uncurry M.insert) env as
            fs' <- forM fs $ \(f, v_f) -> (f,) <$> convertV typeMap env' v_f (env' M.! f)
            e2' <- convertE typeMap env' e2 tau
            return $ To.mkLetRec fs' e2' key
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
                    let info = To.DummyInfo
                    let pty_x = typeOfAtom env a
                    e2' <- convertE typeMap (M.insert x pty_x env) e2 tau
                    return $ To.mkLet x (castWith (getUniqueKey e1) a) info e2' key
                From.LValue _ -> error "RHS of let-binding must not be a pair nor a lambda-abst"
                From.LOther SApp (f, vs) -> do
                    let ((ptys_vs, ps, pred_tmpl_arg), ty_ret) = appPType (env M.! f) vs
                        (pty_x, qs, pred_tmpl_ret) = alphaConv x ty_ret
                    vs' <- zipWithM (convertV typeMap env) vs ptys_vs
                    info_arg <- To.mkAbstInfo ps pred_tmpl_arg
                    let e1' = To.mkApp f info_arg vs' (getUniqueKey e1)
                    e2' <- convertE typeMap (M.insert x pty_x env) e2 tau
                    info_ret <- To.mkAbstInfo qs pred_tmpl_ret
                    return $ To.mkLet x e1' info_ret e2' key
                From.LOther SRand () -> do
                    let info = To.DummyInfo
                    e2' <- convertE typeMap (M.insert x PInt env) e2 tau
                    return $ To.mkLet x (To.mkRand (getUniqueKey e1)) info e2' key
                From.LOther SBranch (e_l, e_r) -> do
                    let key1 = getUniqueKey e1
                        Right tau1@(alphaConv x -> (pty_x, ps, pred_tmpl_x)) = typeMap M.! key1
                    e_l' <- convertE typeMap env e_l tau1
                    e_r' <- convertE typeMap env e_r tau1
                    e2' <- convertE typeMap (M.insert x pty_x env) e2 tau
                    info <- To.mkAbstInfo ps pred_tmpl_x 
                    return $ To.mkLet x (To.mkBranchL e_l' e_r' key1) info e2' key
                From.LOther SOmega _ -> return $ To.mkOmega (getType e) key
                From.LOther SFail  _ -> return $ To.mkFail  (getType e) key
