module Language.DMoCHi.ML.PredicateAbstraction(abstProg, Abst) where
import Control.Monad
import Control.Monad.Writer
import qualified Data.Map as M
import Text.PrettyPrint.HughesPJClass

import qualified Language.DMoCHi.ML.Syntax.PNormal as ML
-- import qualified Language.DMoCHi.ML.PrettyPrint.PNormal as ML
import qualified Language.DMoCHi.Boolean.Syntax.Typed as B
import qualified Language.DMoCHi.Boolean.PrettyPrint.Typed as B
import qualified Language.DMoCHi.ML.SMT as SMT
import Language.DMoCHi.ML.Syntax.PType
import Language.DMoCHi.Common.Id
import Language.DMoCHi.Common.Util
import Data.PolyDict(Assoc,Dict,access)
import Data.Time(NominalDiffTime)

data Abst
type instance Assoc Abst "elapsed_time" = NominalDiffTime
type instance Assoc Abst "number_smt_calls" = Int

type PVar = [(B.Term, Formula)]
-- getSort (abstFormulae cs pv fmls) == TBool^(length fmls)
abstFormulae :: (MonadIO m, MonadLogger m, MonadId m) => Constraints -> PVar -> [Formula] -> m B.Term
abstFormulae cs pvs fml = do
    let ps = map snd pvs ++ fml
    bdd <- liftIO $ SMT.abst cs ps
    let sort = B.Tuple [ B.Bool | _ <- fml ]
    let gen qs (SMT.Leaf _ True) = return $ B.T $ reverse qs
        gen _ (SMT.Leaf _ False) = do
            omega <- B.Symbol sort <$> freshId "Omega"
            return $ B.Omega omega
        gen qs (SMT.Node _ _ hi lo) 
            | hi == lo = do
                let q = (B.f_branch (B.C True) (B.C False))
                gen (q:qs) hi
            | otherwise = do
                term_hi <- gen (B.C True : qs) hi
                term_lo <- gen (B.C False : qs) lo
                return $ B.f_branch term_hi term_lo
        go [] bdd = gen [] bdd
        go (_:_) (SMT.Leaf _ False) = do
            omega <- B.Symbol sort <$> freshId "Omega1"
            return $ B.Omega omega
        go (_:_) (SMT.Leaf _ True) = error "abstFormulae: unexpected satisfiable leaf"
        go ((term_p, _):pvs') (SMT.Node _ _ hi lo) 
            | hi == lo = go pvs' hi
            | otherwise = do
                term_hi <- go pvs' hi
                term_lo <- go pvs' lo
                return $ B.f_branch (B.f_assume term_p         term_hi)
                                    (B.f_assume (B.Not term_p) term_lo)

    term <- go pvs bdd
    let doc = 
            let doc_cs = brackets $ hsep $ punctuate comma (map (pPrint) cs)
                doc_pvar = brackets $ hsep $ punctuate comma (map (pPrint . snd) pvs)
                doc_fml = brackets $ hsep $ punctuate comma (map (pPrint) fml)
                doc_term = B.pprintTerm 0 term
            in braces $
               text "constraints:" <+> doc_cs $+$ 
               text "predicates:" <+> doc_pvar $+$ 
               text "formulae:" <+> doc_fml $+$ 
               text "abst result:" <+> doc_term
    logPretty "abst" LevelDebug "abstFormulae" (PPrinted doc)
    return term

-- getSort (abstFormulae cs pv fmls) == TBool
abstFormula :: (MonadIO m, MonadLogger m, MonadId m) => Constraints -> PVar -> Formula -> m B.Term
abstFormula cs pvs fml = do
    term <- abstFormulae cs pvs [fml]
    tup <- B.Symbol (B.Tuple [B.Bool]) <$> freshId "tuple"
    return $ B.f_let tup term (B.f_proj 0 1 (B.V tup))


-- Function:
--      e' = cast cs pv e curTy newTy
-- assumptions:
--      getSort e == toSort curTy
--      toSimple curTy == toSimple newTy
-- assertion:
--      getSort e' == toSort newTy

cast :: (MonadIO m, MonadLogger m, MonadId m) => Constraints -> PVar -> B.Term -> PType -> PType -> m B.Term
cast cs pv e curTy newTy = do
    let doc_cs = brackets $ hsep $ punctuate comma (map (pPrint) cs)
        doc_pvar = brackets $ hsep $ punctuate comma (map (pPrint . snd) pv)
        doc_e = B.pprintTerm 0 e
        doc_curTy = pprintPType 0 curTy
        doc_newTy = pprintPType 0 newTy
    if curTy /= newTy 
      then do
        let d = braces $
               text "constraints:" <+> doc_cs $+$ 
               text "predicates:" <+> doc_pvar $+$ 
               text "prev term:" <+> doc_e $+$ 
               text "prev type:" <+> doc_curTy $+$
               text "new  type:" <+> doc_newTy
        logPretty "cast" LevelError "unexpected cast" (PPrinted d)
        error "unexpected cast"
      else return e

toSort :: PType -> B.Sort
toSort PInt = B.Tuple []
toSort PBool = B.Bool
toSort (PPair _ t1 t2) = B.Tuple [toSort t1, toSort t2]
toSort (PFun _ tx tr) = toSortArg tx B.:-> toSortTerm tr

toSortTerm :: TermType -> B.Sort
toSortTerm (_, ty, ps, _) = B.Tuple [toSort ty, B.Tuple [ B.Bool | _ <- ps ]]
toSortArg :: ArgType -> B.Sort
toSortArg (_, tys, ps, _) = B.Tuple [B.Tuple $ map toSort tys, B.Tuple [B.Bool | _ <- ps]]

toSymbol :: ML.TId -> PType -> B.Symbol
toSymbol (ML.TId _ x) ty = B.Symbol (toSort ty) (show x)

abstAValue :: (MonadIO m, MonadLogger m, MonadId m) 
            => Env -> Constraints -> PVar -> ML.Atom-> PType -> m B.Term
abstAValue env cs pv = go 
    where 
    go v@(ML.Atom l arg _) ty = case (l,arg) of
        (ML.SVar,x) -> cast cs pv (B.V (toSymbol x (env M.! x))) (env M.! x) ty
        (ML.SLiteral, ML.CInt _) -> return $ B.T []
        (ML.SLiteral, ML.CBool b) -> return $ (B.C b)
        (ML.SLiteral, ML.CUnit) -> error "unexpected pattern"
        (ML.SBinary, ML.BinArg op _ _) -> case op of
            ML.SAdd  -> return $ B.T []
            ML.SSub  -> return $ B.T []
            ML.SDiv  -> return $ B.T []
            ML.SMul  -> return $ B.T []
            ML.SEq   -> abstFormula cs pv v
            ML.SLt   -> abstFormula cs pv v
            ML.SLte  -> abstFormula cs pv v
            ML.SAnd  -> abstFormula cs pv v
            ML.SOr   -> abstFormula cs pv v
        (ML.SUnary, ML.UniArg op v) -> case op of
            ML.SFst -> 
                let PPair _ _ ty2 = typeOfAtom env v in
                B.f_proj 0 2 <$> go v (mkPPair ty ty2)
            ML.SSnd  -> 
                let PPair _ ty1 _ = typeOfAtom env v in
                B.f_proj 1 2 <$> go v (mkPPair ty1 ty)
            ML.SNot -> B.Not <$> go v PBool
            ML.SNeg -> return $ B.T []
abstValue :: (MonadIO m, MonadLogger m, MonadId m) 
            => TypeMap -> Env -> Constraints -> PVar -> ML.Value -> PType -> m B.Term
abstValue tbl env cs pv v ty = 
    case ML.valueView v of
        ML.VAtom av -> abstAValue env cs pv av ty
        ML.VOther ML.SLambda (xs, e) -> 
            abstFunDef tbl env cs pv (getUniqueKey v, xs, e) (Just ty)
        ML.VOther ML.SPair (v1, v2) -> 
            let PPair _ ty1 ty2 = ty in
            (\x y -> B.T [x,y]) <$> abstValue tbl env cs pv v1 ty1 
                                <*> abstValue tbl env cs pv v2 ty2

abstTerm :: forall m. (MonadId m, MonadLogger m, MonadIO m) 
            => TypeMap -> Env -> Constraints -> PVar -> ML.Exp -> TermType -> m B.Term
abstTerm tbl env cs pv e tau = 
    case ML.expView e of
        ML.EValue v -> do
            let (ty, qs, _) = betaConv v tau
            e1 <- abstValue tbl env cs pv v ty
            e2 <- abstFormulae cs pv qs
            return $ B.T [e1,e2]
        ML.EOther ML.SLetRec (fs, e2) -> do
            let as = [ (f, ty_f) | (f,v_f) <- fs, let Left ty_f = tbl M.! (getUniqueKey v_f) ]
                env' = foldr (uncurry M.insert) env as
            fs' <- forM fs $ \(f, v_f) -> do
                let Left ty_f = tbl M.! (getUniqueKey v_f)
                t_f <- abstValue tbl env' cs pv v_f ty_f
                return (toSymbol f ty_f, t_f)
            B.f_letrec fs' <$> abstTerm tbl env' cs pv e2 tau
        ML.EOther ML.SLet (x,e1,e2) -> 
            let key1 = getUniqueKey e1
                exprCase :: ML.Exp -> m B.Term
                exprCase e1 = do
                    let Right tau1@(alphaConv x -> (ty_x,ps, _)) = tbl M.! key1
                    let sx = show $ ML.name x
                    x_pair <- B.freshSym (sx ++ "_pair") (toSortTerm tau1)
                    B.f_let x_pair <$> abstTerm tbl env cs pv e1 tau1 <*> do
                        let x_body  = B.f_proj 0 2 (B.V x_pair)
                            x_preds = B.f_proj 1 2 (B.V x_pair)
                            n = length ps
                            pv' = [ (B.f_proj i n x_preds, fml) | (i,fml) <- zip [0..] ps ] ++ pv
                            env' = M.insert x ty_x env
                        -- let x = abst(cs,pv,t1,tau1) in
                        B.f_let (toSymbol x ty_x) x_body <$> 
                            -- assume phi;
                            (B.f_assume <$> (abstFormula cs pv' (ML.mkLiteral $ ML.CBool True)) 
                                        -- abst(cs,pv',t,tau)
                                        <*> abstTerm tbl env' cs pv' e2 tau)               
            in case ML.lexpView e1 of
                ML.LValue v -> case ML.valueView v of
                    ML.VAtom av -> do
                        let ty_x = typeOfAtom env av
                        ex <- abstValue tbl env cs pv v ty_x
                        e' <- abstTerm tbl (M.insert x ty_x env) (addEq x av cs) pv e2 tau
                        return $ B.f_let (toSymbol x ty_x) ex e'
                    ML.VOther ML.SLambda _ -> exprCase (ML.cast v)
                    ML.VOther ML.SPair _ -> exprCase (ML.cast v)
                ML.LOther ML.SApp (f, vs) -> do
                    let ((ty_vs, ps, _), ret_ty) = appPType (env M.! f) vs
                        (ty_x, qs, _) = alphaConv x ret_ty
                        sx = show $ ML.name x 
                    arg_body  <- B.T <$> zipWithM (abstValue tbl env cs pv) vs ty_vs
                    arg_preds <- abstFormulae cs pv ps
                    let f' = toSymbol f (env M.! f)
                    x' <- B.freshSym (sx ++ "_pair") (toSortTerm ret_ty)
                    let x_body  = B.f_proj 0 2 (B.V x')
                        x_preds = B.f_proj 1 2 (B.V x')
                        n = length qs
                        pv' = [ (B.f_proj i n x_preds, fml) | (i,fml) <- zip [0..] qs ] ++ pv
                    B.f_let x' (B.f_app (B.V f') (B.T [arg_body, arg_preds])) .   -- let x = f <body, preds> in
                      B.f_let (toSymbol x ty_x) x_body <$>                       -- let v = x.fst
                        (B.f_assume <$> abstFormula cs pv' (ML.mkLiteral (ML.CBool True)) -- assume phi; // avoid incosinsitent states
                                    <*> abstTerm tbl (M.insert x ty_x env) cs pv' e2 tau)     -- abst(cs,pv',t,tau)
                ML.LOther ML.SRand _ -> 
                    B.f_let (toSymbol x PInt) (B.T []) <$>
                        abstTerm tbl (M.insert x PInt env) cs pv e2 tau
                ML.LOther ML.SBranch arg -> 
                    exprCase (ML.Exp ML.SBranch arg (ML.getType e1) key1)
                ML.LOther ML.SFail _ -> error "abstTerm: Fail is not supported"
                ML.LOther ML.SOmega _ -> error "abstTerm: Omega is not supported"
        ML.EOther ML.SAssume (v,e) -> do
            e_v <- abstValue tbl env cs pv (ML.cast v) PBool
            B.f_assume e_v <$> abstTerm tbl env (v : cs) pv e tau
        ML.EOther ML.SFail _ -> do
            fail <- B.freshSym "fail" (toSortTerm tau)
            return $ B.Fail fail
        ML.EOther ML.SOmega _ -> do
            fail <- B.freshSym "omega" (toSortTerm tau)
            return $ B.Omega fail
        ML.EOther ML.SBranch (t1, t2) -> do
            B.f_branch_label <$> abstTerm tbl env cs pv t1 tau
                             <*> abstTerm tbl env cs pv t2 tau

addEq :: ML.TId -> ML.Atom -> Constraints -> Constraints
addEq y v cs = (ML.mkBin ML.SEq (ML.mkVar y) v) :cs

abstFunDef :: (MonadId m, MonadLogger m, MonadIO m) => TypeMap -> Env -> Constraints -> PVar -> (UniqueKey,[ML.TId],ML.Exp) -> Maybe PType -> m B.Term
abstFunDef tbl env cs pv (ident,xs,t1) mpty = do
    let PFun _ arg_ty@(_,ty_xs,ps,_) rty = 
            alphaConvFun xs $ case mpty of
                Just pty -> pty
                Nothing -> let Left pty = tbl M.! ident in pty
    x_pair <- B.freshSym "arg" (toSortArg arg_ty)
    B.Lam x_pair <$> do
        let x_body  = B.f_proj 0 2 (B.V x_pair)
            x_preds = B.f_proj 1 2 (B.V x_pair)
            n = length ps
            arity = length xs
            pv' = [ (B.f_proj i n x_preds, fml) | (i,fml) <- zip [0..] ps ] ++ pv
            env' = extendEnv env (zip xs ty_xs)
        flip (foldr (\(i,x,ty_y) -> 
            B.f_let (toSymbol x ty_y) (B.f_proj i arity x_body))) (zip3 [0..] xs ty_xs)
            <$> (B.f_assume <$> (abstFormula cs pv' (ML.mkLiteral $ ML.CBool True)) 
                            <*> (abstTerm tbl env' cs pv' t1 rty))

pprintTypeMap :: TypeMap -> Doc
pprintTypeMap tbl = braces $ vcat $ punctuate comma ds
    where
    ds = flip map (M.assocs tbl) $ \case
        (i,Left pty) -> pPrint i <+> colon <+> pprintPType 0 pty
        (i,Right termType) -> pPrint i <+> colon <+> pprintTermType termType

abstProg :: TypeMap -> ML.Program -> FreshIO (Dict Abst) B.Program
abstProg tbl (ML.Program fs t0) = measure #elapsed_time $ do
    logPretty "abst" LevelInfo "current abstraction type environment" (PPrinted $ pprintTypeMap tbl)
    liftIO SMT.resetSMTCount

    let env = M.fromList [ (f,ty)  | (f,key,_,_) <- fs, let Left ty = tbl M.! key ]
    ds <- forM fs $ \(f,key,xs,e) -> do
        let f' = toSymbol f (env M.! f)
        e_f <- abstFunDef tbl env [] [] (key,xs,e) (Just $ env M.! f)
        return (f',e_f)
    e0 <- do
        r <- ML.TId ML.TInt <$> identify "main"
        abstTerm tbl env [] [] t0 (r,PInt,[], undefined)
    liftIO SMT.getSMTCount >>= \count -> update (access #number_smt_calls ?~ count)
    return $ B.Program ds e0

