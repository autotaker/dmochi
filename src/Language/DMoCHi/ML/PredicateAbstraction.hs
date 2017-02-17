{-# LANGUAGE FlexibleContexts, GADTs, ScopedTypeVariables #-}
module Language.DMoCHi.ML.PredicateAbstraction where
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

type PVar = [(B.Term, Formula)]
-- getSort (abstFormulae cs pv fmls) == TBool^(length fmls)
abstFormulae :: (MonadIO m, MonadId m) => Constraints -> PVar -> [Formula] -> m B.Term
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
    liftIO $ putStrLn $ render (
        let doc_cs = brackets $ hsep $ punctuate comma (map (pPrint) cs)
            doc_pvar = brackets $ hsep $ punctuate comma (map (pPrint . snd) pvs)
            doc_fml = brackets $ hsep $ punctuate comma (map (pPrint) fml)
            doc_term = B.pprintTerm 0 term
        in braces (
           text "constraints:" <+> doc_cs $+$ 
           text "predicates:" <+> doc_pvar $+$ 
           text "formulae:" <+> doc_fml $+$ 
           text "abst result:" <+> doc_term))
    return term

-- getSort (abstFormulae cs pv fmls) == TBool
abstFormula :: (MonadIO m, MonadId m) => Constraints -> PVar -> Formula -> m B.Term
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

cast :: (MonadIO m, MonadId m) => Constraints -> PVar -> B.Term -> PType -> PType -> m B.Term
{-
cast' cs pv e curTy newTy = case (curTy,newTy) of
    _ | curTy == newTy -> return e
    (PPair _ ty1 ty2, PPair _ ty1' ty2') -> do
        e1 <- cast' cs pv (B.f_proj 0 2 e) ty1 ty1'
        e2 <- cast' cs pv (B.f_proj 1 2 e) ty2 ty2'
        return $ B.T [e1,e2]
    (PFun _ (xs,ty_xs,ps) (r,ty_r,qs), 
     PFun _ (ys,ty_ys,ps') (r',ty_r',qs')) -> do
        y_pair <- B.freshSym "arg" (toSortArg (ys,ty_ys,ps'))
        B.Lam y_pair <$> do                                                               {- fun y_pair -> -}
            let y_body = B.f_proj 0 2 (B.V y_pair)                                        {-     let y_body = y_pair.fst in  -}
                y_preds = B.f_proj 1 2 (B.V y_pair)                                       {-     let y_preds = y_pair.snd in -}
                n = length ps'
                pv' = [ (B.f_proj i n y_preds, fml) | (i,fml) <- zip [0..] ps'] ++ pv
                arity = length xs
                subst = M.fromList $ zip xs ys
            x_body  <- B.T <$> forM (zip3 [0..] ty_ys ty_xs) (\(i,ty_y,ty_x) ->           {-     let x_body = <v1...vn>  -}
                 cast' cs pv' (B.f_proj i arity y_body) ty_y (substPType subst ty_x))
            x_preds <- abstFormulae cs pv' (map (substFormula subst) ps)
            r_pair <- B.freshSym (ML.name r) (toSortTerm (r,ty_r,qs))
            B.f_let r_pair (B.f_app e (B.T [x_body,x_preds])) <$> do                      {- let r_pair = e (x_body, x_preds) in -}
                let r_body = B.f_proj 0 2 $ B.V r_pair                                    {- r_body corresponds to ty_r          -}
                    r_preds = B.f_proj 1 2 $ B.V r_pair                                   {- r_preds corresponds to qs           -}
                    m = length qs
                    subst' = M.insert r r' subst
                    pv'' = [ (B.f_proj i m r_preds, 
                              substFormula subst' fml) | (i,fml) <- zip [0..] qs] ++ pv'
                r'_body <- cast' cs pv'' r_body (substPType subst' ty_r) ty_r'
                r'_preds <- abstFormulae cs pv'' qs'
                return $ B.T [r'_body,r'_preds]                                           {- <r_body, r_preds> -}
    _ -> error "cast: unexpected pattern"
    -}
cast cs pv e curTy newTy = do
    let doc_cs = brackets $ hsep $ punctuate comma (map (pPrint) cs)
        doc_pvar = brackets $ hsep $ punctuate comma (map (pPrint . snd) pv)
        doc_e = B.pprintTerm 0 e
        doc_curTy = pprintPType 0 curTy
        doc_newTy = pprintPType 0 newTy
    if curTy /= newTy 
      then do
        liftIO $ putStrLn $ render $
            braces (
               text "constraints:" <+> doc_cs $+$ 
               text "predicates:" <+> doc_pvar $+$ 
               text "prev term:" <+> doc_e $+$ 
               text "prev type:" <+> doc_curTy $+$
               text "new  type:" <+> doc_newTy)
        error "unexpected cast"
      else return e
      {-
        r <- cast' cs pv e curTy newTy
        let doc_r = B.pprintTerm 0 r
        liftIO $ putStrLn $ render $
            braces (
               text "constraints:" <+> doc_cs $+$ 
               text "predicates:" <+> doc_pvar $+$ 
               text "prev term:" <+> doc_e $+$ 
               text "prev type:" <+> doc_curTy $+$
               text "new  type:" <+> doc_newTy $+$
               text "abst result:" <+> doc_r)
        return r
-}

toSort :: PType -> B.Sort
toSort PInt = B.Tuple []
toSort PBool = B.Bool
toSort (PPair _ t1 t2) = B.Tuple [toSort t1, toSort t2]
toSort (PFun _ tx tr) = toSortArg tx B.:-> toSortTerm tr

toSortTerm :: TermType -> B.Sort
toSortTerm (_, ty, ps) = B.Tuple [toSort ty, B.Tuple [ B.Bool | _ <- ps ]]
toSortArg :: ArgType -> B.Sort
toSortArg (_, tys, ps) = B.Tuple [B.Tuple $ map toSort tys, B.Tuple [B.Bool | _ <- ps]]

toSymbol :: ML.TId -> PType -> B.Symbol
toSymbol (ML.TId _ x) ty = B.Symbol (toSort ty) (show x)

abstAValue :: (MonadIO m, MonadId m) => Env -> Constraints -> PVar -> ML.Atom-> PType -> m B.Term
abstAValue env cs pv = go 
    where 
    go v@(ML.Atom l arg _) ty = case (l,arg) of
        (ML.SVar,x) -> cast cs pv (B.V (toSymbol x (env M.! x))) (env M.! x) ty
        (ML.SLiteral, ML.CInt _) -> return $ B.T []
        (ML.SLiteral, ML.CBool b) -> return $ (B.C b)
        (ML.SBinary, ML.BinArg op _ _) -> case op of
            ML.SAdd  -> return $ B.T []
            ML.SSub  -> return $ B.T []
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
abstValue :: (MonadIO m, MonadId m) => TypeMap -> Env -> Constraints -> PVar -> ML.Value -> PType -> m B.Term
abstValue tbl env cs pv v@(ML.Value l arg _ key) ty = case (l,arg) of
    (ML.SLambda, (xs,e)) -> fst <$> abstFunDef tbl env cs pv (key,xs,e) (Just ty)
    (ML.SPair, (v1,v2)) -> 
        let PPair _ ty1 ty2 = ty in
        (\x y -> B.T [x,y]) <$> abstValue tbl env cs pv v1 ty1 <*> abstValue tbl env cs pv v2 ty2
    _ -> case ML.atomOfValue v of
        Just av -> abstAValue env cs pv av ty
        Nothing -> error "abstValue"

{-
abstValue _ env cs pv (ML.Atomic av) ty = abstAValue env cs pv av ty
abstValue tbl env cs pv (ML.Fun fdef) ty = fst <$> abstFunDef tbl env cs pv fdef (Just ty)
abstValue tbl env cs pv (ML.Pair v1 v2) ty = 
    let PPair _ ty1 ty2 = ty in
    (\x y -> B.T [x,y]) <$> abstValue tbl env cs pv v1 ty1 <*> abstValue tbl env cs pv v2 ty2
-}
abstTerm :: forall m. (MonadId m, MonadIO m) => TypeMap -> Env -> Constraints -> PVar -> ML.Exp -> TermType -> m B.Term
abstTerm tbl env cs pv (ML.Exp l arg sty key) (r,ty,qs) = 
    let valueCase :: ML.Value -> m B.Term
        valueCase v = do
            let subst = M.singleton r v
            let ty' = substVPType subst ty
            e1 <- abstValue tbl env cs pv v ty'
            e2 <- abstFormulae cs pv (map (substVFormula subst) qs)
            return $ B.T [e1,e2]
    in case (l,arg) of
        (ML.SLiteral, _) -> valueCase (ML.Value l arg sty key)
        (ML.SVar, _) -> valueCase (ML.Value l arg sty key)
        (ML.SBinary, _) -> valueCase (ML.Value l arg sty key)
        (ML.SUnary, _) -> valueCase (ML.Value l arg sty key)
        (ML.SPair, _) -> valueCase (ML.Value l arg sty key)
        (ML.SLambda, _) -> valueCase (ML.Value l arg sty key)
        (ML.SLet, (x,(ML.LExp l1 arg1 sty1 key1),e2)) -> 
            let atomCase :: ML.Atom -> m B.Term
                atomCase av = do
                    let ty_x = typeOfAtom env av
                    ex <- abstValue tbl env cs pv (ML.castWith key1 av) ty_x
                    e' <- abstTerm tbl (M.insert x ty_x env) (addEq x av cs) pv e2 (r,ty,qs)
                    return $ B.f_let (toSymbol x ty_x) ex e'
                exprCase :: ML.Exp -> m B.Term
                exprCase e1 = do
                    let Right (y,ty_y,ps) = tbl M.! key1
                    let sx = show $ ML.name x
                    x_pair <- B.freshSym (sx ++ "_pair") (toSortTerm (y,ty_y,ps))
                    B.f_let x_pair <$> abstTerm tbl env cs pv e1 (y,ty_y,ps) <*> do
                        let x_body  = B.f_proj 0 2 (B.V x_pair)
                            x_preds = B.f_proj 1 2 (B.V x_pair)
                            n = length ps
                            pv' = [ (B.f_proj i n x_preds, substFormula (M.singleton y x) fml) | (i,fml) <- zip [0..] ps ] ++ pv
                            env' = M.insert x (substPType (M.singleton y x) ty_y) env
                        B.f_let (toSymbol x ty_y) x_body <$>                                        -- let x = abst(cs,pv,t1,tau1)
                            (B.f_assume <$> (abstFormula cs pv' (ML.mkLiteral $ ML.CBool True)) <*> -- assume phi;
                                abstTerm tbl env' cs pv' e2 (r,ty,qs))                              -- abst(cs,pv',t,tau)
            in case l1 of
                ML.SLiteral -> atomCase (ML.Atom l1 arg1 sty1)
                ML.SVar     -> atomCase (ML.Atom l1 arg1 sty1)
                ML.SUnary   -> atomCase (ML.Atom l1 arg1 sty1)
                ML.SBinary   -> atomCase (ML.Atom l1 arg1 sty1)
                ML.SApp -> do
                    let (f,vs) = arg1
                    let PFun _ (ys,ty_ys,ps) (r',ty_r',qs') = env M.! f
                    let subst = M.fromList $ zip ys vs
                    let ty_ys' = map (substVPType subst) ty_ys
                    let sx = show $ ML.name x 
                    arg_body  <- B.T <$> zipWithM (abstValue tbl env cs pv) vs ty_ys'
                    arg_preds <- abstFormulae cs pv (map (substVFormula subst) ps)
                    let f' = toSymbol f (env M.! f)
                    x' <- B.freshSym (sx ++ "_pair") (toSortTerm (r',ty_r',qs'))
                    let x_body  = B.f_proj 0 2 (B.V x')
                        x_preds = B.f_proj 1 2 (B.V x')
                        n = length qs'
                        subst1 = M.insert r' (ML.cast (ML.mkVar x)) subst
                        pv' = [ (B.f_proj i n x_preds, 
                                 substVFormula subst1 fml) | (i,fml) <- zip [0..] qs' ] ++ pv
                        ty_r'' = substVPType subst1 ty_r'
                    B.f_let x' (B.f_app (B.V f') (B.T [arg_body, arg_preds])) .           -- let x = f <body, preds> in
                      B.f_let (toSymbol x ty_r') x_body <$>                               -- let v = x.fst
                        (B.f_assume <$> (abstFormula cs pv' (ML.mkLiteral (ML.CBool True))) <*>          -- assume phi; // avoid incosinsitent states
                            abstTerm tbl (M.insert x ty_r'' env) cs pv' e2 (r,ty,qs))     -- abst(cs,pv',t,tau)
                ML.SRand -> 
                    B.f_let (toSymbol x PInt) (B.T []) <$>
                        abstTerm tbl (M.insert x PInt env) cs pv e2 (r,ty,qs)
                ML.SLambda -> exprCase (ML.Exp l1 arg1 sty1 key1)
                ML.SPair -> exprCase (ML.Exp l1 arg1 sty1 key1)
                ML.SBranch -> exprCase (ML.Exp l1 arg1 sty1 key1)
                ML.SFail -> error "abstTerm: Fail is not supported"
                ML.SOmega -> error "abstTerm: Omega is not supported"
        (ML.SAssume,(v,e)) -> do
            e_v <- abstValue tbl env cs pv (ML.cast v) PBool
            B.f_assume e_v <$> abstTerm tbl env (v : cs) pv e (r,ty,qs)
        (ML.SFail, _) -> do
            fail <- B.freshSym "fail" (toSortTerm (r,ty,qs))
            return $ B.Fail fail
        (ML.SOmega, _) -> do
            fail <- B.freshSym "omega" (toSortTerm (r,ty,qs))
            return $ B.Omega fail
        (ML.SBranch, (t1,t2)) -> do
            B.f_branch_label <$> abstTerm tbl env cs pv t1 (r,ty,qs)
                             <*> abstTerm tbl env cs pv t2 (r,ty,qs)
                             {-
        _ -> case ML.valueOfLExp e of 
            Just v -> do
                let subst = M.singleton r v
                let ty' = substVPType subst ty
                e1 <- abstValue tbl env cs pv v ty'
                e2 <- abstFormulae cs pv (map (substVFormula subst) qs)
                return $ B.T [e1,e2]
            Nothing -> error "abstTerm: impossible"
            -}

{-
        (ML.Value v -> do

-}

addEq :: ML.TId -> ML.Atom -> Constraints -> Constraints
addEq y v cs = (ML.mkBin ML.SEq (ML.mkVar y) v) :cs

abstFunDef :: (MonadId m, MonadIO m) => TypeMap -> Env -> Constraints -> PVar -> (UniqueKey,[ML.TId],ML.Exp) -> Maybe PType -> m (B.Term, PType)
abstFunDef tbl env cs pv (ident,xs,t1) mpty = do
    let ty_f@(PFun _ (ys,ty_ys,ps) rty) = 
            case mpty of
                Just pty -> pty
                Nothing -> let Left pty = tbl M.! ident in pty
    x_pair <- B.freshSym "arg" (toSortArg (ys,ty_ys,ps))
    e <- B.Lam x_pair <$> do
        let x_body  = B.f_proj 0 2 (B.V x_pair)
            x_preds = B.f_proj 1 2 (B.V x_pair)
            n = length ps
            subst = M.fromList $ zip ys xs
            pv' = [ (B.f_proj i n x_preds, substFormula subst fml) | (i,fml) <- zip [0..] ps ] ++ pv
            rty' = substTermType subst rty
            ty_ys' = map (substPType subst) ty_ys
            arity = length xs
        let env' = foldr (uncurry M.insert) env (zip xs ty_ys')
        e' <- B.f_assume <$> (abstFormula cs pv' (ML.mkLiteral $ ML.CBool True)) 
                         <*> (abstTerm tbl env' cs pv' t1 rty')
        return $ foldr (\(i,x,ty_y) -> 
            B.f_let (toSymbol x ty_y) (B.f_proj i arity x_body)) e' (zip3 [0..] xs ty_ys')
    return (e,ty_f)

printTypeMap :: TypeMap -> IO ()
printTypeMap tbl = forM_ (M.assocs tbl) $ \(i,pty') -> 
    case pty' of
        Left pty -> putStrLn $ render $ pPrint i <+> colon <+> pprintPType 0 pty
        Right termType -> putStrLn $ render $ pPrint i <+> colon <+> pprintTermType termType

abstProg :: TypeMap -> ML.Program -> FreshIO B.Program
abstProg tbl (ML.Program fs t0) = do
    liftIO $ putStrLn "current abstraction type environment {"
    liftIO $ printTypeMap tbl 
    liftIO $ putStrLn "}"

    let env = M.fromList [ (f,ty)  | (f,key,_,_) <- fs, let Left ty = tbl M.! key ]
    ds <- forM fs $ \(f,key,xs,e) -> do
        let f' = toSymbol f (env M.! f)
        (e_f,_) <- abstFunDef tbl env [] [] (key,xs,e) (Just $ env M.! f)
        return (f',e_f)
    e0 <- do
        r <- ML.TId ML.TInt <$> identify "main"
        abstTerm tbl env [] [] t0 (r,PInt,[])
    return $ B.Program ds e0

