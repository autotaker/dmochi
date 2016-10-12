{-# LANGUAGE FlexibleContexts #-}
module Language.DMoCHi.ML.PredicateAbstraction where
import Control.Monad
import qualified Data.Map as M
import qualified Data.IntMap as IM
import qualified Data.DList as DL

import qualified Language.DMoCHi.ML.Syntax.PNormal as ML
import qualified Language.DMoCHi.ML.PrettyPrint.PNormal as ML
import qualified Language.DMoCHi.Boolean.Syntax.Typed as B
import qualified Language.DMoCHi.Boolean.PrettyPrint.Typed as B
import qualified Language.DMoCHi.ML.SMT as SMT
import Language.DMoCHi.Common.Util
import Language.DMoCHi.Common.Id
import Control.Monad.Writer
import Text.PrettyPrint
import Debug.Trace

data PType = PInt | PBool
           | PFun ML.Type ArgType TermType
           | PPair ML.Type PType PType


instance Eq PType where
    PInt == PInt = True
    PBool == PBool = True
    (PFun ty_1 (xs_1,xsty_1,ps_1) (r_1,rty_1,qs_1)) == (PFun ty_2 (xs_2,xsty_2,ps_2) (r_2,rty_2,qs_2)) =
        ty_1 == ty_2 && 
        ps_1 == map (substFormula subst1) ps_2 &&
        qs_1 == map (substFormula subst2) qs_2 &&
        xsty_1 == xsty_2 &&
        rty_1 == substPType subst1 rty_2
        where
        subst1 = M.fromList $ zip xs_2 xs_1
        subst2 = M.insert r_2 r_1 subst1
    PPair ty pty_fst pty_snd == PPair ty' pty_fst' pty_snd' =
        ty == ty' && pty_fst == pty_fst' && pty_snd == pty_snd'
    _ == _ = False


type Env = M.Map ML.Id PType
type Constraints = [Formula]
type PVar = [(B.Term, Formula)]
type Formula = ML.AValue

type TermType = (ML.Id, PType, [Formula])
type ArgType = ([ML.Id],[PType],[Formula])

type TypeMap = IM.IntMap (Either PType TermType)
type ScopeMap = IM.IntMap [ML.Id]

pprintTermType :: TermType -> Doc
pprintTermType (x,pty_x,fml) = braces $ 
    text (ML.name x) <+> colon <+> (pprintPType 0 pty_x) <+>
    text "|" <+> (hsep $ punctuate comma $ map (ML.pprintA 0) fml)

pprintPTypeArg :: ArgType -> Doc
pprintPTypeArg (xs,pty_xs,fml) =
    braces $ 
        hsep (punctuate comma $ zipWith (\x pty_x -> text (ML.name x) <+> colon <+> (pprintPType 0 pty_x)) xs pty_xs) <+>
        text "|" <+> (hsep $ punctuate comma $ map (ML.pprintA 0) fml)


pprintPType :: Int -> PType -> Doc
pprintPType _ PInt = text "int"
pprintPType _ PBool = text "bool"
pprintPType assoc (PPair _ pty1 pty2) =
    let d1 = pprintPType 1 pty1
        d2 = pprintPType 1 pty2
        d = d1 <+> text "*" <+> d2
    in if assoc == 0 then d else parens d
pprintPType assoc (PFun _ x_tup r_tup) =
    let d = pprintPTypeArg x_tup <+> text "->" <+> pprintTermType r_tup in
    if assoc == 0 then d else parens d

-- getSort (abstFormulae cs pv fmls) == TBool^(length fmls)
abstFormulae :: (MonadIO m, MonadId m) => Constraints -> PVar -> [Formula] -> m B.Term
abstFormulae cs pvs fml = do
    let ps = map snd pvs ++ fml
    bdd <- liftIO $ SMT.abst cs ps
    let sort = B.Tuple [ B.Bool | _ <- fml ]
    let gen qs (SMT.Leaf _ True) = return $ B.T $ reverse qs
        gen qs (SMT.Leaf _ False) = do
            omega <- B.Symbol sort <$> freshId "Omega"
            return $ B.Omega omega
        gen qs (SMT.Node _ v hi lo) 
            | hi == lo = do
                let q = (B.f_branch (B.C True) (B.C False))
                gen (q:qs) hi
            | otherwise = do
                term_hi <- gen (B.C True : qs) hi
                term_lo <- gen (B.C False : qs) lo
                return $ B.f_branch term_hi term_lo
        go [] bdd = gen [] bdd
        go ((term_p, _):_) (SMT.Leaf _ False) = do
            omega <- B.Symbol sort <$> freshId "Omega1"
            return $ B.Omega omega
        go ((term_p, _):_) (SMT.Leaf _ True) = error "abstFormulae: unexpected satisfiable leaf"
        go ((term_p, _):pvs') (SMT.Node _ _ hi lo) 
            | hi == lo = go pvs' hi
            | otherwise = do
                term_hi <- go pvs' hi
                term_lo <- go pvs' lo
                return $ B.f_branch (B.f_assume term_p         term_hi)
                                    (B.f_assume (B.Not term_p) term_lo)

    term <- go pvs bdd
    liftIO $ putStrLn $ render (
        let doc_cs = brackets $ hsep $ punctuate comma (map (ML.pprintA 0) cs)
            doc_pvar = brackets $ hsep $ punctuate comma (map (ML.pprintA 0 . snd) pvs)
            doc_fml = brackets $ hsep $ punctuate comma (map (ML.pprintA 0) fml)
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

cast, cast' :: (MonadIO m, MonadId m) => Constraints -> PVar -> B.Term -> PType -> PType -> m B.Term
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
cast cs pv e curTy newTy = do
    r <- cast' cs pv e curTy newTy
    liftIO $ putStrLn $ render $
        let doc_cs = brackets $ hsep $ punctuate comma (map (ML.pprintA 0) cs)
            doc_pvar = brackets $ hsep $ punctuate comma (map (ML.pprintA 0 . snd) pv)
            doc_e = B.pprintTerm 0 e
            doc_curTy = pprintPType 0 curTy
            doc_newTy = pprintPType 0 newTy
            doc_r = B.pprintTerm 0 r
        in braces (
           text "constraints:" <+> doc_cs $+$ 
           text "predicates:" <+> doc_pvar $+$ 
           text "prev term:" <+> doc_e $+$ 
           text "prev type:" <+> doc_curTy $+$
           text "new  type:" <+> doc_newTy $+$
           text "abst result:" <+> doc_r)
    return r



toSort :: PType -> B.Sort
toSort PInt = B.Tuple []
toSort PBool = B.Bool
toSort (PPair _ t1 t2) = B.Tuple [toSort t1, toSort t2]
toSort (PFun _ tx tr) = toSortArg tx B.:-> toSortTerm tr

toSortTerm :: TermType -> B.Sort
toSortTerm (_, ty, ps) = B.Tuple [toSort ty, B.Tuple [ B.Bool | _ <- ps ]]
toSortArg :: ArgType -> B.Sort
toSortArg (_, tys, ps) = B.Tuple [B.Tuple $ map toSort tys, B.Tuple [B.Bool | _ <- ps]]


substTermType :: M.Map ML.Id ML.Id -> TermType -> TermType
substTermType subst (x,pty,ps) = (x, substPType subst pty, map (substFormula subst) ps)

substPType :: M.Map ML.Id ML.Id -> PType -> PType
substPType subst = substVPType (fmap (ML.Atomic . ML.Var) subst)

substVPType :: M.Map ML.Id ML.Value -> PType -> PType
substVPType subst = go where
    f = substVFormula subst
    go PInt = PInt
    go PBool = PBool
    go (PPair t t1 t2) = PPair t (go t1) (go t2)
    go (PFun ty (xs,ty_xs,ps) (r,ty_r,qs)) = 
        PFun ty (xs,map go ty_xs,map f ps) (r,go ty_r, map f qs)

substFormula :: M.Map ML.Id ML.Id -> Formula -> Formula
substFormula subst = substVFormula (fmap (ML.Atomic . ML.Var) subst)

substVFormula :: M.Map ML.Id ML.Value -> Formula -> Formula
substVFormula subst = atomic . go where
    atomic (ML.Atomic v) = v
    atomic _ = error "substVFormula: type error"
    go e = case e of
        ML.Var x ->
            case M.lookup x subst of
                Just b -> b
                Nothing -> ML.Atomic e
        ML.CInt _ -> ML.Atomic e
        ML.CBool _ -> ML.Atomic e
        -- ML.Pair v1 v2 -> ML.Pair (go v1) (go v2)
        ML.Op op ->  case op of
            ML.OpAdd v1 v2 -> ML.Atomic $ ML.Op $ (ML.OpAdd `on` atomic) (go v1) (go v2)
            ML.OpSub v1 v2 -> ML.Atomic $ ML.Op $ (ML.OpSub `on` atomic) (go v1) (go v2)
            ML.OpEq  v1 v2 -> ML.Atomic $ ML.Op $ (ML.OpEq `on` atomic) (go v1) (go v2)
            ML.OpLt  v1 v2 -> ML.Atomic $ ML.Op $ (ML.OpLt `on` atomic) (go v1) (go v2)
            ML.OpLte v1 v2 -> ML.Atomic $ ML.Op $ (ML.OpLte `on` atomic) (go v1) (go v2)
            ML.OpAnd v1 v2 -> ML.Atomic $ ML.Op $ (ML.OpAnd `on` atomic) (go v1) (go v2)
            ML.OpOr  v1 v2 -> ML.Atomic $ ML.Op $ (ML.OpOr  `on` atomic) (go v1) (go v2)
            ML.OpFst ty v  -> case go v of 
                ML.Atomic av -> ML.Atomic $ ML.Op $ ML.OpFst ty av
                ML.Pair v1 _ -> v1
            ML.OpSnd ty v  -> case go v of
                ML.Atomic av -> ML.Atomic $ ML.Op $ ML.OpSnd ty av
                ML.Pair _ v2 -> v2
            ML.OpNot v     -> ML.Atomic $ ML.Op $ (ML.OpNot . atomic) (go v)

toSymbol :: ML.Id -> PType -> B.Symbol
toSymbol x ty = B.Symbol (toSort ty) (ML.name x)

abstAValue :: (MonadIO m, MonadId m) => Env -> Constraints -> PVar -> ML.AValue -> PType -> m B.Term
abstAValue env cs pv = go 
    where 
    go v ty = case v of
        ML.Var x -> cast cs pv (B.V (toSymbol x (env M.! x))) (env M.! x) ty
        ML.CInt i -> return $ B.T []
        ML.CBool b -> return $ B.C b
--        ML.Pair v1 v2 -> 
--            let PPair _ ty1 ty2 = ty in
--            (\x y -> B.T [x,y]) <$> go v1 ty1 <*> go v2 ty2
        ML.Op op -> case op of
            ML.OpAdd v1 v2 -> return $ B.T []
            ML.OpSub v1 v2 -> return $ B.T []
            ML.OpEq  v1 v2 -> abstFormula cs pv v
            ML.OpLt  v1 v2 -> abstFormula cs pv v
            ML.OpLte v1 v2 -> abstFormula cs pv v
            ML.OpAnd v1 v2 -> abstFormula cs pv v
            ML.OpOr  v1 v2 -> abstFormula cs pv v
            ML.OpFst _ v   -> 
                let PPair _ _ ty2 = typeOfAValue env v in
                B.f_proj 0 2 <$> go v (PPair (ML.getType v) ty ty2)
            ML.OpSnd _ v   -> 
                let PPair _ ty1 _ = typeOfAValue env v in
                B.f_proj 1 2 <$> go v (PPair (ML.getType v) ty1 ty)
            ML.OpNot v -> B.Not <$> go v PBool
abstValue :: (MonadIO m, MonadId m) => TypeMap -> Env -> Constraints -> PVar -> ML.Value -> PType -> m B.Term
abstValue _ env cs pv (ML.Atomic av) ty = abstAValue env cs pv av ty
abstValue tbl env cs pv (ML.Fun fdef) ty = fst <$> abstFunDef tbl env cs pv fdef (Just ty)
abstValue tbl env cs pv (ML.Pair v1 v2) ty = 
    let PPair _ ty1 ty2 = ty in
    (\x y -> B.T [x,y]) <$> abstValue tbl env cs pv v1 ty1 <*> abstValue tbl env cs pv v2 ty2


typeOfAValue :: Env -> ML.AValue -> PType
typeOfAValue env = go where
    go v = case v of
        ML.Var x -> env M.! x
        ML.CInt i -> PInt
        ML.CBool b -> PBool
--        ML.Pair v1 v2 -> PPair (ML.getType v) (go v1) (go v2)
        ML.Op op -> case op of
            ML.OpAdd v1 v2 -> PInt
            ML.OpSub v1 v2 -> PInt
            ML.OpEq  v1 v2 -> PBool
            ML.OpLt  v1 v2 -> PBool
            ML.OpLte v1 v2 -> PBool
            ML.OpAnd v1 v2 -> PBool
            ML.OpOr  v1 v2 -> PBool
            ML.OpFst _ v   ->
                let PPair _ ty1 _ = go v in ty1
            ML.OpSnd _ v   -> 
                let PPair _ _ ty2 = go v in ty2
            ML.OpNot v -> PBool

abstTerm :: (MonadId m, MonadIO m) => TypeMap -> Env -> Constraints -> PVar -> ML.Exp -> TermType -> m B.Term
abstTerm tbl env cs pv t (r,ty,qs) = doit where
    doit = case t of
        ML.Value v -> do
            let subst = M.singleton r v
            let ty' = substVPType subst ty
            e1 <- abstValue tbl env cs pv v ty'
            e2 <- abstFormulae cs pv (map (substVFormula subst) qs)
            return $ B.T [e1,e2]

{-
        ML.Fun fdef -> do
            (e1,_) <- abstFunDef tbl env cs pv fdef (Just ty)
            e2 <- abstFormulae cs pv qs
            return $ B.T [e1,e2]
-}

        ML.Let _ x (ML.LValue v) t' -> do
            let ty_x = typeOfAValue env v
            ex <- abstValue tbl env cs pv (ML.Atomic v) ty_x
            e' <- abstTerm tbl (M.insert x ty_x env) (addEq x v cs) pv t' (r,ty,qs)
            return $ B.f_let (toSymbol x ty_x) ex e'

        ML.Let _ x (ML.LApp _ _ f vs) t' -> do
            let PFun _ (ys,ty_ys,ps) (r',ty_r',qs') = env M.! f
            let subst = M.fromList $ zip ys vs
            let ty_ys' = map (substVPType subst) ty_ys
            arg_body  <- B.T <$> zipWithM (abstValue tbl env cs pv) vs ty_ys'
            arg_preds <- abstFormulae cs pv (map (substVFormula subst) ps)
            let f' = toSymbol f (env M.! f)
            x' <- B.freshSym (ML.name x ++ "_pair") (toSortTerm (r',ty_r',qs'))
            let x_body  = B.f_proj 0 2 (B.V x')
                x_preds = B.f_proj 1 2 (B.V x')
                n = length qs'
                subst1 = M.insert r' (ML.Atomic (ML.Var x)) subst
                pv' = [ (B.f_proj i n x_preds, 
                         substVFormula subst1 fml) | (i,fml) <- zip [0..] qs' ] ++ pv
                ty_r'' = substVPType subst1 ty_r'
            B.f_let x' (B.f_app (B.V f') (B.T [arg_body, arg_preds])) .  
              B.f_let (toSymbol x ty_r') x_body <$>
                abstTerm tbl (M.insert x ty_r'' env) cs pv' t' (r,ty,qs)

{-
        ML.Let _ f (ML.LFun func) t' -> do
            (e_f,ty_f) <- abstFunDef tbl env cs pv func Nothing
            B.f_let (toSymbol f ty_f) e_f <$> 
                abstTerm tbl (M.insert f ty_f env) cs pv t' (r,ty,qs)
-}

        ML.Let _ x (ML.LExp ident t_x) t' -> do
            let Right (y,ty_y,ps) = tbl IM.! ident
            x_pair <- B.freshSym (ML.name x ++ "_pair") (toSortTerm (y,ty_y,ps))
            B.f_let x_pair <$> abstTerm tbl env cs pv t_x (y,ty_y,ps) <*> do
                let x_body  = B.f_proj 0 2 (B.V x_pair)
                    x_preds = B.f_proj 1 2 (B.V x_pair)
                    n = length ps
                    pv' = [ (B.f_proj i n x_preds, substFormula (M.singleton y x) fml) | (i,fml) <- zip [0..] ps ] ++ pv
                B.f_let (toSymbol x ty_y) x_body <$>
                    abstTerm tbl (M.insert x (substPType (M.singleton y x) ty_y) env) cs pv' t' (r,ty,qs)

        ML.Let _ x ML.LRand t' -> 
            B.f_let (toSymbol x PInt) (B.T []) <$>
                abstTerm tbl (M.insert x PInt env) cs pv t' (r,ty,qs)

        ML.Assume _ v t' -> do
            e_v <- abstValue tbl env cs pv (ML.Atomic v) PBool
            B.f_assume e_v <$> abstTerm tbl env (v : cs) pv t' (r,ty,qs)

        ML.Fail _ -> do
            fail <- B.freshSym "fail" (toSortTerm (r,ty,qs))
            return $ B.Fail fail

        ML.Branch _ _ t1 t2 -> do
            B.f_branch_label <$> abstTerm tbl env cs pv t1 (r,ty,qs)
                             <*> abstTerm tbl env cs pv t2 (r,ty,qs)

addEq :: ML.Id -> ML.AValue -> Constraints -> Constraints
addEq y v cs = ML.Op (ML.OpEq (ML.Var y) v):cs

abstFunDef :: (MonadId m, MonadIO m) => TypeMap -> Env -> Constraints -> PVar -> ML.FunDef -> Maybe PType -> m (B.Term, PType)
abstFunDef tbl env cs pv func mpty = do
    let ML.FunDef ident xs t1 = func
    let ty_f@(PFun _ (ys,ty_ys,ps) rty) = 
            case mpty of
                Just pty -> pty
                Nothing -> let Left pty = tbl IM.! ident in pty
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
        e' <- abstTerm tbl env' cs pv' t1 rty'
        return $ foldr (\(i,x,ty_y) -> 
            B.f_let (toSymbol x ty_y) (B.f_proj i arity x_body)) e' (zip3 [0..] xs ty_ys')
    return (e,ty_f)

printTypeMap :: TypeMap -> IO ()
printTypeMap tbl = forM_ (IM.assocs tbl) $ \(i,pty') -> 
    case pty' of
        Left pty -> putStrLn $ render $ int i <+> colon <+> pprintPType 0 pty
        Right termType -> putStrLn $ render $ int i <+> colon <+> pprintTermType termType

abstProg :: (MonadId m, MonadIO m) => TypeMap -> ML.Program -> m B.Program
abstProg tbl (ML.Program fs t0) = do
    liftIO $ putStrLn "current abstraction type environment {"
    liftIO $ printTypeMap tbl 
    liftIO $ putStrLn "}"
    
    let env = M.fromList [ (f,ty)  | (f,func) <- fs, let Left ty = tbl IM.! ML.ident func ]
    ds <- forM fs $ \(f,func) -> do
        let f' = toSymbol f (env M.! f)
        (e_f,_) <- abstFunDef tbl env [] [] func (Just $ env M.! f)
        return (f',e_f)
    e0 <- do
        r <- ML.Id ML.TInt <$> freshId "main"
        abstTerm tbl env [] [] t0 (r,PInt,[])
    return $ B.Program ds e0

initTypeMap :: MonadId m => ML.Program -> m (TypeMap,ScopeMap)
initTypeMap (ML.Program fs t0) = do
    es <- execWriterT $ do
        let gather fv (ML.Value v) = case v of
                ML.Fun fdef -> gather (ML.args fdef ++ fv) (ML.body fdef)
                ML.Pair v1 v2 -> gather fv (ML.Value v1) >> gather fv (ML.Value v2)
                ML.Atomic _ -> return ()
            gather fv (ML.Let s x lv e) = do
                case lv of
                    ML.LValue _ -> return ()
                    ML.LApp _ _ _ vs -> mapM_ (gather fv . ML.Value) vs
                    ML.LExp i e' -> do
                        gather fv e'
                        ty <- genTermType (ML.getType e')
                        tell (DL.singleton (i, Right ty, fv))
                    ML.LRand -> return ()
                gather (x : fv) e
            gather fv (ML.Assume _ _ e) = gather fv e
            gather _ (ML.Fail _) = return ()
            {-
            gather fv (ML.Fun fdef) = 
                -- DO NOT count tail functions,
                -- because their types are determined elsewhere
                gather (ML.arg fdef : fv) (ML.body fdef)
            -}
            gather fv (ML.Branch _ _ e1 e2) = gather fv e1 >> gather fv e2
            gatherF fv f = do
                gather (ML.args f ++ fv) (ML.body f)
                ty <- genPType (ML.getType f)
                tell (DL.singleton (ML.ident f,Left ty, fv))
        let fv = map fst fs
        forM_ fs $ \(_, f) -> gatherF fv f
        gather fv t0
    let (es1,es2) = unzip [ ((i,v1),(i,v2)) | (i, v1, v2) <- DL.toList es ]
    return (IM.fromList es1, IM.fromList es2)

genTermType :: MonadId m => ML.Type -> m TermType
genTermType s = do
    r <- ML.Id s <$> freshId "r"
    pty <- genPType s
    return (r,pty,[])
genPType :: MonadId m => ML.Type -> m PType
genPType ML.TInt = return PInt
genPType ML.TBool = return PBool
genPType ty@(ML.TPair t1 t2) = PPair ty <$> genPType t1 <*> genPType t2
genPType ty@(ML.TFun ts t2) = do
    xs <- mapM (\t1 -> ML.Id t1 <$> freshId "x") ts
    r <- ML.Id t2 <$> freshId "r"
    ty_xs <- mapM genPType ts
    ty_r <- genPType t2
    return $ PFun ty (xs, ty_xs, []) (r, ty_r, [])
    

