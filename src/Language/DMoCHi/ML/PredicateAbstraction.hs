module Language.DMoCHi.ML.PredicateAbstraction where
import Control.Monad
import qualified Data.Map as M
import qualified Data.IntMap as IM

import qualified Language.DMoCHi.ML.Syntax.Typed as ML
import qualified Language.DMoCHi.Boolean.Syntax.Typed as B
import Language.DMoCHi.Common.Id

data PType = PInt | PBool
           | PFun ML.Type (ML.Id,PType,[Formula]) (ML.Id,PType,[Formula])
           | PPair ML.Type PType PType

type Env = M.Map ML.Id PType
type Constraints = [Formula]
type PVar = [(B.Term, Formula)]
type Formula = ML.Value

type TermType = (ML.Id, PType, [Formula])

type TypeMap = IM.IntMap (Either PType TermType)

-- getSort (abstFormulae cs pv fmls) == TBool^(length fmls)
abstFormulae :: Monad m => Constraints -> PVar -> [Formula] -> m B.Term
abstFormulae = undefined

-- getSort (abstFormulae cs pv fmls) == TBool
abstFormula :: Monad m => Constraints -> PVar -> Formula -> m B.Term
abstFormula cs pv fml = undefined

fromType :: ML.Type -> PType
fromType ML.TInt = PInt
fromType ML.TBool = PBool
fromType (ML.TPair t1 t2) = PPair (ML.TPair t1 t2) (fromType t1) (fromType t2)
fromType (ML.TFun t1 t2) = PFun (ML.TFun t1 t2) 
                                (ML.Id t1 "_", fromType t1, [])
                                (ML.Id t2 "_", fromType t2, [])

-- Function:
--      e' = cast cs pv e curTy newTy
-- assumptions:
--      getSort e == toSort curTy
--      toSimple curTy == toSimple newTy
-- assertion:
--      getSort e' == toSort newTy
cast :: (Monad m, MonadId m) => Constraints -> PVar -> B.Term -> PType -> PType -> m B.Term
cast cs pv e curTy newTy = case (curTy,newTy) of
    (PInt,  PInt) -> return e
    (PBool, PBool) -> return e
    (PPair _ ty1 ty2, PPair _ ty1' ty2') -> do
        e1 <- cast cs pv (B.f_proj 0 2 e) ty1 ty1'
        e2 <- cast cs pv (B.f_proj 1 2 e) ty2 ty2'
        return $ B.T [e1,e2]
    (PFun _ (x,ty_x,ps) (r,ty_r,qs), 
     PFun _ (y,ty_y,ps') (r',ty_r',qs')) -> do
        y_pair <- B.freshSym (ML.name y) (toSort' (y,ty_y,ps'))
        B.Lam y_pair <$> do
            let y_body = B.f_proj 0 2 (B.V y_pair)
                y_preds = B.f_proj 1 2 (B.V y_pair)
                n = length ps'
                pv' = [ (B.f_proj i n y_preds, fml) | (i,fml) <- zip [0..] ps'] ++ pv
            x_body  <- cast cs pv' y_body ty_y ty_x
            x_preds <- abstFormulae cs pv' (map (substFormula x y) ps)
            r_pair <- B.freshSym (ML.name r) (toSort' (r,ty_r,qs))
            B.f_let r_pair (B.f_app e (B.T [x_body,x_preds])) <$> do
                let r_body = B.f_proj 0 2 $ B.V r_pair
                    r_preds = B.f_proj 1 2 $ B.V r_pair
                    m = length qs
                    pv'' = [ (B.f_proj i m r_preds, fml) | (i,fml) <-
                             zip [0..] qs] ++ pv'
                r'_body <- cast cs pv'' r_body (substPType x y ty_r) ty_r'
                r'_preds <- abstFormulae cs pv'' (map (substFormula r r' . substFormula x y) qs)
                return $ B.T [r'_body,r'_preds]

toSort :: PType -> B.Sort
toSort PInt = B.Tuple []
toSort PBool = B.Bool
toSort (PPair _ t1 t2) = B.Tuple [toSort t1, toSort t2]
toSort (PFun _ tx tr) = toSort' tx B.:-> toSort' tr

toSort' (_, ty, ps) = B.Tuple [toSort ty, B.Tuple [ B.Bool | _ <- ps ]]

substPType :: ML.Id -> ML.Id -> PType -> PType
substPType a b = go where
    f = substFormula a b
    go PInt = PInt
    go PBool = PBool
    go (PPair t t1 t2) = PPair t (go t1) (go t2)
    go (PFun ty (x,ty_x,ps) (r,ty_r,qs)) = 
        PFun ty (x,go ty_x,map f ps) (r,go ty_r, map f qs)

substFormula :: ML.Id -> ML.Id -> Formula -> Formula
substFormula a b = substVFormula a (ML.Var b)

substVFormula :: ML.Id -> ML.Value -> Formula -> Formula
substVFormula a b = go where
    go e = case e of
        ML.Var x | x == a -> b
        ML.Pair v1 v2 -> ML.Pair (go v1) (go v2)
        ML.Op op -> ML.Op $ case op of
            ML.OpAdd v1 v2 -> ML.OpAdd (go v1) (go v2)
            ML.OpSub v1 v2 -> ML.OpSub (go v1) (go v2)
            ML.OpEq  v1 v2 -> ML.OpEq  (go v1) (go v2)
            ML.OpLt  v1 v2 -> ML.OpLt  (go v1) (go v2)
            ML.OpLte v1 v2 -> ML.OpLte (go v1) (go v2)
            ML.OpAnd v1 v2 -> ML.OpAnd (go v1) (go v2)
            ML.OpOr  v1 v2 -> ML.OpOr  (go v1) (go v2)
            ML.OpFst ty v  -> ML.OpFst ty (go v)
            ML.OpSnd ty v  -> ML.OpSnd ty (go v)
            ML.OpNot v     -> ML.OpNot (go v)

toSymbol :: ML.Id -> PType -> B.Symbol
toSymbol x ty = B.Symbol (toSort ty) (ML.name x)

abstValue :: MonadId m => Env -> Constraints -> PVar -> ML.Value -> PType -> m B.Term
abstValue env cs pv = go 
    where 
    go v ty = case v of
        ML.Var x -> cast cs pv (B.V (toSymbol x (env M.! x))) (env M.! x) ty
        ML.CInt i -> return $ B.T []
        ML.CBool b -> return $ B.C b
        ML.Pair v1 v2 -> 
            let PPair _ ty1 ty2 = ty in
            (\x y -> B.T [x,y]) <$> go v1 ty1 <*> go v2 ty2
        ML.Op op -> case op of
            ML.OpAdd v1 v2 -> return $ B.T []
            ML.OpSub v1 v2 -> return $ B.T []
            ML.OpEq  v1 v2 -> abstFormula cs pv v
            ML.OpLt  v1 v2 -> abstFormula cs pv v
            ML.OpLte v1 v2 -> abstFormula cs pv v
            ML.OpAnd v1 v2 -> B.And <$> go v1 PBool <*> go v2 PBool
            ML.OpOr  v1 v2 -> B.Or  <$> go v1 PBool <*> go v2 PBool
            ML.OpFst _ v   -> 
                let PPair _ _ ty2 = typeOfValue env v in
                B.f_proj 0 2 <$> go v (PPair (ML.getType v) ty ty2)
            ML.OpSnd _ v   -> 
                let PPair _ ty1 _ = typeOfValue env v in
                B.f_proj 1 2 <$> go v (PPair (ML.getType v) ty1 ty)
            ML.OpNot v -> B.Not <$> go v PBool

typeOfValue :: Env -> ML.Value -> PType
typeOfValue env = go where
    go v = case v of
        ML.Var x -> env M.! x
        ML.CInt i -> PInt
        ML.CBool b -> PBool
        ML.Pair v1 v2 -> PPair (ML.getType v) (go v1) (go v2)
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

abstTerm :: MonadId m => TypeMap -> Env -> Constraints -> PVar -> ML.Exp -> TermType -> m B.Term
abstTerm tbl env cs pv t (r,ty,qs) = doit where
    doit = case t of
        ML.Value v -> do
            e1 <- abstValue env cs pv v ty
            e2 <- abstFormulae cs pv (map (substVFormula r v) qs)
            return $ B.T [e1,e2]

        ML.Let _ x (ML.LValue v) t' -> do
            let ty_x = typeOfValue env v
            ex <- abstValue env cs pv v ty_x
            e' <- abstTerm tbl (M.insert x ty_x env) (addEq x v cs) pv t' (r,ty,qs)
            return $ B.f_let (toSymbol x ty_x) ex e'

        ML.Let _ x (ML.LApp _ _ f v) t' -> do
            let ty_v = typeOfValue env v 
            let PFun _ (y,ty_y,ps) (r',ty_r',qs') = env M.! f
            let cs' = addEq y v cs 
            arg_body  <- abstValue env cs pv v ty_y
            arg_preds <- abstFormulae cs' pv ps
            let f' = toSymbol f (env M.! f)
            x' <- B.freshSym (ML.name x ++ "_pair") (toSort' (r',ty_r',qs'))
            let x_body  = B.f_proj 0 2 (B.V x')
                x_preds = B.f_proj 1 2 (B.V x')
                n = length qs'
                pv' = [ (B.f_proj i n x_preds, substVFormula r v fml) | (i,fml) <- zip [0..] qs' ] ++ pv
            B.f_let x' (B.f_app (B.V f') (B.T [arg_body, arg_preds])) .  
              B.f_let (toSymbol x ty_r') x_body <$>
                abstTerm tbl (M.insert x ty_r' env) cs' pv' t' (r,ty,qs)

        ML.Let _ f (ML.LFun func) t' -> do
            (e_f,ty_f) <- abstFunDef tbl env cs pv func
            B.f_let (toSymbol f ty_f) e_f <$> 
                abstTerm tbl (M.insert f ty_f env) cs pv t' (r,ty,qs)

        ML.Let _ x (ML.LExp ident t_x) t' -> do
            let Right (y,ty_y,ps) = tbl IM.! ident
            x_pair <- B.freshSym (ML.name x ++ "_pair") (toSort' (y,ty_y,ps))
            B.f_let x_pair <$> abstTerm tbl env cs pv t_x (y,ty_y,ps) <*> do
                let x_body  = B.f_proj 0 2 (B.V x_pair)
                    x_preds = B.f_proj 1 2 (B.V x_pair)
                    n = length ps
                    pv' = [ (B.f_proj i n x_preds, substFormula y x fml) | (i,fml) <- zip [0..] ps ] ++ pv
                B.f_let (toSymbol x ty_y) x_body <$>
                    abstTerm tbl (M.insert x ty_y env) cs pv' t' (r,ty,qs)

        ML.Let _ x ML.LRand t' -> 
            B.f_let (toSymbol x PInt) (B.T []) <$>
                abstTerm tbl (M.insert x PInt env) cs pv t' (r,ty,qs)

        ML.Assume _ v t' -> do
            e_v <- abstValue env cs pv v PBool
            B.f_assume e_v <$> abstTerm tbl env (v : cs) pv t' (r,ty,qs)

        ML.Fail _ -> do
            fail <- B.freshSym "fail" (toSort' (r,ty,qs))
            return $ B.Fail fail

        ML.Branch _ _ t1 t2 -> do
            B.f_branch <$> abstTerm tbl env cs pv t1 (r,ty,qs)
                       <*> abstTerm tbl env cs pv t2 (r,ty,qs)

addEq :: ML.Id -> ML.Value -> Constraints -> Constraints
addEq y v cs = ML.Op (ML.OpEq (ML.Var y) v):cs

abstFunDef :: MonadId m => TypeMap -> Env -> Constraints -> PVar -> ML.FunDef -> m (B.Term, PType)
abstFunDef tbl env cs pv func = do
    let ML.FunDef ident x t1 = func
    let Left ty_f@(PFun _ (y,ty_y,ps) rty) = tbl IM.! ident
    x_pair <- B.freshSym (ML.name x ++ "_pair") (toSort' (y,ty_y,ps))
    e <- B.Lam x_pair <$> do
        let x_body  = B.f_proj 0 2 (B.V x_pair)
            x_preds = B.f_proj 1 2 (B.V x_pair)
            n = length ps
            pv' = [ (B.f_proj i n x_preds, fml) | (i,fml) <- zip [0..] ps ] ++ pv
        B.f_let (toSymbol x ty_y) x_body <$>
            abstTerm tbl (M.insert x ty_y env) (addEq x (ML.Var y) cs) pv' t1 rty
    return (e,ty_f)

abstProg :: MonadId m => TypeMap -> ML.Program -> m B.Program
abstProg tbl (ML.Program fs t0) = do
    let env = M.fromList [ (f,ty)  | (f,func) <- fs, let Left ty = tbl IM.! ML.ident func ]
    ds <- forM fs $ \(f,func) -> do
        let f' = toSymbol f (env M.! f)
        (e_f,_) <- abstFunDef tbl env [] [] func
        return (f',e_f)
    e0 <- do
        r <- ML.Id ML.TInt <$> freshId "main"
        abstTerm tbl env [] [] t0 (r,PInt,[])
    return $ B.Program ds e0
