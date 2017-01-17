module Language.DMoCHi.ML.Saturate where

import Control.Monad
import Language.DMoCHi.ML.Syntax.Type
import Language.DMoCHi.ML.Syntax.PNormal
import Z3.Monad
import qualified Language.DMoCHi.ML.SMT as SMT
import Language.DMoCHi.ML.PredicateAbstraction hiding(Env, cast)
import qualified Data.Map as M
import qualified Data.IntMap as IM

data IType = IInt | IBool | IPair IType IType | IFun [([IType], BFormula, ITermType)]
    deriving (Eq,Ord)
data ITermType = IFail | ITerm IType BFormula
    deriving (Eq,Ord)

data BFormula = BAnd BFormula BFormula | BOr BFormula BFormula | BVar Int | BConst Bool
    deriving (Eq,Ord)

type Env = M.Map Id (PType, IType)

getFlow :: Int -> IO [([IType], BFormula)]
getFlow = undefined

cast :: Env -> Formula -> (PType,IType) -> PType -> IO IType
cast = undefined {-
cast env fml (PInt,_) _ = return IInt
cast env fml (PBool,_) _ = return IInt
cast env fml (PPair _ p1 p2,IPair i1 i2) _ = 
    IPair <$> cast env fml p1 i1 <*> cast env fml p2 i2
cast env fml (PFun _ argTy retTy, IFun tys) (PFun _ argTy' retTy') = do
    let (xs, ty_xs, ps) = argTy
        (ys, ty_ys, qs) = argTy'
        subst = M.fromList $ zip ys xs
        ty_xs' = map (substPType subst) ty_ys
        ps' = map (substFormula subst) qs
    forM tys $ \(thetas, phi, iota) -> do
        
        -}
            

calcTypeFunDef :: TypeMap -> Env -> Formula -> FunDef -> PType -> IO IType
calcTypeFunDef tbl env fml (FunDef ident xs e) (PFun _ argTy retTy) = do
    let (ys, ty_ys, ps) = argTy
        subst = M.fromList $ zip ys xs
        ps' = map (substFormula subst) ps
        ty_xs = map (substPType subst) ty_ys
    fs <- getFlow ident
    fmap (IFun . concat) $ forM fs $ \(thetas, phi) -> do
        let cond = fromBFormula ps' phi
            fml' = Op (OpAnd fml cond)
            env' = foldr (uncurry M.insert) env (zip xs (zip ty_xs thetas))
        b <- checkSat fml cond
        if b 
          then map ((,,) thetas phi) <$> calcTypeTerm tbl env' fml' e retTy
          else return []

calcTypeValue :: TypeMap -> Env -> Formula -> Value -> PType -> IO IType
calcTypeValue tbl env fml _v ty = case _v of
    Atomic v -> calcTypeAValue env fml v ty id
    Fun fdef -> calcTypeFunDef tbl env fml fdef ty
    Pair v1 v2 -> do
        let PPair _ ty1 ty2 = ty
        i1 <- calcTypeValue tbl env fml v1 ty1
        i2 <- calcTypeValue tbl env fml v2 ty2
        return (IPair i1 i2)


calcTypeAValue :: Env -> Formula -> AValue -> PType -> ((PType, IType) -> (PType,IType)) -> IO IType
calcTypeAValue env fml _v ty proj = case _v of
    Var x -> let (ty',theta) = proj (env M.! x) in
             cast env fml (ty',theta) ty
    CInt _ -> return IInt
    CBool _ -> return IBool
    Op (OpAdd _ _) -> return IInt
    Op (OpSub _ _) -> return IInt
    Op (OpLt  _ _) -> return IBool
    Op (OpLte _ _) -> return IBool
    Op (OpAnd _ _) -> return IBool
    Op (OpOr _ _) -> return IBool
    Op (OpNot _) -> return IBool
    Op (OpFst _ v) -> 
        calcTypeAValue env fml v ty (\(PPair _ p1 _, IPair i1 _) -> (p1,i1))
    Op (OpSnd _ v) -> 
        calcTypeAValue env fml v ty (\(PPair _ _ p2, IPair _ i2) -> (p2,i2))
    

-- Function: calcCondition fml ps 
-- assumption: fml is a satisfiable formula
-- assertion: phi |- fromBFormula ps ret
calcCondition :: Formula -> [Formula] -> IO BFormula
calcCondition _fml _ps = go 0 _fml _ps
    where
    go _ fml [] = return $ BConst True
    go i fml (p:ps) = do
        let np = Op (OpNot p)
        b1 <- checkSat fml p
        b2 <- checkSat fml np
        v1 <- if b1 then go (i + 1) (Op (OpAnd fml  p)) ps 
                    else return $ BConst False
        v2 <- if b2 then go (i + 1) (Op (OpAnd fml np)) ps 
                    else return $ BConst False
        if v1 == v2 then
            return v1
        else 
            return $ BOr (BAnd (BVar i) v1) (BAnd (BVar (-i)) v2)

fromBFormula :: [Formula] -> BFormula -> Formula
fromBFormula ps (BVar i) 
    | i < 0     = Op (OpNot (ps !! (-i)))
    | otherwise = ps !! i
fromBFormula ps (BConst b) = CBool b
fromBFormula ps (BOr p1 p2)  = Op (OpOr  (fromBFormula ps p1) (fromBFormula ps p2))
fromBFormula ps (BAnd p1 p2) = Op (OpAnd (fromBFormula ps p1) (fromBFormula ps p2))

checkSat :: Formula -> Formula -> IO Bool
checkSat p1 p2 = SMT.sat [Atomic p1, Atomic p2]

calcTypeTerm :: TypeMap -> Env -> Formula -> Exp -> TermType -> IO [ITermType]
calcTypeTerm tbl env fml _e tau = case _e of
    Value v -> do
        let (r, rty, ps) = tau
        let subst = M.singleton r v
            rty' = substVPType subst rty
            ps'  = map (substVFormula subst) ps
        theta <- calcTypeValue tbl env fml v rty
        phi   <- calcCondition fml ps'
        return [ITerm theta phi]
    Let _ x (LValue av) e -> do
        let fml' = Op (OpAnd fml (Op (OpEq (Var x) av)))
        calcTypeTerm tbl env fml' e tau
    Let _ x (LApp _ _ f vs) e -> do
        let (PFun _ argTy retTy, IFun assoc) = env M.! f
        let (ys, ptys, ps) = argTy
            subst = M.fromList $ zip ys vs
            ptys' = map (substVPType subst) ptys
            ps'   = map (substVFormula subst) ps
        phi <- calcCondition fml ps'
        thetas <- zipWithM (calcTypeValue tbl env fml) vs ptys'
        fmap concatITermType $ forM assoc $ \(thetas', phi', iota) ->
            if thetas' == thetas && phi' == phi 
              then case iota of
                    IFail -> return [IFail]
                    ITerm rtheta rphi -> do
                        let (r, rty, qs) = retTy
                            subst' = M.insert r (Atomic (Var x)) subst
                            qs' = map (substVFormula subst') qs
                            cond = fromBFormula qs' rphi
                            fml' = Op (OpAnd fml cond)
                            rty' = substVPType subst' rty
                            env' = M.insert x (rty', rtheta) env
                        b <- checkSat fml cond
                        if b 
                          then calcTypeTerm tbl env' fml' e tau
                          else return []
              else return []
    Let _ x (LExp ident e1) e2 -> do
        let Right tau@(y, ty_y, ps) = tbl IM.! ident
        iotas <- calcTypeTerm tbl env fml e1 tau
        fmap concatITermType $ forM iotas $ \iota_y -> do
            case iota_y of
                IFail -> return [IFail]
                ITerm theta phi -> do
                    let subst = M.singleton y x
                        ps' = map (substFormula subst) ps
                        cond = fromBFormula ps' phi
                        fml' = Op (OpAnd fml cond)
                        ty_x = substPType subst ty_y
                        env' = M.insert x (ty_x, theta) env
                    b <- checkSat fml cond
                    if b
                      then calcTypeTerm tbl env' fml' e2 tau
                      else return []
    Let _ x LRand e ->
        calcTypeTerm tbl (M.insert x (PInt, IInt) env) fml e tau
    Assume _ cond e -> do
        b <- checkSat fml cond
        if b 
          then calcTypeTerm tbl env (Op (OpAnd fml cond)) e tau
          else return []
    Fail _ -> do
        return [IFail]
    Branch _ _ e1 e2 -> do
        ts1 <- calcTypeTerm tbl env fml e1 tau
        ts2 <- calcTypeTerm tbl env fml e2 tau
        return $ mergeITermType ts1 ts2

mergeITermType :: [ITermType] -> [ITermType] -> [ITermType]
mergeITermType a b = a ++ b

concatITermType :: [[ITermType]] -> [ITermType]
concatITermType l = concat l
