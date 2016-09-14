{-# Language BangPatterns, TupleSections #-} 
module Language.DMoCHi.ML.Inline where

import Language.DMoCHi.ML.Syntax.Typed
import Language.DMoCHi.Common.Id
import Language.DMoCHi.Common.Util
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Graph
import Data.Tree
import Control.Monad
import Data.Array
import Text.Printf
import Control.Monad.IO.Class
import Data.Char(isDigit)
import Debug.Trace
import Language.DMoCHi.ML.PrettyPrint.Typed

type InlineLimit = Int

data IValue = IPair IValue IValue | INil | IFun FunDef deriving(Show)

inline :: (MonadId m, MonadIO m) => InlineLimit -> Program -> m Program
inline limit prog = doit
    where
    edges :: [(Int,Int)]
    edges = do
        (f,fdef) <- functions prog
        x <- S.toList (freeVariables (S.fromList (args fdef)) (body fdef))
        return (idTbl M.! f,idTbl M.! x)
    idTbl :: M.Map Id Int
    idTbl = M.fromList $ zip (map fst (functions prog)) [0..]
    funcTbl :: Array Int (Id,FunDef)
    funcTbl = listArray (0,n-1) (functions prog)
    n = length (functions prog)
    depG :: Graph 
    depG = buildG (0,n-1) edges
    recs = map flatten $ scc depG
    recTbl :: Array Int Bool
    recTbl = array (0,n-1) $ do
        l <- recs
        case l of
            [x] -> return (x, x `elem` depG ! x)
            l   -> [ (x, True) | x <- l ]
    sccTbl :: Array Int Int
    sccTbl = array (0,n-1) $ do
        l <- recs
        let m = minimum l
        m `seq` [ (x, m) | x <- l ]
    depG' :: Graph
    depG' = buildG (0,n-1) $ do
        (x, y) <- edges
        let x' = sccTbl ! x
            y' = sccTbl ! y
        guard $ x' /= y'
        return (x', y')

    recursive :: Id -> Bool
    recursive f = recTbl ! (idTbl M.! f)
    
    small :: FunDef -> Bool
    small fdef = sizeE (body fdef) <= limit

    doit = do
        let fs = [ funcTbl ! v | v <- reverse $ topSort depG' ]
        (fs', inlineEnv) <- go fs M.empty
        e0' <- rec (mainTerm prog) $ \loop e0 -> do
            e0' <- inlineE inlineEnv e0 >>= return . elimIndirection M.empty . elimRedundantE . simplify
            if e0 == e0' then
                return e0
            else loop e0'
        return $ Program fs' e0'


    go ((f,fdef):fs) !inlineEnv = do
        fdef' <- rec fdef $ \loop fdef -> do
            fdef' <- inlineF inlineEnv fdef >>= return . elimIndirectionF M.empty . elimRedundantF
            if fdef == fdef' then
                return fdef
            else loop fdef'
        inlineEnv1 <- 
            if not (recursive f) && small fdef' then do
                liftIO $ printf "Select %s as an inline function...\n" (name f)
                return $ M.insert f (IFun fdef') inlineEnv
            else return $ inlineEnv
        (fs',inlineEnv') <- go fs inlineEnv1
        return ((f, fdef') : fs', inlineEnv')
    go [] inlineEnv = return ([], inlineEnv)

    
inlineF :: MonadId m => M.Map Id IValue -> FunDef -> m FunDef
inlineF env (FunDef l x e) = FunDef l x . simplify <$> inlineE env e
inlineE env (Value v) = return (Value v)
inlineE env (Let ty x lv e) = do
    (lv',iv) <- case lv of
        LValue v -> return (lv, eval env v)
        LApp ty0 l f vs -> 
            case M.lookup f env of
                Just (IFun (FunDef _ ys e0)) -> do
                    ys'  <- mapM alphaId ys
                    e0' <- alphaLabel (M.fromList $ zip ys ys') e0
                    i   <- freshInt
                    let e0'' = foldr (\(y',v) acc -> Let ty0 y' (LValue v) acc) e0' (zip ys' vs)
                    return (LExp i e0'', INil)
                Just INil -> return (lv, INil)
                Nothing -> return (lv, INil)
        LFun fdef -> do
            fdef' <- inlineF env fdef
            return (LFun fdef', IFun fdef')
        LExp l e0 -> (, INil) . LExp l <$> inlineE env e0
        LRand -> return (LRand, INil)
    Let ty x lv' <$> inlineE (M.insert x iv env) e
inlineE env (Fun fdef) = Fun <$> inlineF env fdef
inlineE env (Assume ty v e) = Assume ty v <$> inlineE env e
inlineE env (Fail ty) = return (Fail ty)
inlineE env (Branch ty l e1 e2) = Branch ty l <$> inlineE env e1 <*> inlineE env e2

eval :: M.Map Id IValue -> Value -> IValue
eval env (Var x) = case M.lookup x env of Just v -> v
                                          Nothing -> INil
eval env (Pair v1 v2) = IPair (eval env v1) (eval env v2)
eval env (Op (OpFst _ v)) = case eval env v of IPair v1 _ -> v1
                                               _ -> INil
eval env (Op (OpSnd _ v)) = case eval env v of IPair _ v2 -> v2 
                                               _ -> INil
eval env (Op _) = INil
eval env (CInt _) = INil
eval env (CBool _) = INil

alphaId :: MonadId m => Id -> m Id
alphaId x = Id (getType x) <$> freshId (elim $ name x)
    where
    elim x = reverse $ dropWhile (=='_') $ dropWhile isDigit $ reverse x

alphaLabel :: MonadId m => M.Map Id Id -> Exp -> m Exp
alphaLabel = goE
    where
    rename env x = case M.lookup x env of
        Just y -> pure y
        Nothing -> pure x
    goE env (Value v) = Value <$> goV env v
    goE env (Let ty x lv e) = do
        lv' <- case lv of
            LValue v -> LValue <$> goV env v
            LApp ty0 _ f vs -> LApp ty0 <$> freshInt <*> rename env f <*> mapM (goV env) vs
            LFun (FunDef _ ys e0) -> do
                ys' <- mapM alphaId ys
                let env' = foldr (uncurry M.insert) env (zip ys ys')
                LFun <$> (FunDef <$> freshInt <*> pure ys' <*> goE env' e0)
            LExp _ e0 -> LExp <$> freshInt <*> goE env e0
            LRand -> pure LRand
        x' <- alphaId x
        Let ty x' lv' <$> goE (M.insert x x' env) e
    goE env (Assume ty v e) = Assume ty <$> goV env v <*> goE env e
    goE env (Fail ty) = pure $ Fail ty
    goE env (Fun (FunDef _ ys e0)) = do
        ys' <- mapM alphaId ys
        let env' = foldr (uncurry M.insert) env (zip ys ys')
        Fun <$> (FunDef <$> freshInt <*> pure ys' <*> goE env' e0)
    goE env (Branch ty _ e1 e2) =
        Branch ty <$> freshInt <*> goE env e1 <*> goE env e2
    goV env (Var x) = Var <$> rename env x
    goV env (CInt i) = pure $ CInt i
    goV env (CBool b) = pure $ CBool b
    goV env (Pair v1 v2) = Pair <$> goV env v1 <*> goV env v2
    goV env (Op op) = Op <$> case op of
        OpAdd v1 v2 -> OpAdd <$> goV env v1 <*> goV env v2
        OpSub v1 v2 -> OpSub <$> goV env v1 <*> goV env v2
        OpEq  v1 v2 -> OpEq  <$> goV env v1 <*> goV env v2
        OpLt  v1 v2 -> OpLt  <$> goV env v1 <*> goV env v2
        OpLte v1 v2 -> OpLte <$> goV env v1 <*> goV env v2
        OpAnd v1 v2 -> OpAnd <$> goV env v1 <*> goV env v2
        OpOr  v1 v2 -> OpOr  <$> goV env v1 <*> goV env v2
        OpFst ty v  -> OpFst ty <$> goV env v
        OpSnd ty v  -> OpSnd ty <$> goV env v
        OpNot v -> OpNot <$> goV env v

-- Let ty x (LExp l e0) でe0がstraight-line programの時にletのネストを潰す。
simplify :: Exp -> Exp
simplify (Value v) = Value v
simplify (Let ty x (LExp l e0) e) = 
    let e0' = simplify e0
        e'  = simplify e
    in case straight e0' (\lv -> Let ty x lv e') of
        Just e'' -> e''
        Nothing  -> Let ty x (LExp l e0') e'
simplify (Let ty x (LFun fdef) e) =
    let fdef' = FunDef (ident fdef) (args fdef) (simplify $ body fdef) in
    Let ty x (LFun fdef') (simplify e)
simplify (Let ty x lv e) = Let ty x lv (simplify e)
simplify (Assume ty v e) = Assume ty v (simplify e)
simplify (Fail ty) = Fail ty
simplify (Fun fdef) = Fun fdef{ body = simplify $ body fdef }
simplify (Branch ty l e1 e2) = Branch ty l (simplify e1) (simplify e2)

straight :: Exp -> (LetValue -> Exp) -> Maybe Exp
straight (Value v) cont = Just (cont (LValue v))
straight (Let ty x lv e) cont = Let ty x lv <$> straight e cont
straight (Assume ty v e) cont = Assume ty v <$> straight e cont
straight (Fail ty) cont = Nothing
straight (Fun fdef) cont = Just (cont (LFun fdef))
straight (Branch _ _ _ _) cont = Nothing

-- redundant let-expression elimination
elimRedundantF :: FunDef -> FunDef
elimRedundantF (FunDef l x e) = FunDef l x (elimRedundantE e)

elimRedundantE (Value v) = Value v
elimRedundantE (Fun fdef) = Fun (elimRedundantF fdef)
elimRedundantE (Let ty x lv e) | redundant = e'
                               | otherwise = Let ty x lv' e'
    where
    e' = elimRedundantE e
    fv = freeVariables S.empty e'
    redundant = atomic && S.notMember x fv
    (lv', atomic) = case lv of
        LValue v -> (LValue v, True)
        LFun fdef -> (LFun (elimRedundantF fdef), True)
        LExp l e1 -> (LExp l (elimRedundantE e1), False)
        LApp _ _ _ _ -> (lv, False)
        LRand -> (lv, False)
elimRedundantE (Assume ty v e) = Assume ty v (elimRedundantE e)
elimRedundantE (Fail ty) = Fail ty
elimRedundantE (Branch ty l e1 e2) = Branch ty l (elimRedundantE e1) (elimRedundantE e2)

elimIndirectionF :: M.Map Id Id -> FunDef -> FunDef
elimIndirectionF env (FunDef l x e) = FunDef l x (elimIndirection env e)
elimIndirection :: M.Map Id Id -> Exp -> Exp
elimIndirection env (Value v) = Value $ renameV env v
elimIndirection env (Fun fdef) = Fun (elimIndirectionF env fdef)
elimIndirection env (Let ty x (LValue (Var y)) e) = elimIndirection (M.insert x (rename env y) env) e
elimIndirection env (Let ty x lv e) = Let ty x lv' e' where
    lv' = case lv of
        LValue v -> LValue (renameV env v)
        LApp ty l f vs -> LApp ty l (rename env f) (map (renameV env) vs)
        LFun fdef -> LFun (elimIndirectionF env fdef)
        LExp l e -> LExp l (elimIndirection env e)
        LRand -> LRand
    e' = elimIndirection env e
elimIndirection env (Assume ty v e) = Assume ty (renameV env v) (elimIndirection env e)
elimIndirection env (Fail ty) = Fail ty
elimIndirection env (Branch ty l e1 e2) = 
    Branch ty l (elimIndirection env e1) (elimIndirection env e2)

rename :: M.Map Id Id -> Id -> Id
rename env f = 
    case M.lookup f env of 
        Just g -> g 
        Nothing -> f

renameV :: M.Map Id Id -> Value -> Value
renameV env = go
    where 
    go (Var x) = Var (rename env x)
    go (CInt i) = CInt i
    go (CBool b) = CBool b
    go (Pair v1 v2) = Pair (go v1) (go v2)
    go (Op op) = Op $ goOp op
    goOp (OpAdd v1 v2) = OpAdd (go v1) (go v2)
    goOp (OpSub v1 v2) = OpSub (go v1) (go v2)
    goOp (OpEq v1 v2) = OpEq (go v1) (go v2)
    goOp (OpLt v1 v2) = OpLt (go v1) (go v2)
    goOp (OpLte v1 v2) = OpLte (go v1) (go v2)
    goOp (OpAnd v1 v2) = OpAnd (go v1) (go v2)
    goOp (OpOr v1 v2) = OpOr (go v1) (go v2)
    goOp (OpFst ty v) = OpFst ty (go v)
    goOp (OpSnd ty v) = OpSnd ty (go v)
    goOp (OpNot v) = OpNot (go v)
