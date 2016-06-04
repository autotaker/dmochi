{-# Language BangPatterns #-} 
module Language.DMoCHi.ML.Inline where

import Language.DMoCHi.ML.Syntax.Typed
import Language.DMoCHi.Common.Id
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Graph
import Data.Tree
import Control.Monad
import Data.Array
import Text.Printf
import Control.Monad.IO.Class
import Data.Char(isDigit)

type InlineLimit = Int
inline :: (MonadId m, MonadIO m) => InlineLimit -> Program -> m Program
inline limit prog = doit
    where
    edges :: [(Int,Int)]
    edges = do
        (f,fdef) <- functions prog
        x <- S.toList (freeVariables (S.singleton (arg fdef)) (body fdef))
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
        e0' <- inlineE inlineEnv (mainTerm prog)
        return $ Program fs' (simplify e0')

    go ((f,fdef):fs) !inlineEnv = do
        fdef' <- inlineF inlineEnv fdef
        inlineEnv1 <- 
            if not (recursive f) && small fdef' then do
                liftIO $ printf "Select %s as an inline function...\n" (name f)
                return $ M.insert f fdef' inlineEnv
            else return $ inlineEnv
        (fs',inlineEnv') <- go fs inlineEnv1
        return ((f, fdef') : fs', inlineEnv')
    go [] inlineEnv = return ([], inlineEnv)

inlineF env (FunDef l x e) = FunDef l x . simplify <$> inlineE env e
inlineE env (Value v) = return (Value v)
inlineE env (Let ty x lv e) = Let ty x <$> lv' <*> inlineE env e
    where
    lv' = case lv of
        LValue v -> return lv
        LApp ty0 l f v -> 
            case M.lookup f env of
                Just (FunDef _ y e0) -> do
                    y'  <- alphaId y
                    e0' <- alphaLabel (M.singleton y y') e0
                    i   <- freshInt
                    return $ LExp i $ Let ty0 y' (LValue v) e0'
                Nothing -> return lv
        LFun fdef -> LFun <$> inlineF env fdef
        LExp l e0 -> LExp l <$> inlineE env e0
        LRand -> return LRand
inlineE env (Fun fdef) = Fun <$> inlineF env fdef
inlineE env (Assume ty v e) = Assume ty v <$> inlineE env e
inlineE env (Fail ty) = return (Fail ty)
inlineE env (Branch ty l e1 e2) = Branch ty l <$> inlineE env e1 <*> inlineE env e2

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
            LApp ty0 _ f v -> LApp ty0 <$> freshInt <*> rename env f <*> goV env v
            LFun (FunDef _ y e0) -> do
                y' <- alphaId y
                LFun <$> (FunDef <$> freshInt <*> pure y' <*> goE (M.insert y y' env) e0)
            LExp _ e0 -> LExp <$> freshInt <*> goE env e0
            LRand -> pure LRand
        x' <- alphaId x
        Let ty x' lv' <$> goE (M.insert x x' env) e
    goE env (Assume ty v e) = Assume ty <$> goV env v <*> goE env e
    goE env (Fail ty) = pure $ Fail ty
    goE env (Fun (FunDef _ y e0)) = do
        y' <- alphaId y
        Fun <$> (FunDef <$> freshInt <*> pure y' <*> goE (M.insert y y' env) e0)
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
    let fdef' = FunDef (ident fdef) (arg fdef) (simplify $ body fdef) in
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
