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
        return $ Program fs' e0'

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

inlineF env (FunDef l x e) = FunDef l x <$> inlineE env e
inlineE env (Value v) = return (Value v)
inlineE env (Let ty x lv e) = Let ty x <$> lv' <*> inlineE env e
    where
    lv' = case lv of
        LValue v -> return lv
        LApp ty0 l f v -> 
            case M.lookup f env of
                Just (FunDef _ y e0) -> do
                    e0' <- alphaLabel e0
                    i   <- freshInt
                    return $ LExp i $ Let ty0 y (LValue v) e0'
                Nothing -> return lv
        LFun fdef -> LFun <$> inlineF env fdef
        LExp l e0 -> LExp l <$> inlineE env e0
        LRand -> return LRand
inlineE env (Assume ty v e) = Assume ty v <$> inlineE env e
inlineE env (Fail ty) = return (Fail ty)
inlineE env (Branch ty l e1 e2) = Branch ty l <$> inlineE env e1 <*> inlineE env e2

alphaLabel :: MonadId m => Exp -> m Exp
alphaLabel (Value v) = pure $ Value v
alphaLabel (Let ty x lv e) = Let ty x <$> lv' <*> alphaLabel e
    where
    lv' = case lv of
        LValue v -> pure lv
        LApp ty0 _ f v -> LApp ty0 <$> freshInt <*> pure f <*> pure v
        LFun (FunDef _ y e0) ->
            LFun <$> (FunDef <$> freshInt <*> pure y <*> alphaLabel e0)
        LExp _ e0 -> LExp <$> freshInt <*> alphaLabel e0
        LRand -> pure LRand
alphaLabel (Assume ty v e) = Assume ty v <$> alphaLabel e
alphaLabel (Fail ty) = pure $ Fail ty
alphaLabel (Branch ty _ e1 e2) = 
    Branch ty <$> freshInt <*> alphaLabel e1 <*> alphaLabel e2
