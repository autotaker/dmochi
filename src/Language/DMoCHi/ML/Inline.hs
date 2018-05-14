{-# LANGUAGE OverloadedStrings #-}
module Language.DMoCHi.ML.Inline(inline) where

import Language.DMoCHi.ML.Syntax.PNormal
import Language.DMoCHi.Common.Id
import Language.DMoCHi.Common.Util
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Graph
import Data.Tree
import Control.Monad
import Data.Array
import Text.Printf
import qualified Data.Text as Text

type InlineLimit = Int
type Env = M.Map TId Value
type REnv = M.Map TId TId

alphaV :: forall m. MonadId m => REnv -> Value -> m Value
alphaV renv v =
    case valueView v of
        VAtom a -> castWith <$> freshKey <*> pure (alphaA renv a) 
        VOther SPair (v1, v2) -> mkPair <$> alphaV renv v1 <*> alphaV renv v2 <*> freshKey
        VOther SLambda (xs, e) -> do
            ys <- mapM alphaTId xs 
            let renv' = foldr (uncurry M.insert) renv (zip xs ys)
            mkLambda ys <$> alphaE renv' e <*> freshKey

rename :: REnv -> TId -> TId
rename renv x = case M.lookup x renv of
    Just y -> y
    Nothing -> x

alphaA :: REnv -> Atom -> Atom
alphaA renv (Atom l arg sty) = case (l, arg) of
    (SLiteral, _) -> Atom l arg sty
    (SVar, x) -> mkVar (rename renv x)
    (SBinary, BinArg op a1 a2) -> mkBin op (alphaA renv a1) (alphaA renv a2)
    (SUnary, UniArg op a) -> mkUni op (alphaA renv a)

alphaE :: MonadId m => REnv -> Exp -> m Exp
alphaE renv e = 
    case expView e of
        EValue v -> cast <$> alphaV renv v
        EOther SLet (x,e1,e2) -> do
            x' <- alphaTId x
            e1' <- alphaL renv e1
            let renv' = M.insert x x' renv
            e2' <- alphaE renv' e2
            mkLet x' e1' e2' <$> freshKey
        EOther SLetRec (fs, e2) -> do
            names <- mapM (alphaTId . fst) fs
            let renv' = foldr (uncurry M.insert) renv (zip (map fst fs) names)
            fs' <- forM fs $ \(f,v_f) -> do
                v_f' <- alphaV renv' v_f
                return (renv' M.! f, v_f')
            e2' <- alphaE renv' e2
            mkLetRec fs' e2' <$> freshKey
        EOther SAssume (cond, e) -> do
            mkAssume (alphaA renv cond) <$> alphaE renv e <*> freshKey
        EOther SBranch (e1, e2) -> 
            mkBranch <$> alphaE renv e1 <*> alphaE renv e2 <*> freshKey
        EOther SFail  _ -> mkFail  (getType e) <$> freshKey
        EOther SOmega _ -> mkOmega (getType e) <$> freshKey

alphaL :: MonadId m => REnv -> LExp -> m LExp
alphaL renv e =
    case lexpView e of
        LValue v -> cast <$> alphaV renv v
        LOther SBranch (e1, e2) ->
            mkBranchL <$> alphaE renv e1 <*> alphaE renv e2 <*> freshKey
        LOther SFail  _ -> mkFailL  (getType e) <$> freshKey
        LOther SOmega _ -> mkOmegaL (getType e) <$> freshKey
        LOther SRand _  -> mkRand  <$> freshKey
        LOther SApp (f, vs) -> do
            let f' = rename renv f
            vs' <- mapM (alphaV renv) vs
            mkApp f' vs' <$> freshKey

        
inlineA :: MonadId m => Env -> Atom -> m Value
inlineA env (Atom l arg sty) =
    case (l, arg) of
        (SLiteral, _) -> Value l arg sty <$> freshKey
        (SVar, x) -> case M.lookup x env of
            Just v -> alphaV M.empty v
            Nothing -> Value l arg sty <$> freshKey
        (SBinary, BinArg op a1 a2) -> do
            VAtom a1' <- valueView <$> inlineA env a1
            VAtom a2' <- valueView <$> inlineA env a2
            castWith <$> freshKey <*> pure (mkBin op a1' a2')
        (SUnary, UniArg op a) -> do 
            v' <- inlineA env a
            case valueView v' of
                VAtom a1' -> castWith <$> freshKey <*> pure (mkUni op a1')
                VOther SPair (v1,v2) ->
                    case op of
                        SFst -> pure v1
                        SSnd -> pure v2
                        _    -> error "inlineA: unexpected pattern"
                VOther _ _ -> error "inlineA: unexpected pattern"

inlineV :: MonadId m => Env -> Value -> m Value
inlineV env v = 
    let key = getUniqueKey v in
    case valueView v of
        VAtom a -> inlineA env a
        VOther SPair (v1, v2) -> mkPair <$> inlineV env v1 <*> inlineV env v2 <*> pure key
        VOther SLambda (xs, e) -> mkLambda xs <$> inlineE env e <*> pure key

inlineE :: forall m. MonadId m => Env -> Exp -> m Exp
inlineE env e =
    let sty = getType e
        key = getUniqueKey e
    in case expView e of
        EValue v -> cast <$> inlineV env v
        EOther SLet (x, e1, e2) ->
            let defaultCase :: LExp -> m Exp
                defaultCase e1' = do
                    e2' <- inlineE env e2 
                    return $ mkLet x e1' e2' key
                key1 = getUniqueKey e1
            in case lexpView e1 of
                LValue v1 -> do
                    v1'@(Value l1' _ _ _) <- inlineV env v1
                    case l1' of
                        SVar    -> inlineE (M.insert x v1' env) e2
                        SLambda -> inlineE (M.insert x v1' env) e2
                        SPair   -> inlineE (M.insert x v1' env) e2
                        _ -> defaultCase (cast v1')
                LOther SApp (f, vs) -> do
                    vs' <- mapM (inlineV env) vs
                    case M.lookup f env of
                        Just (Value SLambda (xs,ef) _ _) -> do
                            ef' <- alphaE M.empty ef 
                            e2' <- straightE ef' sty (\e1' -> mkLet x e1' e2 <$> freshKey)
                            e' <- foldr (\(x,v) me -> mkLet x (cast v) <$> me <*> freshKey) (pure e2') (zip xs vs)
                            inlineE env e'
                        Just (Value SVar f' _ _) -> defaultCase (mkApp f' vs' key1)
                        Just vf -> do
                            f' <- alphaTId f
                            mkLet f' <$> (cast <$> alphaV M.empty vf)
                                     <*> defaultCase (mkApp f' vs' key1)
                                     <*> freshKey
                        Nothing -> defaultCase (mkApp f vs' key1)
                LOther SBranch (el, er) -> do
                    el' <- inlineE env el
                    er' <- inlineE env er
                    defaultCase (mkBranchL el' er' key1)
                LOther SFail _ -> pure $ mkFail sty key
                LOther SOmega _ -> pure $ mkOmega sty key
                LOther SRand _ -> defaultCase e1
        EOther SLetRec (fs, e2) -> do
            fs' <- forM fs $ \(f,v_f) -> do
                v_f' <- inlineV env v_f 
                return (f, v_f')
            e2' <- inlineE env e2
            pure $ mkLetRec fs' e2' key
        EOther SAssume (cond, e) -> do
            VAtom av <- valueView <$> inlineA env cond 
            mkAssume av <$> inlineE env e <*> pure key
        EOther SBranch (e1, e2) -> 
            mkBranch <$> inlineE env e1 
                     <*> inlineE env e2 
                     <*> pure key
        EOther SFail _ -> pure e
        EOther SOmega _ -> pure e
                            
        
straightE :: MonadId m => Exp -> Type -> (LExp -> m Exp) -> m Exp
straightE e ty_cont cont =  -- ty_cont is the type of answer expression
    let key = getUniqueKey e in
    case expView e of
        EValue v -> cont (cast v)
        EOther SLet (x, e1, e2) -> 
            mkLet x e1 <$> straightE e2 ty_cont cont 
                       <*> pure key
        EOther SLetRec (fs, e2) -> 
            mkLetRec fs <$> straightE e2 ty_cont cont 
                        <*> pure key
        EOther SAssume (cond,e) -> 
            mkAssume cond <$> straightE e ty_cont cont 
                          <*> pure key
        EOther SBranch (e1, e2) -> cont (mkBranchL e1 e2 key)
        EOther SFail _ -> pure $ mkFail ty_cont key
        EOther SOmega _ -> pure $ mkOmega ty_cont key

inline :: InlineLimit -> Program -> FreshLogging Program
inline _limit prog = doit
    where
    edges :: [(Int,Int)]
    edges = do
        (f,_,xs,e) <- functions prog
        x <- S.toList (freeVariables (S.fromList xs) e)
        return (idTbl M.! f,idTbl M.! x)
    idTbl :: M.Map TId Int
    idTbl = M.fromList $ zip (map (\(f,_,_,_) -> f) (functions prog)) [0..]
    funcTbl :: Array Int (TId, UniqueKey, [TId], Exp)
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

    recursive :: TId -> Bool
    recursive f = recTbl ! (idTbl M.! f)
    
    small :: Exp -> Bool
    small _ = True-- sizeE (body fdef) <= limit

    doit = do
        let fs = [ funcTbl ! v | v <- reverse $ topSort depG' ]
        (fs', inlineEnv) <- go fs M.empty
        e0' <- inlineE inlineEnv (mainTerm prog)
        {-
        e0' <- rec (mainTerm prog) $ \loop e0 -> do
            e0' <- inlineE inlineEnv e0 {- >>= return . elimIndirection M.empty . elimRedundantE . simplify -}
            if e0 == e0' then
                return e0
            else loop e0'
                -}
        return $ Program fs' e0'

    go :: [(TId,UniqueKey, [TId], Exp)] -> Env -> FreshLogging ([(TId,UniqueKey, [TId], Exp)], Env)
    go ((f,key,xs,e):fs) !inlineEnv = do
        e' <- inlineE inlineEnv e
        inlineEnv1 <- 
            if not (recursive f) && small e' then do
                logInfoNS "inline" $ Text.pack $ printf "Select %s as an inline function..." (show (name f))
                return $ M.insert f (mkLambda xs e' key) inlineEnv
            else return $ inlineEnv
        (fs',inlineEnv') <- go fs inlineEnv1
        return ((f,key,xs,e') : fs', inlineEnv')
    go [] inlineEnv = return ([], inlineEnv)

