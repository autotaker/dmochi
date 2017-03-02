module Language.DMoCHi.ML.Inline where

import Language.DMoCHi.ML.Syntax.PNormal
import Language.DMoCHi.Common.Id
--import Language.DMoCHi.Common.Util
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Graph
import Data.Tree
import Control.Monad
import Control.Monad.IO.Class
import Data.Array
import Text.Printf

type InlineLimit = Int
type Env = M.Map TId Value
type REnv = M.Map TId TId

alphaV :: forall m. MonadId m => REnv -> Value -> m Value
alphaV renv (Value l arg sty _) =
    let atomCase :: Atom -> m Value
        atomCase av = castWith <$> freshKey <*> pure (alphaA renv av) in
    case (l,arg) of
        (SLiteral, _) -> atomCase (Atom l arg sty)
        (SVar, _)     -> atomCase (Atom l arg sty)
        (SBinary, _)  -> atomCase (Atom l arg sty)
        (SUnary,  _)  -> atomCase (Atom l arg sty)
        (SPair, (v1, v2)) -> mkPair <$> alphaV renv v1 <*> alphaV renv v2 <*> freshKey
        (SLambda,(xs, e)) -> do
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
alphaE renv (Exp l arg sty key) = 
    case (l, arg) of
        (SLiteral, _) -> cast <$> alphaV renv (Value l arg sty key)
        (SVar, _)     -> cast <$> alphaV renv (Value l arg sty key)
        (SBinary, _)  -> cast <$> alphaV renv (Value l arg sty key)
        (SUnary, _)   -> cast <$> alphaV renv (Value l arg sty key)
        (SPair, _)    -> cast <$> alphaV renv (Value l arg sty key)
        (SLambda, _)  -> cast <$> alphaV renv (Value l arg sty key)
        (SLet, (x, e1, e2)) -> do
            x' <- alphaTId x
            e1' <- alphaL renv e1
            let renv' = M.insert x x' renv
            e2' <- alphaE renv' e2
            mkLet x' e1' e2' <$> freshKey
        (SAssume, (cond,e)) -> do
            mkAssume (alphaA renv cond) <$> alphaE renv e <*> freshKey
        (SBranch, (e1,e2)) -> mkBranch <$> alphaE renv e1 
                                       <*> alphaE renv e2 
                                       <*> freshKey
        (SFail, _) -> Exp l arg sty <$> freshKey
        (SOmega, _) -> Exp l arg sty <$> freshKey

alphaL :: MonadId m => REnv -> LExp -> m LExp
alphaL renv (LExp l arg sty key) =
    case (l, arg) of
        (SLiteral, _) -> cast <$> alphaV renv (Value l arg sty key)
        (SVar, _)     -> cast <$> alphaV renv (Value l arg sty key)
        (SBinary, _)  -> cast <$> alphaV renv (Value l arg sty key)
        (SUnary, _)   -> cast <$> alphaV renv (Value l arg sty key)
        (SPair, _)    -> cast <$> alphaV renv (Value l arg sty key)
        (SLambda, _)  -> cast <$> alphaV renv (Value l arg sty key)
        (SBranch, (e1,e2)) -> mkBranchL <$> alphaE renv e1 
                                        <*> alphaE renv e2 
                                        <*> freshKey
        (SFail, _)  -> LExp l arg sty <$> freshKey
        (SOmega, _) -> LExp l arg sty <$> freshKey
        (SRand, _) -> LExp l arg sty <$> freshKey
        (SApp, (f,vs)) -> do
            let f' = rename renv f
            vs' <- mapM (alphaV renv) vs
            mkApp f' vs' <$> freshKey

        
inlineA :: Env -> Atom -> FreshIO Value
inlineA env (Atom l arg sty) =
    case (l, arg) of
        (SLiteral, _) -> Value l arg sty <$> freshKey
        (SVar, x) -> case M.lookup x env of
            Just v -> alphaV M.empty v
            Nothing -> Value l arg sty <$> freshKey
        (SBinary, BinArg op a1 a2) -> do
            Just a1' <- atomOfValue <$> inlineA env a1
            Just a2' <- atomOfValue <$> inlineA env a2
            castWith <$> freshKey <*> pure (mkBin op a1' a2')
        (SUnary, UniArg op a) -> do 
            v'@(Value l' arg' _ _) <- inlineA env a
            case (op,l') of
                (SFst, SPair) -> pure (fst arg')
                (SSnd, SPair) -> pure (snd arg')
                _ -> do
                    let Just a1' = atomOfValue v'
                    castWith <$> freshKey <*> pure (mkUni op a1')

inlineV :: Env -> Value -> FreshIO Value
inlineV env (Value l arg sty key) = 
    case (l, arg) of
        (SLiteral, _) -> inlineA env (Atom l arg sty)
        (SVar, _)     -> inlineA env (Atom l arg sty)
        (SBinary, _)  -> inlineA env (Atom l arg sty)
        (SUnary, _)   -> inlineA env (Atom l arg sty)
        (SPair, (v1, v2)) -> mkPair <$> inlineV env v1 <*> inlineV env v2 <*> pure key
        (SLambda, (xs, e)) -> mkLambda xs <$> inlineE env e <*> pure key

inlineE :: Env -> Exp -> FreshIO Exp
inlineE env (Exp l arg sty key) =
    case (l, arg) of
        (SLiteral, _) -> cast <$> inlineV env (Value l arg sty key)
        (SVar, _)     -> cast <$> inlineV env (Value l arg sty key)
        (SBinary, _)     -> cast <$> inlineV env (Value l arg sty key)
        (SUnary, _)     -> cast <$> inlineV env (Value l arg sty key)
        (SPair, _)     -> cast <$> inlineV env (Value l arg sty key)
        (SLambda, _)     -> cast <$> inlineV env (Value l arg sty key)
        (SLet, (x, e1@(LExp l1 arg1 sty1 key1), e2)) ->
            let defaultCase e1' = do
                    e2' <- inlineE env e2 
                    return $ mkLet x e1' e2' key
                valueCase :: Value -> FreshIO Exp
                valueCase v1 = do
                    v1'@(Value l1' _ _ _) <- inlineV env v1
                    case l1' of
                        SVar    -> inlineE (M.insert x v1' env) e2
                        SLambda -> inlineE (M.insert x v1' env) e2
                        SPair   -> inlineE (M.insert x v1' env) e2
                        _ -> defaultCase (cast v1')
            in case (l1, arg1) of
                (SLiteral, _) -> valueCase (Value l1 arg1 sty1 key1)
                (SVar, _)     -> valueCase (Value l1 arg1 sty1 key1)
                (SBinary, _)  -> valueCase (Value l1 arg1 sty1 key1)
                (SUnary, _)   -> valueCase (Value l1 arg1 sty1 key1)
                (SPair, _)    -> valueCase (Value l1 arg1 sty1 key1)
                (SLambda, _)  -> valueCase (Value l1 arg1 sty1 key1)
                (SApp, (f, vs)) -> do
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
                (SBranch, (el, er)) -> do
                    el' <- inlineE env el
                    er' <- inlineE env er
                    defaultCase (mkBranchL el' er' key1)
                (SFail, _) -> pure $ mkFail sty key
                (SOmega, _) -> pure $ mkOmega sty key
                (SRand, _) -> defaultCase e1
        (SAssume, (cond,e)) -> do
            Just av <- atomOfValue <$> inlineA env cond 
            mkAssume av <$> inlineE env e <*> pure key
        (SBranch, (e1, e2)) -> mkBranch <$> inlineE env e1 <*> inlineE env e2 <*> pure key
        (SFail, _) -> return $ Exp l arg sty key
        (SOmega, _) -> return $ Exp l arg sty key
                            
        
straightE :: Exp -> Type -> (LExp -> FreshIO Exp) -> FreshIO Exp
straightE (Exp l arg sty key) ty_cont cont =  -- ty_cont is the type of answer expression
    case (l, arg) of
        (SLiteral, _) -> cont (LExp l arg sty key)
        (SVar, _)     -> cont (LExp l arg sty key)
        (SBinary, _)  -> cont (LExp l arg sty key)
        (SUnary, _)   -> cont (LExp l arg sty key)
        (SLambda, _)  -> cont (LExp l arg sty key)
        (SPair, _)    -> cont (LExp l arg sty key)
        (SLet, (x, e1, e2)) -> mkLet x e1 <$> straightE e2 ty_cont cont <*> pure key
        (SAssume, (cond,e)) -> mkAssume cond <$> straightE e ty_cont cont <*> pure key
        (SBranch, (e1, e2)) -> cont (mkBranchL e1 e2 key)
        (SFail, _) -> pure $ mkFail ty_cont key
        (SOmega, _) -> pure $ mkOmega ty_cont key

inline :: InlineLimit -> Program -> FreshIO Program
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

    go :: [(TId,UniqueKey, [TId], Exp)] -> Env -> FreshIO ([(TId,UniqueKey, [TId], Exp)], Env)
    go ((f,key,xs,e):fs) !inlineEnv = do
        e' <- inlineE inlineEnv e
        inlineEnv1 <- 
            if not (recursive f) && small e' then do
                liftIO $ printf "Select %s as an inline function...\n" (show (name f))
                return $ M.insert f (mkLambda xs e' key) inlineEnv
            else return $ inlineEnv
        (fs',inlineEnv') <- go fs inlineEnv1
        return ((f,key,xs,e') : fs', inlineEnv')
    go [] inlineEnv = return ([], inlineEnv)

    
    {-
-- Let ty x (LExp l e0) でe0がstraight-line programの時にletのネストを潰す。
simplify :: Exp -> Exp
simplify (Value v) = Value v
simplify (Let ty x (LExp l e0) e) = 
    let e0' = simplify e0
        e'  = simplify e
    in case straight e0' ty (\lv -> Let ty x lv e') of
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

straight :: Exp -> Type -> (LetValue -> Exp) -> Maybe Exp
straight (Value v) _ cont = Just (cont (LValue v))
straight (Let _ x lv e) ty cont = Let ty x lv <$> straight e ty cont
straight (Assume _ v e) ty cont = Assume ty v <$> straight e ty cont
straight (Fail _) _ _ = Nothing
straight (Fun fdef) _ cont = Just (cont (LFun fdef))
straight (Branch _ l e1 e2) ty cont = 
    Branch ty l <$> straightFail e1 ty <*> straight e2 ty cont <|>
    Branch ty l <$> straight e1 ty cont <*> straightFail e2 ty

straightFail :: Exp -> Type -> Maybe Exp
straightFail (Fail _) ty = Just (Fail ty)
straightFail (Let _ l lv e) ty = Let ty l lv <$> straightFail e ty
straightFail (Assume _ lv e) ty = Assume ty lv <$> straightFail e ty
straightFail _ _ = Nothing

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
elimIndirection env (Let _ x (LValue (Var y)) e) = elimIndirection (M.insert x (rename env y) env) e
elimIndirection env (Let ty x lv e) = Let ty x lv' e' where
    lv' = case lv of
        LValue v -> LValue (renameV env v)
        LApp ty l f vs -> LApp ty l (rename env f) (map (renameV env) vs)
        LFun fdef -> LFun (elimIndirectionF env fdef)
        LExp l e -> LExp l (elimIndirection env e)
        LRand -> LRand
    e' = elimIndirection env e
elimIndirection env (Assume ty v e) = Assume ty (renameV env v) (elimIndirection env e)
elimIndirection _ (Fail ty) = Fail ty
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
    -}
