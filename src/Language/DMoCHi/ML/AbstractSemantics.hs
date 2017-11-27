module Language.DMoCHi.ML.AbstractSemantics(genConstraints) where

import qualified Data.Map as M
import qualified Data.HashTable.IO as H
import           Language.DMoCHi.ML.Syntax.PNormal hiding(mkBin,mkVar,mkLiteral)
import           Language.DMoCHi.Common.Id hiding(Id)
import qualified Language.DMoCHi.ML.HornClause as Horn
import           Language.DMoCHi.ML.IncSaturationPre
import           Language.DMoCHi.ML.Syntax.HFormula
import           Language.DMoCHi.ML.Syntax.IType
import           Control.Monad.State
import           Control.Monad.Reader

data AValue = ABase Type 
            | APair AValue AValue 
            | ACls { _clsEnv :: Env
                   , _clsConstraint :: Constraint
                   , _clsBody :: (UniqueKey, [TId], Exp) }

data Meta = Meta !String [String]
type Env = M.Map TId AValue
type Constraint = (HFormula, [Predicate])
data Predicate = Predicate Meta Int Scope
type Trace = [Bool]
type M a = StateT ([Bool], [Horn.Clause], Int) R a

genConstraints :: Trace -> Exp -> R ()
genConstraints trace e = do
    v_true <- mkLiteral (CBool True)
    Nothing <- evalStateT (calcExp M.empty (v_true, []) e) (trace, [], 0)
    return ()

genClause :: Constraint -> Predicate -> M ()
genClause (fml, preds) (Predicate _ i (Scope vs)) = 
    liftIO $ print $ Horn.Clause hd body
    where
    hd = Horn.PVar ("P_" ++ show i) (map toHornTerm vs)
    body = toHornTerm fml : map toHornPred preds

genFailClause :: Constraint -> M ()
genFailClause (fml, preds) = 
    liftIO $ print $ Horn.Clause Horn.Bot (toHornTerm fml : map toHornPred preds)

decomposePairName :: TId -> (TId, TId)
decomposePairName x = (x1, x2)
    where
    x1 = TId t1 (reserved $ show (name x) ++ "_fst")
    x2 = TId t2 (reserved $ show (name x) ++ "_snd")
    TPair t1 t2 = getType x

toHornPred :: Predicate -> Horn.Term
toHornPred (Predicate _ i (Scope vs)) = Horn.Pred ("P_" ++ show i) (map toHornTerm vs)
    
toHornTerm :: HFormula -> Horn.Term
toHornTerm = go [] where
    go :: [Bool] -> HFormula -> Horn.Term
    go meta (HFormula l arg _ _ _) = 
        case (l, arg) of
            (SLiteral, CBool b) -> Horn.Bool b
            (SLiteral, CInt i) -> Horn.Int i
            (SLiteral, _) -> error "unexpected pattern"
            (SVar, x) -> Horn.Var (sub meta x) 
            (SBinary, BinArg SAdd v1 v2) -> Horn.Add (go [] v1) (go [] v2)
            (SBinary, BinArg SSub v1 v2) -> Horn.Sub (go [] v1) (go [] v2)
            (SBinary, BinArg SMul v1 v2) -> Horn.Mul (go [] v1) (go [] v2)
            (SBinary, BinArg SDiv v1 v2) -> Horn.Div (go [] v1) (go [] v2)
            (SBinary, BinArg SEq v1 v2)  -> Horn.Eq  (go [] v1) (go [] v2)
            (SBinary, BinArg SLt v1 v2)  -> Horn.Lt  (go [] v1) (go [] v2)
            (SBinary, BinArg SLte v1 v2) -> Horn.Lte (go [] v1) (go [] v2)
            (SBinary, BinArg SAnd v1 v2) -> Horn.And (go [] v1) (go [] v2)
            (SBinary, BinArg SOr  v1 v2) -> Horn.Or  (go [] v1) (go [] v2)
            (SUnary, UniArg SFst v1) -> go (True:meta) v1
            (SUnary, UniArg SSnd v1) -> go (False:meta) v1
            (SUnary, UniArg SNot v1) -> Horn.Not (go [] v1)
            (SUnary, UniArg SNeg v1) -> Horn.Sub (Horn.Int 0) (go [] v1)
    sub:: [Bool] -> TId -> TId
    sub [] x = x
    sub (b:bs) x = 
        let (x1, x2) = decomposePairName x in
        if b then sub bs x1 else sub bs x2


consumeBranch :: M Bool
consumeBranch = do
    (a:as, b, c) <- get
    put (as, b, c)
    return a


newPGen :: M (Scope -> Predicate)
newPGen = do
    (a,b,c) <- get
    put $! (a,b,) $! c + 1
    return $ Predicate undefined c

calcAtom :: Env -> Atom -> AValue
calcAtom env (Atom l arg sty) = 
    case (l, arg) of
        (SLiteral, _) -> ABase sty
        (SVar, x) -> env M.! x
        (SBinary, _) -> ABase sty
        (SUnary, UniArg SFst a1) -> case calcAtom env a1 of
            APair v1 _ -> v1
            _ -> error "unexpected pattern"
        (SUnary, UniArg SSnd a1) -> case calcAtom env a1 of
            APair _ v2 -> v2
            _ -> error "unexpected pattern"
        (SUnary, _) -> ABase sty

calcValue :: Env -> Constraint -> Value -> AValue
calcValue env c v =
    case valueView v of
        VAtom a -> calcAtom env a
        VOther SLambda (xs, e) -> ACls env c (getUniqueKey v, xs, e)
        VOther SPair (v1, v2) -> APair (calcValue env c v1) (calcValue env c v2)

calcLExp :: Env -> Constraint -> LExp  -> M (Maybe (AValue, BFormula, Scope -> Predicate))
calcLExp env (fml, preds) e =
    let key = getUniqueKey e in
    case lexpView e of
        LValue v -> do
            Just (_, ps, scope) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
            phi <- lift (calcCondition fml ps)
            let av = calcValue env (fml, preds) v
            pGen <- newPGen
            genClause (fml, preds) (pGen scope)
            return (Just (av, phi, pGen))
        LOther SApp (f, vs) -> do
            Just (_, ps, scope) <- ask >>= \ctx -> liftIO $ H.lookup (ctxArgTypeTbl ctx) key
            let ACls env1 (fml1, preds1) (key1, xs, e1) = env M.! f
            pGenArg <- newPGen
            Just (_, ps', scope') <- ask >>= \ctx -> liftIO $ H.lookup (ctxArgTypeTbl ctx) key1
            let env1' = foldr (uncurry M.insert) env1 $ zip xs (map (calcValue env (fml, preds)) vs)
                preds1' = pGenArg scope' : preds1
            genClause (fml, preds) (pGenArg scope)
            phi <- lift (calcCondition fml ps)
            fml1' <- lift $ mkBin SAnd fml1 =<< fromBFormula ps' phi
            calcExp env1' (fml1', preds1') e1
        LOther SRand _ -> do
            Just (_, ps, scope) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
            phi <- lift (calcCondition fml ps)
            let av = ABase TInt
            pGen <- newPGen
            genClause (fml, preds) (pGen scope)
            return (Just (av, phi, pGen))
        LOther SBranch (e1, e2) -> do
            b <- consumeBranch
            case b of
                True  -> calcExp env (fml, preds) e1
                False -> calcExp env (fml, preds) e2
        LOther SFail _ -> genFailClause (fml, preds) >> return Nothing
        LOther SOmega _ -> error "diverged"
            
calcExp :: Env -> Constraint -> Exp  -> M (Maybe (AValue, BFormula, (Scope -> Predicate)))
calcExp env (fml, preds) e = 
    let key = getUniqueKey e in
    case expView e of
        EValue v -> do
            Just (_, ps, scope) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
            phi <- lift (calcCondition fml ps)
            let av = calcValue env (fml, preds) v
            pGen <- newPGen
            genClause (fml, preds) (pGen scope)
            return (Just (av, phi, pGen))
        EOther SLet (x, e1, e2) -> do
            case lexpView e1 of
                LValue (valueView -> VAtom a) -> do
                    let av = calcAtom env a
                        env' = M.insert x av env
                    -- x == v
                    fml' <- lift $ do
                        vx <- mkVar x
                        toHFormula a >>= mkBin SEq vx >>= mkBin SAnd fml
                    calcExp env' (fml', preds) e2
                LOther SRand _ -> do
                    let env' = M.insert x (ABase TInt) env
                    calcExp env' (fml, preds) e2
                _ -> do
                    r1 <- calcLExp env (fml, preds) e1
                    Just (_, ps, scope) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
                    case r1 of
                        Just (av, bfml, pGen') -> do
                            fml' <- lift $ mkBin SAnd fml =<< fromBFormula ps bfml
                            let env' = M.insert x av env
                                preds' = pGen' scope : preds
                            calcExp env' (fml', preds') e2
                        Nothing -> return Nothing
        EOther SLetRec (fs, e1) -> do
            let env' = foldr (uncurry M.insert) env [ (f, calcValue env' (fml, preds) v) | (f,v) <- fs ]
            calcExp env' (fml, preds) e1
        EOther SAssume (cond, e1) -> do
            fml' <- lift $ mkBin SAnd fml =<< toHFormula cond
            calcExp env (fml', preds) e1
        EOther SBranch (e1, e2) -> do
            b <- consumeBranch
            case b of
                True -> calcExp env (fml, preds) e1
                False -> calcExp env (fml, preds) e2
        EOther SFail _ -> genFailClause (fml, preds) >> return Nothing
        EOther SOmega _ -> error "diverged"

