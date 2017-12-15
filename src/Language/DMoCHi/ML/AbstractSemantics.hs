module Language.DMoCHi.ML.AbstractSemantics(genConstraints) where

import qualified Data.Map as M
import qualified Data.HashTable.IO as H
import           Language.DMoCHi.ML.Syntax.CEGAR hiding(mkBin,mkVar,mkLiteral)
import           Language.DMoCHi.Common.Id hiding(Id)
import qualified Language.DMoCHi.ML.HornClause as Horn
import           Language.DMoCHi.ML.IncSaturationPre
import           Language.DMoCHi.ML.Syntax.HFormula
import           Language.DMoCHi.ML.Syntax.IType
import           Control.Monad.State.Strict
import           Control.Monad.Reader
import           Text.Printf

data AValue = ABase Type 
            | APair AValue AValue 
            | ACls { _clsEnv :: Env
                   , _clsConstraint :: Constraint
                   , _clsBody :: (UniqueKey, [TId], AbstInfo, Exp) }

data Meta = Pre UniqueKey | Post UniqueKey | Unique UniqueKey
instance Show Meta where
    show (Pre key)  = show key ++ "_pre" 
    show (Post key) = show key ++ "_post" 
    show (Unique key) = show key


type Env = M.Map TId AValue
type Constraint = (HFormula, [Predicate])
data Predicate = Predicate Meta Int Scope
type Trace = [Bool]
type M a = StateT ([Bool], [Horn.Clause], Int) R a

formatPredicate :: Meta -> Int -> String
formatPredicate meta i = printf "p_%s[%d:0]" (show meta) i

genConstraints :: Trace -> Exp -> R Horn.HCCS
genConstraints trace e = do
    v_true <- mkLiteral (CBool True)
    ([], cs, _) <- execStateT (calcExp M.empty (v_true, []) e) (trace, [], 0)
    return (Horn.HCCS (reverse cs))

genClause :: Constraint -> Predicate -> M ()
genClause (fml, preds) (Predicate meta i (Scope vs)) = modify' (\(a,b,c) -> (a, Horn.Clause hd body : b, c))
    where
    hd = Horn.PVar (formatPredicate meta i) (map toHornTerm vs)
    body = toHornTerm fml : map toHornPred preds

genFailClause :: Constraint -> M ()
genFailClause (fml, preds) = modify' (\(a,b,c) -> (a, Horn.Clause Horn.Bot body : b, c))
    where body = toHornTerm fml : map toHornPred preds

decomposePairName :: TId -> (TId, TId)
decomposePairName x = (x1, x2)
    where
    x1 = TId t1 (reserved $ show (name x) ++ "_fst")
    x2 = TId t2 (reserved $ show (name x) ++ "_snd")
    TPair t1 t2 = getType x

toHornPred :: Predicate -> Horn.Term
toHornPred (Predicate meta i (Scope vs)) = Horn.Pred (formatPredicate meta i) (map toHornTerm vs)
    
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

newPGen :: Meta -> M (Scope -> Predicate)
newPGen meta = do
    (a,b,c) <- get
    put $! (a,b,) $! c + 1
    return $ Predicate meta c

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
        VOther SLambda (xs, info, e) -> ACls env c (getUniqueKey v, xs, info, e)
        VOther SPair (v1, v2) -> APair (calcValue env c v1) (calcValue env c v2)

calcExp :: Env -> Constraint -> Exp -> M (Maybe (AValue, BFormula, (Scope -> Predicate)))
calcExp env (fml, preds) e = 
    let key = getUniqueKey e in
    case expView e of
        EValue v info -> do
            Just (ps, scope) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
            phi <- lift (calcCondition fml ps)
            let av = calcValue env (fml, preds) v
            pGen <- newPGen (Unique (fst (abstTemplate info)))
            genClause (fml, preds) (pGen scope)
            return (Just (av, phi, pGen))
        EOther SLet (x, e1, info, e2) -> do
            let genericCase r1 = do
                    Just (ps, scope) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
                    case r1 of
                        Just (av, bfml, pGen') -> do
                            fml' <- lift $ mkBin SAnd fml =<< fromBFormula ps bfml
                            let env' = M.insert x av env
                                preds' = pGen' scope : preds
                            calcExp env' (fml', preds') e2
                        Nothing -> return Nothing
            case lexpView e1 of
                LAtom a -> do
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
                LOther SApp (f, info_arg, vs) -> do
                    Just (ps, scope) <- ask >>= \ctx -> liftIO $ H.lookup (ctxArgTypeTbl ctx) (getUniqueKey e1)
                    let ACls env1 (fml1, preds1) (key1, xs, _, e1) = env M.! f
                    pGenArg <- newPGen (Unique (fst (abstTemplate info_arg)))
                    Just (ps', scope') <- ask >>= \ctx -> liftIO $ H.lookup (ctxArgTypeTbl ctx) key1
                    let env1' = foldr (uncurry M.insert) env1 $ zip xs (map (calcValue env (fml, preds)) vs)
                        preds1' = pGenArg scope' : preds1
                    genClause (fml, preds) (pGenArg scope)
                    phi <- lift (calcCondition fml ps)
                    fml1' <- lift $ mkBin SAnd fml1 =<< fromBFormula ps' phi
                    calcExp env1' (fml1', preds1') e1 >>= genericCase
                LOther SBranch (e_l, e_r) -> do
                    b <- consumeBranch
                    case b of
                        True -> calcExp env (fml, preds) e_l >>= genericCase
                        False -> calcExp env (fml, preds) e_r >>= genericCase
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


{-
refinePType :: IM.IntMap [([Id], Atom)]  -> PType -> PType
refinePType _ PInt = PInt 
refinePType _ PBool = PBool
refinePType subst (PPair _ p1 p2) = mkPPair (refinePType subst p1) (refinePType subst p2)
refinePType subst (PFun _ argTy@(xs, ptys_xs, ps, (key, args)) tau) =
    let tau' = refineTermType subst tau
    case IM.lookup key subst of
        Nothing -> mkPFun argTy tau'
        Just [] -> mkPFun argTy tau'
        Just fmls -> 
            foldl (\acc (args_i, fml) -> 
                let fml' = substFormula (zip args_i args)

 -}           
