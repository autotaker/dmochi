module Language.DMoCHi.ML.AbstractSemantics(genConstraints, refine) where

import qualified Data.Map as M
import qualified Data.IntMap as IM
import           Language.DMoCHi.ML.Syntax.CEGAR hiding(mkBin,mkVar,mkLiteral)
import           Language.DMoCHi.Common.Id hiding(Id)
import           Language.DMoCHi.Common.Util
import qualified Language.DMoCHi.ML.HornClause as Horn
--import           Language.DMoCHi.ML.IncSaturationPre
import           Language.DMoCHi.ML.Syntax.HFormula
import           Language.DMoCHi.ML.Syntax.IType
import           Language.DMoCHi.ML.Syntax.PType hiding(Env)
import           Control.Monad.State.Strict
import           Text.PrettyPrint.HughesPJClass
import           Text.Printf

data AValue = ABase Type 
            | APair AValue AValue 
            | ACls { _clsEnv :: Env
                   , _clsConstraint :: Constraint
                   , _clsAbstInfo :: AbstInfo
                   , _clsBody :: ([TId], AbstInfo, Exp) }

data AbstractSemantics
newtype Scope = Scope [Atom]
instance Pretty Scope where
    pPrint (Scope vs) = brackets $ hsep $ punctuate comma $ map pPrint vs 

data Meta = Pre UniqueKey | Post UniqueKey | Unique UniqueKey
instance Show Meta where
    show (Pre key)  = show key ++ "_pre" 
    show (Post key) = show key ++ "_post" 
    show (Unique key) = show key

instance HasUniqueKey Meta where
    getUniqueKey (Pre key) = key
    getUniqueKey (Post key) = key
    getUniqueKey (Unique key) = key


type Env = M.Map TId AValue
type Constraint = (HFormula, [Predicate])
data Predicate = Predicate Meta Int Scope
type Trace = [Bool]
type M a = StateT RefineState (HFormulaT (FreshIO AbstractSemantics)) a

data RefineState = 
    RefineState { 
        stTrace :: Trace 
      , stClauses :: [Horn.Clause]
      , stPIdEntries :: [(Int, UniqueKey)]
    }

initState :: Trace ->  RefineState
initState tr = RefineState {
    stTrace = tr
  , stClauses = []
  , stPIdEntries = []
  }


formatPredicate :: Meta -> Int -> String
formatPredicate meta i = printf "p_%s[%d:0]" (show meta) i

genConstraints :: Context -> Trace -> Exp -> FreshIO AbstractSemantics (Horn.HCCS, [(Int, UniqueKey)])
genConstraints ctx trace e = runHFormulaT doit ctx 
    where
    doit = do
        v_true <- mkLiteral (CBool True)
        st <- execStateT (calcExp M.empty (v_true, []) e) (initState trace)
        return (Horn.HCCS (reverse $ stClauses st), stPIdEntries st)

genClause :: Constraint -> Predicate -> M ()
genClause (fml, preds) (Predicate meta i (Scope vs)) = 
    modify' (\st -> st { stClauses = cls : stClauses st })
    where
    hd = Horn.PVar (formatPredicate meta i) (map toHornTerm vs)
    body = toHornTerm (fromHFormula fml) : map toHornPred preds
    cls = Horn.Clause hd body

genFailClause :: Constraint -> M ()
genFailClause (fml, preds) = 
    modify' (\st -> st { stClauses = cls : stClauses st })
    where 
    body = toHornTerm (fromHFormula fml) : map toHornPred preds
    cls = Horn.Clause Horn.Bot body

decomposePairName :: TId -> (TId, TId)
decomposePairName x = (x1, x2)
    where
    x1 = TId t1 (reserved $ show (name x) ++ "_fst")
    x2 = TId t2 (reserved $ show (name x) ++ "_snd")
    TPair t1 t2 = getType x

toHornPred :: Predicate -> Horn.Term
toHornPred (Predicate meta i (Scope vs)) = Horn.Pred (formatPredicate meta i) (map toHornTerm vs)
    
toHornTerm :: Formula -> Horn.Term
toHornTerm = go [] where
    go :: [Bool] -> Formula -> Horn.Term
    go meta (Atom l arg _) = 
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
    st <- get
    case stTrace st of
        (a:as) -> put (st{ stTrace = as }) >> return a
        _ -> error "no more branch"

newPGen :: Meta -> M (Scope -> Predicate)
newPGen meta = do
    st <- get
    c <- freshInt
    put $! st { stPIdEntries = (c, getUniqueKey meta) : stPIdEntries st }
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
        VOther SLambda (xs, info, e) -> ACls env c info ({-getUniqueKey v,-} xs, info, e)
        VOther SPair (v1, v2) -> APair (calcValue env c v1) (calcValue env c v2)

calcExp :: Env -> Constraint -> Exp -> M (Maybe (AValue, BFormula, (Scope -> Predicate)))
calcExp env (fml, preds) e = 
    case expView e of
        EValue v info -> do
            let ps = abstPredicates info
                scope = Scope $ snd $ abstTemplate info
            phi <- lift (calcCondition fml ps)
            let av = calcValue env (fml, preds) v
            pGen <- newPGen (Unique (fst (abstTemplate info)))
            genClause (fml, preds) (pGen scope)
            return (Just (av, phi, pGen))
        EOther SLet (x, e1, info, e2) -> do
            let genericCase r1 = do
                    let ps = abstPredicates info
                        scope = Scope $ snd $ abstTemplate info
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
                    let ps = abstPredicates info_arg
                        scope = Scope $ snd $ abstTemplate info_arg
                    let ACls env1 (fml1, preds1) info_arg' (xs, _, e1) = env M.! f
                    pGenArg <- newPGen (Unique (fst (abstTemplate info_arg)))
                    let ps' = abstPredicates info_arg'
                        scope' = Scope $ snd $ abstTemplate info_arg'
                    -- Just (ps', scope') <- ask >>= \ctx -> liftIO $ H.lookup (ctxArgTypeTbl ctx) key1
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

---- refinement
refine :: [(Int,UniqueKey)] -> [(Int, [Id], Formula)]-> TypeMap -> TypeMap
refine pId2key preds = fmap conv
    where
    conv (Left pty)  = Left (refinePType subst pty)
    conv (Right tau) = Right (refineTermType subst tau)
    g = IM.fromList pId2key
    subst = M.fromListWith (++) [ (key, [(args,fml)]) | (pId, args, fml) <- preds, 
                                                        let key = g IM.! pId ]

    

refinePredicates :: M.Map UniqueKey [([Id], Atom)] -> PredTemplate -> [Formula] -> [Formula]
refinePredicates subst (key, args) ps =
     case M.lookup key subst of
        Nothing -> ps
        Just fmls -> foldl (\acc (args_i, fml) ->
                        let fml' = substAFormula (M.fromList (zip args_i args)) fml in
                        updateFormula fml' acc) ps fmls
            

refinePType :: M.Map UniqueKey [([Id], Atom)]  -> PType -> PType
refinePType _ PInt = PInt 
refinePType _ PBool = PBool
refinePType subst (PPair _ p1 p2) = 
    mkPPair (refinePType subst p1) (refinePType subst p2)
refinePType subst (PFun _ (xs, ptys_xs, ps, predTempl) tau) =
    mkPFun (xs, ptys_xs, ps', predTempl) tau'
    where
    tau' = refineTermType subst tau
    ps' = refinePredicates subst predTempl ps

refineTermType :: M.Map UniqueKey [([Id], Atom)] -> TermType -> TermType
refineTermType subst (r, rty, qs, predTempl) = (r, rty', qs', predTempl)
    where
    rty' = refinePType subst rty
    qs' = refinePredicates subst predTempl qs
