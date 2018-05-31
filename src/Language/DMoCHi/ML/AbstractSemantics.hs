module Language.DMoCHi.ML.AbstractSemantics(refine,AbstractSemantics, RefineConf(..)) where

import qualified Data.Map as M
import qualified Data.IntMap as IM
import           Language.DMoCHi.ML.Syntax.CEGAR hiding(mkBin,mkVar,mkLiteral)
import           Language.DMoCHi.Common.Id hiding(Id)
import           Language.DMoCHi.Common.Util
import           Data.PolyDict(Dict)
import qualified Language.DMoCHi.ML.HornClause as Horn
--import           Language.DMoCHi.ML.IncSaturationPre
import           Language.DMoCHi.ML.Syntax.HFormula
import           Language.DMoCHi.ML.Syntax.IType
import           Control.Monad.State.Strict
import           Control.Monad.Reader
import           Control.Monad.Except
import           Text.PrettyPrint.HughesPJClass
import           Text.Printf
import           Data.MonoTraversable

data AValue = ABase Type 
            | APair AValue AValue 
            | ACls { _clsEnv :: Env
                   , _clsConstraint :: Constraint
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
type M a = ReaderT RefineConf (StateT RefineState (HFormulaT (FreshIO (Dict AbstractSemantics)))) a

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

genConstraints :: Context -> RefineConf -> Trace -> Exp -> FreshIO (Dict AbstractSemantics) (Horn.HCCS, [(Int, UniqueKey)])
genConstraints ctx conf trace e = runHFormulaT doit ctx
    where
    doit = do
        v_true <- mkLiteral (CBool True)
        st <- execStateT (runReaderT (calcExp M.empty (v_true, []) e) conf) (initState trace)
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
        VOther SLambda (xs, info, e) -> ACls env c ({-getUniqueKey v,-} xs, info, e)
        VOther SPair (v1, v2) -> APair (calcValue env c v1) (calcValue env c v2)

{-# INLINE calcLExp #-}
calcLExp :: Env -> Constraint -> TId -> LExp ->
            M (Either (AValue, HFormula) (Maybe (AValue, BFormula, (Scope -> Predicate))))
calcLExp env (fml, preds) x e = 
    case lexpView e of
        LAtom a -> do
            let av = calcAtom env a
            -- x == v
            fml' <- lift . lift $ do
                vx <- mkVar x
                toHFormula a >>= mkBin SEq vx >>= mkBin SAnd fml
            return (Left (av, fml'))
        LOther SRand _ -> return (Left (ABase TInt, fml))
        LOther SApp (f, info_arg, vs) -> do
            -- caller site
            let ps = abstFormulas info_arg
                scope = Scope $ snd $ abstTemplate info_arg
                avs = map (calcValue env (fml, preds)) vs
            pGenArg <- newPGen (Unique (fst (abstTemplate info_arg)))
            genClause (fml, preds) (pGenArg scope)
            -- callee site
            let ACls env1 (fml1, preds1) (xs, info_arg', e1) = env M.! f
                ps' = abstFormulas info_arg'
                scope' = Scope $ snd $ abstTemplate info_arg'
                env1' = extendEnv env1 $ zip xs avs
                preds1' = pGenArg scope' : preds1

            fml1' <- ask >>= \conf ->
              if embedCurCond conf then lift . lift $ do
                    phi <- calcCondition fml ps
                    mkBin SAnd fml1 =<< fromBFormula ps' phi
              else pure fml1
            Right <$> calcExp env1' (fml1', preds1') e1
        LOther SBranch (e_l, e_r) -> do
            b <- consumeBranch
            case b of
                True  -> Right <$> calcExp env (fml, preds) e_l
                False -> Right <$> calcExp env (fml, preds) e_r

calcExp :: Env -> Constraint -> Exp -> M (Maybe (AValue, BFormula, (Scope -> Predicate)))
calcExp env (fml, preds) e = 
    case expView e of
        EValue v info -> do
            let ps = abstFormulas info
                scope = Scope $ snd $ abstTemplate info
            phi <- lift $ lift (calcCondition fml ps)
            let av = calcValue env (fml, preds) v
            pGen <- newPGen (Unique (fst (abstTemplate info)))
            genClause (fml, preds) (pGen scope)
            return (Just (av, phi, pGen))
        EOther SLet (x, e1, info, e2) ->
            calcLExp env (fml, preds) x e1 >>= \case
                Left (av,fml') -> calcExp (M.insert x av env) (fml', preds) e2
                Right Nothing -> return Nothing
                Right (Just (av, bfml, pGen')) -> do
                    let ps = abstFormulas info
                        scope = Scope $ snd $ abstTemplate info
                    let env' = M.insert x av env
                        preds' = pGen' scope : preds
                    fml' <- ask >>= \conf ->
                      if embedCurCond conf then do
                        lift .lift $ mkBin SAnd fml =<< fromBFormula ps bfml
                      else pure fml
                    calcExp env' (fml', preds') e2
        EOther SLetRec (fs, e1) -> do
            let env' = extendEnv env [ (f, calcValue env' (fml, preds) v) | (f,v) <- fs ]
            calcExp env' (fml, preds) e1
        EOther SAssume (cond, e1) -> do
            fml' <- lift . lift $ mkBin SAnd fml =<< toHFormula cond
            calcExp env (fml', preds) e1
        EOther SBranch (e1, e2) -> do
            b <- consumeBranch
            case b of
                True -> calcExp env (fml, preds) e1
                False -> calcExp env (fml, preds) e2
        EOther SFail _ -> genFailClause (fml, preds) >> return Nothing
        EOther SOmega _ -> error "diverged"

data RefineConf =
  RefineConf { solver :: Horn.Solver
             , embedCurCond :: Bool
             , decompose :: Bool }

---- refinement
refine :: Context -> RefineConf -> Int -> Trace -> Program ->
          ExceptT Horn.SolverError (FreshIO (Dict AbstractSemantics)) Program
refine ctx conf cegarId trace prog = do
    (hccs, pId2key) <- lift (genConstraints ctx conf trace (mainTerm prog))
    preds <- mapExceptT lift $ solver conf hccs cegarId
    let pMap = predicateMap pId2key preds
    let subst | decompose conf = fmap (\l -> l >>= \(xs, fml) -> (xs,) <$> decomposeFormula fml []) pMap
              |otherwise = pMap
    runHFormulaT (refineProgram subst prog) ctx

predicateMap :: [(Int, UniqueKey)] -> [(Int, [TId], Formula)] -> M.Map UniqueKey [([TId], Formula)]
predicateMap pId2key preds = subst
    where
    g = IM.fromList pId2key
    subst = M.fromListWith (++) $ do
        (pId, args, fml) <- preds
        return (g IM.! pId, [(args,fml)])
    
refineProgram :: HFormulaFactory m => M.Map UniqueKey [([TId], Formula)] -> Program -> m Program
refineProgram subst  = otraverse conv
    where
    conv DummyInfo = pure DummyInfo
    conv info =
          let (key, _) = abstTemplate info
          in case M.lookup key subst of
              Nothing -> pure info
              Just preds -> updateAbstInfo preds info

{-
refinePredicates :: M.Map UniqueKey [([Id], Formula)] -> PredTemplate -> [Formula] -> [Formula]
refinePredicates subst (key, args) ps =
     case M.lookup key subst of
        Nothing -> ps
        Just fmls -> foldl (\acc (args_i, fml) ->
                        let fml' = substAFormula (M.fromList (zip args_i args)) fml in
                        updateFormula fml' acc) ps fmls
            

refineTypeMap :: [(Int,UniqueKey)] -> [(Int, [Id], Formula)]-> TypeMap -> TypeMap
refineTypeMap  pId2key preds = fmap conv
    where
    conv (Left pty)  = Left (refinePType subst pty)
    conv (Right tau) = Right (refineTermType subst tau)
    subst = predicateMap pId2key preds

refinePType :: M.Map UniqueKey [([Id], Atom)]  -> PType -> PType
refinePType _ PInt = PInt 
refinePType _ PBool = PBool
refinePType subst (PPair _ p1 p2) = 
    mkPPair (refinePType subst p1) (refinePType subst p2)
refinePType subst (PFun _ (xs, ptys_xs, ps, predTempl) tau) =
    mkPFun (xs, ptys_xs', ps', predTempl) tau'
    where
    tau' = refineTermType subst tau
    ps' = refinePredicates subst predTempl ps
    ptys_xs' = map (refinePType subst) ptys_xs

refineTermType :: M.Map UniqueKey [([Id], Atom)] -> TermType -> TermType
refineTermType subst (r, rty, qs, predTempl) = (r, rty', qs', predTempl)
    where
    rty' = refinePType subst rty
    qs' = refinePredicates subst predTempl qs
    -}
