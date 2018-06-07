module Language.DMoCHi.ML.PredicateGeneralizer where
import Language.DMoCHi.ML.Syntax.CEGAR
import           Language.DMoCHi.ML.Syntax.Atom(mkUni)
import           Language.DMoCHi.Common.Id hiding(Id)
import           Language.DMoCHi.Common.Util
import qualified Data.Map as M
import           Data.PolyDict(Dict)
import           Language.DMoCHi.ML.Syntax.HFormula hiding(mkUni)
import           Language.DMoCHi.ML.Syntax.IType
import           Control.Monad.State.Strict
import           Control.Monad.Except
import qualified Language.DMoCHi.ML.ConvexHull.Syntax as ConvexHull
import qualified Language.DMoCHi.ML.ConvexHull.Solver as ConvexHull
import           Data.MonoTraversable
import Debug.Trace


data AValue = ABase 
            | APair AValue AValue 
            | ACls { _clsEnv :: Env
                   , _clsConstraint :: Constraint
                   , _clsBody :: ([TId], AbstInfo, Exp) }

data PredicateGeneralizer

data AState = 
    AState { stTrace :: [Bool]
           , stConditions :: M.Map UniqueKey ([TId],DNFFormula) }
type M a = StateT AState (HFormulaT (FreshIO (Dict PredicateGeneralizer))) a
type Trace = [Bool]

type DNFFormula = [[Atom]]
type Constraint = HFormula
type Env = M.Map TId AValue

setTrace :: Trace -> M ()
setTrace trace = state $ \st -> ((), st { stTrace = trace })

consume :: M Bool
consume = state $ \st -> (head (stTrace st), st { stTrace = tail (stTrace st) })

addCondition :: AbstInfo -> BFormula -> M ()
addCondition info phi = unless (dnf == [] || dnf == [[]]) $ do
    logPretty "PredicateGeneralizer" LevelDebug "addCondition" (key, dnf)
    state $ \st -> 
        ((), st { stConditions = M.insertWith update key (xs, dnf) (stConditions st) })
    where
    (xs, as) = abstPredicates info
    f i = if i > 0 then fml
                   else mkUni SNot fml
        where fml = traceShow (as,i) $ as !! (abs i - 1)
    dnf = map (map f) $ toDNF phi 
    key = fst (abstTemplate info)
    update (xs, dnf1) (_, dnf2) = (xs, dnf1 ++ dnf2)

calc :: Context -> ConvexHull.Solver -> [Trace] -> Program 
        -> FreshIO (Dict PredicateGeneralizer) Program
calc ctx solver traces prog = runHFormulaT doit ctx
    where
    doit = do
        v_true <- mkLiteral (CBool True)
        let initState = AState { stTrace = [], stConditions = M.empty }
        st <- flip execStateT initState $ 
            forM_ traces $ \trace -> do
                setTrace trace
                calcExp M.empty v_true (mainTerm prog)
        let conv DummyInfo = pure DummyInfo
            conv info = 
                let (key, _) = abstTemplate info 
                    (ys, _)  = abstPredicates info
                in
                case M.lookup key (stConditions st) of
                    Just (xs, dnf) 
                      | not (dnf == [] || dnf == [[]]) -> do
                        let q = ConvexHull.Query xs dnf
                        preds <- lift $ lift $ runExceptT (solver q) >>= \case
                            Left err -> do
                                logPretty "convexhull" 
                                          LevelError "error" (show err)
                                return []
                            Right (ConvexHull.Answer answer) -> do
                                logPretty "convexhull" 
                                          LevelInfo "result" answer
                                return $ map (ys,) answer
                        updateAbstInfo preds info
                      | otherwise -> pure info
                    Nothing -> pure info
        otraverse conv prog

calcAtom :: Env -> HFormula -> AValue
calcAtom env (HFormula l arg _ _ _) =
    case (l, arg) of
        (SLiteral, _ ) -> ABase
        (SVar, x) -> env M.! x
        (SUnary, UniArg SFst a) -> 
            let APair a1 _ = calcAtom env a in a1
        (SUnary, UniArg SSnd a) -> 
            let APair _ a2 = calcAtom env a in a2
        (SUnary, _) -> ABase
        (SBinary, _) -> ABase

calcValue :: Env -> Constraint -> Value -> AValue
calcValue env c v =
    case valueView v of
        VAtom a -> calcAtom env a
        VOther SLambda arg -> ACls env c arg
        VOther SPair (v1,v2) -> 
            APair (calcValue env c v1) (calcValue env c v2)



calcExp :: Env -> Constraint -> Exp -> M (Maybe (AValue, BFormula))
calcExp env c e =
    case expView e of
        EValue v info -> do
            let av = calcValue env c v
            phi <- lift $ calcCondition c (abstFormulas info)
            addCondition info phi
            return $ Just (av, phi)
        EOther SLet (x, e1, info, e2) -> 
            calcLExp env c x e1 info >>= \case
                Nothing -> return Nothing
                (Just (env', c')) -> calcExp env' c' e2
        EOther SLetRec (fs, e1) -> do
            let env' = extendEnv env [ (f, calcValue env' c v) | (f, v) <- fs ]
            calcExp env' c e1
        EOther SAssume (cond, e1) -> do
            c' <- lift $ mkBin SAnd c cond
            calcExp env c' e1
        EOther SFail _ -> return Nothing
        EOther SOmega _ -> error "diverged"
        EOther SBranch (e1, e2) -> do
            b <- consume
            if b
                then calcExp env c e1
                else calcExp env c e2

calcLExp :: Env -> Constraint -> TId -> LExp -> AbstInfo -> M (Maybe (Env, Constraint))
calcLExp env c x e info =
    let cont :: Maybe (AValue, BFormula) -> M (Maybe (Env, Constraint))
        cont Nothing = pure Nothing
        cont (Just (av, bfml)) = do
            let ps = abstFormulas info
            c' <- lift $ mkBin SAnd c =<< fromBFormula ps bfml
            return $ Just (M.insert x av env, c')
    in
    case lexpView e of
        LAtom atom -> do
            let av = calcAtom env atom
            c' <- lift $ do
                vx <- mkVar x
                mkBin SEq vx atom >>= mkBin SAnd c
            return $ Just (M.insert x av env, c')
        LOther SRand _ -> return $ Just (M.insert x ABase env, c)
        LOther SApp (f, info_arg, vs) -> do
            let avs = map (calcValue env c) vs
            phi <- lift $ calcCondition c (abstFormulas info_arg)
            let ACls env1 c1 (xs, info_arg', e1) = env M.! f
                env1' = extendEnv env1 $ zip xs avs
            addCondition info_arg phi
            c1' <- lift $ mkBin SAnd c1 
                        =<< fromBFormula (abstFormulas info_arg') phi
            calcExp env1' c1' e1 >>= cont
        LOther SBranch (e_l, e_r) -> do
            b <- consume
            if b
                then calcExp env c e_l >>= cont      
                else calcExp env c e_r >>= cont
