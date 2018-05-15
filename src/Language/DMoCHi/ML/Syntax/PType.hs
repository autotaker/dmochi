{-# LANGUAGE  Rank2Types, BangPatterns, TypeApplications #-}
module Language.DMoCHi.ML.Syntax.PType where

import Language.DMoCHi.ML.Syntax.Type
import Language.DMoCHi.ML.Syntax.Base
import Language.DMoCHi.ML.Syntax.PNormal
-- import Language.DMoCHi.ML.PrettyPrint.PNormal
import Language.DMoCHi.Common.Id hiding(Id)
import qualified Data.Map as M

import Text.PrettyPrint.HughesPJClass
import Control.Monad.Writer
import Data.Proxy
import qualified Data.DList as DL
--import Debug.Trace

data PType = PInt | PBool
           | PFun Type ArgType TermType
           | PPair Type PType PType

instance HasType PType where
    getType PInt = TInt
    getType PBool = TBool
    getType (PFun sty _ _) = sty
    getType (PPair sty _ _) = sty

mkPFun :: ArgType -> TermType -> PType
mkPFun argTy@(xs,_,_,_) termTy@(TId ty_r _,_,_,_) = PFun (TFun ty_xs ty_r) argTy termTy
    where
    ty_xs = map getType xs
mkPPair :: PType -> PType -> PType
mkPPair ty1 ty2 = 
    let !sty1 = getType ty1 in
    let !sty2 = getType ty2 in
    PPair (TPair sty1 sty2) ty1 ty2
    

type Env = M.Map Id PType
type Constraints = [Formula]
type Formula = Atom
type Id = TId

-- Template for predicate generation.
-- ``key`` identifies the location of the predicate
-- ``atoms`` are arguments for the predicates. Each atom must have a base type.
type PredTemplate = (UniqueKey, [Atom])

type TermType = (Id, PType, [Formula], PredTemplate)
type ArgType = ([Id],[PType],[Formula], PredTemplate)

type TypeMap = M.Map UniqueKey (Either PType TermType)
type ScopeMap = M.Map UniqueKey [Id]


instance Eq PType where
    PInt == PInt = True
    PBool == PBool = True
    (PFun ty_1 (xs_1,xsty_1,ps_1,_) (r_1,rty_1,qs_1,_)) == (PFun ty_2 (xs_2,xsty_2,ps_2,_) (r_2,rty_2,qs_2,_)) =
        ty_1 == ty_2 && 
        ps_1 == map (substFormula subst1) ps_2 &&
        qs_1 == map (substFormula subst2) qs_2 &&
        xsty_1 == map (substPType subst1) xsty_2 &&
        rty_1 == substPType subst2 rty_2
        where
        subst1 = M.fromList $ zip xs_2 xs_1
        subst2 = M.insert r_2 r_1 subst1
    PPair ty pty_fst pty_snd == PPair ty' pty_fst' pty_snd' =
        ty == ty' && pty_fst == pty_fst' && pty_snd == pty_snd'
    _ == _ = False

dummyPredTemplate = (reservedKey, [])

pprintTermType :: TermType -> Doc
pprintTermType (TId _ name,pty_x,fml,_) = braces $ 
    pPrint name <+> colon <+> (pprintPType 0 pty_x) <+>
    text "|" <+> (hsep $ punctuate comma $ map pPrint fml)

pprintPTypeArg :: ArgType -> Doc
pprintPTypeArg (xs,pty_xs,fml,_) =
    braces $ 
        hsep (punctuate comma $ zipWith (\(TId _ name_x) pty_x -> pPrint name_x <+> colon <+> (pprintPType 0 pty_x)) xs pty_xs) <+>
        text "|" <+> (hsep $ punctuate comma $ map pPrint fml)

pprintPType :: Int -> PType -> Doc
pprintPType _ PInt = text "int"
pprintPType _ PBool = text "bool"
pprintPType assoc (PPair _ pty1 pty2) =
    let d1 = pprintPType 1 pty1
        d2 = pprintPType 1 pty2
        d = d1 <+> text "*" <+> d2
    in if assoc == 0 then d else parens d
pprintPType assoc (PFun _ x_tup r_tup) =
    let d = pprintPTypeArg x_tup <+> text "->" <+> pprintTermType r_tup in
    if assoc == 0 then d else parens d

instance Pretty PType where
    pPrint = pprintPType 0

instance Show PType where
    show = render . pPrint

substPredTemplate :: M.Map Id Id -> PredTemplate -> PredTemplate
substPredTemplate subst (key, vs) = (key, map (substFormula subst) vs)

substVPredTemplate :: M.Map Id Value -> PredTemplate -> PredTemplate
substVPredTemplate subst (key, vs) = (key, map (substVFormula subst) vs)

substTermType :: M.Map Id Id -> TermType -> TermType
substTermType subst (x,pty,ps,info) = (x, pty', ps', info')
    where
    subst' = M.delete x subst
    pty' = substPType subst' pty
    ps' = map (substFormula subst') ps
    info' = substPredTemplate subst' info

substVTermType :: M.Map Id Value -> TermType -> TermType
substVTermType subst (x,pty,ps,info) = (x, pty', ps', info')
    where
    subst' = M.delete x subst
    pty' = substVPType subst' pty
    ps' = map (substVFormula subst') ps
    info' = substVPredTemplate subst' info

substPType :: M.Map Id Id -> PType -> PType
substPType subst = substVPType (fmap (cast . mkVar) subst)

substVPType :: M.Map Id Value -> PType -> PType
substVPType _ PInt = PInt
substVPType _ PBool = PBool
substVPType subst (PPair t t1 t2) = 
    PPair t (substVPType subst t1) (substVPType subst t2)
substVPType subst (PFun ty (xs,ty_xs,ps,tmpl_arg) (r,ty_r,qs, tmpl_ret)) = 
    PFun ty (xs,ty_xs',ps', tmpl_arg') (r,ty_r',qs', tmpl_ret')
    where
    subst1 = foldr M.delete subst xs
    subst2 = M.delete r subst1
    ty_xs' = map (substVPType subst1) ty_xs
    ps' = map (substVFormula subst1) ps
    tmpl_arg' = substVPredTemplate subst1 tmpl_arg
    ty_r' = substVPType subst2 ty_r
    qs' = map (substVFormula subst2) qs
    tmpl_ret' = substVPredTemplate subst2 tmpl_ret

substFormula :: M.Map Id Id -> Formula -> Formula
substFormula subst = substVFormula (fmap (cast . mkVar) subst)

substAFormula :: M.Map Id Atom -> Formula -> Formula
substAFormula subst = go
    where
    go atom@(Atom l arg _) = case (l, arg) of
        (SVar, x) ->
            case M.lookup x subst of
                Just b -> b
                Nothing -> atom
        (SLiteral, _) -> atom
        (SBinary, BinArg op v1 v2) -> mkBin op (go v1) (go v2)
        (SUnary, UniArg op v1) -> mkUni op (go v1)

substVFormula :: M.Map Id Value -> Formula -> Formula
substVFormula subst = atomic . go where
    atomic v = case valueView v of
        VAtom a -> a
        _ -> error "substVFormula: type error"
    go e@(Atom l arg _) = case (l,arg) of
        (SVar,x) ->
            case M.lookup x subst of
                Just b -> b
                Nothing -> cast e
        (SLiteral, CInt  _) -> cast e
        (SLiteral, CBool _) -> cast e
        (SLiteral, CUnit) -> error "unexpected"
        -- Pair v1 v2 -> Pair (go v1) (go v2)
        (SBinary, BinArg op v1 v2) ->  
            let !v1' = atomic $ go v1
                !v2' = atomic $ go v2 in
            cast $ mkBin op v1' v2'
        (SUnary, UniArg op a) -> case op of
            SFst -> case go a of 
                Value SPair (v1,_) _ _ -> v1
                v -> cast $ mkUni SFst $! atomic v
            SSnd  -> case go a of
                Value SPair (_,v2) _ _ -> v2
                v -> cast $ mkUni SSnd $! atomic v
            SNot -> cast $ mkUni SNot $! atomic (go a)
            SNeg -> cast $ mkUni SNeg $! atomic (go a)

typeOfAtom :: Env -> Atom -> PType
typeOfAtom env = go where
    go (Atom l arg _) = case (l,arg) of
        (SVar,x) -> env M.! x
        (SLiteral,CInt _) -> PInt
        (SLiteral,CBool _) -> PBool
        (SLiteral,CUnit) -> error "unexpected pattern"
        (SBinary, BinArg op _ _) -> case op of
            SAdd -> PInt
            SSub -> PInt
            SMul -> PInt
            SDiv -> PInt
            SEq  -> PBool
            SLt  -> PBool
            SLte -> PBool
            SAnd -> PBool
            SOr  -> PBool
        (SUnary, UniArg op v) -> case op of
            SFst -> let PPair _ ty1 _ = go v in ty1
            SSnd -> let PPair _ _ ty2 = go v in ty2
            SNot -> PBool
            SNeg -> PInt

flatten :: Value -> [Atom] -> [Atom]
flatten (Value l arg sty _) xs = 
    case (l, arg) of
        (SPair, (v1, v2)) -> flatten v1 (flatten v2 xs)
        (SVar, _)         -> Atom l arg sty : xs
        (SLiteral, _)     -> Atom l arg sty : xs
        (SBinary, _)      -> Atom l arg sty : xs
        (SUnary, _)       -> Atom l arg sty : xs
        (SLambda, _)  -> xs

decompose :: Atom -> [Atom] -> [Atom]
decompose x l = case getType x of
    TPair _ _ -> decompose (mkUni SFst x) (decompose (mkUni SSnd x) l)
    TFun _ _  -> l
    TInt -> x : l
    TBool -> x : l



initTypeMap :: forall m. MonadId m => Program -> m (TypeMap,ScopeMap)
initTypeMap (Program fs t0) = do
    es <- execWriterT $ do
        let gatherE :: [TId] -> Exp -> WriterT (DL.DList (UniqueKey, Either PType TermType, [TId])) m ()
            gatherE fv (Exp l arg _ _) = gather (Proxy @Exp) fv l arg
            gatherV :: [TId] -> Value -> WriterT (DL.DList (UniqueKey, Either PType TermType, [TId])) m ()
            gatherV fv (Value l arg _ _) = gather (Proxy @Value) fv l arg
            gather :: (Ident e ~ TId, Normalized l e arg)  => 
                      Proxy e -> [TId] -> SLabel l -> arg -> WriterT (DL.DList (UniqueKey, Either PType TermType, [TId])) m ()
            gather _ fv l arg = case (l,arg) of
                (SLiteral, _) -> return ()
                (SVar, _)     -> return ()
                (SBinary, _)  -> return ()
                (SUnary, _)   -> return ()
                (SLambda, (xs,e)) -> gatherE (xs ++ fv) e
                (SPair, (v1,v2))  -> gatherV fv v1 >> gatherV fv v2 
                (SLet, (x, (LExp l1 arg1 sty1 key1), e2)) -> do
                    gather (Proxy @ LExp) fv l1 arg1
                    let genType :: WriterT (DL.DList (UniqueKey, Either PType TermType, [TId])) m ()
                        genType = genTermType fv sty1 >>= \ty -> tell (DL.singleton (key1, Right ty, fv))
                    (case l1 of
                        SLiteral -> pure ()
                        SVar     -> pure ()
                        SBinary  -> pure ()
                        SUnary   -> pure ()
                        SApp     -> pure ()
                        SLambda  -> genType
                        SPair    -> genType
                        SBranch  -> genType
                        SRand    -> pure ()
                        SOmega   -> genType 
                        SFail    -> genType) :: WriterT (DL.DList (UniqueKey, Either PType TermType, [TId])) m ()
                    gatherE (x : fv) e2
                (SLetRec, (fs, e2)) -> do
                    let fv' = map fst fs ++ fv
                    forM_ fs $ \(_, v) -> do
                        ty <- genPType fv (getType v) 
                        tell (DL.singleton (getUniqueKey v, Left ty, fv'))
                        gatherV fv' v
                    gatherE fv' e2
                (SApp, (_, vs)) -> mapM_ (gatherV fv) vs
                (SAssume, (_,e)) -> gatherE fv e
                (SBranch, (e1, e2)) -> gatherE fv e1 >> gatherE fv e2
                (SFail, _) -> return ()
                (SOmega, _) -> return ()
                (SRand, _) -> return ()
            gatherF fv (TId sty _, key, xs, e) = do
                gatherE (xs ++ fv) e
                ty <- genPType fv sty 
                tell (DL.singleton (key, Left ty, fv))
        let fv = map (\(f,_,_,_) -> f) fs
        mapM_ (gatherF fv) fs
        gatherE fv t0
    let (es1,es2) = unzip [ ((i,v1),(i,v2)) | (i, v1, v2) <- DL.toList es ]
    return (M.fromList es1, M.fromList es2)

genPredTemplate :: MonadId m => [TId] -> m PredTemplate
genPredTemplate xs = do
    key <- freshKey
    let scope = foldr (decompose . mkVar) [] xs
    return (key, scope)

genTermType :: MonadId m => [TId] -> Type -> m TermType
genTermType scope s = do
    r <- TId s <$> identify "r"
    pty <- genPType (r:scope) s
    predTempl <- genPredTemplate (r:scope)
    return (r,pty,[],predTempl)

genPType :: MonadId m => [TId] -> Type -> m PType
genPType _ TInt = return PInt
genPType _ TBool = return PBool
genPType scope ty@(TPair t1 t2) = PPair ty <$> genPType scope t1 <*> genPType scope t2
genPType scope ty@(TFun ts t2) = do
    xs <- mapM (\t1 -> TId t1 <$> identify "x") ts
    let scope' = xs ++ scope
    ty_xs <- mapM (genPType scope') ts
    rty <- genTermType scope' t2
    predTempl <- genPredTemplate scope'
    return $ PFun ty (xs, ty_xs, [], predTempl) rty

updateFormula :: Formula -> [Formula] -> [Formula]
updateFormula phi@(Atom l arg _ ) fml = case (l,arg) of
    (SLiteral, CBool _) -> fml
    (SBinary, BinArg SAnd v1 v2) -> updateFormula v1 (updateFormula v2 fml)
    (SBinary, BinArg SOr  v1 v2) -> updateFormula v1 (updateFormula v2 fml)
    _ | phi `elem` fml -> fml
      | otherwise -> phi : fml

mergeTypeMap :: TypeMap -> TypeMap -> TypeMap
mergeTypeMap typeMap1 typeMap2 = M.unionWith f typeMap1 typeMap2
    where
        f (Left pty1) (Left pty2) = Left $ mergePType pty1 pty2
        f (Right tty1) (Right tty2) = Right $ mergeTermType tty1 tty2
        f _ _ = error "merge type map: sort mismatch"

mergePType :: PType -> PType -> PType
mergePType PInt PInt = PInt
mergePType PBool PBool = PBool
mergePType (PPair ty1 pty_fst1 pty_snd1) (PPair ty2 pty_fst2 pty_snd2) 
    | ty1 == ty2 = PPair ty1 (mergePType pty_fst1 pty_fst2) (mergePType pty_snd1 pty_snd2)
mergePType (PFun ty1 (xs_1,xsty_1,ps_1, pred_tmpl_arg) tau_1)
           (PFun ty2 (xs_2,xsty_2,ps_2, _            ) tau_2)
    | ty1 == ty2 = PFun ty1 (xs_1,xsty, ps, pred_tmpl_arg) tau
        where
        subst1 = M.fromList (zip xs_2 xs_1)
        xsty = zipWith mergePType xsty_1 (map (substPType subst1) xsty_2)
        ps = foldr (updateFormula . substFormula subst1) ps_1 ps_2
        tau = mergeTermType tau_1 tau_2
mergePType _ _ = error "mergePType: sort mismatch"   

mergeTermType :: TermType -> TermType -> TermType
mergeTermType (r_1,rty_1,qs_1, pred_tmpl) (r_2,rty_2,qs_2,_) = (r_1,rty,qs, pred_tmpl)
    where
    subst = M.singleton r_2 r_1
    rty = mergePType rty_1 (substPType subst rty_2)
    qs = foldr (updateFormula . substFormula subst) qs_1 qs_2

alphaConv :: TId -> TermType -> (PType, [Formula], PredTemplate)
alphaConv x (r, r_ty, ps, info) = (x_ty, ps', info')
    where
    subst = M.singleton r x
    x_ty = substPType subst r_ty
    ps' = map (substFormula subst) ps
    info' = substPredTemplate subst info

alphaConvFun :: [TId] -> PType -> PType
alphaConvFun ys (PFun sty sigma tau) = PFun sty sigma' tau'
    where
    (xs, xs_ty, ps, pred_tmpl) = sigma
    sigma' = (ys, ys_ty, ps', pred_tmpl') 
    subst = M.fromList $ zip xs ys
    ys_ty = map (substPType subst) xs_ty
    ps' = map (substFormula subst) ps
    pred_tmpl' = substPredTemplate subst pred_tmpl
    tau' = substTermType subst tau
alphaConvFun xs ty = 
    error $ "alphaConvFun: argument must be a function type" ++ show (xs,ty)

betaConv :: Value -> TermType -> (PType, [Formula], PredTemplate)
betaConv v (r, r_ty, ps, info) = (v_ty, ps', info')
    where
    subst = M.singleton r v
    v_ty = substVPType subst r_ty
    ps' = map (substVFormula subst) ps
    info' = substVPredTemplate subst info

appPType :: PType -> [Value] -> (([PType],[Formula],PredTemplate), TermType)
appPType (PFun _ sigma tau) vs = (sigma', tau')
    where
    tau' = substVTermType subst tau
    subst = M.fromList $ zip ys vs
    (ys,ys_ty, ps, pred_tmpl) = sigma
    sigma' = ( map (substVPType subst) ys_ty
             , map (substVFormula subst) ps
             , substVPredTemplate subst pred_tmpl)
appPType _ _ = error "appPType defined only for function types"

{- compute type environment for e2, given env |- let x = e in e2 : \tau -}
extendEnvByLet :: TypeMap -> Env -> TId -> LExp -> Env
extendEnvByLet tbl env x e = M.insert x x_ty env
    where
    defaultCase = case M.lookup (getUniqueKey e) tbl of
        Just (Right (alphaConv x -> (x_ty, _, _))) -> x_ty
        Just (Left _) -> 
            error $ "extendEnvByLet: expected a term type but found value type for key " 
                  ++ show (getUniqueKey e)
        Nothing -> error $ "extendEnvByLet: No type found for " 
                  ++ show (getUniqueKey e)
    x_ty = case lexpView e of
        LValue v -> case valueView v of
            VAtom av -> typeOfAtom env av
            VOther SLambda _ -> defaultCase
            VOther SPair _   -> defaultCase
        LOther SRand _ -> PInt
        LOther SApp (f, vs) -> x_ty
            where
            (x_ty, _, _) = alphaConv x $ snd $ appPType (env M.! f) vs
        LOther SBranch _ -> defaultCase
        LOther SFail _   -> defaultCase
        LOther SOmega _  -> defaultCase

    
