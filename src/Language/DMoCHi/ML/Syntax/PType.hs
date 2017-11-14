{-# LANGUAGE FlexibleContexts, DataKinds, GADTs, Rank2Types, BangPatterns #-}
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
import Debug.Trace

data PType = PInt | PBool
           | PFun Type ArgType TermType
           | PPair Type PType PType

instance HasType PType where
    getType PInt = TInt
    getType PBool = TBool
    getType (PFun sty _ _) = sty
    getType (PPair sty _ _) = sty

mkPFun :: ArgType -> TermType -> PType
mkPFun argTy@(xs,_,_) termTy@(TId ty_r _,_,_) = PFun (TFun ty_xs ty_r) argTy termTy
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

type TermType = (Id, PType, [Formula])
type ArgType = ([Id],[PType],[Formula])

type TypeMap = M.Map UniqueKey (Either PType TermType)
type ScopeMap = M.Map UniqueKey [Id]

instance Eq PType where
    PInt == PInt = True
    PBool == PBool = True
    (PFun ty_1 (xs_1,xsty_1,ps_1) (r_1,rty_1,qs_1)) == (PFun ty_2 (xs_2,xsty_2,ps_2) (r_2,rty_2,qs_2)) =
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


pprintTermType :: TermType -> Doc
pprintTermType (TId _ name,pty_x,fml) = braces $ 
    pPrint name <+> colon <+> (pprintPType 0 pty_x) <+>
    text "|" <+> (hsep $ punctuate comma $ map pPrint fml)

pprintPTypeArg :: ArgType -> Doc
pprintPTypeArg (xs,pty_xs,fml) =
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

substTermType :: M.Map Id Id -> TermType -> TermType
substTermType subst (x,pty,ps) = (x, substPType subst' pty, map (substFormula subst') ps)
    where
    subst' = M.delete x subst

substPType :: M.Map Id Id -> PType -> PType
substPType subst = substVPType (fmap (cast . mkVar) subst)

substVPType :: M.Map Id Value -> PType -> PType
substVPType _ PInt = PInt
substVPType _ PBool = PBool
substVPType subst (PPair t t1 t2) = 
    PPair t (substVPType subst t1) (substVPType subst t2)
substVPType subst (PFun ty (xs,ty_xs,ps) (r,ty_r,qs)) = 
    PFun ty (xs,ty_xs',ps') (r,ty_r',qs')
    where
    subst1 = foldr M.delete subst xs
    subst2 = M.delete r subst1
    ty_xs' = map (substVPType subst1) ty_xs
    ps' = map (substVFormula subst1) ps
    ty_r' = substVPType subst2 ty_r
    qs' = map (substVFormula subst2) qs

substFormula :: M.Map Id Id -> Formula -> Formula
substFormula subst = substVFormula (fmap (cast . mkVar) subst)

substVFormula :: M.Map Id Value -> Formula -> Formula
substVFormula subst = atomic . go where
    atomic v = case atomOfValue v of
        Just a -> a
        Nothing -> error "substVFormula: type error"
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
            case op of
            SAdd -> cast $ mkBin op v1' v2'
            SSub -> cast $ mkBin op v1' v2'
            SDiv -> cast $ mkBin op v1' v2'
            SMul -> cast $ mkBin op v1' v2'
            SEq  -> cast $ mkBin op v1' v2'
            SLt  -> cast $ mkBin op v1' v2'
            SLte -> cast $ mkBin op v1' v2'
            SAnd -> cast $ mkBin op v1' v2'
            SOr  -> cast $ mkBin op v1' v2'
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

initTypeMap :: forall m. MonadId m => Program -> m (TypeMap,ScopeMap)
initTypeMap (Program fs t0) = do
    es <- execWriterT $ do
        let gatherE :: [TId] -> Exp -> WriterT (DL.DList (UniqueKey, Either PType TermType, [TId])) m ()
            gatherE fv (Exp l arg _ _) = gather (Proxy :: Proxy Exp) fv l arg
            gatherV :: [TId] -> Value -> WriterT (DL.DList (UniqueKey, Either PType TermType, [TId])) m ()
            gatherV fv (Value l arg _ _) = gather (Proxy :: Proxy Value) fv l arg
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
                    gather (Proxy :: Proxy LExp) fv l1 arg1
                    let genType :: WriterT (DL.DList (UniqueKey, Either PType TermType, [TId])) m ()
                        genType = genTermType sty1 >>= \ty -> tell (DL.singleton (key1, Right ty, fv))
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
                        ty <- genPType (getType v) 
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
                ty <- genPType sty 
                tell (DL.singleton (key,Left ty, fv))
        let fv = map (\(f,_,_,_) -> f) fs
        mapM_ (gatherF fv) fs
        gatherE fv t0
    let (es1,es2) = unzip [ ((i,v1),(i,v2)) | (i, v1, v2) <- DL.toList es ]
    return (M.fromList es1, M.fromList es2)

genTermType :: MonadId m => Type -> m TermType
genTermType s = do
    r <- TId s <$> identify "r"
    pty <- genPType s
    return (r,pty,[])
genPType :: MonadId m => Type -> m PType
genPType TInt = return PInt
genPType TBool = return PBool
genPType ty@(TPair t1 t2) = PPair ty <$> genPType t1 <*> genPType t2
genPType ty@(TFun ts t2) = do
    xs <- mapM (\t1 -> TId t1 <$> identify "x") ts
    r <- TId t2 <$> identify "r"
    ty_xs <- mapM genPType ts
    ty_r <- genPType t2
    return $ PFun ty (xs, ty_xs, []) (r, ty_r, [])

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
mergePType (PFun ty1 (xs_1,xsty_1,ps_1) (r_1,rty_1,qs_1)) 
           (PFun ty2 (xs_2,xsty_2,ps_2) (r_2,rty_2,qs_2))
    | ty1 == ty2 = PFun ty1 (xs_1,xsty, ps) (r_1,rty,qs)
        where
        subst1 = M.fromList (zip xs_2 xs_1)
        subst2 = M.insert r_2 r_1 subst1
        xsty = zipWith mergePType xsty_1 (map (substPType subst1) xsty_2)
        ps = foldr (updateFormula . substFormula subst1) ps_1 ps_2
        rty = mergePType rty_1 (substPType subst2 rty_2)
        qs = foldr (updateFormula . substFormula subst2) qs_1 qs_2 
mergePType _ _ = error "mergePType: sort mismatch"   

mergeTermType :: TermType -> TermType -> TermType
mergeTermType (r_1,rty_1,qs_1) (r_2,rty_2,qs_2) = (r_1,rty,qs)
    where
    subst = M.singleton r_2 r_1
    rty = mergePType rty_1 (substPType subst rty_2)
    qs = foldr (updateFormula . substFormula subst) qs_1 qs_2
