{-# LANGUAGE FlexibleContexts #-}
module Language.DMoCHi.ML.Syntax.PType where

import Language.DMoCHi.ML.Syntax.Type
import Language.DMoCHi.ML.Syntax.PNormal
import Language.DMoCHi.ML.PrettyPrint.PNormal
import Language.DMoCHi.Common.Id
import Language.DMoCHi.Common.Util
import qualified Data.Map as M
import qualified Data.IntMap as IM
import Text.PrettyPrint
import Control.Monad.Writer
import qualified Data.DList as DL

data PType = PInt | PBool
           | PFun Type ArgType TermType
           | PPair Type PType PType

type Env = M.Map Id PType
type Constraints = [Formula]
type Formula = AValue

type TermType = (Id, PType, [Formula])
type ArgType = ([Id],[PType],[Formula])

type TypeMap = IM.IntMap (Either PType TermType)
type ScopeMap = IM.IntMap [Id]

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
pprintTermType (x,pty_x,fml) = braces $ 
    text (name x) <+> colon <+> (pprintPType 0 pty_x) <+>
    text "|" <+> (hsep $ punctuate comma $ map (pprintA 0) fml)

pprintPTypeArg :: ArgType -> Doc
pprintPTypeArg (xs,pty_xs,fml) =
    braces $ 
        hsep (punctuate comma $ zipWith (\x pty_x -> text (name x) <+> colon <+> (pprintPType 0 pty_x)) xs pty_xs) <+>
        text "|" <+> (hsep $ punctuate comma $ map (pprintA 0) fml)

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

substTermType :: M.Map Id Id -> TermType -> TermType
substTermType subst (x,pty,ps) = (x, substPType subst' pty, map (substFormula subst') ps)
    where
    subst' = M.delete x subst

substPType :: M.Map Id Id -> PType -> PType
substPType subst = substVPType (fmap (Atomic . Var) subst)

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
substFormula subst = substVFormula (fmap (Atomic . Var) subst)

substVFormula :: M.Map Id Value -> Formula -> Formula
substVFormula subst = atomic . go where
    atomic (Atomic v) = v
    atomic _ = error "substVFormula: type error"
    go e = case e of
        Var x ->
            case M.lookup x subst of
                Just b -> b
                Nothing -> Atomic e
        CInt _ -> Atomic e
        CBool _ -> Atomic e
        -- Pair v1 v2 -> Pair (go v1) (go v2)
        Op op ->  case op of
            OpAdd v1 v2 -> Atomic $ Op $ (OpAdd `on` atomic) (go v1) (go v2)
            OpSub v1 v2 -> Atomic $ Op $ (OpSub `on` atomic) (go v1) (go v2)
            OpEq  v1 v2 -> Atomic $ Op $ (OpEq `on` atomic) (go v1) (go v2)
            OpLt  v1 v2 -> Atomic $ Op $ (OpLt `on` atomic) (go v1) (go v2)
            OpLte v1 v2 -> Atomic $ Op $ (OpLte `on` atomic) (go v1) (go v2)
            OpAnd v1 v2 -> Atomic $ Op $ (OpAnd `on` atomic) (go v1) (go v2)
            OpOr  v1 v2 -> Atomic $ Op $ (OpOr  `on` atomic) (go v1) (go v2)
            OpFst ty v  -> case go v of 
                Atomic av -> Atomic $ Op $ OpFst ty av
                Pair v1 _ -> v1
                Fun _ -> error "substVFormula: unexpected Fun"
            OpSnd ty v  -> case go v of
                Atomic av -> Atomic $ Op $ OpSnd ty av
                Pair _ v2 -> v2
                Fun _ -> error "substVFormula: unexpected Fun"
            OpNot v     -> Atomic $ Op $ (OpNot . atomic) (go v)
typeOfAValue :: Env -> AValue -> PType
typeOfAValue env = go where
    go v = case v of
        Var x -> env M.! x
        CInt _ -> PInt
        CBool _ -> PBool
--        Pair v1 v2 -> PPair (getType v) (go v1) (go v2)
        Op op -> case op of
            OpAdd _v1 _v2 -> PInt
            OpSub _v1 _v2 -> PInt
            OpEq  _v1 _v2 -> PBool
            OpLt  _v1 _v2 -> PBool
            OpLte _v1 _v2 -> PBool
            OpAnd _v1 _v2 -> PBool
            OpOr  _v1 _v2 -> PBool
            OpFst _ v   ->
                let PPair _ ty1 _ = go v in ty1
            OpSnd _ v   -> 
                let PPair _ _ ty2 = go v in ty2
            OpNot _v -> PBool

initTypeMap :: MonadId m => Program -> m (TypeMap,ScopeMap)
initTypeMap (Program fs t0) = do
    es <- execWriterT $ do
        let gather fv (Value v) = case v of
                Fun fdef -> gather (args fdef ++ fv) (body fdef)
                Pair v1 v2 -> gather fv (Value v1) >> gather fv (Value v2)
                Atomic _ -> return ()
            gather fv (Let _ x lv e) = do
                case lv of
                    LValue _ -> return ()
                    LApp _ _ _ vs -> mapM_ (gather fv . Value) vs
                    LExp i e' -> do
                        gather fv e'
                        ty <- genTermType (getType e')
                        tell (DL.singleton (i, Right ty, fv))
                    LRand -> return ()
                gather (x : fv) e
            gather fv (Assume _ _ e) = gather fv e
            gather _ (Fail _) = return ()
            {-
            gather fv (Fun fdef) = 
                -- DO NOT count tail functions,
                -- because their types are determined elsewhere
                gather (arg fdef : fv) (body fdef)
            -}
            gather fv (Branch _ _ e1 e2) = gather fv e1 >> gather fv e2
            gatherF fv f = do
                gather (args f ++ fv) (body f)
                ty <- genPType (getType f)
                tell (DL.singleton (ident f,Left ty, fv))
        let fv = map fst fs
        forM_ fs $ \(_, f) -> gatherF fv f
        gather fv t0
    let (es1,es2) = unzip [ ((i,v1),(i,v2)) | (i, v1, v2) <- DL.toList es ]
    return (IM.fromList es1, IM.fromList es2)

genTermType :: MonadId m => Type -> m TermType
genTermType s = do
    r <- Id s <$> freshId "r"
    pty <- genPType s
    return (r,pty,[])
genPType :: MonadId m => Type -> m PType
genPType TInt = return PInt
genPType TBool = return PBool
genPType ty@(TPair t1 t2) = PPair ty <$> genPType t1 <*> genPType t2
genPType ty@(TFun ts t2) = do
    xs <- mapM (\t1 -> Id t1 <$> freshId "x") ts
    r <- Id t2 <$> freshId "r"
    ty_xs <- mapM genPType ts
    ty_r <- genPType t2
    return $ PFun ty (xs, ty_xs, []) (r, ty_r, [])

updateFormula :: Formula -> [Formula] -> [Formula]
updateFormula phi fml = case phi of
    CBool _ -> fml
    -- decompose boolean combinations
    Op (OpAnd v1 v2) -> updateFormula v1 (updateFormula v2 fml)
    Op (OpOr v1 v2) -> updateFormula v1 (updateFormula v2 fml)
    _ | phi `elem` fml -> fml
      | otherwise -> phi : fml

mergeTypeMap :: TypeMap -> TypeMap -> TypeMap
mergeTypeMap typeMap1 typeMap2 = IM.unionWith f typeMap1 typeMap2
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
