{-# LANGUAGE LambdaCase, BangPatterns #-}
module Language.DMoCHi.ML.Saturate where

import           Control.Monad
import           Control.Monad.Reader
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.HashTable.IO as H
import           Data.IORef
import           Text.Printf
import           Text.PrettyPrint.HughesPJClass

import           Language.DMoCHi.Common.Id
import           Language.DMoCHi.ML.Syntax.Type
import           Language.DMoCHi.ML.Syntax.PType hiding(Env)
import           Language.DMoCHi.ML.Syntax.PNormal
import           Language.DMoCHi.ML.Flow
import qualified Language.DMoCHi.ML.SMT as SMT

data IType = IInt | IBool | IPair IType IType | IFun [([IType], BFormula, ITermType)]
    deriving (Eq,Ord,Show)
data ITermType = IFail | ITerm IType BFormula
    deriving (Eq,Ord,Show)

data BFormula = BAnd BFormula BFormula | BOr BFormula BFormula | BVar Int | BConst Bool
    deriving (Eq,Ord)

mkBAnd, mkBOr :: BFormula -> BFormula -> BFormula
mkBAnd (BConst True) b = b
mkBAnd (BConst False) _ = BConst False
mkBAnd b (BConst True) = b
mkBAnd _ (BConst False) = BConst False
mkBAnd b1 b2 = BAnd b1 b2

mkBOr (BConst False) b = b
mkBOr (BConst True) _ = BConst True
mkBOr b (BConst False) = b
mkBOr _ (BConst True) = BConst True
mkBOr b1 b2 = BOr b1 b2

pprintEnv :: Env -> Doc
pprintEnv (penv, ienv) = brackets $ vcat $ punctuate comma (map pprintAssoc (M.keys penv)) 
    where
    pprintAssoc f = 
        let pty = penv M.! f
            ity = ienv M.! f
        in pPrint (name f) <+> text ":" <+> pPrint pty <+> text "|>" <+> pPrint ity

instance Pretty IType where
    pPrintPrec plevel prec ity =
        case ity of
            IInt  -> text "int"
            IBool -> text "bool"
            IPair ity1 ity2 -> maybeParens (prec > 0) d 
                where
                    d1 = pPrintPrec plevel 1 ity1
                    d2 = pPrintPrec plevel 1 ity2
                    d  = d1 <+> text "*" <+> d2
            IFun ty_assoc -> 
                braces $ vcat $ punctuate comma $ 
                    map (\(ty_xs, fml, ty_ret) -> 
                            let d_xs = hsep $ punctuate comma (map (pPrintPrec plevel 0) ty_xs)
                                d_fml = text $ show fml
                                d_ret = pPrintPrec plevel 0 ty_ret
                            in braces (d_xs <+> text "|" <+> d_fml) <+> text "->" <+> d_ret) ty_assoc
instance Pretty ITermType where
    pPrintPrec _ _ IFail = text "fail"
    pPrintPrec plevel _ (ITerm ty fml) = braces $ pPrintPrec plevel 0 ty <+> text "|" <+> text (show fml)

instance Show BFormula where
    showsPrec p (BVar i) = showsPrec p i
    showsPrec _ (BConst True) = showString "true"
    showsPrec _ (BConst False) = showString "false"
    showsPrec p (BAnd b1 b2) = showParen (p > 2) $ showsPrec 2 b1 . showString " && " . showsPrec 2 b2
    showsPrec p (BOr b1 b2)  = showParen (p > 1) $ showsPrec 1 b1 . showString " || " . showsPrec 1 b2

type Env = (PEnv, IEnv)
type PEnv = M.Map TId PType
type IEnv = M.Map TId IType

type HashTable k v = H.BasicHashTable k v

data Context = Context { ctxFlowTbl :: HashTable UniqueKey (S.Set ([IType], BFormula))
                       , ctxTypeMap :: TypeMap
                       , ctxFlowMap :: FlowMap
                       , ctxRtnTypeTbl :: HashTable UniqueKey (PType, [Formula]) 
                       , ctxArgTypeTbl  :: HashTable UniqueKey ([PType], [Formula]) 
                       , ctxUpdated :: IORef Bool
                       , ctxSMTCount :: IORef Int }
type R a = ReaderT Context IO a

calcContextV :: M.Map TId PType -> Value -> PType -> R ()
calcContextV env (Value l arg _ key) pty = 
    case (l, arg) of
        (SLiteral, _) -> return ()
        (SVar, _) -> return ()
        (SUnary, _) -> return ()
        (SBinary, _) -> return ()
        (SPair, (v1, v2)) -> do
            let PPair _ pty1 pty2 = pty
            calcContextV env v1 pty1
            calcContextV env v2 pty2
        (SLambda, (xs, e)) -> do
            let PFun _ (ys, ty_ys, ps) tau = pty
                subst = M.fromList (zip ys xs)
                ty_ys' = map (substPType subst) ty_ys
                ps'    = map (substFormula subst) ps
                tau'   = substTermType subst tau
                env'   = foldr (uncurry M.insert) env $ zip xs ty_ys'
            ctx <- ask
            liftIO $ H.insert (ctxArgTypeTbl ctx) key (ty_ys', ps')
            calcContextE env' e tau'

calcContextE :: M.Map TId PType -> Exp -> TermType -> R ()
calcContextE env (Exp l arg sty key) tau =
    let valueCase :: Value -> R () 
        valueCase v = do
            let (r, rty, ps) = tau
            let subst = M.singleton r v
                rty' = substVPType subst rty
                ps' = map (substVFormula subst) ps
            tbl <- ctxRtnTypeTbl <$> ask 
            calcContextV env v rty'
            liftIO (H.insert tbl key (rty', ps'))
    in case (l, arg) of
        (SLiteral, _) -> valueCase (Value l arg sty key)
        (SVar, _)     -> valueCase (Value l arg sty key)
        (SUnary, _)   -> valueCase (Value l arg sty key)
        (SBinary, _)  -> valueCase (Value l arg sty key)
        (SPair, _)    -> valueCase (Value l arg sty key)
        (SLambda, _)  -> valueCase (Value l arg sty key)
        (SLet, (x, LExp l1 arg1 sty1 key1, e2)) -> 
            let atomCase av = do
                    let ty_x = typeOfAtom env av
                    let env' = M.insert x ty_x env
                    ask >>= \ctx -> liftIO $ H.insert (ctxRtnTypeTbl ctx) key (ty_x, [])
                    calcContextE env' e2 tau
                exprCase e1 = do
                    ctx <- ask
                    let Right tau1@(y, ty_y, ps) = ctxTypeMap ctx M.! key1
                        subst = M.singleton y x
                        ps'   = map (substFormula subst) ps
                        ty_x  = substPType subst ty_y
                        env'  = M.insert x ty_x env
                    liftIO $ H.insert (ctxRtnTypeTbl ctx) key (ty_x, ps')
                    calcContextE env e1 tau1
                    calcContextE env' e2 tau
            in case (l1, arg1) of
                (SLiteral, _) -> atomCase (Atom l1 arg1 sty1)
                (SVar, _)     -> atomCase (Atom l1 arg1 sty1)
                (SBinary, _)  -> atomCase (Atom l1 arg1 sty1)
                (SUnary, _)   -> atomCase (Atom l1 arg1 sty1)
                (SApp, (f, vs)) -> do
                    let PFun _ argTy retTy = env M.! f
                        (ys, ptys, ps) = argTy
                        subst = M.fromList $ zip ys vs
                        ptys' = map (substVPType subst) ptys
                        ps'   = map (substVFormula subst) ps
                        (r, rty, qs) = retTy
                        subst' = M.insert r (cast (mkVar x)) subst
                        qs' = map (substVFormula subst') qs
                        rty' = substVPType subst' rty
                        env' = M.insert x rty' env
                    ctx <- ask
                    liftIO (H.insert (ctxArgTypeTbl ctx) key (ptys', ps'))
                    liftIO (H.insert (ctxRtnTypeTbl ctx) key (rty', qs'))
                    zipWithM_ (\v ty_v -> calcContextV env v ty_v) vs ptys'
                    calcContextE env' e2 tau
                (SPair, _)   -> exprCase (Exp l1 arg1 sty1 key1)
                (SLambda, _) -> exprCase (Exp l1 arg1 sty1 key1)
                (SFail, _)   -> exprCase (Exp l1 arg1 sty1 key1)
                (SOmega, _)  -> exprCase (Exp l1 arg1 sty1 key1)
                (SRand, _)   -> do
                    ask >>= \ctx -> liftIO (H.insert (ctxRtnTypeTbl ctx) key (PInt, []))
                    calcContextE (M.insert x PInt env) e2 tau
                (SBranch, _) -> exprCase (Exp l1 arg1 sty1 key1)
        (SAssume, (_, e)) -> calcContextE env e tau
        (SBranch, (e1, e2)) -> calcContextE env e1 tau >> calcContextE env e2 tau
        (SFail, _) -> return ()
        (SOmega, _) -> return ()

pprintContext :: Program -> R Doc
pprintContext prog = do
    d_fs <- forM (functions prog) $ \(f,key,xs,e) -> do
        Just (ty_xs, ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxArgTypeTbl ctx) key
        let d_args = vcat $ zipWith (\x ty_x -> parens $ pPrint (name x) 
                                            <+> colon 
                                            <+> pPrint ty_x) xs ty_xs
            d_ps = hsep $ punctuate comma $ map pPrint ps
        d_body <- pprintE e
        return $ text "let" <+> pPrint (name f) <+> (case ps of [] -> d_args <+> text "="
                                                                _  -> d_args $+$ text "|" <+> d_ps <+> text "=")
                            $+$ (nest 4 d_body <> text ";;")
    d_main <- pprintE (mainTerm prog)
    return $ vcat d_fs $+$ d_main 
    where 
    pprintE :: Exp -> R Doc
    pprintE (Exp l arg sty key) = 
        let valueCase :: Value -> R Doc
            valueCase v = do
                d_v <- pprintV 0 v
                Just (ty_r, ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
                return $ comment (ty_r, ps) $+$ d_v
        in case (l, arg) of
            (SLiteral, _) -> valueCase (Value l arg sty key)
            (SVar, _)     -> valueCase (Value l arg sty key)
            (SUnary, _)   -> valueCase (Value l arg sty key)
            (SBinary, _)  -> valueCase (Value l arg sty key)
            (SPair, _)    -> valueCase (Value l arg sty key)
            (SLambda, _)  -> valueCase (Value l arg sty key)
            (SLet, (x, e1@(LExp l1 arg1 sty1 key1), e2)) ->
                let exprCase d_e1 = do
                        Just (ty_x, ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxRtnTypeTbl ctx) key
                        d_e2 <- pprintE e2
                        let d_ps = hsep $ punctuate comma $ map pPrint ps
                        return $ 
                            text "let" <+> pPrint (name x)
                                       <+> (colon <+> pPrint ty_x <+> (case ps of [] -> empty
                                                                                  _  -> text "|" <+> d_ps) $+$
                                            text "=" <+> d_e1) 
                                       <+> text "in" 
                                       $+$ d_e2
                in case l1 of
                    SLiteral -> exprCase (pPrint e1)
                    SVar     -> exprCase (pPrint e1)
                    SUnary   -> exprCase (pPrint e1)
                    SBinary  -> exprCase (pPrint e1)
                    SPair    -> pprintE (Exp l1 arg1 sty1 key1) >>= exprCase
                    SLambda  -> pprintE (Exp l1 arg1 sty1 key1) >>= exprCase
                    SBranch  -> pprintE (Exp l1 arg1 sty1 key1) >>= exprCase
                    SFail    -> pprintE (Exp l1 arg1 sty1 key1) >>= exprCase
                    SOmega   -> pprintE (Exp l1 arg1 sty1 key1) >>= exprCase
                    SApp     -> do
                        let (f, vs) = arg1
                        Just (ty_vs, ps) <- ask >>= \ctx -> liftIO $ H.lookup (ctxArgTypeTbl ctx) key
                        vs' <- mapM (pprintV 0) vs
                        let d_e1 = pPrint (name f) <+> (case ps of [] -> d_vs
                                                                   _  -> d_vs $+$ text "|" <+> d_ps)
                            d_vs = vcat $ zipWith (\d_v ty_v -> parens $ d_v
                                                                     <+> text ":" 
                                                                     <+> pPrint ty_v) vs' ty_vs
                            d_ps = hsep $ punctuate comma $ map pPrint ps
                        exprCase d_e1 
                    SRand    -> exprCase (pPrint e1)
            (SAssume, (cond, e)) -> do
                d_e <- pprintE e
                return $ text "assume" <+> pPrintPrec prettyNormal 9 cond <> text ";" $+$ d_e
            (SBranch, (e1, e2)) -> do
                d_e1 <- pprintE e1
                d_e2 <- pprintE e2
                return $ parens d_e1 <+> text "<>" $+$ parens d_e2
            (SFail, _) -> return $ text "Fail"
            (SOmega, _) -> return $ text "Omega"
    pprintV :: Rational -> Value -> R Doc
    pprintV prec v@(Value l arg _ key) =
        case (l, arg) of
            (SLiteral, _) -> return $ pPrintPrec prettyNormal prec v
            (SVar, _) -> return $  pPrintPrec prettyNormal prec v
            (SBinary, _) -> return $ pPrintPrec prettyNormal prec v
            (SUnary, _) -> return $ pPrintPrec prettyNormal prec v
            (SPair, (v1, v2)) -> do
                d_v1 <- pprintV 0 v1
                d_v2 <- pprintV 0 v2
                return $ parens $ d_v1 <> comma <+> d_v2
            (SLambda, (xs, e)) -> do
                Just (ty_xs, ps) <- do
                    m <- ask >>= \ctx -> liftIO $ H.lookup (ctxArgTypeTbl ctx) key
                    case m of Just v -> return (Just v)
                              Nothing -> error (render (pPrint v))
                d_e <- pprintE e
                let d_args = vcat $ zipWith (\x ty_x -> parens $ pPrint (name x) 
                                                    <+> colon 
                                                    <+> pPrint ty_x) xs ty_xs
                    d_ps = hsep $ punctuate comma $ map pPrint ps
                return $ maybeParens (prec > 0) $ 
                    text "fun" <+> (case ps of 
                                        [] -> d_args <+> text "->"
                                        _  -> d_args $+$ text "|" <+> d_ps <+> text "->") $+$
                        nest 4 d_e

saturate :: TypeMap -> Program -> IO (Bool,[ITermType])
saturate typeMap prog = do
    ctx <- Context <$> H.new
                   <*> pure typeMap
                   <*> flowAnalysis prog
                   <*> H.new
                   <*> H.new
                   <*> newIORef False
                   <*> newIORef 0
    let env0 = ( M.fromList [ (f, pty) | (f, key, _, _) <- functions prog, let Left pty = typeMap M.! key ]
               , M.fromList [ (f, IFun []) | (f, _, _, _) <- functions prog] )
        go :: Env -> R [ITermType]
        go env = do
            resetUpdate
            ienv' <- fmap M.fromList $ forM (functions prog) $ \(f, key, xs, e) -> do
                let (pty,IFun as') = (fst env M.! f, snd env M.! f)
                IFun as <- calcTypeFunDef env (mkLiteral (CBool True)) (key,xs,e) pty
                let as'' = merge as as'
                when (as' /= as'') update
                return (f, IFun as'')
            let env' = (fst env, ienv')
            ts <- calcTypeTerm env' (mkLiteral (CBool True)) (mainTerm prog) (TId TInt (reserved "main"), PInt, [])
            b <- ask >>= liftIO . readIORef . ctxUpdated
            if b 
              then go env'
              else return ts

    ts <- flip runReaderT ctx $ do
        -- initialize context
        forM_ (functions prog) $ \(f, key, xs, e) -> 
            let pty = fst env0 M.! f in
            calcContextV (fst env0) (mkLambda xs e key) pty
        calcContextE (fst env0) (mainTerm prog) (TId TInt (reserved "main"), PInt, [])

        liftIO $ putStrLn "Abstraction Annotated Program"
        pprintContext prog >>= liftIO . print
        go env0
        
    let !b = IFail `elem` ts
    readIORef (ctxSMTCount ctx) >>= printf "[Fusion] Number of SMT Call = %d\n"
    return (b, ts)

getFlow :: UniqueKey -> R [([IType], BFormula)]
getFlow i = do
    tbl <- ctxFlowTbl <$> ask
    liftIO (H.lookup tbl i) >>= \case
        Just v -> return (S.toList v)
        Nothing -> return []

update :: R ()
update = do
    flag <- ctxUpdated <$> ask
    liftIO $ writeIORef flag True

resetUpdate :: R ()
resetUpdate = do
    flag <- ctxUpdated <$> ask
    liftIO $ writeIORef flag False

addFlow :: UniqueKey -> ([IType], BFormula) -> R ()
addFlow i v = do
    tbl <- ctxFlowTbl <$> ask
    liftIO (H.lookup tbl i) >>= \case
        Just vs | S.member v vs -> return ()
                | otherwise -> liftIO (H.insert tbl i $! (S.insert v vs)) >> update
        Nothing -> liftIO (H.insert tbl i $! (S.singleton v)) >> update

calcTypeFunDef :: Env -> Formula -> (UniqueKey, [TId], Exp) -> PType -> R IType
calcTypeFunDef env@(penv,ienv) fml (ident,xs,e) pty@(PFun _ argTy retTy) = do
    let (ys, ty_ys, ps) = argTy
        subst = M.fromList $ zip ys xs
        ps' = map (substFormula subst) ps
        retTy' = substTermType subst retTy
        ty_xs = map (substPType subst) ty_ys
    fs <- getFlow ident
    ity <- fmap (IFun . concat) $ forM fs $ \(thetas, phi) -> do
        let cond = fromBFormula ps' phi
            fml' = mkBin SAnd fml cond
            env' = ( foldr (uncurry M.insert) penv (zip xs ty_xs)
                   , foldr (uncurry M.insert) ienv (zip xs thetas))
        b <- checkSat fml cond
        if b 
          then map ((,,) thetas phi) <$> calcTypeTerm env' fml' e retTy'
          else return []
    liftIO $ print $ text "calcTypeFunDef" $+$ 
            braces (
                text "env:" <+> pprintEnv env $+$
                text "assumption:" <+> pPrint fml $+$
                text "ident:" <+> pPrint ident  $+$
                text "args:" <+> (brackets $ hsep $ punctuate comma (map pPrint xs)) $+$
                text "ptype:" <+> pPrint pty $+$
                text "result:" <+> pPrint ity
            )
    return ity
calcTypeFunDef _ _ _ _ = error "calcTypeFunDef: non-function abstraction type is supplied"

calcTypeValue :: Env -> Formula -> Value -> PType -> R IType
calcTypeValue env fml (Value l arg sty key) ty = 
    let atomCase :: Atom -> R IType
        atomCase v = do
            let (ty', ity) = calcTypeAtom env v
            if ty /= ty' then
                error $ "calcTypeValue: Abstraction type mismatch"
            else return ity
    in case (l,arg) of
        (SLiteral, _) -> atomCase (Atom l arg sty)
        (SVar, _)     -> atomCase (Atom l arg sty)
        (SBinary, _)  -> atomCase (Atom l arg sty)
        (SUnary, _)   -> atomCase (Atom l arg sty)
        (SLambda, (xs,e)) -> calcTypeFunDef env fml (key,xs, e) ty
        (SPair, (v1, v2)) -> do
            let PPair _ ty1 ty2 = ty
            i1 <- calcTypeValue env fml v1 ty1
            i2 <- calcTypeValue env fml v2 ty2
            return (IPair i1 i2)



calcTypeAtom :: Env -> Atom -> (PType,IType)
calcTypeAtom env (Atom l arg _)   = case (l, arg) of
    (SLiteral, CInt _)  -> (PInt, IInt)
    (SLiteral, CBool _) -> (PInt, IInt)
    (SVar, x) -> ((fst env) M.! x, (snd env) M.! x)
    (SBinary, BinArg op _ _) -> case op of
        SAdd -> (PInt, IInt)
        SSub -> (PInt, IInt)
        SEq -> (PBool, IBool)
        SLt -> (PBool, IBool)
        SLte -> (PBool, IBool)
        SAnd -> (PBool, IBool)
        SOr -> (PBool, IBool)
    (SUnary, UniArg op v) -> case op of
        SFst -> (\(PPair _ p1 _, IPair i1 _) -> (p1,i1)) $ calcTypeAtom env v
        SSnd -> (\(PPair _ _ p2, IPair _ i2) -> (p2,i2)) $ calcTypeAtom env v
        SNeg -> (PInt, IInt)
        SNot -> (PBool, IBool)

-- Function: calcCondition fml ps 
-- assumption: fml is a satisfiable formula
-- assertion: phi |- fromBFormula ps ret
calcCondition :: Formula -> [Formula] -> R BFormula
calcCondition _fml _ps = do
    phi <- go 1 _fml _ps
    liftIO $ print $ text "calcCondtion" $+$ 
            braces (
                text "assumption:" <+> pPrint _fml $+$
                text "predicates:" <+> (brackets $ hsep $ punctuate comma (map pPrint _ps)) $+$
                text "result:"     <+> text (show phi)
            )
    return phi
    where
    go _ _ [] = return $ BConst True
    go i fml (p:ps) = do
        let np = mkUni SNot p
        b1 <- checkSat fml p
        b2 <- checkSat fml np
        v1 <- if b1 then go (i + 1) (mkBin SAnd fml  p) ps 
                    else return $ BConst False
        v2 <- if b2 then go (i + 1) (mkBin SAnd fml np) ps 
                    else return $ BConst False
        if v1 == v2 then
            return v1
        else 
            return $ mkBOr (mkBAnd (BVar i) v1) (mkBAnd (BVar (-i)) v2)

fromBFormula :: [Formula] -> BFormula -> Formula
fromBFormula ps (BVar i) 
    | i < 0     = mkUni SNot (ps !! ((-i) - 1))
    | otherwise = ps !! (i - 1)
fromBFormula _  (BConst b)   = mkLiteral (CBool b)
fromBFormula ps (BOr p1 p2)  = mkBin SOr  (fromBFormula ps p1) (fromBFormula ps p2)
fromBFormula ps (BAnd p1 p2) = mkBin SAnd (fromBFormula ps p1) (fromBFormula ps p2)

checkSat :: Formula -> Formula -> R Bool
checkSat p1 p2 = do
    ask >>= \ctx -> liftIO $ modifyIORef' (ctxSMTCount ctx) succ 
    liftIO $ SMT.sat [cast p1, cast p2]

calcTypeTerm :: Env -> Formula -> Exp -> TermType -> R [ITermType]
calcTypeTerm env fml (Exp l arg sty key) tau = 
    let valueCase :: Value -> R [ITermType]
        valueCase v = do
            let (r, rty, ps) = tau
            let subst = M.singleton r v
                rty' = substVPType subst rty
                ps'  = map (substVFormula subst) ps
            theta <- calcTypeValue env fml v rty'
            phi   <- calcCondition fml ps'
            return [ITerm theta phi]
    in
    case (l, arg) of
        (SLiteral, _) -> valueCase (Value l arg sty key)
        (SVar, _)     -> valueCase (Value l arg sty key)
        (SUnary, _)   -> valueCase (Value l arg sty key)
        (SBinary, _)  -> valueCase (Value l arg sty key)
        (SPair, _)    -> valueCase (Value l arg sty key)
        (SLambda, _)  -> valueCase (Value l arg sty key)
        (SLet, (x,LExp l1 arg1 sty1 key1,e2)) ->
            let atomCase av = do
                    let fml' = mkBin SAnd fml (mkBin SEq (mkVar x) av)
                        (ty_av, ity_av) = calcTypeAtom env av
                        env' = (M.insert x ty_av (fst env), M.insert x ity_av (snd env))
                    calcTypeTerm env' fml' e2 tau
                exprCase e1 = do
                    tbl <- ctxTypeMap <$> ask
                    let Right tau1@(y, ty_y, ps) = tbl M.! key1
                    iotas <- calcTypeTerm env fml e1 tau1
                    fmap concatMerge $ forM iotas $ \iota_y -> do
                        case iota_y of
                            IFail -> return [IFail]
                            ITerm theta phi -> do
                                let subst = M.singleton y x
                                    ps'  = map (substFormula subst) ps
                                    cond = fromBFormula ps' phi
                                    fml' = mkBin SAnd fml cond
                                    ty_x = substPType subst ty_y
                                    env' = (M.insert x ty_x (fst env), M.insert x theta (snd env))
                                b <- checkSat fml cond
                                if b
                                  then calcTypeTerm env' fml' e2 tau
                                  else return []
            in case (l1, arg1) of
                (SLiteral, _) -> atomCase (Atom l1 arg1 sty1)
                (SVar, _)     -> atomCase (Atom l1 arg1 sty1)
                (SBinary, _)  -> atomCase (Atom l1 arg1 sty1)
                (SUnary, _)   -> atomCase (Atom l1 arg1 sty1)
                (SApp, (f,vs)) -> do
                    let PFun _ argTy retTy = fst env M.! f
                        IFun assoc = snd env M.! f
                    let (ys, ptys, ps) = argTy
                        subst = M.fromList $ zip ys vs
                        ptys' = map (substVPType subst) ptys
                        ps'   = map (substVFormula subst) ps
                    phi <- calcCondition fml ps'
                    thetas <- zipWithM (calcTypeValue env fml) vs ptys'
                    flowMap <- ctxFlowMap <$> ask
                    forM_ (flowMap M.! f) $ \ident -> addFlow ident (thetas,phi)

                    fmap concatMerge $ forM assoc $ \(thetas', phi', iota) ->
                        if thetas' == thetas && phi' == phi 
                          then case iota of
                                IFail -> return [IFail]
                                ITerm rtheta rphi -> do
                                    let (r, rty, qs) = retTy
                                        subst' = M.insert r (cast (mkVar x)) subst
                                        qs' = map (substVFormula subst') qs
                                        cond = fromBFormula qs' rphi
                                        fml' = mkBin SAnd fml cond
                                        rty' = substVPType subst' rty
                                        env' = ( M.insert x rty' (fst env)
                                               , M.insert x rtheta (snd env))
                                    b <- checkSat fml cond
                                    if b 
                                      then calcTypeTerm env' fml' e2 tau
                                      else return []
                          else return []
                (SPair, _)   -> exprCase (Exp l1 arg1 sty1 key1)
                (SLambda, _) -> exprCase (Exp l1 arg1 sty1 key1)
                (SBranch, _) -> exprCase (Exp l1 arg1 sty1 key1)
                (SFail, _)   -> exprCase (Exp l1 arg1 sty1 key1)
                (SOmega, _)  -> exprCase (Exp l1 arg1 sty1 key1)
                (SRand, _)   -> calcTypeTerm ( M.insert x PInt (fst env)
                                             , M.insert x IInt (snd env)) fml e2 tau
        (SAssume, (cond,e)) -> do
            b <- checkSat fml cond
            if b 
              then calcTypeTerm env (mkBin SAnd fml cond) e tau
              else return []
        (SFail,_ ) -> return [IFail]
        (SOmega,_ ) -> return []
        (SBranch, (e1,e2)) -> do
            ts1 <- calcTypeTerm env fml e1 tau
            ts2 <- calcTypeTerm env fml e2 tau
            return $ merge ts1 ts2

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys) = case compare x y of
    EQ -> x : merge xs ys
    LT -> x : merge xs (y:ys)
    GT -> y : merge (x:xs) ys

concatMerge :: Ord a => [[a]] -> [a]
concatMerge [] = []
concatMerge [x] = x
concatMerge (x:y:xs) = concatMerge (merge x y:xs)

