{-# LANGUAGE LambdaCase #-}
module Language.DMoCHi.ML.Saturate where

import Control.Monad
import Control.Monad.Reader
import Language.DMoCHi.ML.Syntax.Type
import Language.DMoCHi.ML.Syntax.PNormal
import Language.DMoCHi.ML.Flow
--import Z3.Monad
import qualified Language.DMoCHi.ML.SMT as SMT
import Language.DMoCHi.ML.Syntax.PType hiding(Env)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.IntMap as IM
import qualified Data.HashTable.IO as H
import Data.IORef
import Text.PrettyPrint
import qualified Language.DMoCHi.ML.PrettyPrint.PNormal as Pretty

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
pprintEnv env = brackets $ vcat $ punctuate comma (map pprintAssoc (M.assocs env)) 
    where
    pprintAssoc (f,(pty,ity)) = text (name f) <+> text ":" <+> pprintPType 0 pty <+> text "|>" <+> pprintIType 0 ity

pprintIType :: Int -> IType -> Doc
pprintIType _ IInt = text "int"
pprintIType _ IBool = text "bool"
pprintIType p (IPair ity1 ity2) = 
    let d1 = pprintIType 1 ity1
        d2 = pprintIType 1 ity2
        d  = d1 <+> text "*" <+> d2
    in if p > 0 then parens d else d
pprintIType _ (IFun ty_assoc) = braces $ vcat $ punctuate comma $ 
    map (\(ty_xs, fml, ty_ret) -> 
            let d_xs = hsep $ punctuate comma (map (pprintIType 0) ty_xs)
                d_fml = text $ show fml
                d_ret = pprintITermType 0 ty_ret
            in braces (d_xs <+> text "|" <+> d_fml) <+> text "->" <+> d_ret) ty_assoc

pprintITermType :: Int -> ITermType -> Doc
pprintITermType _ IFail = text "fail"
pprintITermType _ (ITerm ty fml) = braces $ pprintIType 0 ty <+> text "|" <+> text (show fml)

instance Show BFormula where
    showsPrec p (BVar i) = showsPrec p i
    showsPrec _ (BConst True) = showString "true"
    showsPrec _ (BConst False) = showString "false"
    showsPrec p (BAnd b1 b2) = showParen (p > 2) $ showsPrec 2 b1 . showString " && " . showsPrec 2 b2
    showsPrec p (BOr b1 b2)  = showParen (p > 1) $ showsPrec 1 b1 . showString " || " . showsPrec 1 b2

type Env = M.Map Id (PType, IType)

type HashTable k v = H.BasicHashTable k v


data Context = Context { ctxFlowTbl :: HashTable Int (S.Set ([IType], BFormula))
                       , ctxTypeMap :: TypeMap
                       , ctxFlowMap :: FlowMap
                       , ctxUpdated :: IORef Bool }
type R a = ReaderT Context IO a


saturate :: TypeMap -> Program -> IO [ITermType]
saturate typeMap prog = do
    ctx <- Context <$> H.new
                   <*> pure typeMap
                   <*> flowAnalysis prog
                   <*> newIORef False
    let env0 = M.fromList [ (f, (pty, IFun [])) | (f, fdef) <- functions prog, 
                                                  let Left pty = typeMap IM.! (ident fdef) ]
        go env = do
            resetUpdate
            env' <- fmap M.fromList $ forM (functions prog) $ \(f, fdef) -> do
                let (pty,IFun as') = env M.! f
                IFun as <- calcTypeFunDef env (CBool True) fdef pty
                let as'' = merge as as'
                when (as' /= as'') update
                return (f, (pty,IFun as''))
            ts <- calcTypeTerm env' (CBool True) (mainTerm prog) (Id TInt "main", PInt, [])
            b <- ask >>= liftIO . readIORef . ctxUpdated
            if b 
              then go env'
              else return ts
    runReaderT (go env0) ctx

getFlow :: Int -> R [([IType], BFormula)]
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

addFlow :: Int -> ([IType], BFormula) -> R ()
addFlow i v = do
    tbl <- ctxFlowTbl <$> ask
    liftIO (H.lookup tbl i) >>= \case
        Just vs | S.member v vs -> return ()
                | otherwise -> liftIO (H.insert tbl i $! (S.insert v vs)) >> update
        Nothing -> liftIO (H.insert tbl i $! (S.singleton v)) >> update

calcTypeFunDef :: Env -> Formula -> FunDef -> PType -> R IType
calcTypeFunDef env fml (FunDef ident xs e) pty@(PFun _ argTy retTy) = do
    let (ys, ty_ys, ps) = argTy
        subst = M.fromList $ zip ys xs
        ps' = map (substFormula subst) ps
        retTy' = substTermType subst retTy
        ty_xs = map (substPType subst) ty_ys
    fs <- getFlow ident
    ity <- fmap (IFun . concat) $ forM fs $ \(thetas, phi) -> do
        let cond = fromBFormula ps' phi
            fml' = Op (OpAnd fml cond)
            env' = foldr (uncurry M.insert) env (zip xs (zip ty_xs thetas))
        b <- liftIO $ checkSat fml cond
        if b 
          then map ((,,) thetas phi) <$> calcTypeTerm env' fml' e retTy'
          else return []
    liftIO $ print $ text "calcTypeFunDef" $+$ 
            braces (
                text "env:" <+> pprintEnv env $+$
                text "assumption:" <+> Pretty.pprintA 0 fml $+$
                text "ident:" <+> int ident  $+$
                text "args:" <+> (brackets $ hsep $ punctuate comma (map (text . name) xs)) $+$
                text "ptype:" <+> pprintPType 0 pty $+$
                text "result:" <+> pprintIType 0 ity
            )
    return ity
calcTypeFunDef _ _ _ _ = error "calcTypeFunDef: non-function abstraction type is supplied"

calcTypeValue :: Env -> Formula -> Value -> PType -> R IType
calcTypeValue env fml _v ty = case _v of
    Atomic v -> do
        let (ty', ity) = calcTypeAValue env v
        if ty /= ty' then
            error $ "calcTypeValue: Abstraction type mismatch"
        else return ity
    Fun fdef -> calcTypeFunDef env fml fdef ty
    Pair v1 v2 -> do
        let PPair _ ty1 ty2 = ty
        i1 <- calcTypeValue env fml v1 ty1
        i2 <- calcTypeValue env fml v2 ty2
        return (IPair i1 i2)

calcTypeAValue :: Env -> AValue -> (PType,IType)
calcTypeAValue env _v  = case _v of
    Var x -> env M.! x
    CInt _ -> (PInt,IInt)
    CBool _ -> (PBool,IBool)
    Op (OpAdd _ _) -> (PInt,IInt)
    Op (OpSub _ _) -> (PInt,IInt)
    Op (OpEq  _ _) -> (PBool,IBool)
    Op (OpLt  _ _) -> (PBool,IBool)
    Op (OpLte _ _) -> (PBool,IBool)
    Op (OpAnd _ _) -> (PBool,IBool)
    Op (OpOr _ _) -> (PBool,IBool)
    Op (OpNot _) -> (PBool,IBool)
    Op (OpFst _ v) -> 
        (\(PPair _ p1 _, IPair i1 _) -> (p1,i1)) $ calcTypeAValue env v
    Op (OpSnd _ v) -> 
        (\(PPair _ _ p2, IPair _ i2) -> (p2,i2)) $ calcTypeAValue env v

-- Function: calcCondition fml ps 
-- assumption: fml is a satisfiable formula
-- assertion: phi |- fromBFormula ps ret
calcCondition :: Formula -> [Formula] -> IO BFormula
calcCondition _fml _ps = do
    phi <- go 1 _fml _ps
    print $ text "calcCondtion" $+$ 
            braces (
                text "assumption:" <+> Pretty.pprintA 0 _fml $+$
                text "predicates:" <+> (brackets $ hsep $ punctuate comma (map (Pretty.pprintA 0) _ps)) $+$
                text "result:"     <+> text (show phi)
            )
    return phi
    where
    go _ _ [] = return $ BConst True
    go i fml (p:ps) = do
        let np = Op (OpNot p)
        b1 <- checkSat fml p
        b2 <- checkSat fml np
        v1 <- if b1 then go (i + 1) (Op (OpAnd fml  p)) ps 
                    else return $ BConst False
        v2 <- if b2 then go (i + 1) (Op (OpAnd fml np)) ps 
                    else return $ BConst False
        if v1 == v2 then
            return v1
        else 
            return $ mkBOr (mkBAnd (BVar i) v1) (mkBAnd (BVar (-i)) v2)

fromBFormula :: [Formula] -> BFormula -> Formula
fromBFormula ps (BVar i) 
    | i < 0     = Op (OpNot (ps !! ((-i) - 1)))
    | otherwise = ps !! (i - 1)
fromBFormula _ (BConst b) = CBool b
fromBFormula ps (BOr p1 p2)  = Op (OpOr  (fromBFormula ps p1) (fromBFormula ps p2))
fromBFormula ps (BAnd p1 p2) = Op (OpAnd (fromBFormula ps p1) (fromBFormula ps p2))

checkSat :: Formula -> Formula -> IO Bool
checkSat p1 p2 = SMT.sat [Atomic p1, Atomic p2]

calcTypeTerm :: Env -> Formula -> Exp -> TermType -> R [ITermType]
calcTypeTerm env fml _e tau = case _e of
    Value v -> do
        let (r, rty, ps) = tau
        let subst = M.singleton r v
            rty' = substVPType subst rty
            ps'  = map (substVFormula subst) ps
        theta <- calcTypeValue env fml v rty'
        phi   <- liftIO $ calcCondition fml ps'
        return [ITerm theta phi]
    Let _ x (LValue av) e -> do
        let fml' = Op (OpAnd fml (Op (OpEq (Var x) av)))
            env' = M.insert x (calcTypeAValue env av) env
        calcTypeTerm env' fml' e tau
    Let _ x (LApp _ _ f vs) e -> do
        let (PFun _ argTy retTy, IFun assoc) = env M.! f
        let (ys, ptys, ps) = argTy
            subst = M.fromList $ zip ys vs
            ptys' = map (substVPType subst) ptys
            ps'   = map (substVFormula subst) ps
        phi <- liftIO $ calcCondition fml ps'
        thetas <- zipWithM (calcTypeValue env fml) vs ptys'
        flowMap <- ctxFlowMap <$> ask
        forM_ (flowMap M.! f) $ \ident -> addFlow ident (thetas,phi)

        fmap concatMerge $ forM assoc $ \(thetas', phi', iota) ->
            if thetas' == thetas && phi' == phi 
              then case iota of
                    IFail -> return [IFail]
                    ITerm rtheta rphi -> do
                        let (r, rty, qs) = retTy
                            subst' = M.insert r (Atomic (Var x)) subst
                            qs' = map (substVFormula subst') qs
                            cond = fromBFormula qs' rphi
                            fml' = Op (OpAnd fml cond)
                            rty' = substVPType subst' rty
                            env' = M.insert x (rty', rtheta) env
                        b <- liftIO $ checkSat fml cond
                        if b 
                          then calcTypeTerm env' fml' e tau
                          else return []
              else return []
    Let _ x (LExp ident e1) e2 -> do
        tbl <- ctxTypeMap <$> ask
        let Right tau@(y, ty_y, ps) = tbl IM.! ident
        iotas <- calcTypeTerm env fml e1 tau
        fmap concatMerge $ forM iotas $ \iota_y -> do
            case iota_y of
                IFail -> return [IFail]
                ITerm theta phi -> do
                    let subst = M.singleton y x
                        ps' = map (substFormula subst) ps
                        cond = fromBFormula ps' phi
                        fml' = Op (OpAnd fml cond)
                        ty_x = substPType subst ty_y
                        env' = M.insert x (ty_x, theta) env
                    b <- liftIO $ checkSat fml cond
                    if b
                      then calcTypeTerm env' fml' e2 tau
                      else return []
    Let _ x LRand e ->
        calcTypeTerm (M.insert x (PInt, IInt) env) fml e tau
    Assume _ cond e -> do
        b <- liftIO $ checkSat fml cond
        if b 
          then calcTypeTerm env (Op (OpAnd fml cond)) e tau
          else return []
    Fail _ -> do
        return [IFail]
    Branch _ _ e1 e2 -> do
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

