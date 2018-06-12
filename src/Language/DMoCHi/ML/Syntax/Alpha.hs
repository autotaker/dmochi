{-# LANGUAGE UndecidableInstances #-}
module Language.DMoCHi.ML.Syntax.Alpha(alpha,AlphaError, Exp(..), Program(..), refresh, Var) where
import qualified Language.DMoCHi.ML.Syntax.UnTyped as U
import Language.DMoCHi.ML.Syntax.UnTyped(Type(..), TypeScheme, SynonymDef(..))
import Language.DMoCHi.ML.Syntax.Base
import Language.DMoCHi.Common.Id hiding(identify, refresh)
import Language.DMoCHi.Common.Util
import qualified Language.DMoCHi.Common.Id as Id(identify, refresh)
import Control.Monad.Except
import Control.Monad.Reader
import qualified Data.Map as M
import Text.PrettyPrint.HughesPJClass
import Data.List(sort,group)

data AlphaError = UndefinedVariable String
                | MultipleDefinition [String]
                deriving(Eq)

data Exp a where
    Exp :: (WellFormed l (Exp a) arg, Supported l (Labels (Exp a))) => 
      !(SLabel l) -> arg -> !(a, UniqueKey) -> Exp a


data Program a = Program { functions :: [(Var a, TypeScheme, Exp a)]
                         , synonyms :: [SynonymDef]
                         , mainTerm :: Exp a}
type Var a = U.AnnotVar (Id String) a

type instance Ident (Exp a) = Var a
type instance Labels (Exp a) = AllLabels
type instance BinOps (Exp a) = AllBinOps
type instance UniOps (Exp a) = AllUniOps

instance HasUniqueKey (Exp a) where
    getUniqueKey (Exp _ _ (_,key)) = key

instance Show AlphaError where
    show (UndefinedVariable s) = "UndefinedVariable: "++s
    show (MultipleDefinition fs) = "MultipleDefinition: "++show fs

instance Pretty (Var a) => Pretty (Exp a) where
    pPrintPrec plevel prec (Exp l arg (_, key)) = 
        if plevel == prettyNormal then doc else comment key <+> doc
            where
            pp :: WellFormedPrinter (Exp a)
            pp = WellFormedPrinter {
                   pPrintExp = pPrintPrec,
                   pPrintIdent = pPrintPrec
                 }
            doc = genericPPrint pp plevel prec l arg

instance Pretty (Var a) => Pretty (Program a) where
    pPrintPrec plevel _ (Program fs syns t) =
        text "(* functions *)" $+$ 
        vcat (map (\(f,ty,e) -> 
            text "let" <+> pPrintPrec plevel 0 f <+> colon <+> pPrintPrec plevel 0 ty <+> equals $+$
            nest 4 (pPrintPrec plevel 0 e <> text ";;")) fs) $+$
        text "(* synonyms *)" $+$
        vcat (map (\syn -> 
            let dargs = case typVars syn of
                    [] -> empty
                    [x] -> text ('\'':x)
                    xs  -> parens $ hsep $ punctuate comma (map (text . ('\'':)) xs)
            in
            text "type" <+> dargs <+> text (synName syn) <+> equals 
                        <+> pPrintPrec plevel 0 (synDef syn) <> text ";;") syns) $+$
        text "(*main*)" $+$
        pPrintPrec plevel 0 t

instance Functor Exp where
    fmap f (Exp l arg (a, key)) = case (l, arg) of
        (SLiteral, _) -> Exp l arg (f a, key)
        (SVar,     x) -> Exp l (fmap f x) (f a, key)
        (SFail,    _) -> Exp l arg (f a, key)
        (SOmega,   _) -> Exp l arg (f a, key)
        (SRand,    _) -> Exp l arg (f a, key)
        (SBinary,  BinArg op e1 e2) -> Exp l (BinArg op (fmap f e1) (fmap f e2)) (f a, key)
        (SUnary,   UniArg op e1) -> Exp l (UniArg op (fmap f e1)) (f a, key)
        (SPair,    (e1, e2)) -> Exp l (fmap f e1, fmap f e2) (f a, key)
        (SLambda,  (xs, e1)) -> Exp l (map (fmap f) xs, fmap f e1) (f a, key)
        (SApp,     (e1, es)) -> Exp l (fmap f e1, map (fmap f) es) (f a, key)
        (SLet,     (x, e1, e2)) -> Exp l (fmap f x, fmap f e1, fmap f e2) (f a, key)
        (SLetRec,  (gs, e2)) -> Exp l (map (\(g,e) -> (fmap f g, fmap f e)) gs, fmap f e2) (f a, key)
        (SAssume,  (e1, e2)) -> Exp l (fmap f e1, fmap f e2) (f a, key)
        (SMark, (x, e)) -> Exp l (fmap f x, fmap f e) (f a, key)
        (SIf,      (e1, e2, e3)) -> Exp l (fmap f e1, fmap f e2, fmap f e3) (f a, key)
        (SBranch,  (e1, e2)) -> Exp l (fmap f e1, fmap f e2) (f a, key)

instance Foldable Exp where
    foldMap f (Exp l arg (a, _)) = case (l, arg) of
        (SLiteral, _) -> f a
        (SVar,     x) -> f a `mappend` foldMap f x
        (SFail,    _) -> f a
        (SOmega,   _) -> f a
        (SRand,    _) -> f a
        (SBinary,  BinArg _ e1 e2) -> f a `mappend` foldMap f e1 `mappend` foldMap f e2
        (SUnary,   UniArg _ e1)    -> f a `mappend` foldMap f e1
        (SPair,    (e1, e2)) -> f a `mappend` foldMap f e1 `mappend` foldMap f e2
        (SLambda,  (xs, e1)) -> f a `mappend` foldMap (foldMap f) xs `mappend` foldMap f e1 
        (SApp,     (e1, es)) -> f a `mappend` foldMap f e1 `mappend` foldMap (foldMap f) es
        (SLet,     (x, e1, e2)) -> f a `mappend` foldMap f x `mappend` foldMap f e1 `mappend` foldMap f e2
        (SLetRec,  (gs, e2)) -> f a 
                                `mappend` mconcat (map (\(g, e) -> foldMap f g `mappend` foldMap f e) gs) 
                                `mappend` foldMap f e2
        (SAssume,  (e1, e2)) -> f a `mappend` foldMap f e1 `mappend` foldMap f e2
        (SIf,      (e1, e2, e3)) -> f a `mappend` foldMap f e1 `mappend` foldMap f e2 `mappend` foldMap f e3
        (SBranch,  (e1, e2)) -> f a `mappend` foldMap f e1 `mappend` foldMap f e2
        (SMark,    (x, e)) -> f a `mappend` foldMap f x `mappend` foldMap f e

instance Traversable Exp where
    traverse f (Exp l arg (a, key)) = case (l, arg) of
        (SLiteral, _) -> (\b -> Exp l arg (b,key)) <$> f a
        (SFail,    _) -> (\b -> Exp l arg (b,key)) <$> f a
        (SOmega,   _) -> (\b -> Exp l arg (b,key)) <$> f a
        (SRand,    _) -> (\b -> Exp l arg (b,key)) <$> f a
        (SVar,     x) -> (\b y -> Exp l y (b,key)) <$> f a <*> traverse f x
        (SBinary,  BinArg op e1 e2) -> 
            (\b e1' e2' -> Exp l (BinArg op e1' e2') (b,key))
                <$> f a 
                <*> traverse f e1 
                <*> traverse f e2
        (SUnary,  UniArg op e1) -> 
            (\b e1' -> Exp l (UniArg op e1') (b, key)) 
                <$> f a 
                <*> traverse f e1 
        (SPair, (e1, e2)) -> 
            (\b e1' e2' -> Exp l (e1',e2') (b, key)) 
                <$> f a 
                <*> traverse f e1 
                <*> traverse f e2
        (SLambda, (xs, e1)) ->
            (\b ys e1' -> Exp l (ys, e1') (b, key))
                <$> f a
                <*> traverse (traverse f) xs
                <*> traverse f e1
        (SApp, (e, es)) ->
            (\b e' es' -> Exp l (e', es') (b, key))
                <$> f a
                <*> traverse f e
                <*> traverse (traverse f) es
        (SLet, (x, e1, e2)) ->
            (\b y e1' e2' -> Exp l (y, e1', e2') (b, key))
                <$> f a
                <*> traverse f x
                <*> traverse f e1
                <*> traverse f e2
        (SLetRec, (gs, e2)) ->
            (\b gs' e2' -> Exp l (gs', e2') (b, key))
                <$> f a
                <*> traverse (\(g,e) -> (,) <$> traverse f g <*> traverse f e) gs
                <*> traverse f e2
        (SAssume, (e1, e2)) ->
            (\b e1' e2' -> Exp l (e1',e2') (b, key)) 
                <$> f a 
                <*> traverse f e1 
                <*> traverse f e2
        (SIf, (e1, e2, e3)) ->
            (\b e1' e2' e3' -> Exp l (e1',e2',e3') (b, key)) 
                <$> f a 
                <*> traverse f e1 
                <*> traverse f e2
                <*> traverse f e3
        (SBranch, (e1, e2)) ->
            (\b e1' e2' -> Exp l (e1',e2') (b, key)) 
                <$> f a 
                <*> traverse f e1 
                <*> traverse f e2
        (SMark, (x, e)) ->
            (\b x' e' -> Exp l (x', e') (b, key))
                <$> f a
                <*> traverse f x
                <*> traverse f e

type M a = ReaderT (M.Map String (Var (Maybe Type))) (ExceptT AlphaError FreshLogging) a

alpha :: U.Program -> ExceptT AlphaError FreshLogging (Program (Maybe Type))
alpha (U.Program fs syns _ t0) = do
    env <- M.fromList <$> mapM (\(x,_,_) -> fmap (U.varName x,) (identify x)) fs
    when (M.size env /= length fs) $ do
        let fs' = map head $ filter ((>1).length) $ group $ sort $ map (\(x,_,_) -> U.varName x) fs
        throwError $ MultipleDefinition fs'
    flip runReaderT env $ do
        fs' <- forM fs $ \(x,p,e) -> (,,) <$> rename x <*> lift (renameS p) <*> renameE e
        t0' <- renameE t0
        return $ Program fs' syns t0'

refresh :: MonadId m => U.AnnotVar (Id String) a -> m (U.AnnotVar (Id String) a)
refresh (U.V x ty) = U.V <$> Id.refresh x <*> pure ty

rename :: U.AnnotVar String (Maybe Type) -> M (U.AnnotVar (Id String) (Maybe Type))
rename x = do
    env <- ask
    let m = M.lookup (U.varName x) env
    case m of
        Nothing -> throwError $ UndefinedVariable (U.varName x)
        Just x' -> return x'

identify :: MonadId m => U.AnnotVar String a -> m (U.AnnotVar (Id String) a)
identify (U.V "" ty) = U.V <$> Id.identify "tmp" <*> pure ty
identify (U.V x ty) = U.V <$> Id.identify x <*> pure ty

renameS :: U.TypeScheme -> ExceptT AlphaError FreshLogging  U.TypeScheme
renameS (U.TypeScheme tvars ty) = do
    tvars' <- mapM freshId tvars
    ty' <- subst (M.fromList $ zip tvars tvars') ty
    return $ U.TypeScheme tvars' ty'

subst :: M.Map String String -> U.Type -> ExceptT AlphaError FreshLogging U.Type
subst rho = go
    where
    go U.TInt  = pure U.TInt
    go U.TBool = pure U.TBool
    go U.TUnit = pure U.TUnit
    go (U.TVar x) = case M.lookup x rho of
        Just v -> return (U.TVar v)
        Nothing -> throwError $ UndefinedVariable x
    go (U.TPair ty1 ty2) = U.TPair <$> (go ty1) <*> (go ty2)
    go (U.TFun ts ty) = U.TFun <$> (mapM go ts) <*> (go ty)
    go (U.TSyn ts synName) = U.TSyn <$> (mapM go ts) <*> pure synName


renameE :: U.Exp -> M (Exp (Maybe Type))
renameE (U.Exp label arg annot) = do
    key <- freshKey
    case (label, arg) of
        (SLiteral, arg) -> return $ Exp label arg (annot,key)
        (SVar, x) -> Exp label <$> rename x <*> pure (annot,key)
        (SBinary, BinArg op e1 e2) -> Exp label <$> (BinArg op <$> renameE e1 <*> renameE e2) <*> pure (annot,key)
        (SUnary, UniArg op e) -> Exp label <$> (UniArg op <$> renameE e) <*> pure (annot,key)
        (SPair, (e1, e2)) -> Exp label <$> ((,) <$> renameE e1 <*> renameE e2) <*> pure (annot,key)
        (SLambda, (xs, e)) -> Exp label <$> register' xs (renameE e) <*> pure (annot,key)
        (SApp, (e, es)) -> Exp label <$> ((,) <$> renameE e <*> mapM renameE es) <*> pure (annot,key)
        (SLet, (x, e1, e2)) -> do
            e1' <- renameE e1
            (x', e2') <- register x (renameE e2)
            return $! Exp label (x', e1', e2') (annot,key)
        (SLetRec, (fs, e)) -> do
            let (names, values) = unzip fs
            names' <- mapM identify names
            let as = zipWith (\x x' -> (U.varName x,x')) names names'
            local (\env -> foldr (uncurry M.insert) env as) $ do
                values' <- mapM renameE values
                e' <- renameE e
                return $! Exp label (zip names' values', e') (annot,key)
        (SMark, (x, e)) -> Exp label <$> ((,) <$> rename x <*> renameE e) <*> pure (annot, key)
        (SAssume, (cond,e)) -> Exp label <$> ((,) <$> renameE cond <*> renameE e) <*> pure (annot,key)
        (SIf, (e1,e2,e3)) -> Exp label <$> ((,,) <$> renameE e1 
                                                 <*> renameE e2
                                                 <*> renameE e3) <*> pure (annot,key)
        (SBranch, (e1,e2)) -> Exp label <$> ((,) <$> renameE e1 <*> renameE e2) <*> pure (annot,key)
        (SFail, _) -> return $ Exp label () (annot, key)
        (SOmega, _) -> return $ Exp label () (annot,key)
        (SRand, _) -> return $ Exp label () (annot, key)

register :: U.AnnotVar String (Maybe Type) -> M a -> M (U.AnnotVar (Id String) (Maybe Type),a)
register x m = do
    x' <- identify x
    v  <- local (M.insert (U.varName x) x') m
    return (x',v)

register' :: [U.AnnotVar String (Maybe Type)] -> M a -> M ([U.AnnotVar (Id String) (Maybe Type)],a)
register' xs m = do
    xs' <- mapM identify xs
    v  <- local (\env -> foldr (\(x,x') -> M.insert (U.varName x) x') env (zip xs xs')) m
    return (xs',v)
