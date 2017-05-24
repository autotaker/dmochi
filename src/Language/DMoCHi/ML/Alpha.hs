{-# LANGUAGE GADTs, FlexibleContexts, TypeFamilies #-}
module Language.DMoCHi.ML.Alpha(alpha,AlphaError, Exp(..), Program(..)) where
import qualified Language.DMoCHi.ML.Syntax.UnTyped as U
import Language.DMoCHi.ML.Syntax.UnTyped(Type(..), SynonymDef(..))
import Language.DMoCHi.ML.Syntax.Base
import Language.DMoCHi.Common.Id hiding(identify)
import qualified Language.DMoCHi.Common.Id as Id(identify)
import Control.Monad.Except
import Control.Monad.Reader
import qualified Data.Map as M
import Text.PrettyPrint.HughesPJClass
import Data.List(sort,group)

data AlphaError = UndefinedVariable String
                | MultipleDefinition [String]
                deriving(Eq)

data Exp where
    Exp :: (WellFormed l Exp arg, Supported l (Labels Exp)) => 
      !(SLabel l) -> arg -> !(Maybe Type, UniqueKey) -> Exp

data Program = Program { functions :: [(Var, Type, Exp)]
                       , synonyms :: [SynonymDef]
                       {- , typeAnn :: [(UniqueKey, Type)] -}
                       , mainTerm :: Exp }
type Var = U.AnnotVar (Id String)

type instance Ident Exp = Var
type instance Labels Exp = AllLabels
type instance BinOps Exp = AllBinOps
type instance UniOps Exp = AllUniOps

instance HasUniqueKey Exp where
    getUniqueKey (Exp _ _ (_,key)) = key

instance Show AlphaError where
    show (UndefinedVariable s) = "UndefinedVariable: "++s
    show (MultipleDefinition fs) = "MultipleDefinition: "++show fs

instance Pretty Exp where
    pPrintPrec plevel prec (Exp l arg (_, key)) = 
        if plevel == prettyNormal then doc else comment key <+> doc
            where
            pp :: WellFormedPrinter Exp
            pp = WellFormedPrinter {
                   pPrintExp = pPrintPrec,
                   pPrintIdent = pPrintPrec
                 }
            doc = genericPPrint pp plevel prec l arg

instance Pretty Program where
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
                        {-
        (if plevel == prettyNormal
         then empty
         else text "(* annotations *)" $+$
              vcat (map (\(key, ty) -> pPrint key <+> colon <+> pPrintPrec plevel 0 ty) annot)) $+$ -}
        text "(*main*)" $+$
        pPrintPrec plevel 0 t

type M a = ReaderT (M.Map String (U.AnnotVar (Id String))) (ExceptT AlphaError FreshIO) a

alpha :: U.Program -> FreshIO (Either AlphaError Program)
alpha (U.Program fs syns t0) = runExceptT $ do
    env <- M.fromList <$> mapM (\(x,_,_) -> fmap (U.varName x,) (identify x)) fs
    when (M.size env /= length fs) $ do
        let fs' = map head $ filter ((>1).length) $ group $ sort $ map (\(x,_,_) -> U.varName x) fs
        throwError $ MultipleDefinition fs'
    flip runReaderT env $ do
        fs' <- forM fs $ \(x,p,e) -> (,,) <$> rename x <*> pure p <*> renameE e
        t0' <- renameE t0
        return $ Program fs' syns t0'

rename :: U.AnnotVar String -> M (U.AnnotVar (Id String))
rename x = do
    env <- ask
    let m = M.lookup (U.varName x) env
    case m of
        Nothing -> throwError $ UndefinedVariable (U.varName x)
        Just x' -> return x'

identify :: MonadId m => U.AnnotVar String -> m (U.AnnotVar (Id String))
identify (U.V x ty) = U.V <$> Id.identify x <*> pure ty

renameE :: U.Exp -> M Exp
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
        (SAssume, (cond,e)) -> Exp label <$> ((,) <$> renameE cond <*> renameE e) <*> pure (annot,key)
        (SIf, (e1,e2,e3)) -> Exp label <$> ((,,) <$> renameE e1 
                                                 <*> renameE e2
                                                 <*> renameE e3) <*> pure (annot,key)
        (SBranch, (e1,e2)) -> Exp label <$> ((,) <$> renameE e1 <*> renameE e2) <*> pure (annot,key)
        (SFail, _) -> return $ Exp label () (annot, key)
        (SOmega, _) -> return $ Exp label () (annot,key)
        (SRand, _) -> return $ Exp label () (annot, key)

register :: U.AnnotVar String -> M a -> M (U.AnnotVar (Id String),a)
register x m = do
    x' <- identify x
    v  <- local (M.insert (U.varName x) x') m
    return (x',v)

register' :: [U.AnnotVar String] -> M a -> M ([U.AnnotVar (Id String)],a)
register' xs m = do
    xs' <- mapM (\x -> identify x) xs
    v  <- local (\env -> foldr (\(x,x') -> M.insert (U.varName x) x') env (zip xs xs')) m
    return (xs',v)
