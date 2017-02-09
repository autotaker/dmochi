{-# LANGUAGE GADTs, FlexibleContexts, TypeFamilies #-}
module Language.DMoCHi.ML.Alpha(alpha,AlphaError, Exp(..), Program(..)) where
import qualified Language.DMoCHi.ML.Syntax.UnTyped as U
import Language.DMoCHi.ML.Syntax.UnTyped(Type(..), SynonymDef)
import Language.DMoCHi.ML.Syntax.Base
import Language.DMoCHi.Common.Id
import Control.Monad.Except
import Control.Monad.Reader
import qualified Data.Map as M
import Text.PrettyPrint.HughesPJClass
import Data.List(sort,group)

data AlphaError = UndefinedVariable String
                | MultipleDefinition [String]

data Exp where
    Exp :: (WellFormed l Exp arg, Supported l (Labels Exp)) => SLabel l -> arg -> UniqueKey -> Exp

data Program = Program { functions :: [(Id String, Type, Exp)]
                       , synonyms :: [SynonymDef]
                       , typeAnn :: [(UniqueKey, Type)]
                       , mainTerm :: Exp }

type instance Ident Exp = Id String
type instance Labels Exp = AllLabels
type instance BinOps Exp = AllBinOps
type instance UniOps Exp = AllUniOps

instance Show AlphaError where
    show (UndefinedVariable s) = "UndefinedVariable: "++s
    show (MultipleDefinition fs) = "MultipleDefinition: "++show fs

instance Pretty Exp where
    pPrintPrec plevel prec (Exp l arg key) = 
        if plevel == prettyNormal then doc else comment key <+> doc
            where
            pp :: WellFormedPrinter Exp
            pp = WellFormedPrinter {
                   pPrintExp = pPrintPrec,
                   pPrintIdent = pPrintPrec
                 }
            doc = genericPPrint pp plevel prec l arg

type M a = ReaderT (M.Map String (Id String)) (ExceptT AlphaError FreshIO) a

alpha :: U.Program -> FreshIO (Either AlphaError Program)
alpha (U.Program fs syns ann t0) = runExceptT $ do
    env <- M.fromList <$> mapM (\(x,_,_) -> (,) x <$> identify x) fs
    when (M.size env /= length fs) $ do
        let fs' = map head $ filter ((>1).length) $ group $ sort $ map (\(x,_,_) -> x) fs
        throwError $ MultipleDefinition fs'
    flip runReaderT env $ do
        fs' <- forM fs $ \(x,p,e) -> (,,) <$> rename x <*> pure p <*> renameE e
        t0' <- renameE t0
        return $ Program fs' syns ann t0'

rename :: String -> M (Id String)
rename x = do
    env <- ask
    let m = M.lookup x env
    case m of
        Nothing -> throwError $ UndefinedVariable x
        Just x' -> return x'

renameE :: U.Exp -> M Exp
renameE (U.Exp label arg key) =
    case (label, arg) of
        (SLiteral, arg) -> return $ Exp label arg key
        (SVar, x) -> Exp label <$> rename x <*> pure key
        (SBinary, BinArg op e1 e2) -> Exp label <$> (BinArg op <$> renameE e1 <*> renameE e2) <*> pure key
        (SUnary, UniArg op e) -> Exp label <$> (UniArg op <$> renameE e) <*> pure key
        (SPair, (e1, e2)) -> Exp label <$> ((,) <$> renameE e1 <*> renameE e2) <*> pure key
        (SLambda, (xs, e)) -> Exp label <$> register' xs (renameE e) <*> pure key
        (SApp, (f, es)) -> Exp label <$> ((,) <$> rename f <*> mapM renameE es) <*> pure key
        (SLet, (x, e1, e2)) -> do
            e1' <- renameE e1
            (x', e2') <- register x (renameE e2)
            return $! Exp label (x', e1', e2') key
        (SAssume, (cond,e)) -> Exp label <$> ((,) <$> renameE cond <*> renameE e) <*> pure key
        (SIf, (e1,e2,e3)) -> Exp label <$> ((,,) <$> renameE e1 
                                                 <*> renameE e2
                                                 <*> renameE e3) <*> pure key
        (SBranch, (e1,e2)) -> Exp label <$> ((,) <$> renameE e1 <*> renameE e2) <*> pure key
        (SFail, _) -> return $ Exp label () key
        (SOmega, _) -> return $ Exp label () key
        (SRand, _) -> return $ Exp label () key

register :: String -> M a -> M (Id String,a)
register x m = do
    x' <- identify x
    v  <- local (M.insert x x') m
    return (x',v)

register' :: [String] -> M a -> M ([Id String],a)
register' xs m = do
    xs' <- mapM identify xs
    v  <- local (\env -> foldr (uncurry M.insert) env (zip xs xs')) m
    return (xs',v)
