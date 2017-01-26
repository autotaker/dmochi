module Language.DMoCHi.ML.DesugarSynonym(SynonymError, desugarType, desugarEnv) where

import qualified Data.Map as M
import Control.Monad.Except
import Control.Applicative
import Data.Graph
import Data.Array
import Data.Monoid
import Language.DMoCHi.ML.Syntax.UnTyped
import Text.Printf

data SynonymError = ArgLengthDiffer Int Int
                  | UndefinedSynonym SynName
                  | UndefinedTypeVariable String

instance Show SynonymError where
    show (ArgLengthDiffer expected actual) = 
        printf "ArgLengthDiffer: expected %d, but actual was %d" expected actual
    show (UndefinedSynonym syn) = printf "UndefinedSynonym: %s" syn
    show (UndefinedTypeVariable x) = printf "UndefinedTypeVariable: %s" x

-- desugar type synonyms
-- assumption: synEnv is already desugared
desugarType :: Monad m => M.Map SynName SynonymDef -> Type -> ExceptT SynonymError m Type
desugarType _synEnv TInt = return TInt
desugarType _synEnv TBool = return TBool
desugarType synEnv (TPair ty1 ty2) = 
    TPair <$> desugarType synEnv ty1 <*> desugarType synEnv ty2
desugarType synEnv (TFun tys ty) =
    TFun <$> mapM (desugarType synEnv) tys <*> desugarType synEnv ty
desugarType synEnv (TSyn tys syn) =
    case M.lookup syn synEnv of
        Just (SynonymDef _ vs ty) 
            | length tys == length vs -> do
                tys' <- mapM (desugarType synEnv) tys
                substType (M.fromList $ zip vs tys') ty
            | otherwise -> throwError (ArgLengthDiffer (length vs) (length tys))
        Nothing -> throwError (UndefinedSynonym syn)
desugarType _synEnv (TVar x) = return $ TVar x

substType :: Monad m => M.Map Id Type -> Type -> ExceptT SynonymError m Type
substType _env TInt = return TInt
substType _env TBool = return TBool
substType env (TPair t1 t2) = liftA2 TPair (substType env t1) (substType env t2)
substType env (TFun ts t) = liftA2 TFun (mapM (substType env) ts) (substType env t)
substType env (TSyn ts syn) = flip TSyn syn <$> (mapM (substType env) ts)
substType env (TVar x) = case M.lookup x env of
    Just ty -> return ty
    Nothing -> throwError (UndefinedTypeVariable x)

desugarEnv :: Monad m => [SynonymDef] -> ExceptT SynonymError m (M.Map SynName SynonymDef)
desugarEnv syns = doit where
    n = length syns
    tbl :: Array Int SynonymDef
    tbl = listArray (0,n-1) syns
    rtbl :: M.Map SynName Int
    rtbl = M.fromList $ zip (map synName syns) [0..]
    depGraph :: Graph
    depGraph = buildG (0,n-1) $ do
        syn <- syns
        let v1 = rtbl M.! (synName syn)
        dep <- (fix $ \loop t -> case t of
            TInt -> mempty
            TBool -> mempty
            TPair ty1 ty2 -> loop ty1 <> loop ty2 
            TFun tys ty -> mconcat (map loop tys) <> loop ty
            TVar _ -> mempty
            TSyn tys syn -> [syn] <> mconcat (map loop tys)) (synDef syn)
        let v2 = rtbl M.! dep
        return (v2, v1)
    vs = topSort depGraph
    doit = foldM (\synEnv v -> do
        let syn = tbl ! v
        ty <- desugarType synEnv (synDef syn)
        return (M.insert (synName syn) (SynonymDef (synName syn) (typVars syn) ty) synEnv)) M.empty vs
