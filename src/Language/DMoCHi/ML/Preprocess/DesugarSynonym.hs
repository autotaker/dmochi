module Language.DMoCHi.ML.Preprocess.DesugarSynonym(SynonymError(..), substType, desugarType, desugarEnv) where

import qualified Data.Map as M
import Control.Monad.Except
import Control.Applicative
import Data.Graph
import Data.Array
import Data.Monoid
import Language.DMoCHi.ML.Syntax.UnTyped
import Language.DMoCHi.Common.Util hiding((!))
import Text.Printf

data SynonymError = ArgLengthDiffer Int Int
                  | UndefinedSynonym SynName
                  | UndefinedTypeVariable String
                  deriving(Eq)

instance Show SynonymError where
    show (ArgLengthDiffer expected actual) =
        printf "ArgLengthDiffer: expected %d, but actual was %d" expected actual
    show (UndefinedSynonym syn) = printf "UndefinedSynonym: %s" syn
    show (UndefinedTypeVariable x) = printf "UndefinedTypeVariable: %s" x

-- desugar type synonyms
-- assumption: synEnv is already desugared
desugarType :: M.Map SynName SynonymDef -> Type -> Except SynonymError Type
desugarType _ TInt = return TInt
desugarType _ TBool = return TBool
desugarType _ TUnit = return TUnit
desugarType synEnv (TPair ty1 ty2) =
    TPair <$> desugarType synEnv ty1 
          <*> desugarType synEnv ty2
desugarType synEnv (TFun tys ty) =
    TFun <$> mapM (desugarType synEnv) tys 
         <*> desugarType synEnv ty
desugarType synEnv (TSyn tys syn) = do
    SynonymDef _ vs ty <- 
        M.lookup syn synEnv & maybe (throwError $ UndefinedSynonym syn) pure 
    unless (length tys == length vs) $ 
        throwError (ArgLengthDiffer (length vs) (length tys))
    tys' <- mapM (desugarType synEnv) tys
    substType (M.fromList $ zip vs tys') ty
desugarType _synEnv (TVar x) = return $ TVar x

substType :: M.Map String Type -> Type -> Except SynonymError Type
substType _ TInt = return TInt
substType _ TBool = return TBool
substType _ TUnit = return TUnit
substType env (TPair t1 t2) = liftA2 TPair (substType env t1) (substType env t2)
substType env (TFun ts t) = liftA2 TFun (mapM (substType env) ts) (substType env t)
substType env (TSyn ts syn) = flip TSyn syn <$> mapM (substType env) ts
substType env (TVar x) = 
    M.lookup x env & maybe (throwError $ UndefinedTypeVariable x) pure

desugarEnv :: [SynonymDef] -> Except SynonymError (M.Map SynName SynonymDef)
desugarEnv syns = doit where
    n = length syns
    tbl :: Array Int SynonymDef
    tbl = listArray (0,n-1) syns
    rtbl :: M.Map SynName Int
    rtbl = M.fromList $ zip (map synName syns) [0..]
    depGraph :: Graph
    depGraph = buildG (0,n-1) $ do
        syn <- syns
        dep <- synDef syn & fix 
            (\loop t -> case t of
                TInt -> mempty
                TBool -> mempty
                TUnit -> mempty
                TPair ty1 ty2 -> loop ty1 <> loop ty2
                TFun tys ty -> mconcat (map loop tys) <> loop ty
                TVar _ -> mempty
                TSyn tys syn -> [syn] <> mconcat (map loop tys))
        let v1 = rtbl M.! synName syn
            v2 = rtbl M.! dep
        return (v2, v1)
    vs = topSort depGraph
    doit = foldM (\synEnv v -> do
        let syn = tbl ! v
        ty <- desugarType synEnv (synDef syn)
        let def = SynonymDef (synName syn) (typVars syn) ty
        return (M.insert (synName syn) def synEnv)) M.empty vs
