{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, Rank2Types, GADTs, TypeOperators #-}
module Language.DMoCHi.ML.TypeCheck where
import qualified Data.Map as M
import Control.Monad.Except
-- import Text.PrettyPrint
import Language.DMoCHi.ML.Syntax.Typed 
import Language.DMoCHi.ML.Syntax.Base
import Language.DMoCHi.ML.Syntax.Type
import qualified Language.DMoCHi.ML.Alpha as U
import qualified Language.DMoCHi.ML.Syntax.UnTyped as U(SynName, SynonymDef(..), Type(..), Lit(..))
import qualified Language.DMoCHi.Common.Id as Id
import Language.DMoCHi.Common.Id(MonadId(..), UniqueKey)
import Language.DMoCHi.ML.DesugarSynonym
import Data.Type.Equality

instance Show TypeError where
    show (UndefinedVariable s)      = "UndefinedVariables: "++ s
    show (TypeMisMatch s t1 t2)     = "TypeMisMatch: " ++ show t1 ++ " should be " ++ show t2 ++ ". context :" ++ show s
    show (TypeMisMatchList s t1 t2) = "TypeMisMatch: " ++ show t1 ++ " should be " ++ show t2 ++ ". context :" ++ s
    show (TypeMisUse t1 t2)         = "TypeUse: " ++ show t1 ++ " should be in " ++ show t2
    show (ArityMisMatch s t1 t2)    = "ArityMismatch: " ++ show t1 ++ " should be  " ++ show t2 ++ ". context :" ++ show s
    show (Synonym err)  = "SynonymError: " ++ show err
    show (OtherError s) = "OtherError: " ++ s

type Env = M.Map (Id.Id String) SomeSType
type Annot = M.Map UniqueKey SomeSType
type SynEnv = M.Map U.SynName U.SynonymDef
data TypeError = UndefinedVariable String  
               | TypeMisMatch UniqueKey SomeSType SomeSType
               | ArityMisMatch UniqueKey Int Int
               | TypeMisMatchList String [Type] [Type]
               | TypeMisUse   Type [Type]
               | Synonym  SynonymError
               | OtherError String

{-
fromUnTyped :: MonadId m => U.Program -> ExceptT TypeError m Program
fromUnTyped (U.Program fs syns t) = do
    synEnv <- withExceptT Synonym (desugarEnv syns)
    fs' <- mapM (\(x,p,e) -> (,,) x <$> convertP synEnv p <*> pure e) fs
    let tenv = M.fromList [ (x,ty) | (x,ty,_) <- fs' ]
    fs'' <- forM fs' $ \(x,ty,U.Lambda y e) -> do
        let x' = Id ty x
        fdef <- convertLambda synEnv tenv y e ty
        return (x',fdef) 
    Program fs'' <$> convertE synEnv tenv TInt t
-}

shouldBe :: Monad m => UniqueKey -> SType ty1 -> SType ty2 -> ExceptT TypeError m (ty1 :~: ty2)
shouldBe s t1 t2 = 
    case testEquality t1 t2 of
        Just Refl -> return Refl
        Nothing -> throwError (TypeMisMatch s (SomeSType t1) (SomeSType t2))

shouldBeList :: Monad m => String -> [Type] -> [Type] -> ExceptT TypeError m ()
shouldBeList s ts1 ts2 | ts1 == ts2 = return ()
                       | otherwise = throwError (TypeMisMatchList s ts1 ts2)

{-
shouldBeValue :: Monad m => Value -> Type -> ExceptT TypeError m ()
shouldBeValue v t1 = shouldBe (render $ pprintV 0 v) (getType v) t1
-}

shouldBeIn :: Monad m => Type -> [Type] -> ExceptT TypeError m ()
shouldBeIn t1 ts = 
    if t1 `elem` ts then return () else throwError (TypeMisUse t1 ts)

shouldBePair :: Monad m => String -> Type -> ExceptT TypeError m (Type,Type)
shouldBePair _ (TPair t1 t2) = return (t1,t2)
shouldBePair s _ = throwError (OtherError $ "expecting pair :" ++ s)

convertType :: forall m. Monad m => SynEnv -> U.Type -> ExceptT TypeError m SomeSType
convertType synEnv ty = do
    ty <- withExceptT Synonym (desugarType synEnv ty) 
    go ty (return. SomeSType)
        where
        go :: U.Type -> (forall ty. SType ty -> ExceptT TypeError m b) -> ExceptT TypeError m b
        go ty k = case ty of
            U.TInt -> k STInt
            U.TBool -> k STBool
            U.TPair ty1 ty2 -> go ty1 $ \sty1 -> go ty2 $ \sty2 -> k (STPair sty1 sty2)
            U.TFun tys ty -> do
                stys <- goArg tys
                go ty $ \sty -> k (STFun stys sty)
            _ -> throwError $ OtherError $ "convertP: unsupported conversion: " {- ++ render (U.pprintT 0 ty)) -}
        goArg :: [U.Type] -> ExceptT TypeError m STypeArg
        goArg [] = return SArgNil
        goArg (ty:tys) = go ty $ \sty -> goArg tys >>= return . SArgCons sty

convertE :: forall m. MonadId m => Annot -> Env -> U.Exp -> ExceptT TypeError m Exp
convertE annot env (U.Exp l arg key) = 
    case annot M.! key of { SomeSType sty -> 
    case (l,arg) of
        (SLiteral, U.CInt _)  -> do
            Refl <- shouldBe key sty STInt
            return $ Exp l arg sty key
        (SLiteral, U.CBool _) -> do
            Refl <- shouldBe key sty STBool
            return $ Exp l arg sty key
        (SVar, x) -> case env M.! x of 
            SomeSType sty' -> do
                shouldBe key sty sty'
                return $ Exp l (SId sty' x) sty key
        (SBinary, BinArg op e1 e2) ->  do
            e1'@(Exp _ _ sty1 key1) <- convertE annot env e1
            e2'@(Exp _ _ sty2 key2) <- convertE annot env e2
            typeOfBinOp op sty1 key1 sty2 key2 (\sty' -> do
                shouldBe key sty sty'
                return $ Exp l (BinArg op e1' e2') sty key)
        (SUnary, UniArg op e1) ->  do
            e1'@(Exp _ _ sty1 key1) <- convertE annot env e1
            typeOfUniOp op sty1 key1 (\sty' -> do
                shouldBe key sty sty'
                return $ Exp l (UniArg op e1') sty key)
        (SPair, (e1, e2)) -> do
            e1'@(Exp _ _ sty1 _) <- convertE annot env e1
            e2'@(Exp _ _ sty2 _) <- convertE annot env e2
            Refl <- shouldBe key sty (STPair sty1 sty2)
            return $ Exp l (e1', e2') sty key
        (SLambda, (xs, e1)) -> do
            case sty of
                STFun stys sty1' -> do
                    let ty_args = mapArg SomeSType stys
                        n = length ty_args
                        m = length xs
                    when (length ty_args /= length xs) $ 
                        throwError $ ArityMisMatch key n m
                    let env' = foldr (uncurry M.insert) env $ zip xs ty_args
                        ys = zipWith (\x (SomeSType ty) -> SId ty x) xs ty_args
                    e1'@(Exp _ _ sty1 key1) <- convertE annot env' e1
                    shouldBe key1 sty1 sty1'
                    return $ Exp l (ys, e1') sty key
                _ -> throwError $ OtherError $ "This function expected to have type " ++ show sty
        (SApp, (f, es)) -> do
            case env M.! f of
                SomeSType sty_f@(STFun tys sty') -> do
                    es' <- mapM (convertE annot env) es
                    let g :: Exp -> SomeSType -> ExceptT TypeError m ()
                        g (Exp _ _ sty_i key_i) (SomeSType sty_i') = 
                            void $ shouldBe key_i sty_i sty_i'
                    zipWithM_ g es' (mapArg SomeSType tys)
                    let n = length es
                        m = foldArg (\_ acc -> acc + 1) 0 tys
                    when (n /= m) $ throwError $ ArityMisMatch key n m
                    shouldBe key sty sty'
                    return $ Exp l (SId sty_f f, es') sty key
                SomeSType sty_f -> throwError $ OtherError $ "App" ++ show sty_f
        (SLet, (x, e1, e2)) -> do
            e1'@(Exp _ _ sty1 _) <- convertE annot env e1
            let env' = M.insert x (SomeSType sty1) env
            e2'@(Exp _ _ sty2 _) <- convertE annot env' e2
            shouldBe key sty sty2
            return $ Exp l (SId sty1 x, e1', e2') sty key
        (SAssume, (e1, e2)) -> do
            e1'@(Exp _ _ sty1 key1) <- convertE annot env e1
            shouldBe key1 sty1 STBool
            e2'@(Exp _ _ sty2 _) <- convertE annot env e2
            shouldBe key sty sty2
            return $ Exp l (e1', e2') sty key
        (SIf, (e1, e2, e3)) -> do
            e1'@(Exp _ _ sty1 key1) <- convertE annot env e1
            shouldBe key1 sty1 STBool
            e2'@(Exp _ _ sty2 _) <- convertE annot env e2
            shouldBe key sty sty2
            e3'@(Exp _ _ sty3 _) <- convertE annot env e3
            shouldBe key sty sty3
            return $ Exp l (e1', e2', e3') sty key
        (SBranch, (e2, e3)) -> do
            e2'@(Exp _ _ sty2 _) <- convertE annot env e2
            shouldBe key sty sty2
            e3'@(Exp _ _ sty3 _) <- convertE annot env e3
            shouldBe key sty sty3
            return $ Exp l (e2', e3') sty key
        (SFail, ()) -> return $ Exp l () sty key
        (SOmega, ()) -> return $ Exp l () sty key
        (SRand, ()) -> shouldBe key sty STInt >> return (Exp l () sty key)
    }
                
typeOfUniOp :: Monad m => SUniOp op -> SType ty -> UniqueKey -> 
               (forall ty'. SType ty' -> ExceptT TypeError m b) -> ExceptT TypeError m b
typeOfUniOp SFst sty1 _key1 k = do
    case sty1 of
        STPair sty' _ -> k sty'
        _ -> throwError $ OtherError $ "Expected a pair type but found " ++ show sty1
typeOfUniOp SSnd sty1 _key1 k = do
    case sty1 of
        STPair _ sty' -> k sty'
        _ -> throwError $ OtherError $ "Expected a pair type but found " ++ show sty1
typeOfUniOp SNot sty1 key1 k = do
    shouldBe key1 sty1 STBool
    k STBool
typeOfUniOp SNeg sty1 key1 k = do
    shouldBe key1 sty1 STInt
    k STInt

        
typeOfBinOp :: Monad m => SBinOp op -> SType ty1 -> UniqueKey -> SType ty2 -> UniqueKey -> 
               (forall ty3. SType ty3 -> ExceptT TypeError m b) -> ExceptT TypeError m b 
typeOfBinOp op = (case op of
    SAdd -> intOp STInt
    SSub -> intOp STInt
    SEq -> intOp STBool
    SLt -> intOp STBool
    SGt -> intOp STBool
    SLte -> intOp STBool
    SGte -> intOp STBool
    SAnd -> boolOp
    SOr  -> boolOp
    ) where intOp sty sty1 key1 sty2 key2 k = do
                shouldBe key1 sty1 STInt
                shouldBe key2 sty2 STInt
                k sty
            boolOp sty1 key1 sty2 key2 k = do
                shouldBe key1 sty1 STBool
                shouldBe key2 sty2 STBool
                k STBool
    
{-
    
    U.Value v -> do
        v' <- convertV env v
        v' `shouldBeValue` ty
        return $ Value v'
    U.Let x lv e -> do
        lv' <- convertLV synEnv env lv
        let ty' = getType lv'
        e' <- Let ty (Id ty' x) lv' <$> convertE synEnv (M.insert x ty' env) ty e
        return e'
    U.Assume v e -> do
        v' <- convertV env v
        shouldBeValue  v' TBool
        Assume ty v' <$> convertE synEnv env ty e
    U.Lambda xs e -> do
        fdef <- convertLambda synEnv env xs e ty
        return $ Fun fdef
    U.Fail -> pure $ Fail ty
    U.Branch e1 e2 -> do
        i <- freshInt
        Branch ty i <$> convertE synEnv env ty e1 <*> convertE synEnv env ty e2

convertLambda :: (MonadId m) => SynEnv -> Env -> [U.Id] -> U.Exp -> Type -> ExceptT TypeError m FunDef
convertLambda synEnv env args body (TFun ts t2) = do
    i <- freshInt
    let env' = foldr (uncurry M.insert) env (zip args ts)
    FunDef i (zipWith Id ts args) <$> convertE synEnv env' t2 body
convertLambda _ _ xs _ _ = throwError $ OtherError $ "Expecting function:" ++ show xs


convertLV :: (MonadId m) => SynEnv -> Env -> U.LetValue -> ExceptT TypeError m (LetValue)
convertLV synEnv env lv = case lv of
    U.LValue v -> do
        v' <- convertV env v
        return $ LValue v'
    U.LRand -> 
        return LRand
    U.LApp f vs -> do
        vs' <- mapM (convertV env) vs
        case M.lookup f env of
            Just ty -> do
                let ts' = map getType vs'
                case ty of
                    TFun ts t2 -> do
                        shouldBeList (show (map (pprintV 0) vs')) ts ts'
                        let f' = Id ty f
                        i <- freshInt
                        return $ LApp t2 i f' vs'
                    _ -> throwError $ OtherError $ "Expecting function" ++ f
            Nothing -> throwError $ UndefinedVariable f
    U.LExp ptyp (U.Lambda x e) -> do
        ty <- convertP synEnv ptyp
        fdef <- convertLambda synEnv env x e ty
        return (LFun fdef)
    U.LExp ptyp e -> do
        ty <- convertP synEnv ptyp
        i <- freshInt
        lv <- LExp i <$> convertE synEnv env ty e
        return lv
                

convertV :: Monad m => Env -> U.Value -> ExceptT TypeError m Value
convertV env v = case v of
    U.Var x -> case M.lookup x env of
        Just ty -> pure $ Var $ Id ty x
        Nothing -> throwError $ UndefinedVariable x
    U.App _ _ -> error "convertV: unexpected App"
    U.CInt i -> pure $ CInt i
    U.CBool b -> pure $ CBool b
    U.Pair v1 v2 -> Pair <$> convertV env v1 <*> convertV env v2
    U.Op op -> do
        let bin f t v1 v2 = do
                v1' <- convertV env v1
                shouldBeValue v1' t
                v2' <- convertV env v2
                shouldBeValue v2' t
                return $ f v1' v2'
        Op <$> case op of
            U.OpAdd v1 v2 -> bin OpAdd TInt v1 v2
            U.OpSub v1 v2 -> bin OpSub TInt v1 v2
            U.OpNeg v1    -> bin OpSub TInt (U.CInt 0) v1
            U.OpEq  v1 v2 -> do
                v1' <- convertV env v1
                v2' <- convertV env v2
                v1' `shouldBeValue` getType v2'
                -- getType v1' `shouldBeIn` [TInt,TBool]
                return $ OpEq v1' v2'
            U.OpLt  v1 v2 -> bin OpLt TInt v1 v2
            U.OpGt  v1 v2 -> bin OpLt TInt v2 v1
            U.OpLte v1 v2 -> bin OpLte TInt v1 v2
            U.OpGte v1 v2 -> bin OpLte TInt v2 v1
            U.OpAnd v1 v2 -> bin OpAnd TBool v1 v2
            U.OpOr  v1 v2 -> bin OpOr TBool v1 v2
            U.OpNot v1    -> do
                v1' <- convertV env v1
                v1' `shouldBeValue` TBool
                return $ OpNot v1'
            U.OpFst v1    -> do
                v1' <- convertV env v1
                (t1,_) <- shouldBePair ("fst" ++ show v1) $ getType v1'
                return $ OpFst t1 v1'
            U.OpSnd v1    -> do
                v1' <- convertV env v1
                (_,t2) <- shouldBePair ("snd" ++ show v1 ++ "," ++ show env++ show (getType v1')) $ getType v1'
                return $ OpSnd t2 v1'

-}
