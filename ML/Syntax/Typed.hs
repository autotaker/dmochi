module ML.Syntax.Typed where
import qualified ML.Syntax.UnTyped as U
import Control.Monad.Except
import Control.Applicative
import qualified Data.Map as M
data Id = Id { _type :: Type, name :: String }
type Predicate = (Id,Value)

data Program = Program { functions :: [(Id,PType,Exp)] 
                       , mainTerm  :: Exp }
data Type = TInt | TBool | TFun Type Type deriving(Eq)

data Exp = Value Value
         | Let Type Id LetValue Exp
         | Assume Type Value Exp
         | Lambda Type Id Exp
         | Fail Type
         | Branch Type Exp Exp

data Value = Var Id
           | CInt  Type Integer
           | CBool Type Bool
           | Op Op

data Op = OpAdd Type Value Value
        | OpSub Type Value Value
        | OpNeg Type Value
        | OpEq  Type Value Value
        | OpLt  Type Value Value
        | OpLte Type Value Value
        | OpAnd Type Value Value
        | OpOr  Type Value Value
        | OpNot Type Value 

data LetValue = LValue Value
              | LApp Type Id [Value]
              | LExp PType Exp 

data PType = PInt  Type [Predicate]
           | PBool Type [Predicate]
           | PFun  Type PType (Id,PType)

class HasType m where
    getType :: m -> Type

instance HasType Id where
    getType = _type

instance HasType Exp where
    getType (Value v) = getType v
    getType (Let a _ _ _) = a
    getType (Assume a _ _) = a
    getType (Lambda a _ _) = a
    getType (Fail a) = a
    getType (Branch a _ _) = a

instance HasType LetValue where
    getType (LValue v) = getType v
    getType (LApp ty _ _) = ty
    getType (LExp p _) = getType p

instance HasType Value where
    getType (Var x) = getType x
    getType (CInt a _) = a
    getType (CBool a _) = a
    getType (Op op) = getType op

instance HasType Op where
    getType (OpAdd a _ _) = a
    getType (OpSub a _ _) = a
    getType (OpNeg a _)   = a
    getType (OpEq  a _ _) = a
    getType (OpLt  a _ _) = a
    getType (OpLte a _ _) = a
    getType (OpAnd a _ _) = a
    getType (OpOr  a _ _) = a
    getType (OpNot a _)   = a

instance HasType PType where
    getType (PInt t _) = t
    getType (PBool t _) = t
    getType (PFun t _ _) = t

type Env = M.Map String Type
data TypeError = UndefinedVariable String 
               | TypeMisMatch Type Type
               | TypeMisUse   Type [Type]
               | OtherError String

fromUnTyped :: U.Program -> Except TypeError Program
fromUnTyped (U.Program fs t) = do
    fs' <- mapM (\(x,p,e) -> (,,) x <$> convertP p <*> pure e) fs
    let tenv = M.fromList [ (x,getType p) | (x,p,_) <- fs' ]
    fs'' <- mapM (\(x,p,e) -> 
        (,,) (Id (getType p) x) p <$> convertE tenv (getType p) e) fs'
    Program fs'' <$> convertE tenv TInt t

convertP :: U.PType -> Except TypeError PType
convertP = go M.empty where
    base f env ty ps = 
        f <$> mapM (\(x,p) -> do
            p' <- convertV (M.insert x ty env) p
            getType p' `shouldBe` TBool
            return (Id ty x,p')) ps
    go env (U.PInt ps) = base (PInt TInt) env TInt ps
    go env (U.PBool ps) = base (PInt TInt) env TInt ps
    go env (U.PFun p (x,f)) = do
        p' <- go env p
        let ty = getType p'
        f' <- go (M.insert x ty env) f
        return $ PFun (TFun ty (getType f')) p' (Id ty x,f')

convertE :: Env -> Type -> U.Exp -> Except TypeError Exp
convertE env ty _e = case _e of
    U.Value v -> Value <$> convertV env v
    U.Let x lv e -> do
        lv' <- convertLV env lv
        let ty' = getType lv'
        Let ty (Id ty' x) lv' <$> convertE (M.insert x ty env) ty e
    U.Assume v e -> do
        v' <- convertV env v
        getType v' `shouldBe` TBool
        Assume ty v' <$> convertE env ty e
    U.Lambda x e -> do
        case ty of
            TFun t1 t2 -> do
                Lambda ty (Id t1 x) <$> convertE (M.insert x t1 env) t2 e
            _ -> throwError $ OtherError "Expecting function"
    U.Fail -> pure $ Fail ty
    U.Branch e1 e2 -> Branch ty <$> convertE env ty e1 <*> convertE env ty e2

convertLV :: Env -> U.LetValue -> Except TypeError LetValue
convertLV env lv = case lv of
    U.LValue v -> LValue <$> convertV env v
    U.LApp x vs -> do
        vs' <- mapM (convertV env) vs
        case M.lookup x env of
            Just ty -> do
                ty' <- foldM (\tf v -> 
                    case tf of
                        TFun t1 t2 -> t2 <$ getType v `shouldBe` t1
                        _ -> throwError $ OtherError "Excepting function") ty vs'
                return $ LApp ty' (Id ty x) vs'
            Nothing -> throwError $ UndefinedVariable x
    U.LExp ptyp e -> do
        ptyp' <- convertP ptyp
        LExp ptyp' <$> convertE env (getType ptyp') e
                
shouldBe :: Type -> Type -> Except TypeError ()
shouldBe t1 t2 | t1 == t2 = pure ()
               | otherwise = throwError (TypeMisMatch t1 t2)

shouldBeIn :: Type -> [Type] -> Except TypeError ()
shouldBeIn t1 ts = 
    if t1 `elem` ts then pure () else throwError (TypeMisUse t1 ts)

convertV :: Env -> U.Value -> Except TypeError Value
convertV env v = case v of
    U.Var x -> case M.lookup x env of
        Just ty -> pure $ Var $ Id ty x
        Nothing -> throwError $ UndefinedVariable x
    U.CInt i -> pure $ CInt TInt i
    U.CBool b -> pure $ CBool TBool b
    U.Op op -> do
        let bin f t v1 v2 = do
            v1' <- convertV env v1
            getType v1' `shouldBe` t
            v2' <- convertV env v2
            getType v2' `shouldBe` t
            return $ f v1' v2'
        Op <$> case op of
            U.OpAdd v1 v2 -> bin (OpAdd TInt) TInt v1 v2
            U.OpSub v1 v2 -> bin (OpSub TInt) TInt v1 v2
            U.OpNeg v1    -> do
                v1' <- convertV env v1
                getType v1' `shouldBe` TInt
                return $ OpNeg TInt v1'
            U.OpEq  v1 v2 -> do
                v1' <- convertV env v1
                v2' <- convertV env v2
                getType v1' `shouldBe` getType v2'
                getType v1' `shouldBeIn` [TInt,TBool]
                return $ OpEq TBool v1' v2'
            U.OpLt  v1 v2 -> bin (OpLt TBool) TInt v1 v2
            U.OpGt  v1 v2 -> bin (OpLt TBool) TInt v2 v1
            U.OpLte v1 v2 -> bin (OpLte TBool) TInt v1 v2
            U.OpGte v1 v2 -> bin (OpLte TBool) TInt v2 v1
            U.OpAnd v1 v2 -> bin (OpAnd TBool) TBool v1 v2
            U.OpOr  v1 v2 -> bin (OpOr TBool) TBool v1 v2
            U.OpNot v1    -> do
                v1' <- convertV env v1
                getType v1' `shouldBe` TBool
                return $ OpNot TBool v1'

