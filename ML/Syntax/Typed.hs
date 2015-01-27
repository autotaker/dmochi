{-# LANGUAGE FlexibleContexts #-}
module ML.Syntax.Typed where
import qualified ML.Syntax.UnTyped as U
import Control.Monad.Except
import Control.Applicative
import qualified Data.Map as M
import Text.PrettyPrint

data Id = Id { _type :: Type, name :: String } deriving(Eq)
type Predicate = (Id,Value)

data Program = Program { functions :: [(Id,PType,Exp)] 
                       , mainTerm  :: Exp }
data Type = TInt | TBool | TPair Type Type | TFun Type Type deriving(Eq)

data Exp = Value Value
         | Let Type Id LetValue Exp
         | Assume Type Value Exp
         | Lambda Type Id Exp
         | Fail Type
         | Branch Type Exp Exp

data Value = Var Id
           | CInt  Integer
           | CBool Bool
           | Pair Value Value
           | Op Op deriving(Eq)


data Op = OpAdd Value Value
        | OpSub Value Value
        | OpEq  Value Value
        | OpLt  Value Value
        | OpLte Value Value
        | OpAnd Value Value
        | OpOr  Value Value
        | OpFst Type Value
        | OpSnd Type Value
        | OpNot Value  deriving(Eq)

data LetValue = LValue Value
              | LApp Type Id [Value]
              | LExp PType Exp 

data PType = PInt  [Predicate]
           | PBool [Predicate]
           | PPair Type PType (Id,PType) 
           | PFun  Type PType (Id,PType) deriving(Eq)

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
    getType (CInt _) = TInt
    getType (CBool _) = TBool
    getType (Pair v1 v2) = TPair (getType v1) (getType v2)
    getType (Op op) = getType op

instance HasType Op where
    getType (OpAdd _ _) = TInt
    getType (OpSub _ _) = TInt
    getType (OpEq  _ _) = TBool
    getType (OpLt  _ _) = TBool
    getType (OpLte _ _) = TBool
    getType (OpAnd _ _) = TBool
    getType (OpOr  _ _) = TBool
    getType (OpNot _)   = TBool
    getType (OpFst a _)   = a
    getType (OpSnd a _)   = a

instance HasType PType where
    getType (PInt _) = TInt
    getType (PBool _) = TBool
    getType (PPair t _ _) = t
    getType (PFun t _ _) = t

type Env = M.Map String Type
data TypeError = UndefinedVariable String 
               | TypeMisMatch Type Type
               | TypeMisUse   Type [Type]
               | OtherError String

substV :: Id -> Value -> Value -> Value
substV x v = go where
    go (Var y) | name x == name y = v
    go (Op op) = Op $ case op of
        OpAdd a b -> OpAdd (go a) (go b)
        OpSub a b -> OpSub (go a) (go b)
        OpEq  a b -> OpEq  (go a) (go b)
        OpLt  a b -> OpLt  (go a) (go b)
        OpLte a b -> OpLte (go a) (go b)
        OpAnd a b -> OpAnd (go a) (go b)
        OpOr  a b -> OpOr  (go a) (go b)
        OpNot a   -> OpNot (go a)
        OpFst t a -> OpFst t (go a)
        OpSnd t a -> OpSnd t (go a)
    go w = w

substPType :: Id -> Value -> PType -> PType
substPType x v = go where
    go (PInt  ps) = PInt (map (\(y,w) -> (y,substV x v w)) ps)
    go (PBool ps) = PBool (map (\(y,w) -> (y,substV x v w)) ps)
    go (PPair ty p1 (y,p2)) = PPair ty (go p1) (y,go p2)
    go (PFun  ty p1 (y,p2)) = PFun ty (go p1) (y,go p2)

pprintT :: Int -> Type -> Doc
pprintT _ TInt = text "int"
pprintT _ TBool = text "bool"
pprintT assoc (TPair t1 t2) =
    let d1 = pprintT 1 t1
        d2 = pprintT 1 t2
        d  = d1 <+> text "*" <+> d2
    in if assoc <= 0 then d else parens d
pprintT assoc (TFun t1 t2) =
    let d1 = pprintT 1 t1
        d2 = pprintT 0 t2
        d  = d1 <+> text "->" <+> d2
    in if assoc == 0 then d else parens d

instance Show Type where
    show = render . pprintT 0

instance Show TypeError where
    show (UndefinedVariable s) = "UndefinedVariables: "++ s
    show (TypeMisMatch t1 t2)   = "TypeMisMatch: " ++ show t1 ++ " should be " ++ show t2
    show (TypeMisUse t1 t2)     = "TypeUse: " ++ show t1 ++ " should be in" ++ show t2
    show (OtherError s)         = "OtherError: " ++ s

fromUnTyped :: (Applicative m,MonadError TypeError m) => U.Program -> m Program
fromUnTyped (U.Program fs t) = do
    fs' <- mapM (\(x,p,e) -> (,,) x <$> convertP p <*> pure e) fs
    let tenv = M.fromList [ (x,getType p) | (x,p,_) <- fs' ]
    fs'' <- mapM (\(x,p,e) -> 
        (,,) (Id (getType p) x) p <$> convertE tenv (getType p) e) fs'
    Program fs'' <$> convertE tenv TInt t

{-
toUnTyped :: Program -> U.Program
toUnTyped (Program fs t) = U.Program fs' t' where
    fs' = map (\(x,p,e) -> (name x,revP p, revE e)) fs
    t'  = revE t
    -}

shouldBe :: MonadError TypeError m => Type -> Type -> m ()
shouldBe t1 t2 | t1 == t2 = return ()
               | otherwise = throwError (TypeMisMatch t1 t2)

shouldBeIn :: MonadError TypeError m => Type -> [Type] -> m ()
shouldBeIn t1 ts = 
    if t1 `elem` ts then return () else throwError (TypeMisUse t1 ts)

shouldBePair :: MonadError TypeError m => String -> Type -> m (Type,Type)
shouldBePair _ (TPair t1 t2) = return (t1,t2)
shouldBePair s _ = throwError (OtherError $ "expecting pair :" ++ s)

convertP :: (Applicative m,MonadError TypeError m) => U.PType -> m PType
convertP = go M.empty where
    base f env ty ps = 
        f <$> mapM (\(x,p) -> do
            p' <- convertV (M.insert x ty env) p
            getType p' `shouldBe` TBool
            return (Id ty x,p')) ps
    go env (U.PInt ps) = base PInt env TInt ps
    go env (U.PBool ps) = base PInt env TInt ps
    go env (U.PPair p (x,f)) =  do
        p' <- go env p
        let ty = getType p'
        f' <- go (M.insert x ty env) f
        return $ PPair (TPair ty (getType f')) p' (Id ty x,f')
    go env (U.PFun p (x,f)) = do
        p' <- go env p
        let ty = getType p'
        f' <- go (M.insert x ty env) f
        return $ PFun (TFun ty (getType f')) p' (Id ty x,f')

convertE :: (Applicative m,MonadError TypeError m) => Env -> Type -> U.Exp -> m Exp
convertE env ty _e = case _e of
    U.Value v -> Value <$> convertV env v
    U.Let x lv e -> do
        lv' <- convertLV env lv
        let ty' = getType lv'
        Let ty (Id ty' x) lv' <$> convertE (M.insert x ty' env) ty e
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

convertLV :: (Applicative m,MonadError TypeError m) => Env -> U.LetValue -> m LetValue
convertLV env lv = case lv of
    U.LValue v -> LValue <$> convertV env v
    U.LApp x vs -> do
        vs' <- mapM (convertV env) vs
        case M.lookup x env of
            Just ty -> do
                ty' <- foldM (\tf v -> 
                    case tf of
                        TFun t1 t2 -> t2 <$ getType v `shouldBe` t1
                        _ -> throwError $ OtherError $ "Excepting function") ty vs'
                return $ LApp ty' (Id ty x) vs'
            Nothing -> throwError $ UndefinedVariable x
    U.LExp ptyp e -> do
        ptyp' <- convertP ptyp
        LExp ptyp' <$> convertE env (getType ptyp') e
                

convertV :: (Applicative m,MonadError TypeError m) => Env -> U.Value -> m Value
convertV env v = case v of
    U.Var x -> case M.lookup x env of
        Just ty -> pure $ Var $ Id ty x
        Nothing -> throwError $ UndefinedVariable x
    U.CInt i -> pure $ CInt i
    U.CBool b -> pure $ CBool b
    U.Pair v1 v2 -> Pair <$> convertV env v1 <*> convertV env v2
    U.Op op -> do
        let bin f t v1 v2 = do
            v1' <- convertV env v1
            getType v1' `shouldBe` t
            v2' <- convertV env v2
            getType v2' `shouldBe` t
            return $ f v1' v2'
        Op <$> case op of
            U.OpAdd v1 v2 -> bin OpAdd TInt v1 v2
            U.OpSub v1 v2 -> bin OpSub TInt v1 v2
            U.OpNeg v1    -> bin OpSub TInt (U.CInt 0) v1
            U.OpEq  v1 v2 -> do
                v1' <- convertV env v1
                v2' <- convertV env v2
                getType v1' `shouldBe` getType v2'
                getType v1' `shouldBeIn` [TInt,TBool]
                return $ OpEq v1' v2'
            U.OpLt  v1 v2 -> bin OpLt TInt v1 v2
            U.OpGt  v1 v2 -> bin OpLt TInt v2 v1
            U.OpLte v1 v2 -> bin OpLte TInt v1 v2
            U.OpGte v1 v2 -> bin OpLte TInt v2 v1
            U.OpAnd v1 v2 -> bin OpAnd TBool v1 v2
            U.OpOr  v1 v2 -> bin OpOr TBool v1 v2
            U.OpNot v1    -> do
                v1' <- convertV env v1
                getType v1' `shouldBe` TBool
                return $ OpNot v1'
            U.OpFst v1    -> do
                v1' <- convertV env v1
                (t1,_) <- shouldBePair ("fst" ++ show v1) $ getType v1'
                return $ OpFst t1 v1'
            U.OpSnd v1    -> do
                v1' <- convertV env v1
                (_,t2) <- shouldBePair ("snd" ++ show v1 ++ "," ++ show env++ show (getType v1')) $ getType v1'
                return $ OpSnd t2 v1'


{-
revP :: PType -> U.PType
revP (PInt ps) = U.PInt (map (\(x,v) -> (name x,revV v)) ps)
revP (PBool ps) = U.PBool (map (\(x,v) -> (name x,revV v)) ps)
revP (PFun _ p (x,f)) = U.PFun (revP p) (name x,revP f)

revV :: Value -> U.Value
revV (Var x) = U.Var $ name x
revV (CInt i) = U.CInt i
revV (CBool b) = U.CBool b
revV (Op op) = U.Op $ case op of
    OpAdd v1 v2 -> U.OpAdd (revV v1) (revV v2)
    OpSub v1 v2 -> U.OpSub (revV v1) (revV v2)
    OpEq  v1 v2 -> U.OpEq  (revV v1) (revV v2)
    OpLt  v1 v2 -> U.OpLt  (revV v1) (revV v2)
    OpLte v1 v2 -> U.OpLte (revV v1) (revV v2)
    OpAnd v1 v2 -> U.OpAnd (revV v1) (revV v2)
    OpOr  v1 v2 -> U.OpOr  (revV v1) (revV v2)
    OpNot v1    -> U.OpNot (revV v1)

revE :: Exp -> U.Exp
revE (Value v)      = U.Value (revV v)
revE (Let _ x lv e) = U.Let (name x) (revLV lv) (revE e) 
revE (Assume _ v e) = U.Assume (revV v) (revE e)
revE (Lambda _ x e) = U.Lambda (name x) (revE e)
revE (Fail _)       = U.Fail
revE (Branch _ e1 e2) = U.Branch (revE e1) (revE e2)

revLV :: LetValue -> U.LetValue
revLV (LValue v) = U.LValue (revV v)
revLV (LApp _ x vs) = U.LApp (name x) (map revV vs)
revLV (LExp p e) = U.LExp (revP p) (revE e)
-}
