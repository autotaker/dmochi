module Language.DMoCHi.ML.SMT(sat) where

import Language.DMoCHi.ML.Syntax.Typed
import Z3.Monad
import Control.Monad.IO.Class

data IValue = Func | ASTValue AST | IPair IValue IValue

toIValue :: MonadZ3 z3 => Value -> z3 IValue
toIValue (Var x) = case getType x of
    TInt -> do
        y <- mkStringSymbol (name x)
        s <- mkIntSort
        v <- mkConst y s
        return $ ASTValue v
    TBool -> do
        y <- mkStringSymbol (name x)
        s <- mkBoolSort
        v <- mkConst y s
        return $ ASTValue v
    TFun _ _ -> return Func
    TPair t1 t2 -> do
        iv1 <- toIValue (Var $ Id t1 (name x ++ ".fst"))
        iv2 <- toIValue (Var $ Id t2 (name x ++ ".snd"))
        return $ IPair iv1 iv2
toIValue (CInt i) = ASTValue <$> mkInteger i
toIValue (CBool b) = ASTValue <$> mkBool b
toIValue (Pair v1 v2) = IPair <$> toIValue v1 <*> toIValue v2
toIValue (Op op) = case op of
    OpAdd v1 v2 -> do
        ASTValue v1' <- toIValue v1
        ASTValue v2' <- toIValue v2
        ASTValue <$> mkAdd [v1', v2']
    OpSub v1 v2 -> do
        ASTValue v1' <- toIValue v1
        ASTValue v2' <- toIValue v2
        ASTValue <$> mkSub [v1', v2']
    OpEq v1 v2 -> do
        iv1 <- toIValue v1
        iv2 <- toIValue v2
        mkEqIValue iv1 iv2
    OpLt v1 v2 -> do
        ASTValue v1' <- toIValue v1
        ASTValue v2' <- toIValue v2
        ASTValue <$> mkLt v1' v2'
    OpLte v1 v2 -> do
        ASTValue v1' <- toIValue v1
        ASTValue v2' <- toIValue v2
        ASTValue <$> mkLe v1' v2'
    OpAnd v1 v2 -> do
        ASTValue v1' <- toIValue v1
        ASTValue v2' <- toIValue v2
        ASTValue <$> mkAnd [v1',v2']
    OpOr v1 v2 -> do
        ASTValue v1' <- toIValue v1
        ASTValue v2' <- toIValue v2
        ASTValue <$> mkOr [v1',v2']
    OpNot v1 -> do
        ASTValue v1' <- toIValue v1
        ASTValue <$> mkNot v1'
    OpFst _ v -> do
        IPair iv1 _ <- toIValue v
        return iv1
    OpSnd _ v -> do
        IPair _ iv2 <- toIValue v
        return iv2

mkEqIValue :: MonadZ3 z3 => IValue -> IValue -> z3 IValue
mkEqIValue iv1 iv2 = ASTValue <$> go iv1 iv2
    where
    go Func Func = mkTrue
    go (ASTValue v1) (ASTValue v2) = mkEq v1 v2
    go (IPair v1 v2) (IPair v3 v4) = do
        b1 <- go v1 v3
        b2 <- go v2 v4
        mkAnd [b1,b2]

sat :: [Value] -> IO Bool
sat [] = return True
sat vs = evalZ3 $ do
    ivs <- mapM toIValue vs
    assert =<< mkAnd [ v | ASTValue v <- ivs]
    (res, model) <- getModel
    liftIO $ print res
    case res of
        Sat -> do 
            case model of 
                Just m -> showModel m >>= liftIO . putStrLn
                Nothing -> return ()
            return True
        Unsat -> return False
        Undef -> return True



