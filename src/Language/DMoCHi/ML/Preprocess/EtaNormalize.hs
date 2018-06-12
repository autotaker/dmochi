module Language.DMoCHi.ML.Preprocess.EtaNormalize(normalize) where

import Language.DMoCHi.ML.Syntax.PNormal hiding(normalize)
import Language.DMoCHi.Common.Id
import Language.DMoCHi.Common.Util

normalize :: Program -> FreshIO c Program
normalize prog = do
    fs' <- mapM (\(f, key, xs, e) -> (f, key, xs,) <$> normalizeT e) (functions prog)
    e' <- normalizeT (mainTerm prog)
    return $ Program fs' e'

etaAtom :: forall m. MonadId m => Atom -> m Value
etaAtom a = 
    case getType a of
        TInt  -> castWith <$> freshKey <*> pure a
        TBool -> castWith <$> freshKey <*> pure a
        TPair _ _ -> do
            v1 <- etaAtom (mkUni SFst a)
            v2 <- etaAtom (mkUni SSnd a)
            mkPair v1 v2 <$> freshKey
        TFun tys ty -> do
            -- f => (\y1 .. yn -> let r = f (etaAtom y1) ... (etaAtom yn) in etaAtom r)
            ys <- mapM (\ty_i -> TId ty_i <$> identify "arg") tys
            e_body <- do
                r <- TId ty <$> identify "r" 
                f <- TId (TFun tys ty) <$> identify "f"
                vs <- mapM (\y -> etaAtom (mkVar y)) ys
                la <- (castWith <$> freshKey <*> pure a) :: m Value
                mkLet f <$> (pure $ cast la)
                        <*> (mkLet r <$> (mkApp f vs <$> freshKey)
                                     <*> (cast <$> etaAtom (mkVar r))
                                     <*> freshKey)
                        <*> freshKey
            mkLambda ys e_body <$> freshKey

normalizeV :: forall m. MonadId m => Value -> m Value
normalizeV v = 
    let key = getUniqueKey v in
    case valueView v of
        VAtom atom -> etaAtom atom
        VOther SPair (v1, v2) -> do
            v1' <- normalizeV v1
            v2' <- normalizeV v2
            return $ mkPair v1' v2' key
        VOther SLambda (xs, e) -> do
            e' <- normalizeT e
            return $ mkLambda xs e' key
    
normalizeL :: forall m. MonadId m => LExp -> m LExp
normalizeL exp =
    let key = getUniqueKey exp
        sty = getType exp
    in case lexpView exp of
        LValue (valueView -> VAtom _) -> return exp
        LValue value -> cast <$> normalizeV value
        LOther SApp (f, vs) -> do
            vs' <- mapM normalizeV vs
            return $ mkApp f vs' key
        LOther SBranch (e1, e2) -> do
            e1' <- normalizeT e1
            e2' <- normalizeT e2
            return $ mkBranchL e1' e2' key
        LOther SFail _ -> return $ mkFailL sty key
        LOther SOmega _ -> return $ mkOmegaL sty key
        LOther SRand _ -> return $ mkRand key

normalizeT :: forall m. MonadId m => Exp ->  m Exp
normalizeT exp = 
    let key = getUniqueKey exp
        sty = getType exp in
    case expView exp of
        EValue v -> cast <$> normalizeV v
        EOther SLet (x, e1, e2) -> do
            e1' <- normalizeL e1
            e2' <- normalizeT e2
            return $ mkLet x e1' e2' key
        EOther SLetRec (ds, e) -> do
            ds' <- mapM (\(f, v) -> (f,) <$> normalizeV v) ds
            e' <- normalizeT e
            return $ mkLetRec ds' e' key
        EOther SAssume (a, e) -> do
            e' <- normalizeT e
            return $ mkAssume a e' key
        EOther SBranch (e1, e2) -> do
            e1' <- normalizeT e1
            e2' <- normalizeT e2
            return $ mkBranch e1' e2' key
        EOther SMark (x, e) -> 
            mkMark x <$> normalizeT e <*> pure key
        EOther SFail _ -> return $ mkFail sty key
        EOther SOmega _ -> return $ mkOmega sty key
