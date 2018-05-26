{-# LANGUAGE ViewPatterns, LambdaCase #-}
module Language.DMoCHi.ML.Flow( FlowMap, flowAnalysis ) where
import           Control.Monad.Writer hiding ((<>))
import           Control.Monad.State
import qualified Data.HashTable.IO as H
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Sequence as Q
import qualified Data.DList  as DL
import           Data.List (foldl')
import           Data.Hashable
import           Text.PrettyPrint.HughesPJClass
-- import Debug.Trace

import           Language.DMoCHi.ML.Syntax.CEGAR hiding(Label)
import           Language.DMoCHi.Common.Id 
import           Language.DMoCHi.Common.Util

type HashTable k v = H.BasicHashTable k v
type Cache = HashTable Key (S.Set Func)

data Key = KFun UniqueKey | KVar TId Proj | KBody UniqueKey Proj
    deriving(Ord,Eq,Show)

instance Hashable Key where
    hashWithSalt salt (KFun i) = 
        salt `hashWithSalt` (1 :: Int) `hashWithSalt` i
    hashWithSalt salt (KVar x i) = 
        salt `hashWithSalt` (2 :: Int) `hashWithSalt` name x `hashWithSalt` i
    hashWithSalt salt (KBody i j) =
        salt `hashWithSalt` (3 :: Int) `hashWithSalt` i `hashWithSalt` j

data Label = LKey Key | LPair Label Label | LBase
    deriving(Ord,Eq,Show)

type Proj = Integer 

data Edge = ELabel Label Label    -- ELabel l1 l2 <=> C(l1) \supseteq C(l2)
          | EApp TId Key [Label] Label
          deriving(Show)
          -- EApp f l_f ls l_x <=> \forall i \in C(l_f). 
          --                 let (fun ys -> e) = def(i) in
          --                 \forall j \in [0..length ls-1]. C(labelOf (ys !! j)) \supseteq C(ls !! i)
          --                 C(l_x) \supseteq C(LBody i)
instance Pretty Edge where
    pPrintPrec _ prec (ELabel l1 l2) = 
        maybeParens (prec > 0) $ text (show l1) <+> text "->" <+> text (show l2)
    pPrintPrec _ prec (EApp f i ls l_x) = 
        maybeParens (prec > 0) $ 
            text (show l_x) <+> text "->" <+> 
            pPrint f <> parens (pPrint i)  <> text "@" <> parens (hsep (punctuate comma $ map pPrint ls))

instance Pretty Key where
    pPrint (KFun key) = pPrint key
    pPrint (KVar x i) = pPrint x <> text "." <> pPrint i
    pPrint (KBody key i) = pPrint key <> text ".body." <> pPrint i

instance Pretty Label where
    pPrint (LKey key) = pPrint key
    pPrint (LPair l1 l2) = parens $ pPrint l1 <> comma <+> pPrint l2
    pPrint LBase = text "Base"


data Func = Func { funcIdent :: UniqueKey
                 , funcArgs  :: [Label]
                 , funcBody  :: Label }
                 deriving(Eq,Ord, Show)
instance Pretty Func where
    pPrint = text .show 

type Env = M.Map TId Label
type W e = Writer (DL.DList Edge, DL.DList Func) e


addEdge :: Edge -> W ()
addEdge e = tell (pure e, DL.empty)

addFunc :: Func -> W ()
addFunc e = tell (DL.empty, pure e)

genCTerm :: Env -> Label -> Exp -> W ()
genCTerm env l e =
    case expView e of
        EValue v _ -> do
            lv <- genCValue env v
            addEdge $ ELabel l lv
        EOther SLet (x, e1, _, e2) -> 
            case lexpView e1 of
                LAtom av -> do
                    let lv = labelOfAtom env av
                        env' = M.insert x lv env
                    genCTerm env' l e2
                LOther SBranch (e_l, e_r) -> do
                    let l_x = labelOfId x
                        env' = M.insert x l_x env
                    genCTerm env l_x e_l
                    genCTerm env l_x e_r
                    genCTerm env' l e2
                LOther SApp (f, _, vs) -> do
                    let LKey l_f  = env M.! f 
                        l_x  = labelOfId x 
                        env' = M.insert x l_x env
                    l_vs <- mapM (genCValue env) vs
                    addEdge $ EApp f l_f l_vs (labelOfId x)
                    genCTerm env' l e2
                LOther SRand _ -> do
                    let env' = M.insert x LBase env
                    genCTerm env' l e2
        EOther SLetRec (fs, e2) -> do
            let as = [ (f, LKey $ KFun (getUniqueKey v_f)) | (f,v_f) <- fs ]
            let env' = foldr (uncurry M.insert) env as
            forM_ fs $ \(_,v_f) -> do
                let (key_f,xs,e_f) = case v_f of
                        Value SLambda (xs,_, e_f) _ key_f -> (key_f, xs, e_f)
                        _ -> error "unexpected"
                genCFunDef env' (key_f,xs,e_f)
            genCTerm env' l e2
        EOther SAssume (_, e) -> genCTerm env l e
        EOther SFail _ -> return ()
        EOther SOmega _ -> return ()
        EOther SBranch (e1,e2) -> genCTerm env l e1 >> genCTerm env l e2

genCValue :: Env -> Value -> W Label
genCValue env v =
    let key = getUniqueKey v in
    case valueView v of
        VAtom a -> return $ labelOfAtom env a
        VOther SLambda (xs, _, e) -> LKey <$> genCFunDef env (key,xs,e)
        VOther SPair (v1,v2) -> LPair <$> genCValue env v1 <*> genCValue env v2

genCFunDef :: Env -> (UniqueKey, [TId], Exp) -> W Key
genCFunDef env (ident,xs,e) = do
    let l_xs = map labelOfId xs
        env' = foldr (uncurry M.insert) env $ zip xs l_xs
        l_e  = labelOfType (KBody ident) (getType e)
    addFunc $ Func ident l_xs l_e
    genCTerm env' l_e e
    return $ KFun ident

labelOfId :: TId -> Label
labelOfId x = labelOfType (KVar x) (getType x)

labelOfType :: (Integer -> Key) -> Type -> Label
labelOfType f = go 1
    where
    go _ TInt = LBase
    go _ TBool = LBase
    go i (TFun _ _) = LKey $ f i
    go i (TPair ty1 ty2) = LPair (go (2*i) ty1) (go (2*i+1) ty2)

labelOfAtom :: Env -> Atom -> Label
labelOfAtom env (Atom l arg _) =
    case (l,arg) of
        (SLiteral, _) -> LBase
        (SVar, x) -> env M.! x
        (SBinary, _) -> LBase
        (SUnary, UniArg op v)  -> case op of
            SFst -> (\(LPair v1 _) -> v1) $ labelOfAtom env v
            SSnd -> (\(LPair _ v2) -> v2) $ labelOfAtom env v
            SNot -> LBase
            SNeg -> LBase

type Graph = HashTable Key [Key]
type Queue = Q.Seq (Key, [Func])

saturate :: HashTable Key [([Label], Label)] -> Graph -> Cache -> StateT Queue (LoggingT IO) ()
saturate appTbl graph cache = pop >>= \case
    Just (key, values) -> do
        logPretty "flow" LevelDebug "pop" (key, values)
        Just cValues <- liftIO $ H.lookup cache key
        let (nValues, diff) = foldl' (\(vs,ds) v -> if S.member v vs 
                                                     then (vs,ds) 
                                                     else (S.insert v vs, v : ds)) 
                                     (cValues,[]) values
        logPretty "flow" LevelDebug "diff" diff
        unless (null diff) $ do
            liftIO $ H.insert cache key nValues
            Just vs <- liftIO (H.lookup graph key)
            forM_ vs $ \nkey -> push (nkey,diff)
            Just apps <- liftIO (H.lookup appTbl key)
            forM_ apps $ \(l_xs, l_r) ->
              forM_ diff $ \func -> do
                zipWithM_ (decompEdge graph cache) (funcArgs func) l_xs
                decompEdge graph cache l_r (funcBody func)
        saturate appTbl graph cache
    Nothing -> return ()

pop :: MonadState Queue m => m (Maybe (Key,[Func]))
pop = (Q.viewl <$> get) >>= \case 
    v Q.:< queue -> put queue >> return (Just v)
    Q.EmptyL -> return Nothing
    
push :: MonadState Queue m => (Key, [Func]) -> m ()
push v = do
    queue <- get
    put $! queue Q.|> v

decompEdge :: (MonadIO m,MonadState Queue m) => Graph -> Cache -> Label -> Label -> m ()
decompEdge graph cache = go where 
    go (LKey k1) (LKey k2) = when (k1 /= k2) $ do
            Just ks <- liftIO $ H.lookup graph k2
            liftIO $ H.insert graph k2 (k1:ks)
            Just vs <- liftIO $ H.lookup cache k2
            unless (S.null vs) $ push (k1, S.toList vs)
    go (LPair l1 l2) (LPair l3 l4) = go l1 l3 >> go l2 l4
    go LBase LBase = return ()
    go l1 l2 = error $ "decompEdge: " ++ show (l1,l2)

decompLabel :: Label -> [Key]
decompLabel (LKey k) = [k]
decompLabel (LPair l1 l2) = decompLabel l1 ++ decompLabel l2
decompLabel LBase = []

type FlowMap = M.Map TId [UniqueKey]
flowAnalysis :: Program -> LoggingT IO FlowMap 
flowAnalysis (Program e0) = do
    let (cs,funcs) = (\(a,b) -> (DL.toList a, DL.toList b)) $ execWriter $ genCTerm M.empty LBase e0
    logPretty "flow" LevelDebug "Constraints" cs
    let keys = S.toList $ S.fromList $ concat $ 
            map (\case 
                ELabel l1 l2 -> decompLabel l1 ++ decompLabel l2
                EApp _ k ls l -> k : concat (map decompLabel (l:ls))) cs ++
            map (\(Func ident ls l) -> KFun ident : concat (map decompLabel (l:ls))) funcs
    graph <- liftIO H.new
    cache <- liftIO H.new
    appTbl <- liftIO H.new
    liftIO $ forM_ keys $ \key -> do
        H.insert graph key []
        H.insert cache key S.empty
        H.insert appTbl key []
    flip evalStateT Q.empty $ do
        forM_ cs $ \case
            ELabel l1 l2 -> decompEdge graph cache l1 l2
            EApp _ key ls l_r -> liftIO $ do
                Just apps <- H.lookup appTbl key
                H.insert appTbl key ((ls, l_r) : apps)
        forM_ funcs $ \func -> push (KFun (funcIdent func), [func])
        saturate appTbl graph cache

    (r, doc) <- foldM (\(acc,acc_doc) e -> case e of
        EApp f key _ _ -> do
            Just values <- liftIO $ H.lookup cache key
            let vs = map funcIdent $ S.toList values
            let !acc' = M.insert f vs acc
                !acc_doc' = acc_doc $+$ pPrint f <+> text "->" <+> hsep (map pPrint vs)
            return $! (acc', acc_doc')
        _ -> return (acc,acc_doc)) (M.empty, empty) cs
    logPretty "flow" LevelDebug "result" (PPrinted doc)
    return r
