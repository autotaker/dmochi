{-# LANGUAGE ViewPatterns, LambdaCase #-}
module Language.DMoCHi.ML.Flow where
import qualified Data.HashTable.IO as H
import Language.DMoCHi.ML.Syntax.PNormal
import qualified Data.Set as S
import qualified Data.Map as M
import Data.List (foldl')
import qualified Data.Sequence as Q
import qualified Data.DList  as DL
import Control.Monad.Writer
import Control.Monad.State
import Data.Hashable

type HashTable k v = H.BasicHashTable k v
type Cache = HashTable Key (S.Set Func)

data Key = KFun Int | KVar Id Proj | KBody Int Proj
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
          | EApp Id Key [Label] Label
          -- EApp l ls l_x <=> \forall i \in C(l). 
          --                 let (fun ys -> e) = def(i) in
          --                 \forall j \in [0..length ls]. C(labelOf (ys !! j)) \supseteq C(ls !! i)
          --                 C(l_x) \supseteq C(LBody i)
data Func = Func { funcIdent :: Int
                 , funcArgs  :: [Label]
                 , funcBody  :: Label }
                 deriving(Eq,Ord)

type Env = M.Map Id Label
type W e = Writer (DL.DList Edge, DL.DList Func) e


addEdge :: Edge -> W ()
addEdge e = tell (pure e, DL.empty)

addFunc :: Func -> W ()
addFunc e = tell (DL.empty, pure e)

genCTerm :: Env -> Label -> Exp -> W ()
genCTerm env l (Value v) = do
    lv <- genCValue env v
    addEdge $ ELabel l lv
genCTerm env l (Let _ x (LValue av) e) = genCTerm env' l e 
    where
    lv = labelOfAValue env av
    env' = M.insert x lv env
genCTerm env l (Let _ x (LApp _ _ f vs) e) = do
    l_vs <- mapM (genCValue env) vs
    addEdge $ EApp f l_f l_vs (labelOfId x)
    genCTerm env' l e
    where
    LKey l_f  = env M.! f
    l_x  = labelOfId x
    env' = M.insert x l_x env
genCTerm env l (Let _ x (LExp _ e1) e2) = 
    genCTerm env l_x e1 >> genCTerm env' l e2
    where
    l_x = labelOfId x
    env' = M.insert x l_x env
genCTerm env l (Let _ x LRand e) = genCTerm env' l e
    where
    env' = M.insert x LBase env
genCTerm env l (Assume _ _ e) = genCTerm env l e
genCTerm _ _ (Fail _) = return ()
genCTerm env l (Branch _ _ e1 e2) = 
    genCTerm env l e1 >> genCTerm env l e2

genCValue :: Env -> Value -> W Label
genCValue env (Atomic av) = return $ labelOfAValue env av
genCValue env (Fun fdef) = LKey <$> genCFunDef env fdef
genCValue env (Pair v1 v2) = LPair <$> genCValue env v1 <*> genCValue env v2

genCFunDef :: Env -> FunDef -> W Key
genCFunDef env (FunDef ident xs e) = do
    let l_xs = map labelOfId xs
        env' = foldr (uncurry M.insert) env $ zip xs l_xs
        l_e  = labelOfType (KBody ident) (getType e)
    addFunc $ Func ident l_xs l_e
    genCTerm env' l_e e
    return $ KFun ident

labelOfId :: Id -> Label
labelOfId x = labelOfType (KVar x) (getType x)

labelOfType :: (Integer -> Key) -> Type -> Label
labelOfType f = go 1
    where
    go i TInt = LKey $ f i
    go i TBool = LKey $ f i
    go i (TFun _ _) = LKey $ f i
    go i (TPair ty1 ty2) = LPair (go (2*i) ty1) (go (2*i+1) ty2)

labelOfAValue :: Env -> AValue -> Label
labelOfAValue env (Var x) = env M.! x
labelOfAValue _ (CInt _) = LBase
labelOfAValue _ (CBool _) = LBase
labelOfAValue env (Op op) = case op of
    OpAdd _ _ -> LBase
    OpSub _ _ -> LBase
    OpEq _ _ -> LBase
    OpLt _ _ -> LBase
    OpLte _ _ -> LBase
    OpAnd _ _ -> LBase
    OpOr _ _ -> LBase
    OpFst _ av -> (\(LPair v1 _) -> v1) $ labelOfAValue env av
    OpSnd _ av -> (\(LPair _ v2) -> v2) $ labelOfAValue env av
    OpNot _ -> LBase


type Graph = HashTable Key [Key]
type Queue = Q.Seq (Key, [Func])

saturate :: HashTable Key [([Label], Label)] -> Graph -> Cache -> StateT Queue IO ()
saturate appTbl graph cache = pop >>= \case
    Just (key, values) -> do
        Just cValues <- liftIO $ H.lookup cache key
        let (nValues, diff) = foldl' (\(vs,ds) v -> if S.member v vs 
                                                     then (vs,ds) 
                                                     else (S.insert v vs, v : ds)) 
                                     (cValues,[]) values
        when (null diff) $ do
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

pop :: StateT Queue IO (Maybe (Key,[Func]))
pop = (Q.viewl <$> get) >>= \case 
    v Q.:< queue -> put queue >> return (Just v)
    Q.EmptyL -> return Nothing
    
push :: (Key, [Func]) -> StateT Queue IO ()
push v = do
    queue <- get
    put $! queue Q.|> v

decompEdge :: Graph -> Cache -> Label -> Label -> StateT Queue IO ()
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

flowAnalysis :: Program -> IO (M.Map Id [Int])
flowAnalysis (Program fs e0) = do
    let (cs,funcs) = (\(a,b) -> (DL.toList a, DL.toList b)) $ execWriter $ do
            let env = M.fromList [ (f, LKey $ KFun (ident fdef))  | (f, fdef) <- fs ]
            mapM_ (genCFunDef env . snd) fs
            genCTerm env LBase e0
    let keys = S.toList $ S.fromList $ concat $ 
            map (\case 
                ELabel l1 l2 -> decompLabel l1 ++ decompLabel l2
                EApp _ k ls l -> k : concat (map decompLabel (l:ls))) cs ++
            map (\(Func _ ls l) -> concat (map decompLabel (l:ls))) funcs
    graph <- H.new :: IO Graph
    cache <- H.new :: IO Cache
    appTbl <- H.new
    forM_ keys $ \key -> do
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

    foldM (\acc e -> case e of
        EApp f key _ _ -> do
            Just values <- H.lookup cache key
            return $! M.insert f (map funcIdent $ S.toList values) acc
        _ -> return acc) M.empty cs
