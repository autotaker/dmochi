{-# LANGUAGE ViewPatterns, LambdaCase #-}
module Language.DMoCHi.ML.Flow( FlowMap, flowAnalysis ) where
import           Control.Monad.Writer
import           Control.Monad.State
import qualified Data.HashTable.IO as H
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Sequence as Q
import qualified Data.DList  as DL
import           Data.List (foldl')
import           Data.Hashable
import           Text.PrettyPrint.HughesPJClass

import           Language.DMoCHi.ML.Syntax.PNormal hiding(Label)
import           Language.DMoCHi.Common.Id 

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
          -- EApp l ls l_x <=> \forall i \in C(l). 
          --                 let (fun ys -> e) = def(i) in
          --                 \forall j \in [0..length ls]. C(labelOf (ys !! j)) \supseteq C(ls !! i)
          --                 C(l_x) \supseteq C(LBody i)
data Func = Func { funcIdent :: UniqueKey
                 , funcArgs  :: [Label]
                 , funcBody  :: Label }
                 deriving(Eq,Ord, Show)

type Env = M.Map TId Label
type W e = Writer (DL.DList Edge, DL.DList Func) e


addEdge :: Edge -> W ()
addEdge e = tell (pure e, DL.empty)

addFunc :: Func -> W ()
addFunc e = tell (DL.empty, pure e)

genCTerm :: Env -> Label -> Exp -> W ()
genCTerm env l (Exp tag arg sty key) =
    let valueCase :: Value -> W ()
        valueCase v = do
            lv <- genCValue env v
            addEdge $ ELabel l lv
    in case (tag, arg) of
        (SLiteral, _) -> valueCase (Value tag arg sty key)
        (SVar,_)      -> valueCase (Value tag arg sty key)
        (SBinary,_)   -> valueCase (Value tag arg sty key)
        (SUnary,_)    -> valueCase (Value tag arg sty key)
        (SPair,_)     -> valueCase (Value tag arg sty key)
        (SLambda,_)   -> valueCase (Value tag arg sty key)
        (SLet,(x, LExp l1 arg1 sty1 key1, e2)) -> 
            let defaultCase e1 = do
                    let l_x = labelOfId x
                        env' = M.insert x l_x env
                    genCTerm env  l_x e1
                    genCTerm env' l   e2
                atomCase av = do
                    let lv = labelOfAtom env av
                        env' = M.insert x lv env
                    genCTerm env' l e2
            in case (l1, arg1) of
                (SLiteral, _) -> atomCase (Atom l1 arg1 sty1)
                (SVar, _)     -> atomCase (Atom l1 arg1 sty1)
                (SBinary, _)  -> atomCase (Atom l1 arg1 sty1)
                (SUnary, _)   -> atomCase (Atom l1 arg1 sty1)
                (SPair, _)    -> defaultCase (Exp l1 arg1 sty1 key1)
                (SLambda, _)  -> defaultCase (Exp l1 arg1 sty1 key1)
                (SFail, _)    -> defaultCase (Exp l1 arg1 sty1 key1)
                (SOmega, _)   -> defaultCase (Exp l1 arg1 sty1 key1)
                (SBranch, _)  -> defaultCase (Exp l1 arg1 sty1 key1)
                (SApp, (f,vs))-> do
                    let LKey l_f  = env M.! f 
                        l_x  = labelOfId x 
                        env' = M.insert x l_x env
                    l_vs <- mapM (genCValue env) vs
                    addEdge $ EApp f l_f l_vs (labelOfId x)
                    genCTerm env' l e2
                (SRand, _) -> do
                    let env' = M.insert x LBase env
                    genCTerm env' l e2
        (SAssume, (_,e)) -> genCTerm env l e 
        (SFail, _) -> return ()
        (SOmega, _) -> return ()
        (SBranch, (e1, e2)) -> genCTerm env l e1 >> genCTerm env l e2


genCValue :: Env -> Value -> W Label
genCValue env (Value tag arg sty key) =
    case (tag, arg) of
        (SLiteral, _) -> return $ labelOfAtom env (Atom tag arg sty)
        (SVar, _)     -> return $ labelOfAtom env (Atom tag arg sty)
        (SUnary, _)   -> return $ labelOfAtom env (Atom tag arg sty)
        (SBinary, _)  -> return $ labelOfAtom env (Atom tag arg sty)
        (SLambda, (xs,e)) -> LKey <$> genCFunDef env (key,xs,e)
        (SPair, (v1,v2)) -> LPair <$> genCValue env v1 <*> genCValue env v2

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

saturate :: HashTable Key [([Label], Label)] -> Graph -> Cache -> StateT Queue IO ()
saturate appTbl graph cache = pop >>= \case
    Just (key, values) -> do
        liftIO $ putStrLn "pop" 
        liftIO $ putStrLn $ "key:" ++ show key
        liftIO $ putStrLn $ "values:" ++ show values
        Just cValues <- liftIO $ H.lookup cache key
        let (nValues, diff) = foldl' (\(vs,ds) v -> if S.member v vs 
                                                     then (vs,ds) 
                                                     else (S.insert v vs, v : ds)) 
                                     (cValues,[]) values
        liftIO $ putStrLn $ "diff:" ++ show diff
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

type FlowMap = M.Map TId [UniqueKey]
flowAnalysis :: Program -> IO FlowMap 
flowAnalysis (Program fs e0) = do
    let (cs,funcs) = (\(a,b) -> (DL.toList a, DL.toList b)) $ execWriter $ do
            let env = M.fromList [ (f, LKey $ KFun key)  | (f, key, _, _) <- fs ]
            mapM_ (\(_,key, xs, e) -> genCFunDef env (key,xs,e)) fs
            genCTerm env LBase e0
    putStrLn "Constraints"
    print cs
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
            let vs = map funcIdent $ S.toList values
            liftIO $ print $ pPrint f <+> text "->" <+> hsep (map pPrint vs)
            return $! M.insert f vs acc
        _ -> return acc) M.empty cs
