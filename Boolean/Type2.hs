{-# LANGUAGE TupleSections, FlexibleContexts #-}
module Boolean.Type2(saturate,Context(..)) where
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Arrow(second)
import Control.Applicative
import Boolean.Syntax
import Boolean.Flow(FlowGraph,Id)
import Control.Monad
--import Boolean.Util
import Data.Array
import Data.Array.IO
import Data.Maybe
import qualified Data.HashTable.IO as H
import Data.Hashable
import Data.IORef
import Control.Monad.Reader
import Data.List hiding (elem)
import Prelude hiding(elem)
import Data.Function(on)
import qualified Heap
import Text.PrettyPrint
import Text.Printf

data VType = VT Id
           | VF Id
           | VTup Id ![VType]
           | VFun Id !VFunType

data VFunType = VNil Id | VAnd Id !VType !TType !VFunType
data TType = TPrim !VType | TFail
data TTypeList = LNil Id | LFail Id | LCons Id VType TTypeList

instance Show VType where
    showsPrec _ (VT _) = showString "T"
    showsPrec _ (VF _) = showString "F"
    showsPrec _ (VTup _ []) = showString "[]"
    showsPrec _ (VTup _ ts) = 
        showChar '[' . (foldl1 (.) $ intersperse (showString ", ") $ map (showsPrec 0) ts) . showChar ']'
    showsPrec p (VFun _ f) = showsPrec p f

instance Show VFunType where
    showsPrec _ (VNil _) = showString "Top"
    showsPrec p t = s where
        go (VNil _) = []
        go (VAnd _ tx tt ts) = 
            foldl1 (.) (intersperse (showChar ' ') [showsPrec 1 tx,showString "->",showsPrec 0 tt]) : go ts
        l = go t
        s = case l of
            [ss] | p == 0 -> ss
            _ -> foldl1 (.) $ intersperse (showString " ^ ") $ map (\x -> showChar '(' . x . showChar ')') l

instance Show TType where
    showsPrec p (TPrim t) = showsPrec p t
    showsPrec _ TFail     = showString "Fail"

ppV :: Int -> VType -> Doc
ppV _ (VT _) = text "T"
ppV _ (VF _) = text "F"
ppV _ (VTup _ ts) = brackets $ hsep $ punctuate (text ",") $ map (ppV 0) ts
ppV p (VFun _ f)  = ppF p f

ppF :: Int -> VFunType -> Doc
ppF _ (VNil _) = text "Top"
ppF p t = s where
    go (VNil _) = []
    go (VAnd _ tx tt ts) = (ppV 1 tx <+> text "->" <+> ppT 0 tt) : go ts
    l = go t
    s = case l of
        [ss] | p == 0 -> ss
        _ -> vcat $ punctuate (text "^") $ map parens l
ppT :: Int -> TType -> Doc
ppT p (TPrim t) = ppV p t
ppT _ TFail     = text "Fail"

class HasId t where
    getId :: t -> Id

(===) :: HasId t => t -> t -> Bool
(===) = (==) `on` getId

instance HasId VType where
    getId (VT x) = x
    getId (VF x) = x
    getId (VTup x _) = x
    getId (VFun x _) = x

instance Eq VType where
    VT _ == VT _ = True
    VF _ == VF _ = True
    VTup _ ts == VTup _ ts' = ((==) `on` map getId) ts ts'
    VFun _ f1 == VFun _ f2  = f1 === f2
    _ == _ = False

instance HasId VFunType where
    getId (VNil x) = x
    getId (VAnd x _ _ _) = x

instance Eq VFunType where
    VNil _ == VNil _ = True
    VAnd _ tx1 tf1 vs1 == VAnd _ tx2 tf2 vs2 =
        tx1 === tx2 &&
        tf1 === tf2 &&
        vs1 === vs2
    _ == _ = False

instance HasId TTypeList where
    getId (LNil x) = x
    getId (LFail x) = x
    getId (LCons x _ _) = x

instance Eq TTypeList where
    LNil _ == LNil _ = True
    LFail _ == LFail _ = True
    LCons _ tx1 ts1 == LCons _ tx2 ts2 =
        tx1 === tx2 && ts1 === ts2
    _ == _ = False

instance HasId TType where
    getId TFail = 0
    getId (TPrim x) = 1 + getId x

type HashTable k v = H.BasicHashTable k v

data Factory = Factory { vTypeTable :: HashTable VType VType
                       , vFunTypeTable :: HashTable VFunType VFunType
                       , tTypeTable :: HashTable TTypeList TTypeList
                       , mergeMemo :: HashTable (Id,Id) TTypeList
                       , applyMemo :: HashTable (Id,Id) TTypeList
                       , insertMemo :: HashTable (Id,Id) TTypeList
                       , singleMemo :: HashTable Id TTypeList
                       , counter :: IORef Int 
                       , queryCounter :: IORef Int
                       , mergeCounter :: IORef Int
                       , applyCounter :: IORef Int
                       , insertCounter :: IORef Int
                       , singleCounter :: IORef Int
                       }

instance Hashable VType where
    hashWithSalt x (VT _) = x `hashWithSalt` (0 :: Int)
    hashWithSalt x (VF _) = x `hashWithSalt` (1 :: Int)
    hashWithSalt x (VTup _ ts) = 
        foldl' hashWithSalt (x `hashWithSalt` (2::Int)) (map getId ts)
    hashWithSalt x (VFun _ f ) = 
        x `hashWithSalt` (3::Int) `hashWithSalt` getId f

instance Hashable VFunType where
    hashWithSalt x (VNil _) = x `hashWithSalt` (0 :: Int)
    hashWithSalt x (VAnd _ vx vt vs) = 
        x `hashWithSalt` (1 :: Int)
          `hashWithSalt` getId vx
          `hashWithSalt` getId vt
          `hashWithSalt` getId vs

instance Hashable TTypeList where
    hashWithSalt x (LNil _) = x `hashWithSalt` (0 :: Int)
    hashWithSalt x (LFail _) = x `hashWithSalt` (1 :: Int)
    hashWithSalt x (LCons _ tx ts) =
        x `hashWithSalt` (2 :: Int)
          `hashWithSalt` getId tx
          `hashWithSalt` getId ts

type VTypeCstr = Id -> VType
type VFunTypeCstr = Id -> VFunType
type TTypeListCstr = Id -> TTypeList
bool :: Bool -> VTypeCstr 
bool True = VT
bool False = VF

tup :: [VType] -> VTypeCstr
tup ts = \i -> VTup i ts

func :: VFunType -> VTypeCstr
func x = flip VFun x

fnil :: VFunTypeCstr
fnil = VNil

fand :: VType -> TType -> VFunType -> VFunTypeCstr
fand tx tb ts = \i -> VAnd i tx tb ts

fand' :: VType -> VType -> VFunType -> VFunTypeCstr
fand' tx tb ts = \i -> VAnd i tx (TPrim tb) ts

lnil :: TTypeListCstr
lnil = LNil

lfail :: TTypeListCstr
lfail = LFail

lcons :: VType -> TTypeList -> TTypeListCstr
lcons tx ts = \i -> LCons i tx ts

newFactory :: IO Factory
newFactory = Factory <$> H.new 
                     <*> H.new
                     <*> H.new
                     <*> H.new
                     <*> H.new
                     <*> H.new
                     <*> H.new
                     <*> newIORef 0
                     <*> newIORef 0
                     <*> newIORef 0
                     <*> newIORef 0
                     <*> newIORef 0
                     <*> newIORef 0

incr :: (MonadReader Factory m, MonadIO m, Functor m) => (Factory -> IORef Int) -> m ()
incr c = do
    x <- fmap c ask
    i <- liftIO $ readIORef x
    liftIO $ writeIORef x $! (i+1)


buildTypeBase :: (MonadReader Factory m, MonadIO m, Functor m, 
                  Hashable a, Eq a) => (Factory -> HashTable a a) -> (Id -> a) -> m a
buildTypeBase sel cstr = do
    let t' = cstr undefined
    tbl <- sel `fmap` ask 
    r <- liftIO $ H.lookup tbl t'
    incr queryCounter
    case r of
        Just t'' -> return t''
        Nothing -> do
            c <- fmap counter ask 
            i <- liftIO $ readIORef c
            liftIO $ writeIORef c $! (i+1)
            let t'' = cstr i
            liftIO $ H.insert tbl t'' t''
            return t''

buildType :: (MonadReader Factory m, MonadIO m, Functor m) => VTypeCstr -> m VType
buildType cstr = {-# SCC buildType #-} buildTypeBase vTypeTable cstr

buildFunType :: (MonadReader Factory m, MonadIO m, Functor m) => VFunTypeCstr -> m VFunType
buildFunType cstr = {-# SCC buildFunType #-} buildTypeBase vFunTypeTable cstr

buildTypeList :: (MonadReader Factory m, MonadIO m, Functor m) => TTypeListCstr -> m TTypeList
buildTypeList cstr = {-# SCC buildTypeList #-} buildTypeBase tTypeTable cstr

insertType :: (MonadReader Factory m, MonadIO m, Functor m) => TType -> TTypeList -> m TTypeList
insertType TFail _ = {-# SCC buildTypeList241 #-} buildTypeList lfail
insertType _ t@(LFail _) = return t
insertType (TPrim t) ts@(LNil _) = {-# SCC buildTypeList244 #-} buildTypeList (lcons t ts)
insertType (TPrim t) ts@(LCons _ vx ts') = do
    incr insertCounter
    if getId vx < getId t then
        {-# SCC buildTypeList248 #-} buildTypeList (lcons t ts)
    else if getId vx == getId t then
        return ts
    else 
        insertType (TPrim t) ts' >>= {-# SCC buildTypeList252 #-} buildTypeList . lcons vx

singleton :: (MonadReader Factory m, MonadIO m, Functor m) => VType -> m TTypeList
singleton t = do
    incr singleCounter
    tbl <- singleMemo <$> ask
    m <- liftIO $ H.lookup tbl (getId t)
    case m of
        Just t -> return t
        Nothing -> do
            nil <- {-# SCC buildTypeList257 #-} buildTypeList lnil
            t' <- {-# SCC buildTypeList258 #-} buildTypeList $ lcons t nil
            liftIO $ H.insert tbl (getId t) t'
            return t'


toFunType :: (MonadReader Factory m, MonadIO m, Functor m) => [(VType,TTypeList)] -> m VFunType
toFunType ts = do
    let ts1 = reverse $ sortBy (compare `on` getId.fst) ts
    let unfoldType (LNil _) = []
        unfoldType (LFail _) = [TFail]
        unfoldType (LCons _ vx ts') = TPrim vx : unfoldType ts'
    let ts2 = reverse [ (vx,t) | (vx,vt) <- ts1, t <- unfoldType vt ]
    t0 <- buildFunType fnil
    foldM (\acc (vx,t) -> buildFunType (fand vx t acc)) t0 ts2

unfoldV :: TTypeList -> [VType]
unfoldV (LNil _) = []
unfoldV (LCons _ vx vs) = vx : unfoldV vs
unfoldV (LFail _) = undefined

applyType :: TTypeList -> TTypeList -> M TTypeList
applyType t1@(LNil _) _ = return t1
applyType t1@(LFail _) _ = return t1
applyType _ t2@(LFail _) = return t2
applyType ts tx = do
    tbl <- applyMemo <$> ask
    incr applyCounter
    let key = (getId ts,getId tx)
    m <- liftIO $ H.lookup tbl key
    case m of
        Just t -> return t
        Nothing -> do
            let unfoldFun (VNil _) = []
                unfoldFun (VAnd _ vx vt vs) = (vx,vt) : unfoldFun vs
            let sx = S.fromList $ map getId $ unfoldV tx
            let res = do VFun _ vs <- unfoldV ts 
                         (tx',tb) <- unfoldFun vs 
                         guard $ S.member (getId tx') sx 
                         return tb
            t0 <- {-# SCC buildTypeList294 #-} buildTypeList lnil
            t <- foldM (\acc t -> insertType t acc) t0 $ sortBy (compare `on` getId) res
            liftIO $ H.insert tbl key t
            return t


mergeTypeList :: TTypeList -> TTypeList -> M TTypeList
mergeTypeList (LNil _) t2 = return t2
mergeTypeList t1 (LNil _) = return t1
mergeTypeList (LFail _) _ = {-# SCC buildTypeList303 #-} buildTypeList lfail
mergeTypeList _ (LFail _) = {-# SCC buildTypeList304 #-} buildTypeList lfail
mergeTypeList t1@(LCons k1 vx1 vs1) t2@(LCons k2 vx2 vs2) = do
    tbl <- mergeMemo <$> ask
    incr mergeCounter
    m <- liftIO $ H.lookup tbl (k1,k2) 
    case m of
        Just t -> return t
        Nothing -> do
            t <- if getId vx1 < getId vx2 then 
                    mergeTypeList t1 vs2 >>= {-# SCC buildTypeList313 #-} buildTypeList . lcons vx2
                else if getId vx1 == getId vx2 then
                    mergeTypeList vs1 vs2 >>= {-# SCC buildTypeList315 #-} buildTypeList .lcons vx1
                else 
                    mergeTypeList vs1 t2 >>= {-# SCC buildTypeList317 #-} buildTypeList . lcons vx1
            liftIO $ H.insert tbl (k1,k2) t
            return t

lsize :: TTypeList -> Int
lsize (LNil _) = 0
lsize (LFail _) = 0
lsize (LCons _ _ xs) = 1 + lsize xs

newtype Fst a b = Fst { unFst :: (a,b) } deriving(Eq)
instance (Ord a,Eq b) => Ord (Fst a b) where
    compare = compare `on` fst . unFst

concatTypeList :: [TTypeList] -> M TTypeList
concatTypeList [] = {-# SCC buildTypeList331 #-} buildTypeList lnil
concatTypeList ts = go q0 where
    q0 = foldr (\x acc -> Heap.insert (Fst (lsize x,x)) acc) Heap.empty ts
    go queue = do
        let Fst (s1,t1) = Heap.minElem queue
        let queue' = Heap.deleteMin queue
        if Heap.isEmpty queue' then
            return t1
        else do
            let Fst (s2,t2) = Heap.minElem queue'
            let queue'' = Heap.deleteMin queue'
            t3 <- mergeTypeList t1 t2
            let m3 = Fst (s1+s2,t3)
            go (Heap.insert m3 queue'')

elem :: VType -> TTypeList -> Bool
elem x (LCons _ y xs) = x == y || elem x xs
elem _ _ = False

type M a = ReaderT Factory IO a
data Context = Context { flowEnv :: M.Map Symbol TTypeList
                       , symEnv  :: M.Map Symbol  VType } deriving(Eq)

saturateFlow :: FlowGraph -> M.Map Symbol VType -> M (M.Map Symbol TTypeList)
saturateFlow (edgeTbl,symMap,leafTbl) env = do
    let terms = [ (i,t) | (i,Just t) <- assocs leafTbl]
        fvarMap = M.fromList $ map (\(i,t) -> (i,freeVariables t \\ M.keys env)) terms
        bvarMap = M.fromList $ map (\(i,t) -> (i,boundVariables t)) terms
    let bb = bounds edgeTbl
    let depTbl :: Array Id [Id]
        depTbl = accumArray (flip (:)) [] bb $
                 [ (t,s) | (s,ts) <- assocs edgeTbl, t <- ts ] ++
                 [ (symMap M.! x, s) | (s, Just _) <- assocs leafTbl, 
                                       x <- nub $ fvarMap M.! s ++ bvarMap M.! s ]
    nil <- {-# SCC buildTypeList365 #-} buildTypeList lnil
    arr <- liftIO $ (newArray (bounds leafTbl) nil :: IO (IOArray Id TTypeList))
    let go s | S.null s = return ()
             | otherwise = do
            let (v,vs) = S.deleteFindMin s
            ty <- liftIO $ readArray arr v
            ty' <- case leafTbl ! v of
                Nothing -> do
                    tys <- forM (edgeTbl ! v) $ liftIO . readArray arr
                    concatTypeList $ ty : tys
                Just (V _) -> do
                    tys <- forM (edgeTbl ! v) $ liftIO . readArray arr
                    concatTypeList $ ty : tys
                Just t -> do
                    let fvars = fvarMap M.! v
                    let bvars = bvarMap M.! v
                    tys <- forM fvars $ liftIO . readArray arr . (symMap M.!)
                    m <- M.fromList <$> forM bvars (\x -> (x,) <$> liftIO (readArray arr (symMap M.! x)))
                    ls <- forM (sequence $ map unfoldV tys) $ \l -> do
                        let env' = updateEnv env (zip fvars l)
                        res <- saturateTerm m env' t 
                        case res of
                            LFail _ -> {-# SCC buildTypeList387 #-} buildTypeList lnil
                            tyl -> return tyl
                    concatTypeList ls
            if ty' === ty 
                then go vs
                else liftIO (writeArray arr v ty') >> go (foldr S.insert vs (depTbl ! v))
    go $ S.fromList $ [ i | (i,Just _) <- assocs leafTbl]
    fmap M.fromList $ forM (M.assocs symMap) $ \(f,i) -> do
        v <- liftIO $ readArray arr i
        return (f,v)

saturateSym :: M.Map Symbol TTypeList -> M.Map Symbol VType -> [Def] -> M (M.Map Symbol VType)
saturateSym _flowEnv _symEnv defs = do
    fmap M.fromList $ forM defs $ \(x,t) -> do
        LCons _ ty _  <- saturateTerm _flowEnv _symEnv t
        return (x,ty)

updateEnv :: M.Map Symbol VType -> [(Symbol,VType)] -> M.Map Symbol VType
updateEnv = foldl (\acc (x,ty) -> M.insert x ty acc)

saturateTerm :: M.Map Symbol TTypeList -> M.Map Symbol VType -> Term -> M TTypeList
saturateTerm _flowEnv _t = {-# SCC saturateTerm_go #-} go _t where
    go _ (C b) = {-# SCC saturateTerm_go_C #-} buildType (bool b) >>= singleton
    go env (V x) = {-# SCC saturateTerm_go_V #-}singleton (env M.! x)
    go _ (Fail _) = {-# SCC saturateTerm_go_Fail #-}{-# SCC buildTypeList411 #-} buildTypeList lfail
    go _ TF = {-# SCC saturateTerm_go_TF #-}
              do t1 <- buildType (bool True)  >>= singleton
                 t2 <- buildType (bool False) >>= singleton
                 mergeTypeList t1 t2
    go _ (Omega _) = {-# SCC saturateTerm_go_Omega #-} {-# SCC buildTypeList415 #-} buildTypeList lnil
    go env (Lam x t) = {-# SCC saturateTerm_go_Lam #-}do
        as <- forM (unfoldV $ _flowEnv M.! x) $ \tyx -> do
            tl <- go (M.insert x tyx env) t
            return $ (tyx,tl)
        toFunType as >>= buildType . func >>= singleton
    go env (App t1 t2) = {-# SCC saturateTerm_go_App #-}do
        ty1 <- go env t1
        ty2 <- go env t2
        applyType ty1 ty2
    go env (If t1 t2 t3) = {-# SCC saturateTerm_go_If #-}do
        ty1 <- go env t1
        case ty1 of
            LFail _ -> {-# SCC buildTypeList428 #-} buildTypeList lfail
            LNil  _ -> {-# SCC buildTypeList429 #-} buildTypeList lnil
            _       -> do
                xs <- if VT undefined `elem` ty1 then 
                        go env t2 
                      else {-# SCC buildTypeList433 #-} buildTypeList lnil
                ys <- if VF undefined `elem` ty1 then 
                        go env t3 
                      else {-# SCC buildTypeList436 #-} buildTypeList lnil
                mergeTypeList xs ys
    go env (T ts) = {-# SCC saturateTerm_go_T #-}do
        tys <- forM ts $ go env 
        let check = foldr (\tyi acc -> 
                        (LFail undefined == tyi) || (LNil undefined /= tyi && acc)) False
        if check tys then
            {-# SCC buildTypeList443 #-} buildTypeList lfail
        else do
            let tys' = map unfoldV tys
            -- can be exponatial
            tys'' <- forM (sequence tys') $ buildType . tup
            let sorted = sortBy (compare `on` getId) tys''
            t0 <- {-# SCC buildTypeList449 #-} buildTypeList lnil
            foldM (\acc t -> {-# SCC buildTypeList450 #-} buildTypeList $ lcons t acc) t0 sorted
    go env (Let x t1 t2) = {-# SCC saturateTerm_go_Let #-}do
        ty1 <- go env t1
        case ty1 of
            LFail _ -> {-# SCC buildTypeList454 #-} buildTypeList lfail
            _ -> (forM (unfoldV ty1) $ \tyx -> go (M.insert x tyx env) t2) >>= concatTypeList
    go env (Proj n _ t) = {-# SCC saturateTerm_go_Proj #-}do
        tys <- go env t
        case tys of
            LFail _ -> {-# SCC buildTypeList459 #-} buildTypeList lfail
            _ -> do
                let tys' = map (\(VTup _ ts) -> ts !! projN n) $ unfoldV tys
                let sorted = map head $ groupBy (===) $ sortBy (compare `on` getId) tys'
                t0 <- {-# SCC buildTypeList463 #-} buildTypeList lnil
                foldM (\acc _t -> {-# SCC buildTypeList464 #-} buildTypeList $ lcons _t acc) t0 sorted

initContext :: Program -> FlowGraph -> M Context
initContext (Program defs _) (_,mapSym,_) = do
    nil <- {-# SCC buildTypeList468 #-} buildTypeList lnil
    ty  <- buildFunType fnil >>= buildType . func
    return $ Context (fmap (const nil) mapSym) (M.fromList (map (second (const ty)) defs))

saturate :: Program -> FlowGraph -> IO (Bool,Context)
saturate p flow = newFactory >>= runReaderT (loop =<< initContext p flow) where
    loop ctx = do
        env1 <- saturateFlow flow (symEnv ctx)
        env2 <- saturateSym env1 (symEnv ctx) (definitions p)
        factory <- ask
        liftIO $ do
            putStrLn "----------ENV----------" 
            forM_ (M.assocs env2) $ \ (x,l) -> do
                putStrLn $ x ++ ":"
                putStrLn $ render $ nest 4 $ ppV 0 l
                putStrLn ""
            readIORef (counter      factory) >>= printf "Counter :%8d\n"
            readIORef (queryCounter factory) >>= printf "Queries :%8d\n"
            readIORef (mergeCounter factory) >>= printf "Merge   :%8d\n"
            readIORef (applyCounter factory) >>= printf "Apply   :%8d\n"
            readIORef (insertCounter factory)>>= printf "Insert  :%8d\n"
            readIORef (singleCounter factory)>>= printf "Single  :%8d\n"
            putStrLn ""
        t0 <- saturateTerm env1 env2 (mainTerm p)
        let ctx' = Context env1 env2
        case t0 of
            LFail _ -> return (False,ctx')
            _ | env2 == symEnv ctx -> return (True,ctx')
              | otherwise          -> loop ctx'
