{-# LANGUAGE TupleSections, FlexibleContexts #-}
module Language.DMoCHi.Boolean.IType where 

import Data.Function
import Data.List hiding(elem)
import Text.PrettyPrint
import Language.DMoCHi.Boolean.Flow(Id)
import Data.Hashable
import Data.IORef
import Control.Applicative
import Prelude hiding(elem)
import qualified Language.DMoCHi.Common.Heap as Heap
import qualified Data.HashTable.IO as H
import Control.Monad.Reader
import qualified Data.Set as S

data VType = VT Id
           | VF Id
           | VTup Id ![VType]
           | VFun Id !VFunType

-- sorted by descending order on Id
data VFunType = VNil Id | VAnd Id !VType !TType !VFunType
data TType = TPrim !VType | TFail
data TTypeList = LNil Id | LFail Id 
               | LCons Id VType TTypeList deriving(Show)

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
--    getId (LCons' x _ _) = x

instance Eq TTypeList where
    LNil _ == LNil _ = True
    LFail _ == LFail _ = True
    LCons _ tx1 ts1 == LCons _ tx2 ts2 =
        tx1 === tx2 && ts1 === ts2
--    LCons' _ tx1 ts1 == LCons' _ tx2 ts2 =
--        tx1 === tx2 && ts1 === ts2
    _ == _ = False

instance Ord TTypeList where
    compare = compare `on` getId


instance HasId TType where
    getId TFail = 0
    getId (TPrim x) = 1 + getId x

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
--    hashWithSalt x (LCons' _ tx ts) =
--        x `hashWithSalt` (2 :: Int)
--          `hashWithSalt` getId tx
--          `hashWithSalt` getId ts

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


lnil :: TTypeListCstr
lnil = LNil

lfail :: TTypeListCstr
lfail = LFail

lcons :: VType -> TTypeList -> TTypeListCstr
lcons tx ts = \i -> LCons i tx ts


type HashTable k v = H.BasicHashTable k v

data Factory = Factory { vTypeTable    :: HashTable VType VType
                       , vFunTypeTable :: HashTable VFunType VFunType
                       , tTypeTable    :: HashTable TTypeList TTypeList
                       , mergeMemo     :: HashTable (Id,Id) TTypeList
                       , applyMemo     :: HashTable (Id,Id) TTypeList
                       , insertMemo    :: HashTable (Id,Id) TTypeList
                       , singleMemo    :: HashTable Id TTypeList
                       , counter       :: IORef Int 
                       , queryCounter  :: IORef Int
                       , mergeCounter  :: IORef Int
                       , applyCounter  :: IORef Int
                       , insertCounter :: IORef Int
                       , singleCounter :: IORef Int
                       , costCounter   :: IORef Int
                       , termCounter   :: IORef Int
                       , combCounter   :: IORef Int
                       }

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
        Just _t -> return _t
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

unfoldFun :: VFunType -> [(VType,TType)]
unfoldFun (VNil _) = []
unfoldFun (VAnd _ vx vt vs) = (vx,vt) : unfoldFun vs

applyType :: (MonadReader Factory m, MonadIO m, Functor m) => TTypeList -> TTypeList -> m TTypeList
applyType t1@(LNil _) _ = return t1
applyType t1@(LFail _) _ = return t1
applyType _ t2@(LFail _) = return t2
applyType _ t2@(LNil _)  = return t2
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


mergeTypeList :: (MonadReader Factory m, MonadIO m, Functor m) => TTypeList -> TTypeList -> m TTypeList
mergeTypeList (LNil _) t2 = return t2
mergeTypeList t1 (LNil _) = return t1
mergeTypeList (LFail _) _ = buildTypeList lfail
mergeTypeList _ (LFail _) = buildTypeList lfail
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

concatTypeList :: (MonadReader Factory m, MonadIO m, Functor m) => [TTypeList] -> m TTypeList
concatTypeList [] = buildTypeList lnil
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

isFail :: TTypeList -> Bool
isFail (LFail _) = True
isFail _ = False
