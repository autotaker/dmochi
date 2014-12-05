{-# LANGUAGE ViewPatterns,BangPatterns #-}
module SortCheck(sortCheck) where
import Control.Monad.Except
import Control.Monad.Writer
import Control.Monad.State
import Control.Applicative

import Sort
import Syntax
import Util
import qualified Data.Sequence as Q
import qualified Data.Map as M
import Data.Traversable(traverse)

sortCheck :: Program -> [Symbol] -> Either Err (M.Map Symbol Sort)
sortCheck prog syms = runExcept $ do
    (env,cs) <- runWriterT (gather prog syms)
    subst <- unify cs
    substEnv env subst

type Env = M.Map Symbol SortLike
type Id = Int
data SortLike = SBase | SVar Id | STup [SortLike] | SFun SortLike SortLike deriving(Show)

type Constraints = Q.Seq (SortLike,SortLike)
type Subst = M.Map Id SortLike
type WMonad a = WriterT Constraints (Except Err) a
type SWM a = StateT Id (WriterT Constraints (Except Err)) a

gather :: Program -> [Symbol] -> WMonad Env
gather prog syms = do
    let env = M.fromList $ zip syms $ map SVar [0..]
        n = M.size env
    evalStateT (gatherP prog env) n
    return env

shouldBe :: SortLike -> SortLike -> SWM ()
shouldBe !s1 !s2 = tell $ Q.singleton (s1,s2)

genFresh :: SWM SortLike
genFresh = (SVar <$> get) <* modify succ
        
gatherP :: Program -> Env -> SWM ()
gatherP (Program defs t0) env = do
    forM_ defs $ \(f,t) -> do
        s <- gatherT t env
        s `shouldBe` (env M.! f)
    s0 <- gatherT t0 env
    s0 `shouldBe` STup []

gatherT :: Term -> Env -> SWM SortLike
gatherT _t env = go _t where
    go _t = case _t of
        C _ -> pure SBase
        TF  -> pure SBase
        V x -> pure $ env M.! x
        T ts -> STup <$> mapM go ts
        Fail x -> pure $ env M.! x
        Omega x -> pure $ env M.! x
        Lam x t -> SFun (env M.! x) <$> go t
        Proj n d t -> do
            st <- go t
            l <- replicateM (projD d) genFresh
            st `shouldBe` STup l
            return (l !! (projN n))
        Let x t1 t2 -> do
            s1 <- go t1
            s1 `shouldBe` (env M.! x)
            go t2
        App t1 t2 -> do
            ss <- go t2
            s  <- go t1
            s1  <- genFresh
            s `shouldBe` SFun ss s1
            return s1
    {-
        t1 :+: t2 -> do
            s1 <- gatherT t1 env
            s2 <- gatherT t2 env
            s1 `shouldBe` s2
            return s1
            -}
        If tp tt te -> do
            sp <- go tp
            st <- go tt
            se <- go te
            sp `shouldBe` SBase
            st `shouldBe` se
            return st
        
unify :: Constraints -> Except Err Subst
unify _cs = execStateT (go _cs) M.empty
    where
    go (Q.viewl -> v) = case v of
        Q.EmptyL -> return ()
        (_s1,_s2) Q.:< cs -> do
            s1' <- substSort _s1
            s2' <- substSort _s2
            case (s1',s2') of
                (SBase,SBase)  -> go cs
                (SVar i1,SVar i2) | i1 == i2 -> go cs 
                (SVar i,s) -> do
                    assert (not $ contains i s) $ "Recursive Type " ++ show (s1',s2')
                    assign i s
                    go cs
                (s,SVar i) -> do
                    assert (not $ contains i s) $ "Recursive Type" ++ show (s1',s2')
                    assign i s
                    go cs
                (SFun sx1 s1,SFun sx2 s2) -> do
                    --assert (length ss1 == length ss2) "Invalid Number of Arguments"
                    go ((sx1,sx2) Q.<| (s1,s2) Q.<| cs)
                (STup ss1,STup ss2) -> do
                    assert (length ss1 == length ss2) "Invalid Size of Tuple"
                    go (Q.fromList (zip ss1 ss2) Q.>< cs)
                (_,_) -> assert False $ "Unification Failed:" ++ show s1' ++ "," ++ show s2'

substSort :: SortLike -> StateT Subst (Except Err) SortLike
substSort SBase = return SBase
substSort (SVar i) = do
    ms <- M.lookup i <$> get
    case ms of
        Nothing -> return (SVar i)
        Just s  -> do
            s' <- substSort s
            modify $ M.insert i s'
            return s'
substSort (SFun sx s) = liftA2 SFun (substSort sx) (substSort s)
substSort (STup l) = STup <$> mapM substSort l

assign :: Id -> SortLike -> StateT Subst (Except Err) ()
assign i s = modify $ M.insert i s

contains :: Id -> SortLike -> Bool
contains i = go where
    go SBase = False
    go (SVar j) = i == j
    go (SFun sx s) = go sx || go s
    go (STup l) = any go l

concretize :: SortLike -> Sort
concretize SBase = Base
concretize (SVar _) = Base
concretize (SFun sx s) = concretize sx :-> concretize s
concretize (STup l) = Tuple (map concretize l)

substEnv :: Env -> Subst -> Except Err (M.Map Symbol Sort)
substEnv env subst = evalStateT doit subst where
    doit = traverse (fmap concretize . substSort) env
