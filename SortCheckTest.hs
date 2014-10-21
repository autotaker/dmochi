import Syntax
import Sort
import SortCheck
import Control.Applicative
import Control.Monad
import qualified Data.Map as M
import Data.Maybe
import Test.QuickCheck

type SortEnv = M.Map Symbol Sort

wellSortedProgram :: SortEnv -> Program -> Bool
wellSortedProgram env p = isJust $ mapM_ g l where
    g (t,s) = sortTerm env t  >>= guard . (==s)
    l = (mainTerm p,Base):[ (t,s) | (f,t) <- definitions p, let s = env M.! f]

sortTerm :: SortEnv -> Term -> Maybe Sort
sortTerm env = go where
    go (C _) = pure Base
    go (V x) = pure $ env M.! x
    go (Fail x)  = pure $ env M.! x
    go (Omega x) = pure $ env M.! x
    go (Lam xs t) = ((map (env M.!) xs) :->) <$> go t
    go (App t ts) = do
        sf <- go t
        ss <- mapM go ts
        case sf of
            ss' :-> sb | ss == ss' -> pure sb
            _ -> empty
    go (t1 :+: t2) = do
        s1 <- go t1
        s2 <- go t2
        guard $ s1 == s2
        return s1
    go (If tp tt te) = do
        sp <- go tp
        guard $ sp == Base
        st <- go tt
        se <- go te
        guard $ st == se
        return st
            
prop_sortCheck_sound :: Program -> [Symbol] -> Property
prop_sortCheck_sound p sym = pre ==> post where
    pre = True 
    post = case sortCheck p sym of
        Left _ -> True
        Right env -> wellSortedProgram env p
