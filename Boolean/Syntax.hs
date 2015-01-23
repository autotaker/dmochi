module Boolean.Syntax where
import qualified Data.Sequence as Q
import qualified Data.Set as S
import Data.Foldable(toList)
import Control.Monad.Writer
import Control.Monad.Reader
import Boolean.Util
import Data.Hashable
import Data.List(intersperse)
import Text.Printf

data Program = Program { definitions :: [Def]
                       , mainTerm    :: Term } deriving(Show)

type Def = (Symbol,Term)
type Symbol = String
newtype ProjN = ProjN { projN :: Int } deriving(Eq,Ord)
newtype ProjD = ProjD { projD :: Int } deriving(Eq,Ord)

instance Show ProjN where
    show (ProjN x) = show x
instance Show ProjD where
    show (ProjD x) = show x

data Term = C Bool | V Symbol | T [Term] | TF
          | Lam Symbol Term
          | Let Symbol Term Term
          | Proj ProjN ProjD Term
          | App Term Term
--          | Term :+: Term 
          | If Term Term Term 
          | Fail Symbol | Omega Symbol deriving(Ord,Eq)


isPrim :: Term -> Bool
isPrim (C _) = True
isPrim (V _) = True
isPrim (Fail _) = True
isPrim (Omega _) = True
isPrim TF = True
isPrim _ = False

instance Show Term where
    show (C True) = "true"
    show (C False) = "false"
    show (V x) = x
    show TF = "*"
    show (T xs) = "["++concat (intersperse "," (map show xs)) ++ "]"
    show (Lam x t) = "λ " ++ x ++ " . "++show t
    show (Let x t1 t2) = unwords ["let",x,"=",show t1,"in",show t2]
    show (Proj i n t) = printf "#(%d/%d)" (projN i) (projD n) ++ " " ++ (if isPrim t then show t else "(" ++ show t ++ ")")
    show (App t1 t2) | isPrim t1 = show t1 ++ " " ++ show t2
                     | otherwise = "("++show t1++") "++ show t2
--    show (t1 :+: t2) = unwords ["("++show t1++")","<>",show t2]
    show (If t1 t2 t3) = unwords ["if",show t1,"then",show t2,"else",show t3]
    show (Fail s) = "Fail(" ++ s ++ ")"
    show (Omega s) = "Omega("++ s ++ ")"


symbols :: Program -> [Symbol]
symbols (Program defs t0) = nub $ toList $ execWriter doit where
    push = tell . Q.singleton
    doit = mapM_ (\(f,t) -> push f >> go t) defs >> go t0
    go (C _) = return ()
    go (V x) = push x
    go TF = return ()
    go (T ts) = mapM_ go ts
    go (Fail x) = push x
    go (Omega x) = push x
    go (Lam x t) = push x >> go t
    go (Let x t1 t2) = push x >> go t1 >> go t2
    go (Proj _ _ t) = go t
    go (App t1 t2) = go t1 >> go t2
    --go (t1 :+: t2) = go t1 >> go t2
    go (If t1 t2 t3) = go t1 >> go t2 >> go t3

freeVariables :: Term -> [Symbol]
freeVariables = nub . toList . execWriter . flip runReaderT S.empty . go where
    push = tell . Q.singleton
    go (V x) = fmap (S.member x) ask >>= \b -> unless b $ push x
    go (T ts) = mapM_ go ts
    go (Proj _ _ t) = go t
    go (Lam x t) = local (S.insert x) $ go t
    go (Let x t1 t2) = go t1 >> local (S.insert x) (go t2)
    go (App t1 t2) = go t1 >> go t2
    --go (t1 :+: t2) = go t1 >> go t2
    go (If t1 t2 t3) = go t1 >> go t2 >> go t3
    go _ = return ()

boundVariables :: Term -> [Symbol]
boundVariables = nub . toList . execWriter . go where
    push = tell . Q.singleton
    go (Lam x t) = push x >> go t
    go (Let x t1 t2) = push x >> go t1 >> go t2
    go (Proj _ _ t) = go t
    go (App t1 t2) = go t1 >> go t2
    go (T ts) = mapM_ go ts
    --go (t1 :+: t2) = go t1 >> go t2
    go (If t1 t2 t3) = go t1 >> go t2 >> go t3
    go _ = return ()
    

instance Hashable Term where
    hashWithSalt s (C b) = s `hashWithSalt` (0::Int) `hashWithSalt` b
    hashWithSalt s (V x) = s `hashWithSalt` (1::Int) `hashWithSalt` x
    hashWithSalt s (Fail x) = s `hashWithSalt` (2::Int) `hashWithSalt` x
    hashWithSalt s (Omega x) = s `hashWithSalt` (3::Int) `hashWithSalt` x
    hashWithSalt s TF = s `hashWithSalt` (4 :: Int)
    hashWithSalt _ _ = undefined

printProgram :: Program -> IO ()
printProgram p = do
    printf "(* functions *)\n"
    forM_ (definitions p) $ \(x,e) -> do
        printf "let %s = %s\n" x (show e)
    printf "(* main *)\n"
    print (mainTerm p)

