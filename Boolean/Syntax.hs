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
                       , mainTerm    :: Term () } deriving(Show)

type Def = (Symbol,Term ())
type Symbol = String
newtype ProjN = ProjN { projN :: Int } deriving(Eq,Ord)
newtype ProjD = ProjD { projD :: Int } deriving(Eq,Ord)

instance Show ProjN where
    show (ProjN x) = show x
instance Show ProjD where
    show (ProjD x) = show x

data Term a = C a Bool | V a Symbol | T a [Term a] | TF a
          | Lam a Symbol (Term a)
          | Let a Symbol (Term a) (Term a)
          | Proj a ProjN ProjD (Term a)
          | App a (Term a) (Term a)
--          | Term :+: Term 
          | If a (Term a) (Term a) (Term a)
          | Fail a Symbol | Omega a Symbol deriving(Ord,Eq)

getValue :: Term a -> a
getValue (C a _) = a
getValue (V a _) = a
getValue (T a _) = a
getValue (TF a)  = a
getValue (Lam a _ _) = a
getValue (Let a _ _ _) = a
getValue (Proj a _ _ _) = a
getValue (App a _ _) = a
getValue (If a _ _ _) = a
getValue (Fail a _) = a
getValue (Omega a _) = a


isPrim :: Term a -> Bool
isPrim (C _ _) = True
isPrim (V _ _) = True
isPrim (Fail _ _) = True
isPrim (Omega _ _) = True
isPrim (TF _) = True
isPrim _ = False

instance Show (Term a) where
    show (C _ True) = "true"
    show (C _ False) = "false"
    show (V _ x) = x
    show (TF _) = "*"
    show (T _ xs) = "["++concat (intersperse "," (map show xs)) ++ "]"
    show (Lam _ x t) = "λ " ++ x ++ " . "++show t
    show (Let _ x t1 t2) = unwords ["let",x,"=",show t1,"in",show t2]
    show (Proj _ i n t) = printf "#(%d/%d)" (projN i) (projD n) ++ " " ++ (if isPrim t then show t else "(" ++ show t ++ ")")
    show (App _ t1 t2) | isPrim t1 = show t1 ++ " " ++ "(" ++ show t2 ++ ")"
                     | otherwise = "("++show t1++") "++ "(" ++ show t2  ++ ")"
    show (If _ t1 t2 t3) = unwords ["if",show t1,"then",show t2,"else",show t3]
    show (Fail _ s) = "Fail(" ++ s ++ ")"
    show (Omega _ s) = "Omega("++ s ++ ")"

size :: Program -> Int
size (Program ds t) = sum [ sizeT ti + 1 | (_,ti) <- ds ] + sizeT t

sizeT :: Term a -> Int
sizeT (C _ _) = 1
sizeT (V _ _) = 1
sizeT (TF _)  = 1
sizeT (T _ ts) = 1 + sum (map sizeT ts)
sizeT (Lam _ _ t) = 1 + sizeT t
sizeT (Let _ _ t1 t2) = 1 + sizeT t1 + sizeT t2
sizeT (Proj _ _ _ t) = 1 + sizeT t
sizeT (App _ t1 t2) = 1 + sizeT t1 + sizeT t2
sizeT (If _ t1 t2 t3) = 1 + sizeT t1 + sizeT t2 + sizeT t3
sizeT (Fail _ _) = 1
sizeT (Omega _ _) = 1

symbols :: Program -> [Symbol]
symbols (Program defs t0) = nub $ toList $ execWriter doit where
    push = tell . Q.singleton
    doit = mapM_ (\(f,t) -> push f >> go t) defs >> go t0
    go (C _ _) = return ()
    go (V _ x) = push x
    go (TF _) = return ()
    go (T _ ts) = mapM_ go ts
    go (Fail _ x) = push x
    go (Omega _ x) = push x
    go (Lam _ x t) = push x >> go t
    go (Let _ x t1 t2) = push x >> go t1 >> go t2
    go (Proj _ _ _ t) = go t
    go (App _ t1 t2) = go t1 >> go t2
    --go (t1 :+: t2) = go t1 >> go t2
    go (If _ t1 t2 t3) = go t1 >> go t2 >> go t3

freeVariables :: Term a -> [Symbol]
freeVariables = nub . toList . execWriter . flip runReaderT S.empty . go where
    push = tell . Q.singleton
    go (V _ x) = fmap (S.member x) ask >>= \b -> unless b $ push x
    go (T _ ts) = mapM_ go ts
    go (Proj _ _ _ t) = go t
    go (Lam _ x t) = local (S.insert x) $ go t
    go (Let _ x t1 t2) = go t1 >> local (S.insert x) (go t2)
    go (App _ t1 t2) = go t1 >> go t2
    --go (t1 :+: t2) = go t1 >> go t2
    go (If _ t1 t2 t3) = go t1 >> go t2 >> go t3
    go _ = return ()

boundVariables :: Term a -> [Symbol]
boundVariables = nub . toList . execWriter . go where
    push = tell . Q.singleton
    go (Lam _ x t) = push x >> go t
    go (Let _ x t1 t2) = push x >> go t1 >> go t2
    go (Proj _ _ _ t) = go t
    go (App _ t1 t2) = go t1 >> go t2
    go (T _ ts) = mapM_ go ts
    --go (t1 :+: t2) = go t1 >> go t2
    go (If _ t1 t2 t3) = go t1 >> go t2 >> go t3
    go _ = return ()
    
instance Hashable (Term a) where
    hashWithSalt s (C _ b) = s `hashWithSalt` (0::Int) `hashWithSalt` b
    hashWithSalt s (V _ x) = s `hashWithSalt` (1::Int) `hashWithSalt` x
    hashWithSalt s (Fail _ x) = s `hashWithSalt` (2::Int) `hashWithSalt` x
    hashWithSalt s (Omega _ x) = s `hashWithSalt` (3::Int) `hashWithSalt` x
    hashWithSalt s (TF _) = s `hashWithSalt` (4 :: Int)
    hashWithSalt _ _ = undefined

printProgram :: Program -> IO ()
printProgram p = do
    printf "(* functions *)\n"
    forM_ (definitions p) $ \(x,e) -> do
        printf "let %s = %s\n" x (show e)
    printf "(* main *)\n"
    print (mainTerm p)

