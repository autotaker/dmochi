{-# LANGUAGE FlexibleContexts #-}
module Language.DMoCHi.Boolean.Syntax.Typed ( Symbol(..)
                            , Program(..)
                            , Sort(..)
                            , Def, Index, Size
                            , Term(..)
                            , HasSort(..)
                            , toUnTyped
                            , freshSym
                            , tCheck
                            , modifySort
                            , order
                            , f_assume
                            , f_branch
                            , f_branch_label
                            , f_let
                            , f_letrec
                            , f_app
                            , f_proj
                            , f_not
                            , f_and
                            , f_or
                            , size
                            , freeVariables
                            ) where


import qualified Language.DMoCHi.Boolean.Syntax as B
import Control.Monad
import Control.Monad.Except
import Language.DMoCHi.Common.Id
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.Identity
data Symbol = Symbol { _sort :: Sort, name :: String } deriving(Show)

freshSym :: MonadId m => String -> Sort -> m Symbol
freshSym _name sort = freshId _name >>= \x -> return (Symbol sort x)

instance Eq Symbol where
    (==) a b = name a == name b

instance Ord Symbol where
    compare a b = name a `compare` name b

data Program = Program { definitions :: [Def]
                       , mainTerm :: Term }

infixr :->
data Sort = X | Bool | Tuple [Sort] | Sort :-> Sort deriving(Eq,Ord,Show)
type Index = Int
type Size = Int

type Def = (Symbol,Term)
data Term = C Bool
          | V Symbol
          | T [Term]
          | Lam Symbol Term
          | Let Sort Symbol Term Term
          | LetRec Sort [(Symbol, Term)] Term
          | App Sort Term Term
          | Proj Sort Index Size  Term
          | Assume Sort Term Term
          | Branch Sort Bool Term Term
          | And Term Term
          | Or  Term Term
          | Not Term
          | Fail Symbol 
          | Omega Symbol deriving(Ord,Eq,Show)

f_assume :: Term -> Term -> Term
f_assume _ e@(Omega _) = e
f_assume (C True) e = e
f_assume p e = Assume (getSort e) p e
f_branch :: Term -> Term -> Term
f_branch (Omega _) e = e
f_branch e (Omega _) = e
f_branch e1 e2 = Branch (getSort e1) False e1 e2

f_branch_label :: Term -> Term -> Term
f_branch_label e1 e2 = Branch (getSort e1) True e1 e2
f_let :: Symbol -> Term -> Term -> Term
f_let x ex e = Let (getSort e) x ex e
f_letrec :: [(Symbol, Term)] -> Term -> Term
f_letrec fs e = LetRec (getSort e) fs e
f_app :: Term -> Term -> Term
f_app e1 e2 = 
    let _ :-> s2 = getSort e1 in 
    App s2 e1 e2
f_proj :: Index -> Size -> Term -> Term
f_proj i n e = 
    let Tuple ts = getSort e in
    Proj (ts !! i) i n e

f_not :: Term -> Term
f_not = Not
f_and, f_or :: Term -> Term -> Term
f_and (C True) x2 = x2
f_and x1 (C True) = x1
f_and (C False) _ = C False
f_and x1 x2 = And x1 x2
f_or (C False) x2 = x2
f_or x1 (C False) = x1
f_or (C True) _ = C False
f_or x1 x2 = Or x1 x2

class HasSort m where
    getSort :: m -> Sort

instance HasSort Symbol where
    getSort = _sort

instance HasSort Term where
    getSort (C _) = Bool
    getSort (V x) = getSort x
    getSort (T ts) = Tuple $ map getSort ts
    getSort (Lam x t) = getSort x :-> getSort t
    getSort (Let s _ _ _) = s
    getSort (LetRec s _ _) = s
    getSort (App s _ _)   = s
    getSort (Proj s _ _ _) = s
    getSort (Assume s _ _) = s
    getSort (Branch s _ _ _) = s
    getSort (And _ _) = Bool
    getSort (Or _ _)  = Bool
    getSort (Not _)   = Bool
    getSort (Fail x) = getSort x
    getSort (Omega x) = getSort x

modifySort :: (Sort -> Sort) -> Symbol -> Symbol
modifySort f s = Symbol (f $ _sort s) (name s)

order :: Sort -> Int
order X = 0
order Bool = 0
order (Tuple xs) = maximum (0:map order xs)
order (t1 :-> t2) = max (order t1+1) (order t2)

toUnTyped :: Program -> B.Program
toUnTyped (Program ds t0) = runIdentity doit where
    doit = do
        ds' <- mapM (\(x,t) -> (,) (name x) <$> convert t) ds 
        t0' <- convert t0
        return $ B.Program ds' t0'
    convert :: Term -> Identity (B.Term ())
    convert (C b) = return $ B.C () b
    convert (V x) = return $ B.V () (name x)
    convert (T ts) = B.T () <$> mapM convert ts
    convert (Lam x t) = B.Lam () (name x) <$> convert t
    convert (Let _ x tx t) = B.Let () (name x) <$> convert tx <*> (convert t)
    convert (App _ t1 t2) = B.App () <$> convert t1 <*> convert t2
    convert (Proj _ i s t) = B.Proj () (B.ProjN i) (B.ProjD s) <$> convert t
    convert (Assume _ p t) = B.If () False <$> (convert p) <*> (convert t) <*> omega
    convert (Branch _ b t1 t2) = B.If () b (B.TF ()) <$> (convert t1) <*> (convert t2)
    convert (And t1 t2) = B.If () False <$> (convert t1) <*> (convert t2) <*> pure (B.C () False)
    convert (Or t1 t2) = B.If () False <$> (convert t1) <*> pure (B.C () True) <*> (convert  t2)
    convert (Not t) = B.If () False <$> (convert t) <*> pure (B.C () False) <*> pure (B.C () True)
    convert (Fail x) = return $ B.Fail () (name x)
    convert (Omega x) = return $ B.Omega () (name x)
    convert (LetRec _ _ _) = error "local recursion is unsupported"
    omega = do
        -- x <- freshId "Omega"
        return $ B.Omega () ""

tCheck :: Program -> Except (Sort,Sort,String,[Term]) ()
tCheck (Program ds t0) = doit where
    check s1 s2 str ctx = when (s1 /= s2) $ throwError (s1,s2,str,ctx)
    doit :: Except (Sort,Sort,String,[Term]) ()
    doit = do
        let env = M.fromList [ (x , getSort x) | (x,_) <- ds ]
        forM_ ds $ \(x,t) -> do
            go env [] t
            check (getSort x) (getSort t) "let rec" []
        go env [] t0
    go :: M.Map Symbol Sort -> [Term] -> Term -> Except (Sort,Sort,String,[Term]) ()
    go env ctx _t = let ctx' = _t:ctx in case _t of
        C _ -> return ()
        V x -> check (getSort x) (env M.! x) "var" ctx'
        T ts -> mapM_ (go env ctx') ts
        Lam x t -> go (M.insert x (getSort x) env) ctx' t
        Let s x tx t -> do
            go env ctx' tx
            check (getSort x) (getSort tx) "let var" ctx'
            go (M.insert x (getSort x) env) ctx' t
            check s (getSort t) "let body" ctx'
        LetRec s fs t -> do
            let as = map (\(f,_) -> (f,getSort f)) fs
                env' = foldr (uncurry M.insert) env as
            forM_ fs $ \(f, tf) -> do
                go env' ctx' tf
                check (getSort f) (getSort tf) "let rec var" ctx'
            go env' ctx' t
            check s (getSort t) "let rec body" ctx'
        App s t1 t2 -> do
            go env ctx' t1
            go env ctx' t2
            case getSort t1 of
                s1 :-> s2 -> check s1 (getSort t2) "app arg" ctx' >> 
                             check s s2 "app result" ctx'
                s' -> throwError (s',X,"app fun",ctx')
        Proj s i n t -> do
            go env ctx' t
            case getSort t of
                Tuple ts | length ts == n -> check s (ts !! i) "proj" ctx'
                s' -> throwError (s',X,"tuple size",t:ctx')
        Assume s p t -> do
            go env ctx' p
            check (getSort p) Bool "assume pred" (p:ctx')
            go env ctx' t
            check s (getSort t) "assume body" ctx'
        Branch s _ t1 t2 -> do
            go env ctx' t1
            check s (getSort t1) "branch fst" (t1:ctx')
            go env ctx' t2
            check s (getSort t2) "branch snd" (t2:ctx')
        And t1 t2 -> do
            go env ctx' t1
            check Bool (getSort t1) "and fst" (t1:ctx')
            go env ctx' t2
            check Bool (getSort t2) "and snd" (t2:ctx')
        Or t1 t2 -> do
            go env ctx' t1
            check Bool (getSort t1) "or fst" (t1:ctx')
            go env ctx' t2
            check Bool (getSort t2) "or snd" (t2:ctx')
        Not t -> do
            go env ctx' t
            check Bool (getSort t) "not" (t:ctx')
        Fail _ -> return ()
        Omega _ -> return ()

size :: Program -> Int
size (Program ds t0) = sum [ sizeT ti + 1 | (_,ti) <- ds] + sizeT t0

sizeT :: Term -> Int
sizeT (C _) = 1
sizeT (V _) = 1
sizeT (T ts) = 1 + sum (map sizeT ts)
sizeT (Lam _ t) = 1 + sizeT t
sizeT (Let _ _ t1 t2) = 1 + sizeT t1 + sizeT t2
sizeT (LetRec _ fs t2) = 1 + sum (map (sizeT. snd) fs) + sizeT t2
sizeT (App _ t1 t2) = 1 + sizeT t1 + sizeT t2
sizeT (Proj _ _ _ t) = 1 + sizeT t
sizeT (Assume _ t1 t2) = 1 + sizeT t1 + sizeT t2
sizeT (Branch _ _ t1 t2) = 1 + sizeT t1 + sizeT t2
sizeT (And t1 t2) = 1 + sizeT t1 + sizeT t2
sizeT (Or  t1 t2) = 1 + sizeT t1 + sizeT t2
sizeT (Not t) = 1 + sizeT t
sizeT (Fail _) = 1
sizeT (Omega _) = 1

freeVariables :: Term -> S.Set Symbol
freeVariables t = case t of
    C _ -> S.empty
    V f -> S.singleton f
    T ts -> S.unions (map freeVariables ts)
    Lam x t -> S.delete x (freeVariables t)
    Let _ x t1 t2 -> freeVariables t1 `S.union` (S.delete x (freeVariables t2))
    LetRec _ fs t2 -> S.unions (map freeVariables (t2:values)) `S.difference` (S.fromList names)
        where
        (names,values) = unzip fs
    App _ t1 t2 -> freeVariables t1 `S.union` freeVariables t2
    Proj _ _ _ t -> freeVariables t
    Assume _ t1 t2 -> freeVariables t1 `S.union` freeVariables t2
    Branch _ _ t1 t2 -> freeVariables t1 `S.union` freeVariables t2
    And t1 t2 -> freeVariables t1 `S.union` freeVariables t2
    Or  t1 t2 -> freeVariables t1 `S.union` freeVariables t2
    Not t     -> freeVariables t
    Fail _    -> S.empty
    Omega _   -> S.empty
