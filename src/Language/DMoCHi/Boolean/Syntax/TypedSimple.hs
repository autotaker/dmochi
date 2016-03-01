module Language.DMoCHi.Boolean.Syntax.TypedSimple where
import qualified Language.DMoCHi.Boolean.Syntax.Typed as B
import Language.DMoCHi.Boolean.Syntax.Typed(Symbol, Index, Size,Sort(..), HasSort(..),freshSym)
import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Language.DMoCHi.Common.Id

data VTerm = C Bool
           | V Symbol
           | T [VTerm]
           | Lam Symbol Term
           | Proj Sort Index Size VTerm
           | And VTerm VTerm
           | Or VTerm VTerm
           | Not VTerm

data Term = Pure VTerm
          | App Sort VTerm VTerm
          | Let Sort Symbol Term Term
          | Assume Sort VTerm Term
          | Branch Sort Term Term
          | Fail Symbol

instance HasSort VTerm where
    getSort (C _) = Bool
    getSort (V x) = getSort x
    getSort (T vs) = Tuple $ map getSort vs
    getSort (Lam x d) = getSort x :-> getSort d
    getSort (Proj s _ _ _) = s
    getSort (And _ _) = Bool
    getSort (Or _ _) = Bool
    getSort (Not _) = Bool

instance HasSort Term where
    getSort (Pure t) = getSort t
    getSort (App s _ _) = s
    getSort (Let s _ _ _) = s
    getSort (Assume s _ _) = s
    getSort (Branch s _ _) = s
    getSort (Fail x) = getSort x

isPure :: Term -> Bool
isPure (Pure _) = True
isPure _ = False

f_let :: Symbol -> Term -> Term -> Term
f_let x ex e = Let (getSort e) x ex e

f_app :: VTerm -> VTerm -> Term
f_app e1 e2 = 
    let _ :-> s2 = getSort e1 in 
    App s2 e1 e2

f_proj :: Index -> Size -> VTerm -> VTerm
f_proj i n e = 
    let Tuple ts = getSort e in
    Proj (ts !! i) i n e

f_assume :: VTerm -> Term -> Term
f_assume (C True) e = e
f_assume p e = Assume (getSort e) p e

f_not :: VTerm -> VTerm
f_not = Not
f_and, f_or :: VTerm -> VTerm -> VTerm
f_and (C True) x2 = x2
f_and x1 (C True) = x1
f_and (C False) _ = C False
f_and x1 x2 = And x1 x2
f_or (C False) x2 = x2
f_or x1 (C False) = x1
f_or (C True) _ = C False
f_or x1 x2 = Or x1 x2

normalize :: (MonadId m) => Term -> m (VTerm, [(Symbol,Term)])
normalize (Pure v) = return (v,[])
normalize t = do
    x <- freshSym "smpl" (getSort t)
    return (V x,[(x,t)])

toSimple :: (Applicative m, MonadId m) => B.Term -> m Term
toSimple (B.C b) = return $ Pure (C b)
toSimple (B.V x) = return $ Pure (V x)
toSimple (B.T ts) = do
    ts' <- forM ts $ \t -> toSimple t >>= normalize
    let (vs,ls) = unzip ts'
    return $ foldr (uncurry f_let) (Pure (T vs)) (concat ls)
toSimple (B.Lam x t) =
    Pure . Lam x <$> toSimple t
toSimple (B.Let _ x ex e) =
    f_let x <$> toSimple ex <*> toSimple e
toSimple (B.App _ t1 t2) = do
    (e1,l1) <- normalize =<< toSimple t1
    (e2,l2) <- normalize =<< toSimple t2
    return $ foldr (uncurry f_let) (f_app e1 e2) (l1 ++ l2)
toSimple (B.Proj _ idx size t') = do
    (e,l) <- toSimple t' >>= normalize
    return $ foldr (uncurry f_let) (Pure (f_proj idx size e)) l
toSimple (B.Assume _ t1 t2) = do
    (e1,l1) <- toSimple t1 >>= normalize
    e2 <- toSimple t2
    return $ foldr (uncurry f_let) (f_assume e1 e2) l1
toSimple (B.Branch s t1 t2) = Branch s <$> toSimple t1 <*> toSimple t2
toSimple (B.And t1 t2) = do
    (e1,l1) <- normalize =<< toSimple t1
    (e2,l2) <- normalize =<< toSimple t2
    return $ foldr (uncurry f_let) (Pure (f_and e1 e2)) (l1 ++ l2)
toSimple (B.Or t1 t2) = do
    (e1,l1) <- normalize =<< toSimple t1
    (e2,l2) <- normalize =<< toSimple t2
    return $ foldr (uncurry f_let) (Pure (f_or e1 e2)) (l1 ++ l2)
toSimple (B.Not t') = do
    (e,l) <- toSimple t' >>= normalize
    return $ foldr (uncurry f_let) (Pure (f_not e)) l
toSimple (B.Fail s) = return $ Fail s

data Program = Program { definitions :: [Def]
                       , mainTerm :: Term }
type Def = (Symbol,VTerm)
toSimpleProgram :: (Applicative m, MonadId m) => B.Program -> m Program
toSimpleProgram (B.Program ds t0) = do
    ds' <- forM ds $ \(x,t) -> do
        Pure v <- toSimple t
        return (x,v)
    t0' <- toSimple t0
    return $ Program ds' t0'
    

tCheck :: Program -> Except (Sort,Sort,String) ()
tCheck (Program ds t0) = doit where
    check s1 s2 str = when (s1 /= s2) $ throwError (s1,s2,str)
    doit = do
        forM_ ds $ \(x,t) -> do
            goV t
            check (getSort x) (getSort t) "let rec" 
        go t0
    goV _t = case _t of
        C _ -> return ()
        V _ -> return ()
        T ts -> mapM_ goV ts
        Lam _ t -> go t
        Proj s i n t -> do
            goV t
            case getSort t of
                Tuple ts | length ts == n -> check s (ts !! i) "proj"
                s' -> throwError (s',X,"tuple size")
        And t1 t2 -> do
            goV t1
            check Bool (getSort t1) "and fst"
            goV t2
            check Bool (getSort t2) "and snd"
        Or t1 t2 -> do
            goV t1
            check Bool (getSort t1) "or fst"
            goV t2
            check Bool (getSort t2) "or snd"
        Not t -> do
            goV t
            check Bool (getSort t) "not"
    go _t = case _t of
        Pure t -> goV t
        Let s x tx t -> do
            go tx
            check (getSort x) (getSort tx) "let var"
            go t
            check s (getSort t) "let body"
        App s t1 t2 -> do
            goV t1
            goV t2
            case getSort t1 of
                s1 :-> s2 -> check s1 (getSort t2) "app arg" >> 
                             check s s2 "app result"
                s' -> throwError (s',X,"app fun")
        Assume s p t -> do
            goV p
            check (getSort p) Bool "assume pred"
            go t
            check s (getSort t) "assume body"
        Branch s t1 t2 -> do
            go t1
            check s (getSort t1) "branch fst"
            go t2
            check s (getSort t2) "branch snd"
        Fail _ -> return ()
        



