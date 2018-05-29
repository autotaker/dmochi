{-# LANGUAGE MultiParamTypeClasses #-}
module Language.DMoCHi.ML.Syntax.CEGAR(
      Program(..)
    , Exp(..), Value(..), Atom(..), LExp(..), Normalized, AbstInfo(..)
    , LExpView(..), ExpView(..), ValueView(..), expView, valueView, lexpView
    , mkBin, mkUni, mkLiteral, mkVar, mkPair, mkLambda 
    , mkApp, mkLet, mkLetRec, mkAssume, mkBranch, mkBranchL, mkFail, mkOmega, mkRand
    , mkAbstInfo, updateAbstInfo, Formula
    , Castable(..)
    , module Language.DMoCHi.ML.Syntax.Type
    , module Language.DMoCHi.ML.Syntax.Base )
     where

import Language.DMoCHi.Common.Id
-- import Language.DMoCHi.Common.Util
-- import qualified Data.Set as S
import GHC.Exts(Constraint)
import Language.DMoCHi.ML.Syntax.Atom
import Language.DMoCHi.ML.Syntax.PNormal(Castable(..))
import qualified Language.DMoCHi.ML.Syntax.HFormula as HFormula
import Language.DMoCHi.ML.Syntax.Type
import Language.DMoCHi.ML.Syntax.Base
import Text.PrettyPrint.HughesPJClass
import qualified Data.Map as M
import Data.MonoTraversable
import Control.Monad
import Data.Maybe
import Text.Printf
import Debug.Trace


data AbstInfo 
 = AbstInfo { abstFormulas    :: [HFormula.HFormula]  -- current predicates to be used
            , abstTemplate   :: PredTemplate         -- represents P_k(a_1,...a_n) 
            , abstPredicates :: ([TId], [Atom]) -- (xs, [p_1,..., p_m]) s.t.
                                                     -- [a_1/x_1,...,a_n/x_n] p_i = phi_i
            }
  | DummyInfo
  deriving(Show)

newtype Program = Program { mainTerm :: Exp }


data Exp where
    Exp :: (Normalized l Exp arg
           , Supported l (Labels Exp)
           , Meta l Exp info) 
            => SLabel l -> arg -> !Type -> info -> !UniqueKey -> Exp

data Value where
    Value :: (Normalized l Value arg
             , Supported l (Labels Value)) 
            => SLabel l -> arg -> !Type -> !UniqueKey -> Value

data LExp where
    LExp :: (Normalized l LExp arg
            , Supported l (Labels LExp)) 
            => SLabel l -> arg -> !Type -> !UniqueKey -> LExp

type family Normalized (l :: Label) (e :: *) (arg :: *) :: Constraint where
    Normalized 'Literal e arg = arg ~ Lit
    Normalized 'Var     e arg = arg ~ Ident e
    Normalized 'Unary   e arg = arg ~ UniArg Atom
    Normalized 'Binary  e arg = arg ~ BinArg Atom
    Normalized 'Pair    e arg = arg ~ (Value, Value)
    Normalized 'Lambda  e arg = arg ~ ([Ident e], AbstInfo, Exp)
    Normalized 'App     e arg = arg ~ (Ident e, AbstInfo, [Value])
    Normalized 'Let     e arg = arg ~ (Ident e, LExp, AbstInfo, Exp)
    Normalized 'LetRec  e arg = arg ~ ([(Ident e, Value)], Exp)
    Normalized 'Assume  e arg = arg ~ (Atom, Exp)
    Normalized 'Branch  e arg = arg ~ (Exp, Exp)
    Normalized 'Fail    e arg = arg ~ ()
    Normalized 'Omega   e arg = arg ~ ()
    Normalized 'Rand    e arg = arg ~ ()
    Normalized l        e arg = 'True ~ 'False

instance HasUniqueKey Exp where
    getUniqueKey (Exp _ _ _ _ key) = key
instance HasUniqueKey LExp where
    getUniqueKey (LExp _ _ _ key) = key
instance HasUniqueKey Value where
    getUniqueKey (Value _ _ _ key) = key


type instance Ident  Exp = TId
type instance Ident  LExp = TId
type instance Ident  Value = TId

type family Meta (l :: Label) (e :: *) (info :: *) :: Constraint where
    Meta 'Literal Exp info = info ~ AbstInfo
    Meta 'Var     Exp info = info ~ AbstInfo
    Meta 'Unary   Exp info = info ~ AbstInfo
    Meta 'Binary  Exp info = info ~ AbstInfo
    Meta 'Pair    Exp info = info ~ AbstInfo
    Meta 'Lambda  Exp info = info ~ AbstInfo
    Meta l        Exp info = info ~ ()
    Meta l        e   info = 'True ~ 'False

data ExpView where
    EValue :: Value -> AbstInfo -> ExpView
    EOther :: ( Normalized l Exp arg
              , Supported l '[ 'Let, 'LetRec, 'Assume
                             , 'Branch, 'Fail, 'Omega]) 
                => SLabel l -> arg -> ExpView

data LExpView where
    LAtom  :: Atom -> LExpView
    LOther :: ( Normalized l LExp arg
              , Supported l '[  'App, 'Branch, 'Rand]) 
                => SLabel l -> arg -> LExpView

data ValueView where
    VAtom  :: Atom -> ValueView
    VOther :: ( Normalized l Value arg
              , Supported l '[ 'Pair, 'Lambda ]) 
                => SLabel l -> arg -> ValueView

type instance Labels Exp = '[ 'Literal, 'Var, 'Binary, 'Unary, 'Pair, 'Lambda
                            , 'Let, 'LetRec, 'Assume, 'Branch, 'Fail, 'Omega ]
type instance Labels LExp = '[ 'Literal, 'Var, 'Binary, 'Unary, 'App, 'Branch, 'Rand]
type instance Labels Value = '[ 'Literal, 'Var, 'Binary, 'Unary, 'Pair, 'Lambda ]
type instance Labels Atom  = '[ 'Literal, 'Var, 'Binary, 'Unary ]


{-# INLINE expView #-}
expView :: Exp -> ExpView
expView (Exp l arg sty meta key) = case l of
    SLiteral -> EValue (Value l arg sty key) meta
    SVar     -> EValue (Value l arg sty key) meta
    SBinary  -> EValue (Value l arg sty key) meta
    SUnary   -> EValue (Value l arg sty key) meta
    SPair    -> EValue (Value l arg sty key) meta
    SLambda  -> EValue (Value l arg sty key) meta
    SLet     -> EOther l arg 
    SLetRec  -> EOther l arg
    SAssume  -> EOther l arg
    SBranch  -> EOther l arg
    SFail    -> EOther l arg
    SOmega   -> EOther l arg

{-# INLINE valueView #-}
valueView :: Value -> ValueView
valueView (Value l arg sty _) = case l of
    SLiteral -> VAtom (Atom l arg sty)
    SVar     -> VAtom (Atom l arg sty)
    SBinary  -> VAtom (Atom l arg sty)
    SUnary   -> VAtom (Atom l arg sty)
    SPair    -> VOther l arg
    SLambda  -> VOther l arg

{-# INLINE lexpView #-}
lexpView :: LExp -> LExpView
lexpView (LExp l arg sty _) = case l of
    SLiteral -> LAtom (Atom l arg sty)
    SVar     -> LAtom (Atom l arg sty)
    SBinary  -> LAtom (Atom l arg sty)
    SUnary   -> LAtom (Atom l arg sty)
    SBranch  -> LOther l arg
    SRand    -> LOther l arg
    SApp     -> LOther l arg


mkPair :: Value -> Value -> UniqueKey -> Value
mkPair v1@(Value _ _ sty1 _) v2@(Value _ _ sty2 _) key = Value SPair (v1, v2) (TPair sty1 sty2) key

mkLambda :: [TId] -> AbstInfo -> Exp -> UniqueKey -> Value
mkLambda xs info e key = 
    Value SLambda (xs, info, e) (TFun stys (getType e)) key
    where !stys = map getType xs

mkApp :: TId -> AbstInfo -> [Value] -> UniqueKey -> LExp
mkApp f@(TId (TFun _ r_ty) _) info vs key = LExp SApp (f, info, vs) r_ty key
mkApp _ _ _ _ = error "mkApp"

mkLet :: TId -> LExp -> AbstInfo -> Exp -> UniqueKey -> Exp
mkLet f e1 info e2 key = Exp SLet (f, e1, info, e2) (getType e2) () key

mkLetRec :: [(TId, Value)] -> Exp -> UniqueKey -> Exp
mkLetRec fs e2 key = Exp SLetRec (fs, e2) (getType e2) () key


mkAssume :: Atom -> Exp -> UniqueKey -> Exp
mkAssume v e key = Exp SAssume (v, e) (getType e) () key

mkBranch :: Exp -> Exp -> UniqueKey -> Exp
mkBranch e1 e2 key = Exp SBranch (e1, e2) (getType e1) () key

mkBranchL :: Exp -> Exp -> UniqueKey -> LExp
mkBranchL e1 e2 key = LExp SBranch (e1, e2) (getType e1) key

mkFail, mkOmega :: Type -> UniqueKey -> Exp
mkFail sty key = Exp SFail () sty () key
mkOmega sty key = Exp SOmega () sty () key

mkRand :: UniqueKey -> LExp
mkRand key = LExp SRand () TInt key

mkAbstInfo :: HFormula.HFormulaFactory m => [Atom] -> PredTemplate -> m AbstInfo
mkAbstInfo ps' tmpl@(_, vs) = do
    ps <- mapM HFormula.toHFormula ps'
    let f :: Type -> String
        f TBool = "b"
        f _ = "x"
        xs = zipWith (\(getType -> ty) i -> 
            let name = printf "%s_%d" (f ty) i in
            TId ty $ reserved name) vs [0::Int ..]
        subst = M.fromList $ zip xs vs
    return $ AbstInfo 
        { abstFormulas = ps
        , abstTemplate = tmpl
        , abstPredicates = (xs, map (desubstAtom subst) ps')
        }

updateAbstInfo :: HFormula.HFormulaFactory m => [([TId], Atom)] -> AbstInfo -> m AbstInfo
updateAbstInfo _ DummyInfo = pure DummyInfo
updateAbstInfo preds (AbstInfo ps tmpl (xs,fs)) = do
    (ps',fs') <- foldM (\(ps, fs) (ys, fml) -> do
        let fml' = substFormula (M.fromList $ zip ys xs) fml
        fml'' <- HFormula.toHFormula $ substAFormula (M.fromList $ zip ys (snd tmpl)) fml
        if fml'' `elem` ps 
            then pure (ps, fs)
            else pure (fml'' : ps, fml' : fs)
        ) (ps, fs) [ (ys, fml) | (ys, fml') <- preds
                               , fml <- decomposeFormula fml' [] ]
    pure $ AbstInfo ps' tmpl (xs, fs') 
    
instance HasType Exp where
    getType (Exp _ _ sty _ _) = sty
instance HasType Value where
    getType (Value _ _ sty _) = sty
instance HasType LExp where
    getType (LExp _ _ sty _) = sty

instance Castable Atom Value where
    type Attr Atom Value = UniqueKey
    cast = castWith reservedKey
    castWith key (Atom l arg sty) = case l of
        SLiteral -> Value l arg sty key
        SVar -> Value l arg sty key
        SBinary -> Value l arg sty key
        SUnary -> Value l arg sty key

instance Castable Atom LExp where
    type Attr Atom LExp = UniqueKey
    cast = castWith reservedKey
    castWith key (Atom l arg sty) = case l of
        SLiteral -> LExp l arg sty key
        SVar     -> LExp l arg sty key
        SBinary  -> LExp l arg sty key
        SUnary   -> LExp l arg sty key

instance Castable Value Exp where
    type Attr Value Exp = AbstInfo
    cast = undefined
    castWith info (Value l arg sty key) = case l of
        SLiteral -> Exp l arg sty info key
        SVar -> Exp l arg sty info key
        SBinary -> Exp l arg sty info key
        SUnary -> Exp l arg sty info key
        SLambda -> Exp l arg sty info key
        SPair -> Exp l arg sty info key

instance Pretty AbstInfo where
    pPrint (AbstInfo ps (key,vs) (xs,qs)) =
        -- [ p_1, ..., p_k; P_k(v1,...,v_n); (xs,qs) ]
        brackets $ 
            (hsep $ punctuate comma (map pPrint ps)) <> semi $+$ 
                dTemp <> semi $+$ pPrint (xs, qs)
        where dTemp = text "P_" <> pPrint key <> parens (hsep $ punctuate comma (map pPrint vs))
    pPrint DummyInfo = empty

instance Pretty Exp where
    pPrint e = case expView e of
        EValue v info -> comment info $+$ pPrint v
        EOther SLet (x, e1, info, e2) ->
            text "let" <+> pPrint (name x) <+> (dType $+$ text "=" <+> pPrint e1) <+> text "in" $+$
            pPrint e2
            where dType = colon <+> pPrint (getType x) <+> char '|' <+> pPrint info
        EOther SLetRec (fs, e2) ->
            text "let rec" <+> vcat (punctuate (text "and") d_fs) <+> text "in" $+$
            pPrint e2
            where d_fs = map (\(f, v_f) -> pPrint (name f) <+> text "=" <+> pPrint v_f) fs
        EOther SAssume (cond, e) ->
            text "assume" <+> pPrintPrec prettyNormal 9 cond <> text ";" $+$ pPrint e
        EOther SBranch (e1, e2) ->
            parens (pPrint e1) <+> text "<>" $+$ parens (pPrint e2)
        EOther SFail _ -> text "Fail"
        EOther SOmega _ -> text "Omega"

instance Pretty Value where
    pPrintPrec level prec v = case valueView v of
        VAtom a -> pPrintPrec level prec a
        VOther SPair (v1, v2) -> parens $ pPrint v1 <> comma <+> pPrint v2
        VOther SLambda (xs, info, e) -> 
            maybeParens (prec > 0) $
                text "fun" <+> d_args $+$ char '|' <+> pPrint info <+> text "->" $+$
                nest 4 (pPrint e)
            where d_args = hsep $ map (parens . pPrint) xs

instance Pretty LExp where
    pPrint e = case lexpView e of
        LAtom a -> pPrint a
        LOther SApp (f, info, vs) -> 
            hsep (pPrint (name f):(map (pPrintPrec prettyNormal 9) vs)) <+> pPrint info
        LOther SRand () -> text "randint()"
        LOther SBranch (e1, e2) ->
            parens (pPrint e1) <+> text "<>" $+$ parens (pPrint e2)

instance Pretty Program where
    pPrint (Program e) = pPrint e
    
instance Show Exp where
    show = render . pPrint 
instance Show Value where
    show = render . pPrint 
instance Show LExp where
    show = render . pPrint 

type instance Element Exp = AbstInfo
type instance Element LExp = AbstInfo
type instance Element Value = AbstInfo
type instance Element Program = AbstInfo

instance MonoFunctor Program where
    omap f (Program e) = Program (omap f e)

instance MonoFoldable Program  where
    ofoldMap f (Program e) = ofoldMap f e
    ofoldr f z (Program e) = ofoldr f z e
    ofoldl' f z (Program e) = ofoldl' f z e
    ofoldr1Ex f (Program e) = ofoldr1Ex f e
    ofoldl1Ex' f (Program e) = ofoldl1Ex' f e


instance MonoTraversable Program where
    otraverse f (Program e) = Program <$> otraverse f e

instance MonoFunctor Exp where
    omap f e =
        let key = getUniqueKey e in
        case expView e of
            EValue v meta -> castWith (f meta) v
            EOther SLet (x, e1, info, e2) -> 
                mkLet x (omap f e1) (f info) (omap f e2) key
            EOther SLetRec (fs, e1) -> mkLetRec fs' (omap f e1) key
                where
                fs' = fmap (\(g, v) -> (g, omap f v)) fs
            EOther SAssume (cond, e1) -> mkAssume cond (omap f e1) key
            EOther SBranch (e1, e2) -> mkBranch (omap f e1) (omap f e2) key
            EOther SOmega _ -> e
            EOther SFail _ -> e

instance MonoFoldable Exp where
    ofoldr f z e = 
        case expView e of
            EValue v meta -> f meta (ofoldr f z v)
            EOther SLet (_, e1, meta, e2) -> 
                ofoldr f (f meta (ofoldr f z e2)) e1
            EOther SLetRec (fs, e) -> 
                foldr (\(_,v) acc -> ofoldr f acc v) (ofoldr f z e) fs 
            EOther SAssume (_, e) -> ofoldr f z e
            EOther SBranch (e1, e2) -> ofoldr f (ofoldr f z e2) e1 
            EOther SFail  _ -> z
            EOther SOmega _ -> z
    ofoldMap f = ofoldr (mappend . f) mempty
    ofoldl' f z0 e = ofoldr f' id e z0
        where f' x k z = k $! f z x
    ofoldr1Ex f e = fromJust $ ofoldr g Nothing e
        where
        g v Nothing = Just v
        g v1 (Just v2) = Just (f v1 v2)
    ofoldl1Ex' f e = fromJust $ ofoldl' g Nothing e
        where
        g Nothing v = Just v
        g (Just v1) v2 = Just $! f v1 v2

instance MonoTraversable Exp where
    otraverse f e =
        let key = getUniqueKey e in
        case expView e of
            EValue v meta -> castWith <$> f meta <*> otraverse f v
            EOther SLet (x, e1, meta, e2) -> 
                mkLet x <$> otraverse f e1 
                        <*> f meta
                        <*> otraverse f e2
                        <*> pure key
            EOther SLetRec (fs, e2) ->
                mkLetRec <$> traverse (\(g, v) -> (g,) <$> otraverse f v) fs
                         <*> otraverse f e2
                         <*> pure key
            EOther SAssume (cond, e) ->
                mkAssume cond <$> otraverse f e <*> pure key
            EOther SBranch (e1, e2) -> 
                mkBranch <$> otraverse f e1 <*> otraverse f e2 <*> pure key
            EOther SFail _ -> pure e
            EOther SOmega _ -> pure e

instance MonoFunctor LExp where
    omap f e =
        let key = getUniqueKey e in
        case lexpView e of
            LAtom _ -> e
            LOther SBranch (e1, e2) -> 
                mkBranchL (omap f e1) (omap f e2) key
            LOther SApp (g, info, vs) ->
                mkApp g (f info) (map (omap f) vs) key
            LOther SRand _ -> mkRand key

instance MonoFoldable LExp where
    ofoldr f z e =
        case lexpView e of
            LAtom _ -> z
            LOther SApp (_, info, vs) -> f info (foldr (flip (ofoldr f)) z vs)
            LOther SRand _ -> z
            LOther SBranch (e1, e2) -> ofoldr f (ofoldr f z e2) e1
    ofoldMap f = ofoldr (mappend . f) mempty
    ofoldl' f z0 e = ofoldr f' id e z0
        where f' x k z = k $! f z x
    ofoldr1Ex f e = fromJust $ ofoldr g Nothing e
        where
        g v Nothing = Just v
        g v1 (Just v2) = Just (f v1 v2)
    ofoldl1Ex' f e = fromJust $ ofoldl' g Nothing e
        where
        g Nothing v = Just v
        g (Just v1) v2 = Just $! f v1 v2

instance MonoTraversable LExp where
    otraverse f e =
        let key = getUniqueKey e in
        case lexpView e of
            LAtom _ -> pure e
            LOther SApp (g, info, vs) -> 
                mkApp g <$> f info <*> traverse (otraverse f) vs <*> pure key
            LOther SRand _ -> pure e
            LOther SBranch (e1, e2) -> 
                mkBranchL <$> otraverse f e1 <*> otraverse f e2 <*> pure key

instance MonoFunctor Value where
    omap f v =
        let key = getUniqueKey v in
        case valueView v of
            VAtom _ -> v
            VOther SPair (v1, v2) -> mkPair (omap f v1) (omap f v2) key
            VOther SLambda (xs, info, e) ->
                mkLambda xs (f info) (omap f e) key

instance MonoFoldable Value where
    ofoldr f z v = 
        case valueView v of
            VAtom _ -> z
            VOther SPair (v1, v2) -> ofoldr f (ofoldr f z v2) v1
            VOther SLambda (_, info, e) -> f info (ofoldr f z e)
    ofoldMap f = ofoldr (mappend . f) mempty
    ofoldl' f z0 e = ofoldr f' id e z0
        where f' x k z = k $! f z x
    ofoldr1Ex f e = fromJust $ ofoldr g Nothing e
        where
        g v Nothing = Just v
        g v1 (Just v2) = Just (f v1 v2)
    ofoldl1Ex' f e = fromJust $ ofoldl' g Nothing e
        where
        g Nothing v = Just v
        g (Just v1) v2 = Just $! f v1 v2

instance MonoTraversable Value where
    otraverse f v =
        let key = getUniqueKey v in
        case valueView v of
            VAtom _ -> pure v
            VOther SPair (v1, v2) -> 
                mkPair <$> otraverse f v1 <*> otraverse f v2 <*> pure key
            VOther SLambda (xs, info, e) -> 
                mkLambda xs <$> f info <*> otraverse f e <*> pure key
