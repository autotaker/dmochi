{-# LANGUAGE FlexibleContexts, GADTs, TypeFamilies, DataKinds #-}
module Language.DMoCHi.ML.Syntax.Typed  where
-- import qualified Data.Map as M
-- import qualified Data.Set as S
import Language.DMoCHi.Common.Id 
import Language.DMoCHi.ML.Syntax.Type
import Language.DMoCHi.ML.Syntax.Base
import Text.PrettyPrint.HughesPJClass

data Program = Program { functions :: [(TId, UniqueKey, [TId], Exp)] 
                       , mainTerm  :: Exp }

data Exp where
    Exp :: ( WellFormed l Exp arg
           , Supported l (Labels Exp)) => SLabel l -> arg -> Type -> UniqueKey -> Exp

type instance Labels Exp = AllLabels
type instance BinOps Exp = AllBinOps
type instance UniOps Exp = AllUniOps
type instance Ident Exp = TId

instance HasType Exp where
    getType (Exp _ _ sty _) = sty
instance HasUniqueKey Exp where
    getUniqueKey (Exp _ _ _ key) = key

instance Pretty Exp where
    pPrintPrec plevel prec (Exp op arg sty key) =
        if plevel == prettyNormal
            then doc 
            else comment (key, sty) <+> doc
        where
        doc = genericPPrint pp plevel prec op arg
        pp :: WellFormedPrinter Exp
        pp = WellFormedPrinter { pPrintExp   = pPrintPrec
                               , pPrintIdent = pPrintPrec }

instance Pretty Program where
    pPrintPrec plevel _ (Program fs t) = 
        text "(* functions *)" $+$ 
        vcat (map (\(f,key,xs,e) -> 
            comment key $+$
            text "let" <+> pPrintPrec plevel 0 f <+> hsep (map (pPrintPrec prettyBind 1) xs) <+> colon <+> pPrint (getType e) <+> equals $+$
            nest 4 (pPrintPrec plevel 0 e <> text ";;")) fs) $+$
        text "(*main*)" $+$
        pPrintPrec plevel 0 t

mkBin :: SBinOp op -> Exp -> Exp -> UniqueKey -> Exp
mkBin op e1 e2 key = 
    let f :: Type -> Type -> Exp -> Exp
        f ty1 ty2 k | getType e1 /= ty1 = error "mkBin: Type Error"
                    | getType e2 /= ty2 = error "mkBin: Type Error"
                    | otherwise = k
    in case op of
        SAdd -> f TInt TInt $ Exp SBinary (BinArg op e1 e2) TInt key
        SSub -> f TInt TInt $ Exp SBinary (BinArg op e1 e2) TInt key
        SDiv -> f TInt TInt $ Exp SBinary (BinArg op e1 e2) TInt key
        SMul -> f TInt TInt $ Exp SBinary (BinArg op e1 e2) TInt key
        SEq  -> f TInt TInt $ Exp SBinary (BinArg op e1 e2) TBool key
        SNEq -> f TInt TInt $ Exp SBinary (BinArg op e1 e2) TBool key
        SLt  -> f TInt TInt $ Exp SBinary (BinArg op e1 e2) TBool key
        SLte -> f TInt TInt $ Exp SBinary (BinArg op e1 e2) TBool key
        SGt  -> f TInt TInt $ Exp SBinary (BinArg op e1 e2) TBool key
        SGte -> f TInt TInt $ Exp SBinary (BinArg op e1 e2) TBool key
        SAnd -> f TBool TBool $ Exp SBinary (BinArg op e1 e2) TBool key
        SOr  -> f TBool TBool $ Exp SBinary (BinArg op e1 e2) TBool key

mkUni :: SUniOp op -> Exp -> UniqueKey -> Exp
mkUni op e1 key =
    let f :: Type -> Exp -> Exp
        f ty1 k | getType e1 /= ty1 = error "mkBin: TypeError"
                | otherwise = k in
    case op of
        SFst -> case getType e1 of
            TPair ty1 _ -> Exp SUnary (UniArg op e1) ty1 key
            _ -> error "mkUni: SFst: Type Error"
        SSnd -> case getType e1 of
            TPair _ ty2 -> Exp SUnary (UniArg op e1) ty2 key
            _ -> error "mkUni: SFst: Type Error"
        SNeg -> f TInt  $ Exp SUnary (UniArg op e1) TInt key
        SNot -> f TBool $ Exp SUnary (UniArg op e1) TBool key

mkLiteral :: Lit -> UniqueKey -> Exp
mkLiteral l key = case l of
    CInt _ -> Exp SLiteral l TInt key
    CBool _ -> Exp SLiteral l TBool key
    CUnit  -> error "mkLiteral: unexpected unit literal"

mkVar :: TId -> UniqueKey -> Exp
mkVar x key = Exp SVar x (getType x) key

mkPair :: Exp -> Exp -> UniqueKey -> Exp
mkPair e1 e2 key = Exp SPair (e1, e2) (TPair (getType e1) (getType e2)) key

mkLambda :: [TId] -> Exp -> UniqueKey -> Exp
mkLambda xs e key = Exp SLambda (xs, e) (TFun (map getType xs) (getType e)) key

mkApp :: Exp -> [Exp] -> UniqueKey -> Exp
mkApp e1 es key = case getType e1 of
    TFun tys ty | tys == map getType es -> Exp SApp (e1, es) ty key
    _ -> error "mkApp: Type Error"

mkLet :: TId -> Exp -> Exp -> UniqueKey -> Exp
mkLet x e1 e2 key | getType x == getType e1 = Exp SLet (x, e1, e2) (getType e2) key
                  | otherwise = error "mkLet: Type Error"

mkLetRec :: [(TId, Exp)] -> Exp -> UniqueKey -> Exp
mkLetRec fs e key | ok = Exp SLetRec (fs, e) (getType e) key
                  | otherwise = error "mkLetRec: Type Error"
    where
    ok = all (\(f, e_f) -> case e_f of
        Exp SLambda _ _ _ | getType e_f == getType f -> True
        _ -> False) fs

mkAssume :: Exp -> Exp -> UniqueKey -> Exp
mkAssume e1 e2 key = case getType e1 of
    TBool -> Exp SAssume (e1, e2) (getType e2) key
    _ -> error "mkAssume: Type Error"

mkIf :: Exp -> Exp -> Exp -> UniqueKey -> Exp
mkIf eCond eThen eElse key = case (getType eCond, getType eThen, getType eElse) of
    (TBool, ty1, ty2) | ty1 == ty2 -> Exp SIf (eCond, eThen, eElse) ty1 key
    _ -> error "mkIf: Type Error"
    
mkBranch ::  Exp -> Exp -> UniqueKey -> Exp
mkBranch eThen eElse key = case (getType eThen, getType eElse) of
    (ty1, ty2) | ty1 == ty2 -> Exp SBranch (eThen, eElse) ty1 key
    _ -> error "mkBranch: Type Error"

mkFail :: Type -> UniqueKey -> Exp
mkFail ty key = Exp SFail () ty key

mkOmega :: Type -> UniqueKey -> Exp
mkOmega ty key = Exp SOmega () ty key

mkRand :: UniqueKey -> Exp
mkRand key = Exp SRand () TInt key
        
mkMark :: TId -> Exp -> UniqueKey -> Exp
mkMark x e key = Exp SMark  (x, e) (getType e) key
