module Language.DMoCHi.ML.ConstPropagation where


import Language.DMoCHi.ML.Syntax.PNormal
import Language.DMoCHi.Common.Id
import qualified Data.Map as M

simplify :: Program -> Program
simplify prog = Program fs e
    where
    fs = map (\(f, key, xs, e) -> (f, key, xs, simplifyExp M.empty e)) (functions prog)
    e  = simplifyExp M.empty $ mainTerm prog

simplifyAtom :: M.Map TId Atom -> Atom -> Atom
simplifyAtom env a@(Atom l arg _) =
    case (l, arg) of
        (SLiteral, _) -> a
        (SVar, x) -> case M.lookup x env of
            Just a' -> a'
            Nothing -> a
        (SBinary, BinArg op a1 a2) -> mkBin op (simplifyAtom env a1) (simplifyAtom env a2)
        (SUnary, UniArg op a1) -> mkUni op (simplifyAtom env a1)
            
simplifyValue :: M.Map TId Atom -> Value -> Value
simplifyValue env v =
    let key = getUniqueKey v in
    case valueView v of
        VAtom a -> castWith key (simplifyAtom env a)
        VOther SPair (v1, v2) -> mkPair (simplifyValue env v1) (simplifyValue env v2) key
        VOther SLambda (xs, e) -> mkLambda xs (simplifyExp env e) key

simplifyLExp :: M.Map TId Atom -> LExp -> LExp
simplifyLExp env e =
    let key = getUniqueKey e in
    case lexpView e of
        LValue v -> cast (simplifyValue env v)
        LOther SApp (f, vs) -> 
            case M.lookup f env of
                Just (Atom SVar f' _) -> mkApp f' (map (simplifyValue env) vs) key
                Just _ -> error "simplifyLExp: unexpected pattern"
                Nothing -> mkApp f (map (simplifyValue env) vs) key
        LOther SFail _ -> e
        LOther SOmega _ -> e
        LOther SRand _ -> e
        LOther SBranch (e1, e2) ->
            mkBranchL (simplifyExp env e1) (simplifyExp env e2) key

simplifyExp :: M.Map TId Atom -> Exp -> Exp
simplifyExp env e = 
    let key = getUniqueKey e in
    case expView e of
        EValue v -> cast (simplifyValue env v)
        EOther SLetRec (fs, e1) -> mkLetRec (map (\(f, v) -> (f, simplifyValue env v)) fs) (simplifyExp env e1) key
        EOther SAssume (a, e1) -> mkAssume (simplifyAtom env a) (simplifyExp env e1) key
        EOther SBranch (e1, e2) -> mkBranch (simplifyExp env e1) (simplifyExp env e2) key
        EOther SFail   _ -> e
        EOther SOmega  _ -> e
        EOther SLet (x, e1, e2) -> 
            let e1' = simplifyLExp env e1 in
            case lexpView e1' of
                LValue (valueView -> VAtom a@(Atom SLiteral _ _)) -> simplifyExp (M.insert x a env) e2
                LValue (valueView -> VAtom a@(Atom SVar _ _))     -> simplifyExp (M.insert x a env) e2
                _ -> mkLet x e1' (simplifyExp env e2) key
