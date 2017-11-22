module Language.DMoCHi.ML.TailOptimization where

-- simplify by the following law: let x = e in x ==> e

import Language.DMoCHi.ML.Syntax.PNormal
import Language.DMoCHi.Common.Id

simplify :: Program -> Program
simplify prog = Program fs e
    where
    fs = map (\(f, key, xs, e) -> (f, key, xs, simplifyExp e)) (functions prog)
    e  = simplifyExp $ mainTerm prog

simplifyValue :: Value -> Value
simplifyValue v =
    let key = getUniqueKey v in
    case valueView v of
        VAtom _ -> v
        VOther SPair (v1, v2) -> mkPair (simplifyValue v1) (simplifyValue v2) key
        VOther SLambda (xs, e) -> mkLambda xs (simplifyExp e) key

simplifyLExp ::LExp -> LExp
simplifyLExp e =
    let key = getUniqueKey e in
    case lexpView e of
        LValue v -> cast (simplifyValue v)
        LOther SApp (f, vs) -> mkApp f (map simplifyValue vs) key
        LOther SFail _ -> e
        LOther SOmega _ -> e
        LOther SRand _ -> e
        LOther SBranch (e1, e2) ->
            mkBranchL (simplifyExp e1) (simplifyExp e2) key

simplifyExp :: Exp -> Exp
simplifyExp e = 
    let key = getUniqueKey e in
    case expView e of
        EValue v -> cast (simplifyValue v)
        EOther SLetRec (fs, e1) -> mkLetRec (map (\(f, v) -> (f, simplifyValue v)) fs) (simplifyExp e1) key
        EOther SAssume (a, e1) -> mkAssume a (simplifyExp e1) key
        EOther SBranch (e1, e2) -> mkBranch (simplifyExp e1) (simplifyExp e2) key
        EOther SFail   _ -> e
        EOther SOmega  _ -> e
        EOther SLet (x, e1, e2) -> 
            case simplifyExp e2 of
                e2'@(Exp SVar y _ _) | y == x -> 
                    let e1' = simplifyLExp e1 in
                    case lexpView e1'  of
                        LValue v -> cast v
                        LOther SFail _ -> mkFail (getType e1') key
                        LOther SOmega _ -> mkOmega (getType e1') key
                        LOther SBranch (e1, e2) -> mkBranch e1 e2 key
                        LOther SApp _ -> mkLet x e1' e2' key
                        LOther SRand _ -> mkLet x e1' e2' key
                e2' -> mkLet x (simplifyLExp e1) e2' key
