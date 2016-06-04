module Language.DMoCHi.ML.Refine

import Language.DMoCHi.ML.Syntax.Typed hiding(PType(..))
import Language.DMoCHi.ML.PredicateAbstraction(PType(..), TypeMap, typeOfValue)
import qualified Data.IntMap as IM
import qualified Data.Map as M

{-
propagateAbsType :: Program -> TypeMap -> TypeMap
propagateAbsType prog typeMap = foldl (propagateExp tenv) typeMap
    where
    tenv = M.fromList [ (f, pty) | (f,fdef) <- functions prog, let Left pty = typeMap IM.! ident fdef ]
    terms = (mainTerm prog, PInt) : 
          [ (f, tenv M.! f)  | (f,_) <- functions prog ]

propagateExp :: M.Map Symbol PType -> TypeMap -> (Exp,PType) -> TypeMap
propagateExp genv = uncurry . go M.empty genv
    where
    go env tenv typeMap _e pty = case _e of
        Value v -> 
            let sv = eval env v in
            subType typeMap sv pty
        Fun f -> 
            let PFun _ (_,pty_arg,_) (_,pty_body,_) = pty
                tenv' = M.insert (arg f) pty_arg tenv
            in go env tenv' typeMap (body f) pty_body
        Assume _ v e -> go env tenv typeMap e pty
        Fail _ -> typeMap
        Let _ x lv e -> 
            case lv of
                LValue v -> 
                    let sv = eval env v
                        pty_x = typeOfValue tenv v
                        env' = M.insert x sv env
                        tenv' = M.insert x pty_x tenv
                    in
                    go env' tenv' typeMap e pty
                LApp _ _ f v ->
                    let sv = eval env v
                        PFun _ (_,pty_arg,_) (_,pty_body,_) = tenv M.! f
                        typeMap' = subType typeMap sv pty_arg
                        tenv' = M.insert x pty_body
                    in
                    go env tenv' typeMap' e pty
                LFun fdef ->
                    let env' = M.insert x (SFun (Just (ident fdef))) env
                        tenv' = 
                    go 


        Branch _ _ e1 e2 -> propagateExp (propagateExp typeMap e1 pty) e2 pty
        -}

data SValue = SBase | SFun (Maybe Int) | SPair SValue SValue

valueOfType :: Type -> SValue
valueOfType TInt = SBase
valueOfType TBool = SBase
valueOfType (TPair t1 t2) = valueOfType t1 `SPair` valueOfType t2
valueOfType (TFun t1 t2) = SFun Nothing

eval :: M.Map Id SValue -> Value -> SValue
eval env (Var x) = case M.lookup x env of 
                        Just it -> it 
                        Nothing -> valueOfType (getType x)
eval env (CInt _) = SBase
eval env (CBool _) = SBase
eval env (Pair v1 v2) = eval env v1 `SPair` eval env v2
eval env (Op _ ) = SBase

