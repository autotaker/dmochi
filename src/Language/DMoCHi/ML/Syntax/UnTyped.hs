{-# LANGUAGE DeriveFunctor #-}
module Language.DMoCHi.ML.Syntax.UnTyped where

data Exp = Value Value 
         | Let Id LetValue Exp 
         | Assume Value Exp
         | Lambda Id Exp
         | Fail
         | Branch Exp Exp deriving(Show)

data Program = Program { functions :: [(Id,PType,Exp)] 
                       , mainTerm  :: Exp }

data Value = Var Id
           | CInt Integer
           | CBool Bool
           | Pair Value Value
           | Op Op deriving(Show)

data Op = OpAdd Value Value
        | OpSub Value Value
        | OpNeg Value
        | OpEq  Value Value
        | OpLt  Value Value
        | OpGt  Value Value
        | OpLte Value Value
        | OpGte Value Value
        | OpAnd Value Value
        | OpOr  Value Value
        | OpFst Value
        | OpSnd Value
        | OpNot Value deriving(Show)

data LetValue = LValue Value
              | LApp Id [Value]
              | LExp PType Exp
              | LRand
              deriving(Show)

data PType = PInt [Predicate]
           | PBool [Predicate]
           | PPair PType (Id,PType)
           | PFun  PType (Id,PType)

instance Show PType where
    show (PInt xs) = "int"++ show xs
    show (PBool xs) = "bool"++show xs
    show (PPair ty_f (x,ty_s)) = 
        let s1 = "("++x++ " ; " ++ show ty_f ++ ") * " in
        s1 ++ show ty_s
    show (PFun ty (x,f)) = 
        let s1 = "("++x ++ " : " ++ show ty ++ ") -> " in
        s1 ++ show f

type Id = String
type Predicate = (Id,Value)

