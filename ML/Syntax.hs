{-# LANGUAGE DeriveFunctor #-}
module ML.Syntax where

data Exp = Value Value 
         | Let Id LetValue Exp 
         | Assume Value Exp
         | Lambda Id Exp
         | Fail
         | Branch Exp Exp deriving(Show)

data Value = Var Id
           | CInt Integer
           | CBool Bool
           | Op (Op Value) deriving(Show)

data Op a = OpAdd a a
          | OpSub a a
          | OpNeg a
          | OpEq  a a
          | OpLt  a a
          | OpGt  a a
          | OpAnd a a
          | OpOr  a a
          | OpNot a deriving(Show,Functor)

data LetValue = LValue Value
              | LApp Id [Value]
              | LExp PType Exp
              deriving(Show)

data PType = PInt [Predicate]
           | PBool [Predicate]
           | PFun PType (Value -> PType)

instance Show PType where
    show = sub (1::Int) where
        sub i (PInt xs) = 
            let x = "x_" ++ show i in
            show $ map ((,) x . ($Var x)) xs
        sub i (PBool xs) = 
            let x = "b_" ++ show i in
            show $ map ((,) x . ($Var x)) xs
        sub i (PFun ty f) = 
            let x = "x_" ++ show i in
            let s1 = "("++x ++ " : " ++ sub i ty ++ ") -> " in
            s1 ++ sub (i+1) (f (Var x))

type Id = String
type Predicate = Value -> Value

substV :: Id -> Value -> Value -> Value
substV x v = go where
    go (Var y) | x == y = v
    go (Op op) = Op $ fmap go op
    go w = w
