module Syntax where

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
          | OpNot a deriving(Show)

data LetValue = LValue Value
              | LApp Id [Value]
              | LExp PType Exp
              deriving(Show)

data PType = PInt [Predicate]
           | PBool [Predicate]
           | PFun Id PType PType
           deriving(Show)

type Id = String
type Predicate = (Id,Value)

