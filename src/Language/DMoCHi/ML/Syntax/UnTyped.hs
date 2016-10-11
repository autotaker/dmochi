{-# LANGUAGE DeriveFunctor #-}
module Language.DMoCHi.ML.Syntax.UnTyped(Exp(..)
                                        ,Program(..)
                                        ,Value(..)
                                        ,Op(..)
                                        ,LetValue(..)
                                        ,Id
                                        ,Type(..)
                                        ) where
import Language.DMoCHi.ML.Syntax.Type hiding(Id)

data Exp = Value Value 
         | Let Id LetValue Exp 
         | Assume Value Exp
         | Lambda [Id] Exp
         | Fail
         | Branch Exp Exp deriving(Show)

data Program = Program { functions :: [(Id,Type,Exp)] 
                       , mainTerm  :: Exp }

data Value = Var Id
           | CInt Integer
           | CBool Bool
           | Pair Value Value
           | App Id [Value]
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
              | LExp Type Exp
              | LRand
              deriving(Show)

type Id = String
