module Sort where

data Sort = Base | [Sort] :-> Sort deriving(Eq,Ord,Show)




