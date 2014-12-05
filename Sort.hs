module Sort where

data Sort = Base | Tuple [Sort] | Sort :-> Sort deriving(Eq,Ord,Show)




