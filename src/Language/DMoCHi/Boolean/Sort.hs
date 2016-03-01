module Language.DMoCHi.Boolean.Sort where

data Sort = Base | Tuple [Sort] | Sort :-> Sort deriving(Eq,Ord,Show)

order :: Sort -> Int
order Base = 0
order (Tuple l) = maximum $ 0:map order l
order (t1 :-> t2) = max (order t1 + 1) (order t2)




