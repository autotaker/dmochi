module Heap ( Tree
            , empty
            , isEmpty
            , minElem
            , deleteMin
            , insert ) where


data Tree a = Null | Fork a (Tree a) (Tree a) deriving(Show)

empty :: Tree a
empty = Null

isEmpty :: Tree a -> Bool
isEmpty Null = True
isEmpty _ = False

minElem :: Tree a -> a
minElem (Fork a _ _) = a
minElem Null = error "min for empty queue is not supported"

deleteMin :: (Ord a) => Tree a -> Tree a
deleteMin (Fork _ a b) = merge a b
deleteMin Null = error "empty queue"

insert :: (Ord a) => a -> Tree a -> Tree a
insert x a = merge (Fork x Null Null) a

merge :: (Ord a) => Tree a -> Tree a -> Tree a
merge a Null = a
merge Null b = b
merge a b | minElem a <= minElem b = join a b
          | otherwise = join b a
    where
    join (Fork x _a _b) _c = Fork x _b (merge _a _c)
    join _ _ = undefined

