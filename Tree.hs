module Tree where

import Data.Foldable

data Tree a = Leaf a | Node (Tree a) (Tree a)
            deriving (Eq, Show)

instance Functor Tree where
  fmap f (Leaf l) = Leaf $ f l
  fmap f (Node a b) = Node (fmap f a) (fmap f b)

instance Foldable Tree where
  foldMap f (Leaf x) = f x
  foldMap f (Node a b) = (foldMap f a) `mappend` (foldMap f b)


flatten :: Tree a -> [a]
flatten (Leaf x) = [x] 
flatten (Node x y) = (flatten x) ++ (flatten y)


replace :: (Eq a) => Tree a -> Tree a -> Tree a -> Tree a
replace subTree1 subTree2 bigTree = 
  if bigTree == subTree1
  then subTree2
  else case bigTree of
    Leaf x  -> Leaf x
    Node x y -> Node (replace subTree1 subTree2 x)
                (replace subTree1 subTree2 y)

