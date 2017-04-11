
module Finite where

import Data.List

    
-- A type with a finite number of elements
class Finite a where
  allElements :: [a]

instance (Finite a, Show b) => Show (a -> b) where
  show f = show $ toList f

toList :: Finite a => (a -> b) -> [b]
toList f = map f allElements

toIndex :: (Finite a, Eq a) => a -> Int
toIndex x =
  case elemIndex x allElements of
    Just i -> i
    Nothing -> error "Finite.toIndex: index not found"

fromList :: (Finite a, Eq a) => [b] -> a -> b
fromList bs x = bs !! (toIndex x)
