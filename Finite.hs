



module Finite where

    
-- A type with a finite number of elements
class Finite a where
  allElements :: [a]

instance (Finite a, Show b) => Show (a -> b) where
  show f = show $ toList f

toList :: Finite a => (a -> b) -> [b]
toList f = map f allElements

