
module TwoComplex where

import Data.List
import Finite
import Tree

-- Left and right refer to positions before the braiding operation
data Puncture = LeftPuncture | RightPuncture
  deriving (Show, Eq)

data InteriorVertex = Main | Midpoint Edge | Contraction Edge
  deriving (Show, Eq)

data Vertex = Punc Puncture | IV InteriorVertex
  deriving (Show, Eq)

--initial edges
data InitialEdge = LeftLoop | RightLoop | LeftLeg | RightLeg
  deriving (Show, Eq, Enum)

toInitialEdge :: Edge -> InitialEdge
toInitialEdge (IE ie) = ie
toInitialEdge e = error  $ "Failed to cast " ++ (show e) ++ " to InitialEdge"

instance Finite InitialEdge where
  allElements = [LeftLoop, RightLoop, LeftLeg, RightLeg]


-- Orientations of initial edges are given by arrows in the figures in
-- the paper
data Edge =
  -- initial edges
  IE InitialEdge

  -- result of adding coev vertex (--(e)--> (coev e) --(e)-->)
  | FirstHalf Edge | SecondHalf Edge

  -- connects the start of the two edges with a 1 in the disk
  | Connector Edge Edge Disk

   -- stick together parallel edges
  | TensorE Edge Edge

  -- don't use this constructor except to pattern match, use "rev"
  -- instead
  | Reverse Edge  
          deriving (Show, Eq)


-- type cast 
toIV :: Vertex -> InteriorVertex
toIV (IV v) = v

rev :: Edge -> Edge
rev (Reverse e) = e
-- MAYBE: (need to deal with Eq instance)
-- rev (TensorE a b) = TensorE (rev a) (rev b)
rev e = Reverse e


-- endpoints before finding the images of the vertices under
-- contractions
initialEndpoints :: Edge -> [Vertex]
initialEndpoints edge  = case edge of
  IE LeftLoop  -> [IV Main, IV Main]
  IE RightLoop -> [IV Main, IV Main]
  IE LeftLeg   -> [IV Main, Punc LeftPuncture]
  IE RightLeg  -> [IV Main, Punc RightPuncture]
  FirstHalf e -> [(initialEndpoints e) !! 0, IV $ Midpoint e]
  SecondHalf e -> [IV $ Midpoint e, (initialEndpoints e) !! 1]
  Connector e1 e2 _ -> [initialStart e1, initialStart e2]
  TensorE e1 _ -> initialEndpoints e1
  Reverse e -> reverse (initialEndpoints e)

initialStart :: Edge -> Vertex
initialStart e = (initialEndpoints e) !! 0

initialEnd :: Edge -> Vertex
initialEnd e = (initialEndpoints e) !! 1


-- probably not needed
replaceIE :: (InitialEdge -> Edge) -> Edge -> Edge
replaceIE f (IE ie) = f ie
replaceIE f (FirstHalf e) =  FirstHalf (replaceIE f e)
replaceIE f (SecondHalf e) = SecondHalf (replaceIE f e)
replaceIE f (Connector e1 e2 (Cut e3)) = Connector (replaceIE f e1) (replaceIE f e2) (Cut (replaceIE f e3))
replaceIE f (Connector e1 e2 Outside) = Connector (replaceIE f e1) (replaceIE f e2) Outside
replaceIE f (Connector e1 e2 LeftDisk) = Connector (replaceIE f e1) (replaceIE f e2) LeftDisk
replaceIE f (Connector e1 e2 RightDisk) = Connector (replaceIE f e1) (replaceIE f e2) RightDisk
replaceIE f (TensorE e1 e2) = TensorE (replaceIE f e1) (replaceIE f e2)
replaceIE f (Reverse e) = rev (replaceIE f e)

data Disk =
  -- initial disks
  Outside | LeftDisk | RightDisk

  -- Edge should be of type Connect
  | Cut Edge          
          deriving (Show, Eq)


data TwoComplex = TwoComplex
  { vertices      :: ![InteriorVertex]
  , edges         :: ![Edge]
  , disks         :: ![Disk]
  
  -- The edges returned by perimeter should form a
  -- cycle (the end point of an edge should be the the
  -- starting point of the next edges).  Additionally,
  -- the edges should either lie in the edges of the
  -- Stringnet or be the reverse of such an edge.  CCW
  -- ordering.
  , perimeter     :: !(Disk -> [Edge])

  -- image under contractions
  , imageVertex    :: !(Vertex -> Vertex)
  }



indexV :: TwoComplex -> InteriorVertex -> Int
indexV tc v = case elemIndex v (vertices tc) of
  Just i -> i
  Nothing -> error "indexV: vertex not found"

indexE :: TwoComplex -> Edge -> Int
indexE tc e = case elemIndex e (edges tc) of
  Just i -> i
  Nothing -> error "indexE: edge not found"


