
module TwoComplex where

import qualified Stringnet as S

data TwoComplex = TwoComplex
  { vertices      :: ![S.InteriorVertex]
  , edges         :: ![S.Edge]
  , disks         :: ![S.Disk]
  
  -- The edges returned by perimeter should form a
  -- cycle (the end point of an edge should be the the
  -- starting point of the next edges).  Additionally,
  -- the edges should either lie in the edges of the
  -- Stringnet or be the reverse of such an edge.  CCW
  -- ordering.
  , perimeter     :: !(S.Disk -> [S.Edge])

  -- image under contractions
  , imageVertex    :: !(S.Vertex -> S.Vertex)     
    
  -- CCW ordering, outgoing orientation
  , edgeTree      :: !(S.Vertex -> S.Tree S.Edge)  
  }
