module Test where

import TambaraYamagami as TY
import Stringnet as S
import Data.Tree as T
import Data.Matrix as M
import Data.Maybe
import Finite
import Algebra


obj = (toObject M) `TY.tensorO` (toObject M) `TY.tensorO` (toObject M)

m = toObject M
o = toObject one
notOne = toObject $ AE $ AElement 1

-- a snake equation
snake o = idMorphism o == ((ev o) `TY.tensorM` (idMorphism o))
  `TY.compose` (alpha o o o)
  `TY.compose` ((idMorphism o) `TY.tensorM` (coev o))

-- ((ab)c)d) -> (ab)(cd) -> a(b(cd))
pentagonLHS a b c d =
  (alpha a b (c `TY.tensorO` d))
  `TY.compose` (alpha (a `TY.tensorO` b) c d)

-- ((ab)c)d -> (a(bc))d -> a((bc)d) -> a(b(cd))
pentagonRHS a b c d =
  ((idMorphism a) `tensorM` (alpha b c d))
  `TY.compose` (alpha a (b `TY.tensorO` c) d)
  `TY.compose` ((alpha a b c) `tensorM` idMorphism d)

--FIXME: pentagon m m m m
pentagon a b c d = (pentagonLHS a b c d) == (pentagonRHS a b c d)
  
  


-- 81 is interesting 
-- finalET =  map (\ib -> map (substO (initialLabel ib)) $ map (S.objectLabel S.finalSN) $ S.flatten S.finalEdgeTree) (allElements :: [InitialBasisElement])


-- old (finalMorphism) testing

tree = fmap (\x -> case x of
                     Nothing -> "+"
                     Just e -> show e
            ) $ toTree S.finalMorphism

prin = (putStr. T.drawTree) tree

cList = toCompositionList S.finalMorphism

leaves = catMaybes $ T.flatten $ toTree S.finalMorphism

leftT (TensorM a b) = a
rightT (TensorM a b) = b

-- leftC (Compose a b) = a
-- rightC (Compose a b) = b

-- bad = Compose (AlphaI (Star (OVar RightLoop)) (OVar RightLoop) (Star One)) (Compose (RhoI (OVar RightLoop)) (Coev (OVar RightLoop)))


-- small = (Compose (TensorM (PivotalJI (Star (OVar RightLoop))) (LambdaI (OVar RightLoop))) (Coev (OVar RightLoop)))


-- -- new testing

-- -- TODO: Calculate a matrix for addCoev.  What I need to do is figure
-- -- out how to turn the monad actions into a list of actions.  
