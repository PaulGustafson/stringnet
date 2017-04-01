module Test where

import TambaraYamagami as TY
import Stringnet as S
import Data.Tree as T
import Data.Matrix as M
import Data.Maybe
import Finite
import Algebra


obj = (toObject M) `TY.tensorO` (toObject M) `TY.tensorO` (toObject M)

-- snake equations
snake o = idMorphism o == ((ev o) `TY.tensorM` (idMorphism o))
  `TY.compose` alpha o o o
  `TY.compose` ((idMorphism o) `TY.tensorM` (coev o))





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
