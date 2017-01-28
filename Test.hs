module Test where

import TambaraYamagami as TY
import Stringnet as S
import Data.Tree as T
import Data.Matrix as M

tree = fmap (\x -> case x of
                     Nothing -> "+"
                     Just e -> show e
            ) $ toTree finalMorphism

prin = (putStr. T.drawTree) tree

cList = toCompositionList finalMorphism

leaves = fmap (fmap substM) $ toTree finalMorphism

q = (TensorM (Id (OVar RightLeg)) (Rho (TensorO (Star (TensorO (TensorO (TensorO (Star (OVar LeftLoop)) (Star (OVar LeftLeg))) (OVar LeftLoop)) (Star (OVar RightLoop)))) (Star (OVar RightLoop)))))


-- takes ~10 seconds to run
big =  (TensorM (Id (OVar RightLeg)) (TensorM (Compose (AlphaI (Star (TensorO (TensorO (TensorO (Star (OVar LeftLoop)) (Star (OVar LeftLeg))) (OVar LeftLoop)) (Star (OVar RightLoop)))) (Star (OVar RightLoop)) (OVar RightLeg)) (Compose (TensorM (Id (Star (TensorO (TensorO (TensorO (Star (OVar LeftLoop)) (Star (OVar LeftLeg))) (OVar LeftLoop)) (Star (OVar RightLoop))))) (Rho (TensorO (Star (OVar RightLoop)) (OVar RightLeg)))) (Compose (TensorM (Id (Star (TensorO (TensorO (TensorO (Star (OVar LeftLoop)) (Star (OVar LeftLeg))) (OVar LeftLoop)) (Star (OVar RightLoop))))) (TensorM (Id (TensorO (Star (OVar RightLoop)) (OVar RightLeg))) (Ev (TensorO (TensorO (TensorO (Star (OVar LeftLoop)) (Star (OVar LeftLeg))) (OVar LeftLoop)) (Star (OVar RightLoop)))))) (Compose (TensorM (Id (Star (TensorO (TensorO (TensorO (Star (OVar LeftLoop)) (Star (OVar LeftLeg))) (OVar LeftLoop)) (Star (OVar RightLoop))))) (Alpha (TensorO (Star (OVar RightLoop)) (OVar RightLeg)) (Star (TensorO (TensorO (TensorO (Star (OVar LeftLoop)) (Star (OVar LeftLeg))) (OVar LeftLoop)) (Star (OVar RightLoop)))) (TensorO (TensorO (TensorO (Star (OVar LeftLoop)) (Star (OVar LeftLeg))) (OVar LeftLoop)) (Star (OVar RightLoop))))) (Compose (TensorM (Id (Star (TensorO (TensorO (TensorO (Star (OVar LeftLoop)) (Star (OVar LeftLeg))) (OVar LeftLoop)) (Star (OVar RightLoop))))) (TensorM (Compose (AlphaI (Star (OVar RightLoop)) (OVar RightLeg) (Star (TensorO (TensorO (TensorO (Star (OVar LeftLoop)) (Star (OVar LeftLeg))) (OVar LeftLoop)) (Star (OVar RightLoop))))) (Compose (Alpha (OVar RightLeg) (OVar RightLoop) (Star (TensorO (TensorO (Star (OVar LeftLoop)) (Star (OVar LeftLeg))) (OVar LeftLoop)))) (Compose (Alpha (Star (OVar RightLoop)) (TensorO (OVar RightLeg) (OVar RightLoop)) (Star (TensorO (TensorO (Star (OVar LeftLoop)) (Star (OVar LeftLeg))) (OVar LeftLoop)))) Phi))) (Id (TensorO (TensorO (TensorO (Star (OVar LeftLoop)) (Star (OVar LeftLeg))) (OVar LeftLoop)) (Star (OVar RightLoop)))))) (Compose (TensorM (PivotalJI (Star (TensorO (TensorO (TensorO (Star (OVar LeftLoop)) (Star (OVar LeftLeg))) (OVar LeftLoop)) (Star (OVar RightLoop))))) (LambdaI (TensorO (TensorO (TensorO (Star (OVar LeftLoop)) (Star (OVar LeftLeg))) (OVar LeftLoop)) (Star (OVar RightLoop))))) (Coev (TensorO (TensorO (TensorO (Star (OVar LeftLoop)) (Star (OVar LeftLeg))) (OVar LeftLoop)) (Star (OVar RightLoop)))))))))) (Id (Star (OVar RightLeg)))))

notAsBig =  ( ( ( ( ( (TensorM (Id (Star (TensorO (TensorO (TensorO (Star (OVar LeftLoop)) (Star (OVar LeftLeg))) (OVar LeftLoop)) (Star (OVar RightLoop))))) (TensorM (Compose (AlphaI (Star (OVar RightLoop)) (OVar RightLeg) (Star (TensorO (TensorO (TensorO (Star (OVar LeftLoop)) (Star (OVar LeftLeg))) (OVar LeftLoop)) (Star (OVar RightLoop))))) (Compose (Alpha (OVar RightLeg) (OVar RightLoop) (Star (TensorO (TensorO (Star (OVar LeftLoop)) (Star (OVar LeftLeg))) (OVar LeftLoop)))) (Compose (Alpha (Star (OVar RightLoop)) (TensorO (OVar RightLeg) (OVar RightLoop)) (Star (TensorO (TensorO (Star (OVar LeftLoop)) (Star (OVar LeftLeg))) (OVar LeftLoop)))) Phi))) (Id (TensorO (TensorO (TensorO (Star (OVar LeftLoop)) (Star (OVar LeftLeg))) (OVar LeftLoop)) (Star (OVar RightLoop)))))) )))))

smaller =  ( ( ( ( ( ( ( ( ( (Compose (Alpha (Star (OVar RightLoop)) (TensorO (OVar RightLeg) (OVar RightLoop)) (Star (TensorO (TensorO (Star (OVar LeftLoop)) (Star (OVar LeftLeg))) (OVar LeftLoop)))) Phi))) )) )))))

smallest = (Alpha (Star (OVar RightLoop)) (TensorO (OVar RightLeg) (OVar RightLoop)) (Star (TensorO (TensorO (Star (OVar LeftLoop)) (Star (OVar LeftLeg))) (OVar LeftLoop))))
