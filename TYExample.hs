-- Calculate R-matrix for TY(\ZZ_7, \zeta_7^{ab}, \sqrt{7})
-- References:
--
-- Daisuke Tambara, Shigeru Yamagami, Tensor Categories with Fusion
-- Rules of Self-Duality for Finite Abelian Groups
--
-- Shlomo Gelaki, Deepak Naidu: “Centers of graded fusion categories”
--

module TYExample where

import qualified Stringnet as S
import           Data.Semigroup
import Data.List.NonEmpty as N

order = 7

-- group element, assuming cyclicity
-- dependent types would be nice here
data GroupElement = GroupElement Int deriving (Show, Eq)

inv :: GroupElement -> GroupElement
inv (GroupElement e) = GroupElement  $ (-e) `mod` order

plus :: GroupElement -> GroupElement -> GroupElement
(GroupElement e1) `plus` (GroupElement e2) = GroupElement $ (e1 + e2) `mod` order

-- \pm (order)^{-1/2}
data Tau = Plus | Minus


data Scalar =
  Zero
  | Tau
  -- use a group element to represent the root of unity
  | RootOfUnity GroupElement 
  | MultS_ Scalar Scalar 


oneScalar :: Scalar
oneScalar = RootOfUnity $ GroupElement 0

-- TODO: Some more cancellation should  show up here
multS :: Scalar -> Scalar -> Scalar
multS Zero _ = Zero
multS _ Zero = Zero
multS (RootOfUnity a) (RootOfUnity b) = RootOfUnity (a `plus` b)
multS a b = MultS_ a b


chi :: GroupElement -> GroupElement -> Scalar
chi (GroupElement e1) (GroupElement e2) = RootOfUnity $ GroupElement $ (e1*e2) `mod` order

chiI :: GroupElement -> GroupElement -> Scalar
chiI (GroupElement e1) (GroupElement e2) = RootOfUnity $ GroupElement $ (-e1*e2) `mod` order


data SimpleObject =
  -- non-group simple object
  M

  -- Group-element-indexed simple objects
  | GE GroupElement
                  deriving (Show,Eq)


-- would really like dependent typing here...
data Index =
  UnitIndex

  -- the abelian group
  | GEIndex GroupElement

  | ProdI Index Index


data Object = SumO (Index -> SimpleObject)

so :: SimpleObject -> Object
so x = SumO $ \y -> case y of
  UnitIndex ->  x
  
-- Matrices of scalars times identity maps
data Morphism =  Matrix (Index -> Index -> Scalar)

scalarMorphism s =
  Matrix $ \x ->
             \y -> case x of
                     UnitIndex -> case y of
                       UnitIndex -> s

idMorphism = scalarMorphism $ RootOfUnity $ GroupElement 0

groupSum :: (Index -> Scalar) -> Morphism
groupSum f =
  Matrix $ \x -> case x of GEIndex gx ->
                             \y -> case y of GEIndex gy ->
                                               if gx == gy
                                               then f x
                                               else Zero


-- carrier set for the group
carrier :: NonEmpty GroupElement
carrier = N.map GroupElement $ fromList [0..(order - 1)]

starSO :: SimpleObject -> SimpleObject
starSO M =  M
starSO (GE g) = GE (inv g)

star :: Object -> Object
star (SumO f) = SumO $ starSO . f

tensorM :: Morphism -> Morphism -> Morphism
tensorM (Matrix f) (Matrix g) =
  Matrix $ \p q ->
             case p of
               ProdI a b ->
                 case q of
                   ProdI c d -> 
                     (f a c) `multS` (g b d)
                   
                   
-- validInitialLabels :: S.InitialEdge -> [SimpleObject]
-- validInitialLabels ie = [M, GE $ GEVar ie]

tensorSO :: SimpleObject -> SimpleObject -> Object
tensorSO M M = \i -> case i of
  GEIndex g -> GroupElement g
tensorSO M (GE _) = so M
tensorSO (GE _) M = so M
tensorSO (GE g1) (GE g2) = so $ GE $ g1 `plus` g2

--TODO: figure out how to flatten nested direct sums
-- Should be able to use the fact that they are independent sums
tensorO :: Object -> Object -> Object
tensorO (SumO f) (SumO g) = SumO $ \i -> case i of
  ProdI i1 i2 ->
    let
      so1 = f i1
      so2 = f i2
    in
      if so1 == M && so2 == M
      then 

-- TODO: un-hardcode initial edge labels
-- Substitute in the TY-specific objects. 
substO :: S.Object -> Object
substO o0 =  case o0 of
  S.One -> so $ GE (GroupElement 0)
  S.Star o -> star $ substO o
  S.TensorO o1 o2 -> (substO o1) `tensorO` (substO o2)


alpha :: SimpleObject -> SimpleObject -> SimpleObject -> Morphism
alpha (GE g1) (GE g2) (GE g3) = idMorphism
alpha (GE _) (GE _) M = idMorphism
alpha M (GE _) (GE _) = idMorphism
alpha (GE a) M (GE b) = scalarMorphism (chi a b) 
alpha (GE _) M M = groupSum (\x -> oneScalar)
alpha M M (GE _) = groupSum (\x -> oneScalar)
alpha M (GE a) M = groupSum (\b -> chi a b) 
alpha M M M =
  let alphaMMM (GEIndex a) (GEIndex b) = scalarMorphism $ chi a b in
     Matrix alphaMMM
             
                     
-- Substitute in the TY-specific morphisms 
substM :: S.Morphism -> Morphism
substM m = case m of
  S.Phi -> idMorphism
  S.Id o -> idMorphism
  S.Lambda o -> idMorphism
  S.LambdaI o -> idMorphism
  S.Rho o -> idMorphism
  S.RhoI o -> idMorphism
  S.TensorM m1 m2 -> (substM m1) `tensorM` (substM m2)

  -- Alpha o1 o2 o3 -> case (substO o1) of
  --   SumO o11 o12
  -- --
  -- AlphaI o1 o2 o3 ->
  -- Coev o ->
  -- Ev o ->

  
  
              -- | Coev Object   --  right coev
              -- | Ev Object     -- right ev
              -- | PivotalJ Object -- X -> X**
              -- | PivotalJI Object -- X** -> X
              -- | Compose Morphism Morphism
    
