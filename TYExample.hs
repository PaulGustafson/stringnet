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

-- group element 
data Element = Element Int

one :: Element
one = Element 0

inv :: Element -> Element
inv (Element e) = Element  $ (-e) `mod` order

plus :: Element -> Element -> Element
(Element e1) `plus` (Element e2) = Element $ (e1 + e2) `mod` order

data Scalar = Tau
  | SElement Element
  | MultS Scalar Scalar

chi :: Element -> Element -> Scalar
chi (Element e1) (Element e2) = SElement $ Element $ (e1*e2) `mod` order

chiI :: Element -> Element -> Scalar
chiI (Element e1) (Element e2) = SElement $ Element $ (-e1*e2) `mod` order

-- \pm (order)^{-1/2}
data Tau = Plus | Minus


data SimpleObject =
  -- non-group simple object
  M

  -- Group-element-indexed simple objects
  | GE Element


data Object =
  SO SimpleObject

  | SumO Object Object


data IndexSet = A | ProdI IndexSet IndexSet

data Morphism =

  -- arbitary initial morphism
  Phi

  | Id Object

  | SumM Morphism Morphism

  | MultM Scalar Morphism

  -- the Int n describes the domain A^n
  | Matrix Int [[Scalar]]

-- TODO: Consider using wrapper types here to reduce the cognitive
-- overhead of remembering with the monoid structure is with respect
-- to sum, tensor, or composition.
instance Semigroup Object where
  x <> y = x `SumO` y

instance Semigroup Morphism where
  x <> y = x `SumM` y


linearize :: Semigroup b => (SimpleObject -> b)
                         -> (Object -> b)
linearize f (SumO o1 o2) = (linearize f o1) <> (linearize f o2)
linearize f (SO so) = f so

linearize2 :: Semigroup b => (a -> SimpleObject -> b)
                         -> (a -> Object -> b)
linearize2 f x (SumO o1 o2) = (linearize2 f x o1) <> (linearize2 f x o2)
linearize2 f x (SO so) = f x so

elements :: NonEmpty Element
elements = N.map Element $ fromList [0..(order - 1)]

groupSum :: Semigroup a => (Element -> a) -> a
groupSum f = sconcat $ N.map f elements 

starSO :: SimpleObject -> SimpleObject
starSO M =  M
starSO (GE g) = GE (inv g)

star :: Object -> Object
star = linearize (SO . starSO)

tensorM :: Morphism -> Morphism -> Morphism
tensorM (MultM s1 m1) (MultM s2 m2) = (s1 `MultS` s2) `MultM` (m1 `tensorM` m2)
tensorM (Id _) m2 = 

-- validInitialLabels :: S.InitialEdge -> [SimpleObject]
-- validInitialLabels ie = [M, GE $ GEVar ie]

tensorSO :: SimpleObject -> SimpleObject -> Object
tensorSO M _ = SO M
tensorSO _ M = SO M
tensorSO (GE g1) (GE g2) = SO $ GE $ g1 `plus` g2

-- computes the tensor of two objects
tensorO :: Object -> Object -> Object
tensorO  =  linearize $ linearize2 tensorSO

-- TODO: un-hardcode initial edge labels
-- Substitute in the TY-specific objects. 
substO :: S.Object -> Object
substO o0 =  case o0 of
  S.One -> SO $ GE one
  S.Star o -> star $ substO o
  S.TensorO o1 o2 -> (substO o1) `tensorO` (substO o2)

alpha :: SimpleObject -> SimpleObject -> SimpleObject -> Morphism
alpha (GE g1) (GE g2) (GE g3) = Id $ SO $ GE $ g1 `plus` g2 `plus` g3
alpha (GE _) (GE _) M = Id $ SO M
alpha M (GE _) (GE _) = Id $ SO M
alpha (GE a) M (GE b) = (chi a b) `MultM` (Id $ SO M)
alpha (GE _) M M = groupSum (Id . SO . GE)
alpha M M (GE _) = groupSum (Id . SO . GE)
alpha M (GE a) M =  (\b -> (chi a b) `MultM` ((Id . SO . GE) b))
alpha M M M =
  Matrix [[Tau `MultM` (chiI a b) `MultM` (Id $ SO M) |
           a <- elements] |
           b <- elements]
                                                     
           
                     
-- Substitute in the TY-specific morphisms 
substM :: S.Morphism -> Morphism
substM m = case m of
  S.Phi -> Phi
  S.Id o -> Id $ substO o
  S.Lambda o -> Id $ substO o
  S.LambdaI o -> Id $ substO o
  S.Rho o -> Id $ substO o
  S.RhoI o -> Id $ substO o
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
    
