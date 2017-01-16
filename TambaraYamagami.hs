-- Definition of a Tambara-Yamagami category
-- References:
--
-- Daisuke Tambara, Shigeru Yamagami, Tensor Categories with Fusion
-- Rules of Self-Duality for Finite Abelian Groups
--
-- Shlomo Gelaki, Deepak Naidu: “Centers of graded fusion categories”
--

module TambaraYamagami where

import qualified Stringnet as S
import           Data.Semigroup 


data GroupElement = GEVar S.InitialEdge
  | One
  | Inverse GroupElement -- use "inv" constructor
  | Prod GroupElement GroupElement

-- TODO: Is there a Group typeclass?
-- Also, a Ring typeclass would be nice too.
inv :: GroupElement -> GroupElement
inv (Inverse g) = g
inv g = Inverse g

data SimpleObject =
  -- non-group simple object
  M

  -- Group-element-indexed simple objects
  | GE GroupElement

  | SOVar S.InitialEdge


data Object =
  SO SimpleObject

  -- $n \bigoplus_{a \in A} a$
  | GroupSum Int

  -- $n \bigoplus_{a \in A} m$
  | MSum Int

  
star :: Object -> Object
star (SO M) = SO M
star (SO (GE g)) = SO $ GE (inv g)
star (GroupSum n) = GroupSum n
star (MSum n) = MSum n

data Scalar =
  Chi GroupElement GroupElement
  | Tau
  | ChiI GroupElement GroupElement
  | MultS Scalar Scalar

data Morphism =

  -- arbitary initial morphism
  Id Object

  -- \bigoplus_b \chi(a,b) 1_b
  | CharacterSum GroupElement

  | MultM Scalar Morphism
  
  -- Dependent types could make this a lot cleaner
  -- number of copies of the group in the direct sum
  | Matrix Int [[Scalar]]


tensorM :: Morphism -> Morphism -> Morphism
tensorM (MultM s1 m1) (MultM s2 m2) = (s1 `MultS` s2) `MultM` (m1 `tensorM` m2)
tensorM (Id _ ) x = x --   


validInitialLabels :: S.InitialEdge -> [SimpleObject]
validInitialLabels ie = [M, GE $ GEVar ie]

-- instance Semigroup Object where
--   x <> y = x `SumO` y

-- instance Semigroup Morphism where
--   x <> y = x `SumM` y

-- --TODO: change types and export this method
-- --      typeclasses: AdditivelyGenerated and Summable
-- linearize :: Semigroup b => (SimpleObject -> b)
--                          -> (Object -> b)
-- linearize f (SumO o1 o2) = (linearize f o1) <> (linearize f o2)
-- linearize f (SO so) = f so

-- linearize2 :: Semigroup b => (a -> SimpleObject -> b)
--                          -> (a -> Object -> b)
-- linearize2 f x (SumO o1 o2) = (linearize2 f x o1) <> (linearize2 f x o2)
-- linearize2 f x (SO so) = f x so

tensorOH :: SimpleObject -> SimpleObject -> Object
tensorOH M _ = SO M
tensorOH _ M = SO M
tensorOH (GE g1) (GE g2) = SO $ GE $ Product g1 g2

-- computes the tensor of two objects
tensorO :: Object -> Object -> Object
tensorO  =  linearize $ linearize2 tensorOH 



-- Substitute in the TY-specific morphisms
substO :: S.Object -> Object
substO o0 =  case o0 of
  S.OVar ie -> SO $ SOVar ie
  S.One -> SO $ GE One
  S.Star o -> star $ substO o
  S.TensorO o1 o2 -> (substO o1) `tensorO` (substO o2)

                         
-- Substitute in the TY-specific morphisms 
substM :: S.Morphism -> Morphism
substM m = case m of
  S.Phi -> Phi
  S.Id o -> Id $ substO o
  S.Lambda o -> Id $ substO o
  S.LambdaI o -> Id $ substO o
  S.Rho o -> Id $ substO o
  S.RhoI o -> Id $ substO o
  -- TODO: figure out how to automate linearity
  let 
    alpha (GE g1) (GE g2) (GE g3) = Id $ SO $ GE $ g1 `Prod` g2 `Prod` g3
    alpha (GE _) (GE _) M = Id $ SO M
    alpha M (GE _) (GE _) = Id $ SO M
    alpha (GE a) M (GE b) = (Chi a b) `MultM` Id $ SO M
    alpha (GE _) M M =  GroupSum $ 
    

  -- Alpha o1 o2 o3 -> case (substO o1) of
  --   SumO o11 o12
  -- --
  -- AlphaI o1 o2 o3 ->
  -- Coev o ->
  -- Ev o ->

  TensorM m1 m2 -> m1 `tensorM` m2
  
              -- | Coev Object   --  right coev
              -- | Ev Object     -- right ev
              -- | PivotalJ Object -- X -> X**
              -- | PivotalJI Object -- X** -> X
              -- | Compose Morphism Morphism
    
