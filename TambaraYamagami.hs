--- Definition of a Tambara-Yamagami category
-- References:
--
-- Daisuke Tambara, Shigeru Yamagami, Tensor Categories with Fusion
-- Rules of Self-Duality for Finite Abelian Groups
--
-- Shlomo Gelaki, Deepak Naidu: “Centers of graded fusion categories”
--

module TambaraYamagami where

import qualified Stringnet as S

data GroupElement = GEVar S.InitialEdge
  | One
  | Inverse GroupElement -- use "inv" constructor
  | Product GroupElement GroupElement

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

  -- Direct sum of sums of simple objects
  | SumO Object Object

star :: Object -> Object
star (SO M) = SO M
star (SO (GE g)) = SO $ GE (inv g)
star (SumO o1 o2) = SumO (star o1) (star o2)

data Scalar = Tau
  | Chi GroupElement GroupElement
  | MultS Scalar Scalar

data Morphism =

  -- arbitary initial morphism
  Phi

  | Id Object

  | SumM Morphism Morphism

  | MultM Scalar Morphism

  -- use tensorM constructor
  | TensorM Morphism Morphism



tensorM :: Morphism -> Morphism -> Morphism
tensorM (MultM s1 m2) (MultM s2 m2) = MultM (s1 `tensorM` s2)
tensorM m1 m2 = TensorM m1 m2


validInitialLabels :: S.InitialEdge -> [SimpleObject]
validInitialLabels ie = [M, GE $ GEVar ie]

-- computes the tensor of two objects
tensorO :: Object -> Object -> Object
tensorO (SO M) _ = SO M
tensorO _ (SO M) = SO M
tensorO (SO (GE g1)) (SO (GE g2)) = SO $ GE $ Product g1 g2
tensorO (SumO o1 o2) o3 = SumO (o1 `tensorO` o3) (o2 `tensorO` o3)
tensorO o1 (SumO o2 o3) = SumO (o1 `tensorO` o2) (o1 `tensorO` o3)


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
  Alpha o1 o2 o3 -> case (substO o1) of
    SumO o11 o12 -> 
  -- AlphaI o1 o2 o3 ->
  -- Coev o ->
  -- Ev o ->

  TensorM m1 m2 -> m1 `tensorM` m2
  
              -- | Coev Object   --  right coev
              -- | Ev Object     -- right ev
              -- | PivotalJ Object -- X -> X**
              -- | PivotalJI Object -- X** -> X
              -- | Compose Morphism Morphism
    
