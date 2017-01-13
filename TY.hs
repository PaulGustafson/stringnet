-- Definition of a Tambara-Yamagami category
-- References:
--
-- TODO: TY paper
--
-- Shlomo Gelaki, Deepak Naidu: “Centers of graded fusion categories”,
-- 2009, Algebra Number Theory 3 (2009), no. 8, 959-990; <a
-- href='http://arxiv.org/abs/0905.3117'>arXiv:0905.3117</a>

module TambaraYamagami where

import qualified Stringnet as S

data GroupElement = A Int | Product GroupElement GroupElement

data TYObject =

  -- non-group simple object
  M

  -- Group-element-indexed simple objects
  | GE GroupElement

  -- Direct sum of sums of simple objects
  | SumO TYObject TYObject

data Scalar = Tau | Chi GroupElement GroupElement

data TYMorphism =

  -- arbitary initial morphism
  Phi

  | Id TYObject

  | SumM TYMorphism TYMorphism

  | Mult Scalar TYMorphism


-- Substitute in the TY-specific morphisms
substO :: S.Object -> TYObject



-- Substitute in the TY-specific morphisms 
substM :: S.Morphism -> TYMorphism
substM m = case m of
  S.Phi -> Phi
  S.Id x -> Id $ substO x
