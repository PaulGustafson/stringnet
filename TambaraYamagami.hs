{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- Calculate R-matrix for TY(\ZZ_3, \zeta_3^{ab}, \sqrt{3})
-- For now, do everything assuming the abelian group has prime order.
--
-- References:
--
-- Daisuke Tambara, Shigeru Yamagami. Tensor Categories with Fusion
-- Rules of Self-Duality for Finite Abelian Groups
--
-- Kenichi Shimizu. Frobenius-Schur indicators in Tambara-Yamagami
-- categories.
--



module TambaraYamagami where

import Finite
import           Control.Monad.State
import TwoComplex as TC
import qualified Data.List.NonEmpty as N
import qualified Data.Matrix as M
import qualified Data.Foldable as F
import Data.Semigroup
import qualified Data.Vector        as V
import qualified Data.List          as L
import qualified Stringnet          as S
import Data.Group
import Control.Monad as CM
import Algebra
import qualified Data.Tree as T
import Tree


----------------------
-- TY specific code
----------------------

data SimpleObject =
  -- Group-element-indexed simple objects
  AE !AElement

  -- non-group simple object
  | M
                  deriving (Show,Eq)

one :: SimpleObject
one = AE $ AElement 0

allSimpleObjects = (map AE group) ++ [M]

data Object = Object
  { simples :: [SimpleObject]
  } deriving (Eq, Show)

-- -- isomorphic
-- instance Eq Object where
--   o1 == o2 = and $ zipWith (==)
--     (map (multiplicity o1) allSimpleObjects)
--     (map (multiplicity o2) allSimpleObjects)

-- instance Show Object where
--   show o = show $ map (multiplicity o) allSimpleObjects

multiplicity :: Object -> SimpleObject -> Int
multiplicity o so = length $ filter (== so) $ simples o

object :: (SimpleObject -> Int) -> Object
object f = Object $ concat $ map (\so -> replicate (f so) so) allSimpleObjects

toObject :: SimpleObject -> Object
toObject x = Object [x]
             -- object $ \y ->
             --      if x == y
             --      then 1
             --      else 0


tensorSO :: SimpleObject -> SimpleObject -> Object
tensorSO M M = groupObject
tensorSO M (AE _) = toObject M
tensorSO (AE _) M = toObject M
tensorSO (AE g1) (AE g2) = toObject $ AE $ g1 `mappend` g2


----------------------------------------------------
-- Matrices of scalars
----------------------------------------------------

data Morphism = Morphism 
  { domain   :: !Object 
  , codomain :: !Object 
  , matrix :: !(M.Matrix Scalar)
  } deriving (Eq)
  
morphism :: Object -> Object -> M.Matrix Scalar -> Morphism
morphism o1 o2 m =
  if 0 /= (length $ [ 1 | i <- [0 .. M.nrows m]
                       , j <- [0 .. M.ncols m]
                       , m M.! (i,j) /= 0
                       , (simples o1) !! i == (simples o2) !! j]
          )
  then error "Invalid morphism matrix"
  else Morphism o1 o2 m

instance Show Morphism where
  show m = show $ matrix m


scalarMorphism :: Object -> Scalar -> Morphism
scalarMorphism o scalar =
  morphism o o $ 
  M.diagonal 0 (V.replicate (length $ simples o) scalar)


idMorphism :: Object -> Morphism
idMorphism o = scalarMorphism o 1


-- projection :: Object -> Int -> Morphism
-- projection o i =
--   let
--     len = length $ summandsO $ substO $ treeLabel
--       $ initialEdgeTree $ IV Main
--   in
--     Morphism [TauMatrix  (M.diagonal 0
--                          $ V.fromList ([1] ++ replicate (len - 1) 0)) 0]

emptyMatrix :: M.Matrix Scalar
emptyMatrix = M.matrix 0 0 undefined


groupObject :: Object
groupObject = 
  object $ \so ->
      case so of
        AE _ -> 1
        M    -> 0

groupSum :: (AElement -> Scalar) -> Morphism
groupSum f =  --M.diagonal 0 $ V.generate order (f . AElement)
  morphism groupObject groupObject $ M.diagonal 0 $ V.fromList $ map f allElements


-- Turn a scalar function on A \times A into a matrix
toMatrix :: (AElement -> AElement -> Scalar) -> M.Matrix Scalar
toMatrix f = let
  f2 (x,y) =  f (AElement $ x + 1) (AElement $ y + 1)
  in
    M.matrix order order f2

-- Turn a scalar function on A \times A into a matrix
-- acting on the a direct sum of M's
toMorphism :: (AElement -> AElement -> Scalar) -> Morphism
toMorphism f = 
  let
    domain0 =
      object $ \so ->
        case so of
          AE _ -> 0
          M    -> order
  in
    morphism domain0 domain0 $ toMatrix f

directSum :: Num a => M.Matrix a -> M.Matrix a -> M.Matrix a
directSum x y = 
  let
    topRight = M.matrix (M.nrows x) (M.ncols y) $ \_ -> 0
    lowerLeft = M.matrix (M.nrows y) (M.ncols x) $ \_ -> 0
  in
     (x M.<|> topRight)
    M.<-> (lowerLeft M.<|> y)

-- instance Semigroup Morphism where
--   m1 <> m2 = m1 `directSum` m2


starSO :: SimpleObject -> SimpleObject
starSO M =  M
starSO (AE g) = AE (invert g)

star :: Object -> Object
star o = object $ (multiplicity o) . starSO 


-- -- https://en.wikipedia.org/wiki/Kronecker_product
kronecker :: (Num a) => M.Matrix a -> M.Matrix a -> M.Matrix a
kronecker f g =
  let
    m = M.nrows f
    n = M.ncols f
    p = M.nrows g
    q = M.ncols g
    shiftedMod x y =
      let z = x `mod` y in
        if z == 0
        then y
        else z
  in
    M.matrix (m*p) (n*q) $ \ij ->
    let
      i = fst ij
      j = snd ij
      v = i `shiftedMod` p 
      w = j `shiftedMod` q
      r = 1 + (i - v) `div` p
      s = 1 + (j - w) `div` q
    in
      (f M.! (r,s)) * (g M.! (v,w))


tensorInv :: SimpleObject -> [(SimpleObject, SimpleObject)]
tensorInv M = (zipWith (,) (map AE group) (repeat M))
              ++ (zipWith (,) (repeat M) (map AE group))
tensorInv (AE g0) = [(AE $ g0 `plus` g, AE $ invert g) | g <- group]
                    ++ [(M,M)]


tensorO :: Object -> Object -> Object
tensorO o1 o2 =
  Object $ concat $ [simples $ tensorSO s t | s <- simples o1, t <- simples o2]

-- Go through the direct sum of simple objects in the domain and range
-- and check if each pair is (M,M)
tensorM :: Morphism -> Morphism -> Morphism
tensorM m1 m2 =
  morphism (tensorO (domain m1) (domain m2))
  (tensorO (codomain m1) (codomain m2))
  $ kronecker (matrix m1) (matrix m2)

 
-- linearize2 :: (SimpleObject -> SimpleObject -> M.Matrix Scalar)
--   -> (Object -> Object -> M.Matrix Scalar)
-- linearize2 f o1 o2 =
--   Object [f s t |  s <- simples o1, t <- simples o2]


-- Morphism: (o1 \otimes o2) \otimes o3 \to o1 \otimes (o2 \otimes o3)
linearize3 :: (SimpleObject -> SimpleObject -> SimpleObject -> M.Matrix Scalar)
  -> (Object -> Object -> Object -> M.Matrix Scalar)
linearize3 f o1 o2 o3 = 
  foldl directSum emptyMatrix [f s t u |  s <- simples o1, t <- simples o2, u <- simples o3]


alphaSO :: SimpleObject -> SimpleObject -> SimpleObject -> Morphism
alphaSO (AE g1) (AE g2) (AE g3) = idMorphism $ toObject $ AE $ g1 `mappend` g2 `mappend` g3
alphaSO (AE _) (AE _) M = idMorphism $ toObject M
alphaSO M (AE _) (AE _) = idMorphism $ toObject M
alphaSO (AE a) M (AE b) = scalarMorphism (toObject M) (chi a b)
alphaSO (AE a) M M =
  morphism groupObject (Object (map (AE . (mappend a)) group))
  $ M.matrix order order
  $ \(i,j) -> 
      if (AElement i) `mappend` a == AElement j
      then 1
      else 0        
alphaSO M M (AE a) =
    morphism (Object $ map (AE . (mappend a)) group) groupObject
  $ M.matrix order order
  $ \(i,j) -> 
      if (AElement i)  == AElement j `mappend` a
      then 1
      else 0
alphaSO M (AE a) M = groupSum (\b -> chi a b)
alphaSO M M M =
  let
     domain0 =
      object $  \so ->
        case so of
          AE _ -> 0
          M    -> order
  in
    morphism domain0 domain0 $ toMatrix $ \x y -> tau * chiI x y

-- TODO: Double-check this
alpha :: Object -> Object -> Object -> Morphism
alpha o1 o2 o3 =
  morphism ((o1 `tensorO` o2) `tensorO` o3)
  (o1 `tensorO` (o2 `tensorO` o3))
  $ linearize3 (\so1 so2 so3 ->
                  matrix (alphaSO so1 so2 so3)
               )
  o1 o2 o3

alphaISO :: SimpleObject -> SimpleObject -> SimpleObject -> Morphism
alphaISO (AE g1) (AE g2) (AE g3) = idMorphism $ toObject $ AE $ g1 `mappend` g2 `mappend` g3
alphaISO (AE _) (AE _) M = idMorphism $ toObject M
alphaISO M (AE _) (AE _) = idMorphism $ toObject M
alphaISO (AE a) M (AE b) = scalarMorphism (toObject M) (chiI a b)
alphaISO (AE _) M M = groupSum (\_ -> 1)
alphaISO M M (AE _) = groupSum (\_ -> 1)
alphaISO M (AE a) M = groupSum (\b -> chiI a b)
alphaISO M M M =
   let
     domain0 =
      object $ \so ->
        case so of
          AE _ -> 0
          M    -> order
  in
     morphism domain0 domain0
     $ toMatrix $ \x y -> tauI * chi x y
       
    

alphaI :: Object -> Object -> Object -> Morphism
alphaI o1 o2 o3 =
  morphism
   (o1 `tensorO` (o2 `tensorO` o3))
   ((o1 `tensorO` o2) `tensorO` o3)
   $ linearize3 (\so1 so2 so3 ->
                    matrix (alphaISO so1 so2 so3))
   o1 o2 o3


-- coevSO :: SimpleObject -> Morphism
-- coevSO M =
--   Morphism
--   { domain = toObject one
--   , codomain = groupObject
--   , subMatrix = \so ->
--       if so == one
--       then M.fromLists [[1]]
--       else emptyMatrix
--   }
-- coevSO so@(AE _) = scalarMorphism so 1




coev :: Object -> Morphism
coev o =
  let codomain0 = (star o) `tensorO` o in        
    morphism
    (toObject one)
    (codomain0)
    $ M.fromLists $ L.replicate (multiplicity codomain0 one) [1]

-- ev :: SimpleObject -> Morphism
-- ev M =  Morphism
--   { domain = groupObject
--   , codomain = toObject one
--   , subMatrix = \so ->
--       if so == one
--       then M.fromLists [[tauI]]
--       else emptyMatrix
--   }
-- ev so@(AE _) = scalarMorphism so 1

ev :: Object -> Morphism
ev o =
  let
    domain0 = o `tensorO` (star o)
    mSquares = (multiplicity o M)^2
  in        
    morphism domain0 (toObject one)
    $ M.fromLists $
    [L.replicate ((multiplicity domain0 one) - mSquares) 1
     ++
     L.replicate mSquares tauI
    ]
     
    
-- pivotalJSO :: SimpleObject -> Morphism
-- pivotalJSO so = scalarMorphism so $
--   case so of
--     M -> nu
--     AE _ -> 1

pivotalJ :: Object -> Morphism
pivotalJ o =
  morphism o o $
      M.diagonal 0
      (V.fromList
       $ map (\so -> case so of
                       M -> nu
                       AE _ -> 1
             )
        $ simples o
      )       

-- pivotalJISO :: SimpleObject -> Morphism
-- pivotalJISO = pivotalJSO

pivotalJI :: Object -> Morphism
pivotalJI = pivotalJ
