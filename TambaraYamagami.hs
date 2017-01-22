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
-- TODO: write unit tests for important methods
--
--
-- TODO: implement simple reductions for scalars,
-- e.g. \sum_{i=0}^{p-1} \zeta^i = 0
--



module TambaraYamagami where

import qualified Data.List.NonEmpty as N
import qualified Data.Matrix as M
import           Data.Semigroup
import qualified Data.Vector        as V
import qualified Data.List          as L
import qualified Stringnet          as S
import Data.Group

order = 3

-- \pm 1
nu = 1

-- group element, assuming cyclicity
-- dependent types would be nice here
data GroupElement = GroupElement Int deriving (Show)

instance Eq GroupElement where
  (GroupElement a) == (GroupElement b) = (a `mod` order) == (b `mod` order)

instance Monoid GroupElement where
  (GroupElement e1) `mappend` (GroupElement e2) = GroupElement $ (e1 + e2) `mod` order
  mempty = GroupElement 0
    
instance Group GroupElement where
  invert (GroupElement e) = GroupElement  $ (-e) `mod` order

-- carrier set for the group
group :: [GroupElement]
group = Prelude.map GroupElement [0..(order - 1)]

plus :: GroupElement -> GroupElement -> GroupElement
plus = mappend


newtype RootOfUnity = RootOfUnity GroupElement deriving (Eq, Monoid, Group)

-- A scalar is an algebraic integer over the cyclotomic field corresponding
-- to the order of the group.
data Scalar =  Scalar {
  coefficient :: RootOfUnity -> Int
  }


toCoeffList :: Scalar -> [Int]
toCoeffList (Scalar coeff) =
  let domain = map RootOfUnity group in
    map coeff domain

instance Show Scalar where
  show = show . toCoeffList

instance Eq Scalar where
  s == t = (toCoeffList s) == (toCoeffList t)

-- http://mathworld.wolfram.com/GroupConvolution.html
convolve :: Num c =>  (RootOfUnity -> c) -> (RootOfUnity -> c) -> (RootOfUnity -> c)
convolve a b = \g -> sum $ map (\k -> (a k)*(b $ (invert k) `mappend` g)) $ map RootOfUnity group
  

instance Num Scalar where
  s + t = Scalar $ \x -> (coefficient s x) + (coefficient t x)
  negate s = Scalar $ \x -> coefficient s (invert x)
  s * t =  Scalar $ convolve (coefficient s) (coefficient t)
  fromInteger x = Scalar $ \r ->
    if r == (RootOfUnity $ GroupElement 0)
    then fromIntegral x
    else 0
  signum s = undefined
  abs s = undefined



fromBag :: [RootOfUnity] -> Scalar
fromBag rs = Scalar $ \r ->
  length $ L.elemIndices r rs


fromRootOfUnity :: RootOfUnity -> Scalar
fromRootOfUnity x = Scalar $ \y ->
  if y == x
  then 1
  else 0

-- Quadratic gauss sum
-- Currently only works if order = 1 (mod 4)
-- tauI :: Scalar
-- tauI =  nu * fromBag [RootOfUnity $ GroupElement (n^2) | n <- [0..(order - 1)]]



chi :: GroupElement -> GroupElement -> Scalar
chi (GroupElement e1) (GroupElement e2) = fromRootOfUnity $ RootOfUnity $ GroupElement $ (e1*e2) `mod` order

chiI :: GroupElement -> GroupElement -> Scalar
chiI (GroupElement e1) (GroupElement e2) = fromRootOfUnity $ RootOfUnity $ GroupElement $ (-e1*e2) `mod` order


data SimpleObject =
  -- non-group simple object
  M

  -- Group-element-indexed simple objects
  | GE GroupElement
                  deriving (Show,Eq)


data Object = SumO {
  summandsO :: [SimpleObject]
  } deriving (Show)

so :: SimpleObject -> Object
so x = SumO [x]

-- (tau ^ tauExponent) * matrix
data TauMatrix =  TauMatrix
  { matrix :: M.Matrix Scalar
  , tauExponent :: Sum Int
  } deriving Show

-- Matrices of scalars mappend identity maps
-- TODO: convert this to a dependent type Domain -> Codomain -> Scalar
data Morphism = Morphism {
  summandsM :: [(TauMatrix)]
  } deriving Show

instance Semigroup Morphism where
  m1 <>  m2 = Morphism $ (summandsM m1) ++ (summandsM m2)


toMorphism :: M.Matrix Scalar -> Morphism
toMorphism m = Morphism [TauMatrix m 0]

idMorphism :: Object -> Morphism
idMorphism o = Morphism [TauMatrix (M.diagonal 0 $ V.replicate (length $ summandsO o) 1) 0]


scalarMorphism s = toMorphism (M.fromLists [[s]])


groupSum :: (GroupElement -> Scalar) -> Morphism
groupSum f = toMorphism $ M.diagonal 0 $ V.generate order (f . GroupElement)

fromFunction :: (GroupElement -> GroupElement -> Scalar) -> Sum Int -> Morphism
fromFunction f exp = let
  f2 (x,y) =  f (GroupElement $ x + 1) (GroupElement $ y + 1)
  in
    Morphism [TauMatrix (M.matrix order order f2) exp]


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
starSO (GE g) = GE (invert g)

star :: Object -> Object
star (SumO sos) = SumO $ map starSO sos


-- https://en.wikipedia.org/wiki/Kronecker_product
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


tensorM :: Morphism -> Morphism -> Morphism
tensorM (Morphism tms1) (Morphism tms2) = Morphism
  [TauMatrix (kronecker (matrix tm1) (matrix tm2))
   ((tauExponent tm1) + (tauExponent tm2))
  | tm1 <- tms1
  , tm2 <- tms2]


-- validInitialLabels :: S.InitialEdge -> [SimpleObject]
-- validInitialLabels ie = [M, GE $ GEVar ie]

tensorSO :: SimpleObject -> SimpleObject -> Object
tensorSO M M = SumO $ map GE group
tensorSO M (GE _) = so M
tensorSO (GE _) M = so M
tensorSO (GE g1) (GE g2) = so $ GE $ g1 `mappend` g2

--TODO: figure out how to flatten nested direct sums
-- Should be able to use the fact that they are independent sums
tensorO :: Object -> Object -> Object
tensorO (SumO sos1) (SumO sos2) = SumO $
  concat $ map summandsO
  [ so1 `tensorSO` so2 | so1 <- sos1
                       , so2 <- sos2
  ]

-- FIXME
initialLabel :: S.InitialEdge -> Object
initialLabel ie = so $ GE (GroupElement 0)

-- Substitute in the TY-specific objects.
substO :: S.Object -> Object
substO o0 =  case o0 of
  S.OVar ie -> initialLabel ie
  S.One -> so $ GE (GroupElement 0)
  S.Star o -> star $ substO o
  S.TensorO o1 o2 -> (substO o1) `tensorO` (substO o2)

alpha :: SimpleObject -> SimpleObject -> SimpleObject -> Morphism
alpha (GE g1) (GE g2) (GE g3) = idMorphism $ so $ GE $ g1 `mappend` g2 `mappend` g3
alpha (GE _) (GE _) M = idMorphism $ so M
alpha M (GE _) (GE _) = idMorphism $ so M
alpha (GE a) M (GE b) = scalarMorphism (chi a b)
alpha (GE _) M M = groupSum (\_ -> 1)
alpha M M (GE _) = groupSum (\_ -> 1)
alpha M (GE a) M = groupSum (\b -> chi a b)
alpha M M M = fromFunction (\x y -> (chiI x y)) 1


alphaI :: SimpleObject -> SimpleObject -> SimpleObject -> Morphism
alphaI (GE g1) (GE g2) (GE g3) = idMorphism $ so $ GE $ g1 `mappend` g2 `mappend` g3
alphaI (GE _) (GE _) M = idMorphism $ so M
alphaI M (GE _) (GE _) = idMorphism $ so M
alphaI (GE a) M (GE b) = scalarMorphism (chiI a b)
alphaI (GE _) M M = groupSum (\x -> 1)
alphaI M M (GE _) = groupSum (\x -> 1)
alphaI M (GE a) M = groupSum (\b -> chiI a b)
alphaI M M M = fromFunction (\x y -> (chi x y)) (-1)

coev :: SimpleObject -> Morphism
coev M = toMorphism $ M.matrix 1 order $ \ij ->
  if ij == (1,1)
  then 1
  else 0
coev (GE _) = scalarMorphism 1

ev :: SimpleObject -> Morphism
ev M =  Morphism [TauMatrix (M.matrix order 1 $ \ij ->
  if ij == (1,1)
  then 1
  else 0)
  (-1)]
ev (GE _) = scalarMorphism 1

pivotalJ :: SimpleObject -> Morphism
pivotalJ M = scalarMorphism nu
pivotalJ (GE _) = scalarMorphism 1

pivotalJI :: SimpleObject -> Morphism
pivotalJI M = scalarMorphism nu
pivotalJI (GE _) = scalarMorphism 1

composeTM :: TauMatrix -> TauMatrix -> TauMatrix
composeTM tm1 tm2 =
  TauMatrix ((matrix tm1) * (matrix tm2))
  ((tauExponent tm1) + (tauExponent tm2))

-- Assume all summands match up 
compose :: Morphism -> Morphism -> Morphism
compose (Morphism tms1) (Morphism tms2) = Morphism $
  zipWith composeTM tms1 tms2
  
-- TODO: Figure out where the program is hanging
-- Substitute in the TY-specific morphisms
substM :: S.Morphism -> Morphism
substM m = case m of
  S.Phi -> idMorphism $ substO $ S.treeLabel
           $ S.initialEdgeTree $ S.IV S.Main
  S.Id o -> idMorphism $ substO o
  S.Lambda o -> idMorphism $ substO o
  S.LambdaI o -> idMorphism $ substO o
  S.Rho o -> idMorphism $ substO o
  S.RhoI o -> idMorphism $ substO o
  S.TensorM m1 m2 -> (substM m1) `tensorM` (substM m2)
  S.Alpha o1 o2 o3 ->
    sconcat $ N.fromList
    [alpha x y z | x <- summandsO $ substO o1
                 , y <- summandsO $ substO o2
                 , z <- summandsO $ substO o3]
  S.AlphaI o1 o2 o3 ->
    sconcat $ N.fromList
    [alphaI x y z | x <- summandsO $ substO o1
                  , y <- summandsO $ substO o2
                  , z <- summandsO $ substO o3]
  S.Coev o -> sconcat $ N.fromList $ map coev $ summandsO $ substO o
  S.Ev   o -> sconcat $ N.fromList $ map   ev $ summandsO $ substO o
  S.PivotalJ  o -> sconcat $ N.fromList $ map pivotalJ  $ summandsO $ substO o
  S.PivotalJI o -> sconcat $ N.fromList $ map pivotalJI $ summandsO $ substO o
  S.Compose m1 m2 -> compose (substM m1) (substM m2)
