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
-- FIXME: Change Scalar class to include tau exponent
--        Objects should be represented by multiplicity lists
--        so that they are represented uniquely.
--        Morphisms should be maps of indexed objects
--
-- TODO: write unit tests for important methods
--
-- TODO: implement simple reductions for scalars,
-- e.g. \sum_{i=0}^{p-1} \zeta^i = 0
--



module TambaraYamagami where

import qualified Data.List.NonEmpty as N
import qualified Data.Matrix as M
import Data.Semigroup
import qualified Data.Vector        as V
import qualified Data.List          as L
import qualified Stringnet          as S
import Data.Group

order = 2

-- \pm 1
nu = 1

-- group element, assuming cyclicity
-- dependent types would be nice here
newtype AElement = AElement Int deriving (Show)

instance Eq AElement where
  (AElement a) == (AElement b) = (a `mod` order) == (b `mod` order)

instance Monoid AElement where
  (AElement e1) `mappend` (AElement e2) = AElement $ (e1 + e2) `mod` order
  mempty = AElement 0
    
instance Group AElement where
  invert (AElement e) = AElement  $ (-e) `mod` order

-- carrier set for the group
group :: [AElement]
group = Prelude.map AElement [0..(order - 1)]

plus :: AElement -> AElement -> AElement
plus = mappend


newtype RootOfUnity = RootOfUnity AElement deriving (Eq, Monoid, Group)

-- A scalar is an algebraic integer over the cyclotomic field corresponding
-- to the order of the group.
data Scalar =  Scalar 
  { coeff :: [Int]
  , tauExp :: Sum Int
  } deriving (Show, Eq)

tau :: Scalar
tau =
  Scalar
  { coeff = [1] ++ replicate (order - 1) 0
  , tauExp = 1
  }


tauI :: Scalar
tauI =
  Scalar
  { coeff = [1] ++ replicate (order - 1) 0
  , tauExp = -1
  }


-- http://mathworld.wolfram.com/GroupConvolution.html
-- convolve :: Num c =>  (RootOfUnity -> c) -> (RootOfUnity -> c) -> (RootOfUnity -> c)
-- convolve a b = \g -> sum $ map (\k -> (a k)*(b $ (invert k) `mappend` g)) $ map RootOfUnity group

-- Source: https://www.blaenkdenum.com/posts/naive-convolution-in-haskell/
convolve :: (Num a) => [a] -> [a] -> [a]
convolve hs xs =
  let pad = replicate ((length hs) - 1) 0
      ts  = pad ++ xs
  in map (sum . zipWith (*) (reverse hs)) (init $ L.tails ts)

-- Use the fact that \zeta^n = 1
reduce :: [Int] -> [Int]
reduce xs =
  if length xs < order
  then xs ++ replicate (order - length xs) 0
  else zipWith (+) (take order xs) (reduce $ drop order xs)
                                          
instance Num Scalar where
  s1 + s2 = 
    if tauExp s1 == tauExp s2
    then Scalar {
      coeff = zipWith (+) (coeff s1) (coeff s2)
      , tauExp = tauExp s1
      }
    else error "Can't add; tauExponents don't match."
  s1 * s2 =  Scalar {
    coeff = reduce $ convolve (coeff s1) (coeff s2)
    , tauExp = (tauExp s1) + (tauExp s2)
    }
  fromInteger x = Scalar {
    coeff = [fromIntegral x] ++ (replicate (order - 1) 0)
    , tauExp = 0
    }
  negate _ = undefined
  signum s = undefined
  abs s = undefined


fromFunction :: (RootOfUnity -> Int) -> Scalar
fromFunction f =
  Scalar [f $ RootOfUnity $ AElement $ x | x <- [0..(order - 1)]] 0

fromBag :: [RootOfUnity] -> Scalar
fromBag rs = fromFunction $ \r ->
  length $ L.elemIndices r rs


fromRootOfUnity :: RootOfUnity -> Scalar
fromRootOfUnity x = fromFunction $ \y ->
  if y == x
  then 1
  else 0

-- Quadratic gauss sum
-- Currently only works if order = 1 (mod 4)
-- tauI :: Scalar
-- tauI =  nu * fromBag [RootOfUnity $ AElement (n^2) | n <- [0..(order - 1)]]


chi :: AElement -> AElement -> Scalar
chi (AElement e1) (AElement e2) = fromRootOfUnity $ RootOfUnity $ AElement $ (e1*e2) `mod` order

chiI :: AElement -> AElement -> Scalar
chiI (AElement e1) (AElement e2) = fromRootOfUnity $ RootOfUnity $ AElement $ (-e1*e2) `mod` order

data SimpleObject =
  -- non-group simple object
  M

  -- Group-element-indexed simple objects
  | AE AElement
                  deriving (Show,Eq)

one :: SimpleObject
one = AE $ AElement 0

allSimpleObjects = [M] ++ (map AE group)

data Object = Object
  { multiplicity :: SimpleObject -> Int
  }

toObject :: SimpleObject -> Object
toObject x = Object { multiplicity = \y ->
                  if x == y
                  then 1
                  else 0
              }


groupObject :: Object
groupObject = Object $ \_ -> 1

-- Matrices of scalars 
data Morphism = Morphism 
  { domain   :: Object
  , codomain :: Object
  
  -- the only morphisms between simple objects are identity morphisms
  , subMatrix :: SimpleObject -> M.Matrix Scalar
  } 


idMorphism :: Object -> Morphism
idMorphism o@(Object multiplicity) =
  Morphism
  { domain = o
  , codomain = o
  , subMatrix = \so ->
      M.diagonal 0 (V.replicate (multiplicity so) 1)      
  }


-- projection :: Object -> Int -> Morphism
-- projection o i =
--   let
--     len = length $ summandsO $ substO $ S.treeLabel
--       $ S.initialEdgeTree $ S.IV S.Main
--   in
--     Morphism [TauMatrix  (M.diagonal 0
--                          $ V.fromList ([1] ++ replicate (len - 1) 0)) 0]

emptyMatrix = M.Matrix 0 0 undefined

scalarMorphism :: SimpleObject -> Scalar -> Morphism
scalarMorphism domain0 scalar =
  Morphism
  { domain = domain0
  , codomain = domain0
  , subMatrix = \so ->
      if so == domain0
      then M.fromLists [[scalar]]
      else emptyMatrix
  }

groupObject :: Object
groupObject =
  Object
  { multiplicity = \so ->
      case so of
        AE _ -> 1
        M    -> 0
  }

groupSum :: (AElement -> Scalar) -> Morphism
groupSum f =  --M.diagonal 0 $ V.generate order (f . AElement)
  Morphism
  { domain = groupObject
  , codomain = groupObject
  , subMatrix = \so ->
      case so of
        AE g -> M.fromLists [[f g]]
        M    -> emptyMatrix
  }

-- Turn a scalar function on A \times A into a matrix
toMatrix :: (AElement -> AElement -> Scalar) -> M.Matrix
toMatrix f exp = let
  f2 (x,y) =  f (AElement $ x + 1) (AElement $ y + 1)
  in
    M.matrix order order f2

-- Turn a scalar function on A \times A into a matrix
-- acting on the a direct sum of M's
toMorphism :: (AElement -> AElement -> Scalar) -> Morphism
toMorphism f = 
  let
    domain0 =
      Object
      { multiplicity = \so ->
        case so of
          AE _ -> 0
          M    -> order
      }
  in
    Morphism
    { domain = domain0
    , codomain = domain0
    , subMatrix = \so ->
        case so of
          M ->  toMatrix f
          AE _ -> emptyMatrix
    }

-- directSum :: Num a => M.Matrix a -> M.Matrix a -> M.Matrix a
-- directSum x y = 
--   let
--     topRight = M.matrix (M.nrows x) (M.ncols y) $ \_ -> 0
--     lowerLeft = M.matrix (M.nrows y) (M.ncols x) $ \_ -> 0
--   in
--      (x M.<|> topRight)
--     M.<-> (lowerLeft M.<|> y)

-- -- instance Semigroup Morphism where
-- --   m1 <> m2 = m1 `directSum` m2


starSO :: SimpleObject -> SimpleObject
starSO M =  M
starSO (AE g) = AE (invert g)

star :: Object -> Object
star o = Object { multiplicity = (multiplicity o) . starSO }


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

-- expandRows :: [Int] -> M.Matrix a -> Int -> M.Matrix a
-- expandRows indices m multiple =
--   let list = M.toLists m in
--     (take index list)
--     ++ repeat multiple (list !! index)
--     ++ drop index list


-- expandColumn :: Int -> M.Matrix a -> Int -> M.Matrix a
-- expandColumn index m multiple =
--   transpose $ expandRow (transpose M) index multiple

-- tensorSO :: SimpleObject -> SimpleObject -> Object
-- tensorSO M M = Object $ map AE group
-- tensorSO M (AE _) = toObject M
-- tensorSO (AE _) M = toObject M
-- tensorSO (AE g1) (AE g2) = toObject $ AE $ g1 `mappend` g2


-- Coefficient of so in the product
tensorHelper :: (Num a) =>  (SimpleObject -> SimpleObject -> a)  -> SimpleObject -> a
tensorHelper prod so = 
  case so of
    M -> sum $
         (map (\ae -> prod M (AE ae)) group)
         ++ (map (\ae -> prod (AE ae) M) group)
    AE ae -> sum $
      [prod (AE ae1) (AE ae2) |
        ae1 <- group,
        ae2 <- group,
        ae1 `plus` ae2 == ae]
      ++ [prod M M]


-- TODO: Double check that this really works
tensorO :: Object -> Object -> Object
tensorO o1 o2 = Object {
    multiplicity =
     let prod a b = (multiplicity o1 a) * (multiplicity o2 b) in
       tensorHelper prod
  }



-- Go through the direct sum of simple objects in the domain and range
-- and check if each pair is (M,M)
tensorM :: Morphism -> Morphism -> Morphism
tensorM m1 m2 =
  Morphism 
  { domain = tensorO (domain m1) (domain m2)
  , codomain = tensorO (codomain m1) (codomain m2)
  , subMatrix = 
      let kron so1 so2 = kronecker (subMatrix m1 so1) (subMatrix m2 so2)
      in
        tensorHelper kron
  }


-- -- validInitialLabels :: S.InitialEdge -> [SimpleObject]
-- -- validInitialLabels ie = [M, AE $ AEVar ie]



-- ------------------------------------------------------
-- --  Initial labels
-- ------------------------------------------------------

-- -- FIXME
-- initialLabel :: S.InitialEdge -> Object 
-- initialLabel ie = -- toObject $ AE (AElement 0)
--   case ie of
--     S.LeftLoop -> toObject $ M
--     S.RightLoop -> toObject $ M --AE (AElement 1)
--     S.LeftLeg -> toObject $ M --AE (AElement 1)
--     S.RightLeg -> toObject $ M --AE (AElement 1)

-- phi = projection
--       (substO $ S.treeLabel $ S.initialEdgeTree $ S.IV S.Main)
--       0



initialLabel :: S.InitialEdge -> Object 
initialLabel ie = 
  case ie of
    S.LeftLoop -> toObject $ AE (AElement 1)
    S.RightLoop -> toObject $ AE (AElement 1)
    S.LeftLeg -> toObject $ AE (AElement 1)
    S.RightLeg -> toObject $ AE (AElement 1)


phi =  idMorphism $ substO $ S.treeLabel
  $ S.initialEdgeTree $ S.IV S.Main



-- ------------------------------------------------------
-- --  Substituting TY labels for arbitrary ones
-- ------------------------------------------------------

      
-- Substitute in the TY-specific objects.
substO :: S.Object -> Object
substO o0 =  case o0 of
  S.OVar ie -> initialLabel ie
  S.One -> toObject $ AE (AElement 0)
  S.Star o -> star $ substO o
  S.TensorO o1 o2 -> (substO o1) `tensorO` (substO o2)




alpha2 :: Object -> Object -> Object -> Morphism
alpha2 f o1 o2 o3 =
  Morphism
  { domain = (o1 `tensorO` o2) `tensorO` o3
  , codomain =  o1 `tensorO` (o2 `tensorO` o3)
  , subMatrix = \so ->
      --FIXME
  }
    

alpha :: SimpleObject -> SimpleObject -> SimpleObject -> Morphism
alpha (AE g1) (AE g2) (AE g3) = idMorphism $ toObject $ AE $ g1 `mappend` g2 `mappend` g3
alpha (AE _) (AE _) M = idMorphism $ toObject M
alpha M (AE _) (AE _) = idMorphism $ toObject M
alpha (AE a) M (AE b) = scalarMorphism (chi a b)
alpha (AE _) M M = groupSum (\_ -> 1)
alpha M M (AE _) = groupSum (\_ -> 1)
alpha M (AE a) M = groupSum (\b -> chi a b)
alpha M M M =
  let
    domain0 =
      Object
      { multiplicity = \so ->
        case so of
          AE _ -> 0
          M    -> order
      }
  in
    Morphism
    { domain = domain0
    , codomain = domain0
    , subMatrix = \so ->
        case so of
          M ->  toMatrix (tau * chiI)
          AE _ -> emptyMatrix
    }


alphaI :: SimpleObject -> SimpleObject -> SimpleObject -> Morphism
alphaI (AE g1) (AE g2) (AE g3) = idMorphism $ toObject $ AE $ g1 `mappend` g2 `mappend` g3
alphaI (AE _) (AE _) M = idMorphism $ toObject M
alphaI M (AE _) (AE _) = idMorphism $ toObject M
alphaI (AE a) M (AE b) = scalarMorphism (chiI a b)
alphaI (AE _) M M = groupSum (\x -> 1)
alphaI M M (AE _) = groupSum (\x -> 1)
alphaI M (AE a) M = groupSum (\b -> chiI a b)
alphaI M M M = toMatrix (\x y -> tauI * (chi x y))

coev :: SimpleObject -> Morphism
coev M =
  Morphism
  { domain = toObject one
  , codomain = groupObject
  , subMatrix = \so ->
      if so == one
      then M.fromLists [[1]]
      else emptyMatrix
}
coev so@(AE _) = scalarMorphism so 1

ev :: SimpleObject -> Morphism
ev M =  Morphism
  { domain = groupObject
  , codomain = toObject one
  , subMatrix = \so ->
      if so == one
      then M.fromLists [[tauI]]
      else emptyMatrix
  }
ev so@(AE _) = scalarMorphism so 1

pivotalJ :: SimpleObject -> Morphism
pivotalJ so = scalarMorphism so $
  case so of
    M -> nu
    AE _ -> 1

pivotalJI :: SimpleObject -> Morphism
pivotalJI = pivotalJ

-- standard (nondiagrammatic) order 
compose :: Morphism -> Morphism -> Morphism
compose m1 m2 =
  Morphism
  { domain = domain m2
  , codomain = codomain m1
  , subMatrix = \so ->
      (subMatrix m1 so) * (subMatrix m2 so)
  } 

    
-- Substitute in the TY-specific morphisms
substM :: S.Morphism -> Morphism
substM m = case m of
  S.Phi -> phi
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


-- -- Debugging strategies
-- -- 
-- -- 1. finalMorphism (Look at subtrees)
-- --
-- -- 2. Look at TY code for error
-- -- (Direct sum stuff).  In particular, add conceptual types to wrap
-- -- around the computational types (i.e. SimpleObject functions to wrap
-- -- around the matrices)
