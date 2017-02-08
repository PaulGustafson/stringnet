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

import Data.List.NonEmpty as N
import Data.Matrix as M
import Data.Semigroup
import Data.Vector        as V
import Data.List          as L
import qualified Stringnet          as S
import Data.Group

order = 3

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
  , tauExp :: Int
  } deriving (Show, Eq)

  

coefficient :: Scalar -> RootOfUnity -> Int
coefficient (Scalar coeffs _) r =
  case r of RootOfUnity g ->
              case g of AElement i ->
                          coeffs !! i
                                        
toCoeffList :: Scalar -> [Int]
toCoeffList s =
  let domain = map RootOfUnity group in
    map (coefficient s) domain

instance Show Scalar where
  show = show . toCoeffList

instance Eq Scalar where
  s == t = (toCoeffList s) == (toCoeffList t)

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
  (Scalar xs) + (Scalar ys) = Scalar $ zipWith (+) xs ys
  (Scalar xs) * (Scalar ys) =  Scalar $ reduce $ convolve xs ys
  fromInteger x = Scalar $ [fromIntegral x] ++ (replicate (order - 1) 0)   
  negate (Scalar xs) = undefined
  signum s = undefined
  abs s = undefined


fromFunction :: (RootOfUnity -> Int) -> Scalar
fromFunction f =
  Scalar [f $ RootOfUnity $ AElement $ x | x <- [0..(order - 1)]]

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

allSimpleObjects = [M] ++ (map AE group)

data Object = Object
  { multiplicity :: SimpleObject -> Int
  } 

so :: SimpleObject -> Object
so x = \y ->
  if x == y
  then 1
  else 0


groupObject :: Object
groupObject = Object $ map AE group

-- (tau ^ tauExponent) * matrix
-- Should be a map betweeen two simple objects
data TauMatrix =  TauMatrix
  { domain :: Object
  , codomain :: Object  
  , matrix :: M.Matrix Scalar
  , tauExponent :: Sum Int
  } deriving Show

-- Matrices of scalars mappend identity maps
-- TODO: convert this to a dependent type Domain -> Codomain -> Scalar
data Morphism = Morphism 
  { domain   :: Object
  , codomain :: Object
  , 
  } deriving Show


-- TODO: newtype wrapping
instance Semigroup Morphism where
  m1 <>  m2 = Morphism $ (summandsM m1) ++ (summandsM m2)


-- toMorphism :: M.Matrix Scalar -> Morphism
-- toMorphism m = Morphism [TauMatrix m 0]

idMorphism :: Object -> Morphism
idMorphism o = Morphism
  [TauMatrix o o (M.diagonal 0 $ V.replicate (length $ summandsO o) 1) 0]


projection :: Object -> Int -> Morphism
projection o i =
  let
    len = length $ summandsO $ substO $ S.treeLabel
      $ S.initialEdgeTree $ S.IV S.Main
  in
    Morphism [TauMatrix  (M.diagonal 0
                         $ V.fromList ([1] ++ replicate (len - 1) 0)) 0]


-- scalarMorphism s = toMorphism (M.fromLists [[s]])


groupSum :: (AElement -> Scalar) -> Morphism
groupSum f =  M.diagonal 0 $ V.generate order (f . AElement)

morFromFunction :: (AElement -> AElement -> Scalar) -> Sum Int -> Morphism
morFromFunction f exp = let
  f2 (x,y) =  f (AElement $ x + 1) (AElement $ y + 1)
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
starSO (AE g) = AE (invert g)

star :: Object -> Object
star (Object sos) = Object $ map starSO sos


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

expandRows :: [Int] -> M.Matrix a -> Int -> M.Matrix a
expandRows indices m multiple =
  let list = M.toLists m in
    (take index list)
    ++ repeat multiple (list !! index)
    ++ drop index list



expandColumn :: Int -> M.Matrix a -> Int -> M.Matrix a
expandColumn index m multiple =
  transpose $ expandRow (transpose M) index multiple

-- Go through the direct sum of simple objects in the domain and range
-- and check if each pair is (M,M)
tensorM :: Morphism -> Morphism -> Morphism
tensorM (Morphism tms1) (Morphism tms2) = Morphism
  [
    let
      domPairs = [ (so1, so2) | so1 <- summandsO $ domain tm1
                              , so2 <- summandsO $ domain tm2
                              ]
      codPairs = [ (so1, so2) | so1 <- summandsO $ codomain tm1
                              , so2 <- summandsO $ codomain tm2
                              ]
    in
      TauMatrix
      { domain = (domain tm1) `tensorO` (domain tm2)
      , codomain = (codomain tm1) `tensorO` (codomain tm2)
      , matrix = (kronecker (matrix tm1) (matrix tm2))
      , tauExponent = ((tauExponent tm1) + (tauExponent tm2))

  ]
    }
  | tm1 <- tms1
  , tm2 <- tms2]


-- validInitialLabels :: S.InitialEdge -> [SimpleObject]
-- validInitialLabels ie = [M, AE $ AEVar ie]

tensorSO :: SimpleObject -> SimpleObject -> Object
tensorSO M M = Object $ map AE group
tensorSO M (AE _) = so M
tensorSO (AE _) M = so M
tensorSO (AE g1) (AE g2) = so $ AE $ g1 `mappend` g2

-- TODO: figure out how to flatten nested direct sums
-- Should be able to use the fact that they are independent sums
tensorO :: Object -> Object -> Object
tensorO (Object sos1) (Object sos2) = Object $
  concat $ map summandsO
  [ so1 `tensorSO` so2 | so1 <- sos1
                       , so2 <- sos2
  ]


------------------------------------------------------
--  Initial labels
------------------------------------------------------

-- FIXME
initialLabel :: S.InitialEdge -> Object 
initialLabel ie = -- so $ AE (AElement 0)
  case ie of
    S.LeftLoop -> so $ M
    S.RightLoop -> so $ M --AE (AElement 1)
    S.LeftLeg -> so $ M --AE (AElement 1)
    S.RightLeg -> so $ M --AE (AElement 1)

phi = projection
      (substO $ S.treeLabel $ S.initialEdgeTree $ S.IV S.Main)
      0



-- initialLabel :: S.InitialEdge -> Object 
-- initialLabel ie = 
--   case ie of
--     S.LeftLoop -> so $ AE (AElement 1)
--     S.RightLoop -> so $ AE (AElement 1)
--     S.LeftLeg -> so $ AE (AElement 1)
--     S.RightLeg -> so $ AE (AElement 1)


-- phi =  idMorphism $ substO $ S.treeLabel
--   $ S.initialEdgeTree $ S.IV S.Main



------------------------------------------------------
--  Substituting TY labels for arbitrary ones
------------------------------------------------------

      
-- Substitute in the TY-specific objects.
substO :: S.Object -> Object
substO o0 =  case o0 of
  S.OVar ie -> initialLabel ie
  S.One -> so $ AE (AElement 0)
  S.Star o -> star $ substO o
  S.TensorO o1 o2 -> (substO o1) `tensorO` (substO o2)

alpha :: SimpleObject -> SimpleObject -> SimpleObject -> Morphism
alpha (AE g1) (AE g2) (AE g3) = idMorphism $ so $ AE $ g1 `mappend` g2 `mappend` g3
alpha (AE _) (AE _) M = idMorphism $ so M
alpha M (AE _) (AE _) = idMorphism $ so M
alpha (AE a) M (AE b) = scalarMorphism (chi a b)
alpha (AE _) M M = groupSum (\_ -> 1)
alpha M M (AE _) = groupSum (\_ -> 1)
alpha M (AE a) M = groupSum (\b -> chi a b)
alpha M M M = morFromFunction (\x y -> (chiI x y)) 1


alphaI :: SimpleObject -> SimpleObject -> SimpleObject -> Morphism
alphaI (AE g1) (AE g2) (AE g3) = idMorphism $ so $ AE $ g1 `mappend` g2 `mappend` g3
alphaI (AE _) (AE _) M = idMorphism $ so M
alphaI M (AE _) (AE _) = idMorphism $ so M
alphaI (AE a) M (AE b) = scalarMorphism (chiI a b)
alphaI (AE _) M M = groupSum (\x -> 1)
alphaI M M (AE _) = groupSum (\x -> 1)
alphaI M (AE a) M = groupSum (\b -> chiI a b)
alphaI M M M = morFromFunction (\x y -> (chi x y)) (-1)

coev :: SimpleObject -> Morphism
coev M = toMorphism $ M.matrix order 1 $ \ij ->
  if ij == (1,1)
  then 1
  else 0
coev (AE _) = scalarMorphism 1

ev :: SimpleObject -> Morphism
ev M =  Morphism [TauMatrix (M.matrix 1 order $ \ij ->
  if ij == (1,1)
  then 1
  else 0)
  (-1)]
ev (AE _) = scalarMorphism 1

pivotalJ :: SimpleObject -> Morphism
pivotalJ M = scalarMorphism nu
pivotalJ (AE _) = scalarMorphism 1

pivotalJI :: SimpleObject -> Morphism
pivotalJI M = scalarMorphism nu
pivotalJI (AE _) = scalarMorphism 1


composeTM :: TauMatrix -> TauMatrix -> TauMatrix
composeTM tm1 tm2 =
  TauMatrix ((matrix tm1) * (matrix tm2))
  ((tauExponent tm1) + (tauExponent tm2))

-- FIXME
-- Assume all summands match up 
compose :: Morphism -> Morphism -> Morphism
compose (Morphism tms1) (Morphism tms2) = Morphism $
  zipWith composeTM tms1 tms2
  
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
