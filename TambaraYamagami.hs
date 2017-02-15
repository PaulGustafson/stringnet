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
-- TODO: Write unit tests for important methods.
--
-- TODO: Write Num instances.
--
-- TODO: Dehackify ev method.
--
-- TODO: Implement simple reductions for scalars,
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
import Control.Monad as CM

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
  { coeff :: ![Int]
  , tauExp :: !(Sum Int)
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
  -- Group-element-indexed simple objects
  AE !AElement

  -- non-group simple object
  | M
                  deriving (Show,Eq)

one :: SimpleObject
one = AE $ AElement 0

allSimpleObjects = (map AE group) ++ [M]

newtype Object = Object
  { multiplicity :: SimpleObject -> Int
  }

-- Modularize constructor for testing different object implementations
funToObject :: (SimpleObject -> Int) -> Object
funToObject f = Object f


instance Eq Object where
  o1 == o2 = and $ zipWith (==)
    (map (multiplicity o1) allSimpleObjects)
    (map (multiplicity o2) allSimpleObjects)

instance Show Object where
  show o = show $ map (multiplicity o) allSimpleObjects

-- TODO: fix this
-- instance Num Object where
--   o1 + o2 = Object $ multiplicity o1 + multiplicity o2
--   o1 * o2 = o1 `tensorO` o2
--   fromInteger = undefined -- could change
--   negate _ = undefined
--   signum _ = undefined
--   abs _ = undefined

toObject :: SimpleObject -> Object
toObject x = Object { multiplicity = \y ->
                  if x == y
                  then 1
                  else 0
              }


-- Matrices of scalars 
data Morphism = Morphism 
  { domain   :: !Object
  , codomain :: !Object
  
  -- the only morphisms between simple objects are identity morphisms
  , subMatrix :: !(SimpleObject -> M.Matrix Scalar)
  }

instance Show Morphism where
  show m = show $ map (subMatrix m) allSimpleObjects

  

-- instance Num Morphism where
--   m1 + m2 =
--     Morphism
--     { domain = if (domain m1) ==  (domain m2)
--                then domain m1
--                else undefined
--     , codomain = if (codomain m1) == (codomain m2)
--                  then codomain m1
--                  else undefined
--     , subMatrix = (subMatrix m1) + (subMatrix m2)
--     }
--   m1 * m2 = m1 `tensorM` m2
--   fromInteger _ = undefined
--   negate _ = undefined
--   signum _ = undefined
--   abs _ = undefined


scalarMorphism :: Object -> Scalar -> Morphism
scalarMorphism o scalar =
  Morphism
  { domain = o
  , codomain = o
  , subMatrix = \so ->
      M.diagonal 0 (V.replicate (multiplicity o so) scalar)      
  }


idMorphism :: Object -> Morphism
idMorphism o = scalarMorphism o 1


-- projection :: Object -> Int -> Morphism
-- projection o i =
--   let
--     len = length $ summandsO $ substO $ S.treeLabel
--       $ S.initialEdgeTree $ S.IV S.Main
--   in
--     Morphism [TauMatrix  (M.diagonal 0
--                          $ V.fromList ([1] ++ replicate (len - 1) 0)) 0]

emptyMatrix = M.matrix 0 0 undefined


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

tensorSO :: SimpleObject -> SimpleObject -> Object
tensorSO M M = groupObject
tensorSO M (AE _) = toObject M
tensorSO (AE _) M = toObject M
tensorSO (AE g1) (AE g2) = toObject $ AE $ g1 `mappend` g2


-- TODO: deal with higher multiplicity
-- tensorInv :: SimpleObject -> [(SimpleObject, SimpleObject)]
-- tensorInv so = [(x,y) | x <- allSimpleObjects
--                       , y <- allSimpleObjects
--                       , multiplicity (x `tensorSO` y) so == 1]

tensorInv :: SimpleObject -> [(SimpleObject, SimpleObject)]
tensorInv M = (zipWith (,) (map AE group) (repeat M))
              ++ (zipWith (,) (repeat M) (map AE group))
tensorInv (AE g0) = [(AE $ g0 `plus` g, AE $ invert g) | g <- group]
                    ++ [(M,M)]


-- Given an additive function $f$ on objects, 
tensorHelper :: (Num a) =>  (SimpleObject -> SimpleObject -> a) -> SimpleObject -> [a]
tensorHelper f so = map (uncurry f) $ tensorInv so


tensorO :: Object -> Object -> Object
tensorO o1 o2 = Object {
    multiplicity =
     let jointMultiplicity a b
           = (multiplicity o1 a) * (multiplicity o2 b)
     in
       sum . tensorHelper jointMultiplicity
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
        foldl directSum emptyMatrix . (tensorHelper kron)
  }

-- FIXME
linearize :: ([SimpleObject] -> M.Matrix Scalar) -> [Object] -> M.Matrix Scalar
linearize f os =
  let
    soTuples = CM.replicateM (length os) allSimpleObjects
  in
    foldl directSum emptyMatrix $ -- sum $
    concat $
    map (\sos ->
           replicate
           (product $ zipWith multiplicity os sos)
           (f sos)
        )
    soTuples

linearize1 :: (SimpleObject ->  M.Matrix Scalar)
  -> (Object -> M.Matrix Scalar)
linearize1 f o1 = 
  linearize (\sos -> f (sos !! 0)) [o1]


linearize2 :: (SimpleObject -> SimpleObject -> M.Matrix Scalar)
  -> (Object -> Object -> M.Matrix Scalar)
linearize2 f o1 o2 = 
  linearize (\sos -> f (sos !! 0) (sos !! 1)) [o1, o2]


linearize3 :: (SimpleObject -> SimpleObject -> SimpleObject -> M.Matrix Scalar)
  -> (Object -> Object -> Object -> M.Matrix Scalar)
linearize3 f o1 o2 o3 = 
  linearize (\sos -> f (sos !! 0) (sos !! 1) (sos !! 2)) [o1, o2, o3]



-- tensorInv :: SimpleObject -> [(SimpleObject, SimpleObject)]
-- tensorInv so =
--   case so of
--     M -> [(M, AE ae) | ae <- group] ++ [(AE ae, M) | ae <- group]
--     AE ae -> [(ae1, ae2) |
--               ae1 <- group,
--               ae2 <- group,
--               ae1 `plus` ae2 == ae]
--              ++ [(M,M)]



-- -- validInitialLabels :: S.InitialEdge -> [SimpleObject]
-- -- validInitialLabels ie = [M, AE $ AEVar ie]



-- ------------------------------------------------------
-- --  Initial labels
-- ------------------------------------------------------

--
initialLabel :: S.InitialEdge -> Object 
initialLabel ie = -- toObject $ AE (AElement 0)
  case ie of
    S.LeftLoop -> toObject $ M
    S.RightLoop -> toObject $ M --AE (AElement 1)
    S.LeftLeg -> toObject $ M --AE (AElement 1)
    S.RightLeg -> toObject $ M --AE (AElement 1)

phi =
  let
    domain0 =  substO $ S.treeLabel $ S.initialEdgeTree $ S.IV S.Main
  in
    Morphism
    { domain = domain0
    , codomain = toObject one
    , subMatrix = \so ->
        if so == one
        then M.fromLists
             [[1]
               ++ replicate (multiplicity domain0 one) 0
             ]
        else emptyMatrix
    }


-- initialLabel :: S.InitialEdge -> Object 
-- initialLabel ie = 
--   case ie of
--     S.LeftLoop -> toObject $ AE (AElement 0)
--     S.RightLoop -> toObject $ AE (AElement 0)
--     S.LeftLeg -> toObject $ AE (AElement 0)
--     S.RightLeg -> toObject $ AE (AElement 0)


-- phi =  idMorphism $ substO $ S.treeLabel
--   $ S.initialEdgeTree $ S.IV S.Main



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

    

alphaSO :: SimpleObject -> SimpleObject -> SimpleObject -> Morphism
alphaSO (AE g1) (AE g2) (AE g3) = idMorphism $ toObject $ AE $ g1 `mappend` g2 `mappend` g3
alphaSO (AE _) (AE _) M = idMorphism $ toObject M
alphaSO M (AE _) (AE _) = idMorphism $ toObject M
alphaSO (AE a) M (AE b) = scalarMorphism (toObject M) (chi a b)
alphaSO (AE _) M M = groupSum (\_ -> 1)
alphaSO M M (AE _) = groupSum (\_ -> 1)
alphaSO M (AE a) M = groupSum (\b -> chi a b)
alphaSO M M M =
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
          M ->  toMatrix $ \x y -> tau * chiI x y
          AE _ -> emptyMatrix
    }

alpha :: Object -> Object -> Object -> Morphism
alpha o1 o2 o3 =
  Morphism
  { domain = (o1 `tensorO` o2) `tensorO` o3
  , codomain =   o1 `tensorO` (o2 `tensorO` o3)
  , subMatrix = \so ->
      linearize3 (\so1 so2 so3 ->
                    subMatrix (alphaSO so1 so2 so3) so)
      o1 o2 o3
  }

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
          M ->    toMatrix $ \x y -> tauI * chi x y
          AE _ -> emptyMatrix
    }

alphaI :: Object -> Object -> Object -> Morphism
alphaI o1 o2 o3 =
  Morphism
  { domain = o1 `tensorO` (o2 `tensorO` o3)
  , codomain =  (o1 `tensorO` o2) `tensorO` o3
  , subMatrix = \so ->
       linearize3 (\so1 so2 so3 ->
                    subMatrix (alphaISO so1 so2 so3) so)
       o1 o2 o3
  }


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
    Morphism
    { domain = toObject one
    , codomain = codomain0
    , subMatrix = \so ->
        if so == one
        then M.fromLists $ [[1]] ++ 
                           replicate
                           ((multiplicity codomain0 one) - 1)
                           [0]
        else emptyMatrix
    }
      

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
  let domain0 = o `tensorO` (star o) in        
    Morphism
    { domain = domain0
    , codomain = toObject one
    , subMatrix = \so ->
        if so == one
        then M.fromLists $
        [[ --FIXME: the following is a hack
            if multiplicity o M > 0
            then tauI
            else 1
         ]
         ++ (replicate
             ((multiplicity domain0 one) - 1)
             0
            )
        ]
        else emptyMatrix
    }

-- pivotalJSO :: SimpleObject -> Morphism
-- pivotalJSO so = scalarMorphism so $
--   case so of
--     M -> nu
--     AE _ -> 1

pivotalJ :: Object -> Morphism
pivotalJ o =
  Morphism
  { domain = o
  , codomain = o
  , subMatrix = \so ->
      M.diagonal 0
      (V.replicate (multiplicity o so) $
        case so of
          M -> nu
          AE _ -> 1
      )
  }
      

-- pivotalJISO :: SimpleObject -> Morphism
-- pivotalJISO = pivotalJSO

pivotalJI :: Object -> Morphism
pivotalJI = pivotalJ

-- standard (nondiagrammatic) order 
compose :: Morphism -> Morphism -> Morphism
compose m1 m2 =
  if domain m1 == codomain m2
  then 
    Morphism
    { domain = domain m2
    , codomain = codomain m1
    , subMatrix = \so ->
        (subMatrix m1 so) * (subMatrix m2 so)
    }
  else error $ "Invalid composition: Codomain doesn't match domain. Codomain: "
       ++ (show $ codomain m2) ++ ". Domain: " 
       ++ (show $ domain m1)

    
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
  S.Alpha o1 o2 o3 -> alpha (substO o1) (substO o2) (substO o3)
  S.AlphaI o1 o2 o3 -> alphaI (substO o1) (substO o2) (substO o3)
  S.Coev o -> coev $ substO o
  S.Ev   o -> ev $ substO o
  S.PivotalJ  o -> pivotalJ $ substO o
  S.PivotalJI o -> pivotalJI $ substO o
  S.Compose m1 m2 -> compose (substM m1) (substM m2)


-- -- Debugging strategies
-- -- 
-- -- 1. finalMorphism (Look at subtrees)
-- --
-- -- 2. Look at TY code for error
-- -- (Direct sum stuff).  In particular, add conceptual types to wrap
-- -- around the computational types (i.e. SimpleObject functions to wrap
-- -- around the matrices)
