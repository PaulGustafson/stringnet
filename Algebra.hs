{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Algebra where

import Data.Group
import Data.Semigroup
import qualified Data.List as L

-- order of abelian group A
order :: Int
order = 2

-- Show for order 2 group
instance Show Scalar where
  show s0 =
    let s = normalize s0 in
      (case () of
         _  | (coeff s) !! 1 == 0 -> show $ (coeff s) !! 0
            | (coeff s) !! 0 == 0 -> "-" ++ (show $ (coeff s) !! 1)
            | otherwise -> error "Show scalar leftover case"
      ) ++
      (case () of
          _ | getSum (tauExp s) == 0 -> ""
            | getSum (tauExp s) == -1 -> "\\sqrt{2}"
            | otherwise ->
                "*2^{-" ++ (show $ getSum $ tauExp s) ++ "/2}"
      )
  
-- \pm 1
nu :: Scalar
nu = 1

-- Group element, assuming cyclicity
newtype AElement = AElement Int deriving (Show)

instance Eq AElement where
  (AElement a) == (AElement b) = (a `mod` order) == (b `mod` order)

instance Monoid AElement where
  (AElement e1) `mappend` (AElement e2) = AElement $ (e1 + e2) `mod` order
  mempty = AElement 0
    
instance Group AElement where
  invert (AElement e) = AElement  $ (-e) `mod` order

-- Carrier set for the group
group :: [AElement]
group = Prelude.map AElement [0..(order - 1)]

-- Nicer synonym for the group operation
plus :: AElement -> AElement -> AElement
plus = mappend


newtype RootOfUnity = RootOfUnity AElement deriving (Eq, Monoid, Group)

-- A scalar is an algebraic integer over the cyclotomic field
-- corresponding to the order of the group.  Normal form:  tauExp > -1
data Scalar =  Scalar 
  { coeff :: ![Int]
  , tauExp :: !(Sum Int)
  } deriving (Eq)


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


-- Source: https://www.blaenkdenum.com/posts/naive-convolution-in-haskell/
convolve :: (Num a) => [a] -> [a] -> [a]
convolve hs xs =
  let pad = replicate ((length hs) - 1) 0
      ts  = pad ++ xs
  in map (sum . zipWith (*) (reverse hs)) (init $ L.tails ts)

-- Reduce \sum_{i=0}^{p-1} \zeta^i = 0
normalize :: Scalar -> Scalar
normalize s = normalize4 $ normalize3 $ normalize2 $ Scalar
  { coeff = if order /= 1
            then map (\x -> x - minimum (coeff s)) (coeff s)
            else coeff s
  , tauExp = tauExp s
  }

-- Reduction of positive tauExponents
normalize2 :: Scalar -> Scalar
normalize2 s =
  if (and $ map (== 0) $ map (`mod` order) (coeff s))
     && ((coeff s) !! 0) > 0
     && tauExp s > 0
  then normalize2 $ Scalar
       { coeff = map (`div` order) $ coeff s
       , tauExp = (tauExp s) - 2
       }
  else s

-- Reduction of negative tauExponents
normalize3 :: Scalar -> Scalar
normalize3 s =
  if tauExp s < 0
     && (getSum $ tauExp s) `mod` 2 == 0
  then normalize3 $ Scalar
       { coeff = map (* order) $ coeff s
       , tauExp = (tauExp s) + 2
       }
  else s

-- Get rid of tauExps for 0 
normalize4 :: Scalar -> Scalar
normalize4 s =
  if and $ map (== 0) $ coeff s
  then Scalar (replicate order 0) 0
  else s

-- Use the fact that \zeta^n = 1 to reduce after convolution
reduce :: [Int] -> [Int]
reduce xs =
  if length xs < order
  then xs ++ replicate (order - length xs) 0
  else zipWith (+) (take order xs) (reduce $ drop order xs)

isZero :: Scalar -> Bool
isZero s = and $ map (== 0) $ coeff s

-- Assuming even offset of tauExps
matchTauExps :: Scalar -> Scalar -> (Scalar, Scalar)
matchTauExps s1 s2 =
  let
    t1 = getSum $ tauExp s1
    t2 = getSum $ tauExp s2
  in
    if (t1 - t2) `mod` 2 == 0
    then
       case () of
         _ | t1 == t2 -> (s1, s2)
           | t1 < t2  -> (Scalar
                          { coeff =
                            map (* order^((t2 - t1) `div` 2))
                            $ coeff s1
                          , tauExp = Sum t2
                          }
                         ,
                           s2
                         )
           | t1 > t2  -> (s1
                         ,
                          Scalar
                          { coeff =
                            map (* order^((t1 - t2) `div` 2))
                            $ coeff s1
                          , tauExp = Sum t1
                          }
                         )
    else error "Odd tauExp offset unimplemented"
  
           
instance Num Scalar where
  s1 + s2 =
    normalize $ case () of
    _ | isZero s1 -> s2
      | isZero s2 -> s1
      | otherwise ->
        let
          (sn1, sn2) = matchTauExps s1 s2
        in
          Scalar
          { coeff = zipWith (+) (coeff sn1) (coeff sn2)
          , tauExp = tauExp sn1
          }
          
  s1 * s2 = normalize $  Scalar {
    coeff = reduce $ convolve (coeff s1) (coeff s2)
    , tauExp = (tauExp s1) + (tauExp s2)
    }
  fromInteger x = normalize $ Scalar {
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
