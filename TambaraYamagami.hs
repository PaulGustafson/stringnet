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
-- TODO: Actually calculate the $R$ matrix wrt to basis of simple
-- objects.  
--
-- TODO: Optimization: Keep objects/morphisms as tensor products.
-- Calculate compositions factorwise if possible.
--
-- TODO: Extract Stringnet typeclass
--
-- TODO: Use sums instead of direct sum at appropriate times
--
-- TODO: Dehackify ev method.
--
-- TODO: Write unit tests for important methods.
--
-- TODO: Write Num instances.
--
--


module TambaraYamagami where

import Finite
import qualified TwoComplex as TC
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

data SimpleObject =
  -- Group-element-indexed simple objects
  AE !AElement

  -- non-group simple object
  | M
                  deriving (Show,Eq)

one :: SimpleObject
one = AE $ AElement 0

toIndex :: SimpleObject -> Int
toIndex (AE ae) = case ae of AElement i -> i
toIndex M  =  order

fromIndex :: Int -> SimpleObject
fromIndex i = if (0 <= i && i < order)
              then AE $ AElement i
              else if (i == order)
                   then M
                   else error "Simple Object index out of bounds"

allSimpleObjects = (map AE group) ++ [M]

newtype Object = Object
  { multiplicity_ :: [Int]
  }

multiplicity :: Object -> SimpleObject -> Int
multiplicity o so = (multiplicity_ o) !! (toIndex so)


-- Modularize constructor for testing different object implementations
object :: (SimpleObject -> Int) -> Object
object f = Object $ map f allSimpleObjects


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
toObject x = object $ \y ->
                  if x == y
                  then 1
                  else 0


-- Matrices of scalars 
data Morphism = Morphism 
  { domain   :: !Object -- redundant
  , codomain :: !Object -- redundant

  --  , stringnet :: S.Stringnet -- keep track of edge labels after every morphism 
  
  -- the only morphisms between simple objects are identity morphisms
  , subMatrix_ :: ![M.Matrix Scalar]
  }

subMatrix :: Morphism -> SimpleObject -> M.Matrix Scalar
subMatrix m so = (subMatrix_ m) !! (toIndex so)

morphism :: Object -> Object -> (SimpleObject -> M.Matrix Scalar) -> Morphism
morphism o1 o2 f = Morphism o1 o2 (map f allSimpleObjects)

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
  morphism o o $ \so -> 
  M.diagonal 0 (V.replicate (multiplicity o so) scalar)


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
  object $ \so ->
      case so of
        AE _ -> 1
        M    -> 0

groupSum :: (AElement -> Scalar) -> Morphism
groupSum f =  --M.diagonal 0 $ V.generate order (f . AElement)
  morphism groupObject groupObject $ \so ->
      case so of
        AE g -> M.fromLists [[f g]]
        M    -> emptyMatrix

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
    morphism domain0 domain0 $ \so ->
        case so of
          M ->  toMatrix f
          AE _ -> emptyMatrix

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
tensorO o1 o2 = object $
     let jointMultiplicity a b
           = (multiplicity o1 a) * (multiplicity o2 b)
     in
       sum . tensorHelper jointMultiplicity


-- Go through the direct sum of simple objects in the domain and range
-- and check if each pair is (M,M)
tensorM :: Morphism -> Morphism -> Morphism
tensorM m1 m2 =
  let kron so1 so2 = kronecker (subMatrix m1 so1) (subMatrix m2 so2)
  in
    morphism (tensorO (domain m1) (domain m2))
    (tensorO (codomain m1) (codomain m2))
    (foldl directSum emptyMatrix . (tensorHelper kron))


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




-- ------------------------------------------------------
-- --  Substituting TY labels for arbitrary ones
-- ------------------------------------------------------
     
-- Substitute in the TY-specific objects.
substO :: (S.InitialEdge -> SimpleObject) -> S.Object -> Object
substO il o0 =  case o0 of
  S.OVar ie -> toObject $ il ie
  S.One -> toObject $ AE (AElement 0)
  S.Star o -> star $ substO il o
  S.TensorO o1 o2 -> (substO il o1) `tensorO` (substO il o2)

    

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
      object $  \so ->
        case so of
          AE _ -> 0
          M    -> order
  in
    morphism domain0 domain0 $ \so ->
        case so of
          M ->  toMatrix $ \x y -> tau * chiI x y
          AE _ -> emptyMatrix

alpha :: Object -> Object -> Object -> Morphism
alpha o1 o2 o3 =
  morphism ((o1 `tensorO` o2) `tensorO` o3)
  (o1 `tensorO` (o2 `tensorO` o3))
  $ \so ->
      linearize3 (\so1 so2 so3 ->
                    subMatrix (alphaSO so1 so2 so3) so)
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
     $ \so ->
        case so of
          M    -> toMatrix $ \x y -> tauI * chi x y
          AE _ -> emptyMatrix
    

alphaI :: Object -> Object -> Object -> Morphism
alphaI o1 o2 o3 =
  morphism
   (o1 `tensorO` (o2 `tensorO` o3))
   ((o1 `tensorO` o2) `tensorO` o3)
   $ \so ->
       linearize3 (\so1 so2 so3 ->
                    subMatrix (alphaISO so1 so2 so3) so)
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
    $ \so ->
        if so == one
        then M.fromLists [[1]] 
        else emptyMatrix      

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
    morphism domain0 (toObject one)
    $ \so ->
        if so == one
        then M.fromLists $
        [[  -- TODO: double check this
            if multiplicity o M > 0
            then tauI
            else 1
         ]
        ]
        else emptyMatrix
     
    
-- pivotalJSO :: SimpleObject -> Morphism
-- pivotalJSO so = scalarMorphism so $
--   case so of
--     M -> nu
--     AE _ -> 1

pivotalJ :: Object -> Morphism
pivotalJ o =
  morphism o o $ \so ->
      M.diagonal 0
      (V.replicate (multiplicity o so) $
        case so of
          M -> nu
          AE _ -> 1
      )
      

-- pivotalJISO :: SimpleObject -> Morphism
-- pivotalJISO = pivotalJSO

pivotalJI :: Object -> Morphism
pivotalJI = pivotalJ

-- standard (nondiagrammatic) order 
compose :: (S.InitialEdge -> SimpleObject) -> Morphism -> S.Morphism -> S.Morphism -> Morphism
compose il phi sm1 sm2 =
  let
    m1 = substM il phi sm1
    m2 = substM il phi sm2
  in
    if domain m1 == codomain m2
    then 
      morphism (domain m2) (codomain m1) $ \so ->
          let
            mat1 = (subMatrix m1 so)
            mat2 = (subMatrix m2 so)
            minDim = min (M.ncols mat1) (M.nrows mat2)
          in
            if minDim == 0
            then emptyMatrix
            else (M.submatrix 1 (M.nrows mat1) 1 minDim mat1)
                 * (M.submatrix 1 minDim 1 (M.ncols mat2) mat2)
            -- else 
            --   error $ "Invalid composition: "
            --   ++ "dimensions don't match at SimpleObject "
            --   ++ (show so) ++ ". "
            --   ++ (show sm1) ++ " has " ++ (show $ M.ncols mat1)
            --   ++ " columns. "
            --   ++ (show sm2) ++ " has " ++ (show $ M.nrows mat2)
            --   ++ " rows. "
    else error $ "Invalid composition: Codomain doesn't match domain. "
         ++ (show sm2) ++ " has codomain: "
         ++ (show $ codomain m2) ++ ". "
         ++ (show sm1) ++ " has domain: " ++ (show $ domain m1)
  


    
-- Substitute in the TY-specific morphisms
substM :: (S.InitialEdge -> SimpleObject) -> Morphism -> S.Morphism -> Morphism
substM il phi m = case m of
  S.Phi -> phi
  S.Id o -> idMorphism $ substO il o
  S.Lambda o -> idMorphism $ substO il o
  S.LambdaI o -> idMorphism $ substO il o
  S.Rho o -> idMorphism $ substO il o
  S.RhoI o -> idMorphism $ substO il o
  S.TensorM m1 m2 -> (substM il phi m1) `tensorM` (substM il phi m2)
  S.Alpha o1 o2 o3 -> alpha (substO il o1) (substO il o2) (substO il o3)
  S.AlphaI o1 o2 o3 -> alphaI (substO il o1) (substO il o2) (substO il o3)
  S.Coev o -> coev $ substO il o
  S.Ev   o -> ev $ substO il o
  S.PivotalJ  o -> pivotalJ $ substO il o
  S.PivotalJI o -> pivotalJI $ substO il o
  S.Compose m1 m2 -> compose il phi m1 m2

allInitialEdges :: [S.InitialEdge]
allInitialEdges = [S.LeftLoop, S.RightLoop, S.LeftLeg, S.RightLeg]

numInitialEdges :: Int
numInitialEdges = length allInitialEdges

allInitialLabels :: [S.InitialEdge -> SimpleObject]
allInitialLabels = map (\x y -> x !! (fromEnum y))
  (replicateM (length allInitialEdges) allSimpleObjects) 

toCodomain :: (S.InitialEdge -> SimpleObject) -> Object
toCodomain il =
  substO il $ S.treeLabel (S.objectLabel S.initialStringnet) (S.initialEdgeTree $ S.IV S.Main)

-- TODO: Convert to Edge instead of IE, and InteriorVertex -> OneIndex
type InitialBasisElement = (S.InitialEdge -> SimpleObject,  Int)

-- data B_asisElement = B_asisElement
--   { initialLabel :: S.InitialEdge -> SimpleObject
--   , oneIndex :: Int
--   }

-- ------------------------------------------------------
-- --  Initial labels
-- ------------------------------------------------------

morphismSet :: Object -> [Int]
morphismSet codomain0 =
  if multiplicity codomain0 one > 0
  then [0..(multiplicity codomain0 one)]
  else []

oneIndexToMorphism :: Object -> Int -> Morphism
oneIndexToMorphism codomain0 n =
  if multiplicity codomain0 one > 0
  then morphism (toObject one) codomain0  $ \so ->
           if so == one
           then M.fromLists $
                (replicate n [0])
                ++ [[1]]
                ++ (replicate
                    ((multiplicity codomain0 one) - 1 - n) [0])
           else emptyMatrix
  else error "One index for wrong object"


data SimpleStringnet = SimpleStringnet
                  { twoComplex    :: TC.TwoComplex
                  , simpleObjectLabel   :: !(S.Edge -> SimpleObject)
                  , oneIndex :: !(S.InteriorVertex -> Int)
                  }


newtype TensorObject = TensorObject { getObject :: Object}

instance Monoid TensorObject where
  mempty = TensorObject $ toObject $ one
  mappend a b = TensorObject $ tensorO (getObject a) (getObject b)


-- Given a two complex, a basis element is parametrized by a labelling
-- of all edges in the two complex by simple objects and, for each
-- interior vertex, a choice of basis for the resulting Hom space
-- TODO: Figure out ordering of 1's in Hom space
-- simpleStringnet :: TC.TwoComplex -> (S.Edge -> SimpleObject)
--   -> (S.InteriorVertex -> Int) -> Stringnet
-- simpleStringnet twoComplex0 label oneIndex =
--   Stringnet 
--   { twoComplex = twoComplex0
--   , objectLabel = toObject . label
--   , morphismLabel = \iv ->
--       oneIndexToMorphism
--       (getObject $ F.fold $ fmap
--        (TensorObject . toObject . label)
--        $ TC.edgeTree twoComplex0 $ S.IV iv)
--       (oneIndex iv)
--   }



type Stringnet = SimpleStringnet -> Scalar




initialBasis :: [InitialBasisElement]
initialBasis =  concat $ map (uncurry $ \il ms -> [(il, m)
                                           |  m <- ms])
  [(il, morphismSet $ toCodomain il) | il <- allInitialLabels]


finalMorphism :: InitialBasisElement -> Morphism
finalMorphism be =
  let
    (initialLabel, initialOneIndex) = be
    initialCodomain = toCodomain initialLabel
    initialMorphism = oneIndexToMorphism
      initialCodomain initialOneIndex
  in
    substM initialLabel initialMorphism S.finalMorphism
  
  

answer = map finalMorphism initialBasis

