module LocalMoves where


import TambaraYamagami as TY
import Algebra
import Finite
import Control.Monad.State
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
import qualified Data.Tree as T
import Tree
import TambaraYamagami


-- Tree corresponding to a summand of a vertex-morphism's codomain
data InternalTree = ILeaf Edge SimpleObject
                  | INode SimpleObject InternalTree InternalTree
                  deriving (Eq, Show)

rootLabel :: InternalTree -> SimpleObject
rootLabel it =
  case it of
    ILeaf _ so -> so
    INode so _ _ -> so

-- Simple colored graph
data SimpleColoring = SimpleColoring
  { objectLabel   :: !(Edge -> SimpleObject)
                  
  -- CCW ordering, outgoing orientation
  , objectTree      :: !(Vertex -> InternalTree)
                    
  }


data Stringnet = Stringnet
                 { twoComplex :: TC.TwoComplex
                 , edgeTree :: (Vertex -> Tree Edge)
                 , colorCoeff :: SimpleColoring -> Scalar
                 }

-- vertices sn = TC.vertices $ twoComplex sn
-- edges sn = TC.edges $ twoComplex sn
-- disks sn = TC.disks $ twoComplex sn
-- perimeter sn = TC.perimeter $ twoComplex sn
-- imageVertex sn = TC.imageVertex $ twoComplex sn


-- toTensorTree :: Morphism -> Tree Morphism
-- toTensorTree (tensorM x y) =
--   Node (toTensorTree x) (toTensorTree y)
-- toTensorTree x = Leaf x

-- toCompositionList :: Morphism -> [Morphism]
-- toCompositionList (Compose ms) = ms
-- toCompositionList m = [m]

-- toTree :: Morphism -> T.Tree (Maybe Morphism)
-- -- toTree m@(Compose _) =
-- --   T.Node Nothing  (map toTree $ toCompositionList m)
-- toTree (tensorM x y) =
--   T.Node Nothing [(toTree x), (toTree y)]
-- toTree x = T.Node (Just x) []


instance Semigroup Morphism where
   a <> b = compose a b


-- toDataTree :: Tree a -> T.Tree (Maybe a)
-- toDataTree (Leaf x) = T.Node (Just x) []
-- toDataTree (Node x y) = T.Node Nothing [toDataTree x, toDataTree y]


-- -- Pretty print
-- pprint :: (Show a) => Tree a-> IO ()
-- pprint = putStr. T.drawTree . fmap (\x -> case x of
--                                        Nothing -> "+"
--                                        Just e -> show e
--                                    )
--                                    . toDataTree

-- TODO: maybe put this into SimpleColoring, to make parallel with
--       perimeter also, eliminate "image"
endpoints :: Edge -> TC.TwoComplex -> [Vertex]
endpoints e tc = map (TC.imageVertex tc) (initialEndpoints e)

-- Monadic versions of methods
edgeTreeM :: Vertex -> State Stringnet (Tree Edge)
edgeTreeM v = state $ \sn -> (edgeTree sn v, sn)

endpointsM :: Edge -> State Stringnet [Vertex]
endpointsM e = state $ \sn -> (endpoints e sn, sn)

perimeterM :: Disk -> State Stringnet [Edge]
perimeterM d = state $ \sn -> (perimeter (twoComplex sn) d, sn)

start :: Edge -> SimpleColoring -> Vertex
start e sn = (endpoints e sn) !! 0

end :: Edge -> SimpleColoring -> Vertex
end e sn = (endpoints e sn) !! 1


treeLabel :: (Edge -> Object) -> Tree Edge -> Object
treeLabel label (Leaf e) = label e
treeLabel label (Node x y) =
  tensorO (treeLabel label x) (treeLabel label y)


-- perimeter before contractions
initialPerimeter :: Disk -> [Edge]
initialPerimeter Outside    = [IE LeftLoop, IE RightLoop]
initialPerimeter LeftDisk   =
  [Reverse $ IE LeftLoop, IE LeftLeg, Reverse $ IE LeftLeg]
initialPerimeter RightDisk  =
  [Reverse $ IE RightLoop, IE RightLeg, Reverse $ IE RightLeg]

initialEdgeTree :: Vertex -> Tree Edge
initialEdgeTree v = case v of
  Punc LeftPuncture -> Leaf $ Reverse $ IE LeftLeg
  Punc RightPuncture -> Leaf $ Reverse $ IE RightLeg
  IV Main ->
    Node
     (Node
      (Leaf $ Reverse $ IE RightLoop)
       (Node
         (Leaf $ IE RightLeg)
         (Leaf $ IE RightLoop)
       )
     )
     (Node
       (Leaf $ Reverse $ IE LeftLoop)
       (Node
         (Leaf $ IE LeftLeg)
        (Leaf $ IE LeftLoop)
       )                                                          
     )



-- objectLabel0 :: InitialBasisElement -> Edge -> Object
-- objectLabel0 be (IE e) = toObject $ initialLabel be e
-- objectLabel0 be (FirstHalf e) = objectLabel0 be e 
-- objectLabel0 be (SecondHalf e) = objectLabel0 be e
-- objectLabel0 be (Connector _ _ _) = toObject one
-- objectLabel0 be (TensorE e1 e2)
--   = tensorO (objectLabel0 be e1) (objectLabel0 be e2)
-- objectLabel0 be (Reverse e)  = star (objectLabel0 be e)


initialTwoComplex :: TwoComplex
initialTwoComplex =
  TwoComplex
  { vertices = [Main]
  , edges    = map IE [LeftLoop, RightLoop, LeftLeg, RightLeg]
  , disks    = [Outside, LeftDisk, RightDisk]
  , imageVertex    = id
  , perimeter = initialPerimeter
  }

-- initialSimpleColoring :: InitialBasisElement -> SimpleColoring
-- initialSimpleColoring basisElement =
--   SimpleColoring { twoComplex = initialTwoComplex
--                  , morphismLabel =  \m ->
--                      case m of Main
--                                  -> morphismFromBE basisElement
--                  , edgeTree = initialEdgeTree
--                  , objectLabel = objectLabel0 basisElement
--                  }

braid :: State Stringnet ()            
braid = do
  (_,l1,r1) <- addCoev $ IE LeftLoop
  (_,l2,r2) <- addCoev $ IE LeftLeg
  (_,r13,l3) <- addCoev r1
  (_,_,r4) <- addCoev $ IE RightLoop
  e1 <- connect (rev l1) r2 LeftDisk
  e2 <- connect (rev l2) (rev r13) (Cut $ e1)
  e3 <- connect l3 r4 Outside
  contract e1                   
  contract e2
  contract e3
  tensor (Cut $ rev e1)
  tensor (Cut $ rev e2)
  tensor (Cut $ rev e3)
  v <- contract r4
  
  -- At this point we're done with local moves, but we still need to
  -- modify the final vertex's edge tree. It should look the same as
  -- the initial edge tree, except left and right are swapped. This is
  -- somewhat implementation-dependent since I haven't specified
  -- complete edgeTree behavior for most of the local moves.
  --
  -- TODO: make a method to turn a tree into a specified shape
  --
  -- Current Edgetree:
  --
  -- 
  --
  -- +
  -- |
  -- +- +
  -- |  |
  -- |  +- +
  -- |  |  |
  -- |  |  +- +
  -- |  |  |  |
  -- |  |  |  +- Reverse (FirstHalf (SecondHalf LeftLoop))
  -- |  |  |  |
  -- |  |  |  `- SecondHalf LeftLeg
  -- |  |  |
  -- |  |  `- FirstHalf (SecondHalf LeftLoop)
  -- |  |
  -- |  `- TensorE (TensorE (TensorE (Reverse (FirstHalf LeftLoop)) (Reverse (FirstHalf LeftLeg))) (SecondHalf (SecondHalf LeftLoop))) (Reverse (FirstHalf RightLoop))
  -- |
  -- `- +
  --    |
  --    +- RightLeg
  --    |
  --    `- Reverse (TensorE (TensorE (TensorE (Reverse (FirstHalf LeftLoop)) (Reverse (FirstHalf LeftLeg))) (SecondHalf (SecondHalf LeftLoop))) (Reverse (FirstHalf RightLoop)))

  associateR v
    (Node
      (Node
        (Leaf (Reverse (FirstHalf (SecondHalf $ IE LeftLoop))))
        (Leaf (SecondHalf $ IE LeftLeg))
      )
      (Leaf (FirstHalf (SecondHalf $ IE LeftLoop)))
    )

  et <- edgeTreeM (IV v)
  associateR v et
  
  return ()


newInitialEdge :: InitialEdge -> Edge
newInitialEdge ie =
  case ie of
    RightLeg -> SecondHalf (IE LeftLeg)
    RightLoop ->  FirstHalf (SecondHalf (IE LeftLoop))
    LeftLeg ->  IE RightLeg
    LeftLoop -> Reverse (TensorE (TensorE (TensorE (Reverse (FirstHalf (IE LeftLoop))) (Reverse (FirstHalf (IE LeftLeg)))) (SecondHalf (SecondHalf (IE LeftLoop)))) (Reverse (FirstHalf (IE RightLoop))))

--fragile
-- midMorphism :: InitialBasisElement -> State Stringnet () -> Morphism
-- midMorphism be st =
--   let
--     cg = (execState st . initialSimpleColoring) be
--   in
--     morphismLabel cg (vertices cg !! 0) 

-- finalSN :: InitialBasisElement -> SimpleColoring
-- finalSN = execState braid . initialSimpleColoring

-- finalVertex :: InitialBasisElement -> InteriorVertex
-- finalVertex be = vertices (finalSN be) !! 0

-- finalMorphism :: InitialBasisElement -> Morphism
-- finalMorphism be = morphismLabel (finalSN be) (finalVertex be)

-- finalEdgeTree :: InitialBasisElement -> Tree Edge
-- finalEdgeTree be = edgeTree (finalSN be) $ IV (finalVertex be)

-- finalObjectTree :: InitialBasisElement -> Tree Object
-- finalObjectTree be = fmap (objectLabel (finalSN be)) $ finalEdgeTree be



-- TODO: fix this
-- instance Num Object where
--   o1 + o2 = Object $ multiplicity o1 + multiplicity o2
--   o1 * o2 = o1 `tensorO` o2
--   fromInteger = undefined -- could change
--   negate _ = undefined
--   signum _ = undefined
--   abs _ = undefined

  
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


-- expandRows :: [Int] -> M.Matrix a -> Int -> M.Matrix a
-- expandRows indices m multiple =
--   let list = M.toLists m in
--     (take index list)
--     ++ repeat multiple (list !! index)
--     ++ drop index list


-- expandColumn :: Int -> M.Matrix a -> Int -> M.Matrix a
-- expandColumn index m multiple =
--   transpose $ expandRow (transpose M) index multiple

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
-- substO :: (InitialEdge -> SimpleObject) -> Object -> Object
-- substO il o0 =  case o0 of
--   OVar ie -> toObject $ il ie
--   One -> toObject $ AE (AElement 0)
--   Star o -> star $ substO il o
--   TensorO o1 o2 -> (substO il o1) `tensorO` (substO il o2)

    

type InitialData = (InitialEdge -> SimpleObject, Morphism)

-- standard (nondiagrammatic) order
compose :: Morphism -> Morphism -> Morphism
compose m1 m2 =
    if domain m1 /=  codomain m2
    then error $ "Invalid composition: Codomain doesn't match domain. "
         ++ (show m2) ++ " has codomain: "
         ++ (show $ codomain m2) ++ ". "
         ++ (show m1) ++ " has domain: " ++ (show $ domain m1)
    else morphism (domain m1) (codomain m2) $ (matrix m1) * (matrix m2)

lambda :: Object -> Morphism
lambda o =  idMorphism o

lambdaI :: Object -> Morphism
lambdaI o =  idMorphism o

rho :: Object -> Morphism
rho o  =  idMorphism o

rhoI :: Object -> Morphism
rhoI o = idMorphism o

    
-- Substitute in the TY-specific morphisms
-- substM :: (InitialEdge -> SimpleObject) -> Morphism -> Morphism -> Morphism
-- substM il phi m = case m of
--   Phi -> phi
--   Id o -> idMorphism $ substO il o
--   Lambda o -> idMorphism $ substO il o
--   LambdaI o -> idMorphism $ substO il o
--   Rho o -> idMorphism $ substO il o
--   RhoI o -> idMorphism $ substO il o
--   TensorM m1 m2 -> (substM il phi m1) `tensorM` (substM il phi m2)
--   Alpha o1 o2 o3 -> alpha (substO il o1) (substO il o2) (substO il o3)
--   AlphaI o1 o2 o3 -> alphaI (substO il o1) (substO il o2) (substO il o3)
--   Coev o -> coev $ substO il o
--   Ev   o -> ev $ substO il o
--   PivotalJ  o -> pivotalJ $ substO il o
--   PivotalJI o -> pivotalJI $ substO il o
--   Compose sms ->
--       foldl (compose (il, phi)) (substM il phi $ head sms) (tail sms)

allInitialEdges :: [InitialEdge]
allInitialEdges = [LeftLoop, RightLoop, LeftLeg, RightLeg]

numInitialEdges :: Int
numInitialEdges = length allInitialEdges

allInitialLabels :: [InitialEdge -> SimpleObject]
allInitialLabels = map (\x y -> x !! (fromEnum y))
  (replicateM (length allInitialEdges) allSimpleObjects) 

-- toCodomainSO :: (InitialEdge -> SimpleObject) -> Object
-- toCodomainSO il =
--   substO il $ treeLabel (objectLabel initialSimpleColoring) (initialEdgeTree $ IV Main)

--FIXME: use this function to define an order on InitialBasisElement
toCodomain :: (InitialEdge -> Object) -> Object
toCodomain il =
 (star $ il RightLoop)
 `tensorO`
  (il RightLeg)
  `tensorO`
  (il RightLoop)
  `tensorO`
  (star $ il LeftLoop)
  `tensorO`
  (il LeftLeg)
  `tensorO`
  (il LeftLoop)
  


-- Basis element for the stringnet space corresponding to
-- initial and final configurations
-- data InitialBasisElement = InitialBasisElement
--   { initialLabel :: !(Edge -> SimpleObject)
--   , initialTree :: !(InteriorVertex -> InternalTree)
--   } deriving (Show)

-- instance Eq InitialBasisElement where
--   be1 == be2 =
--     (and $
--     map (\ie ->
--             initialLabel be1 ie == initialLabel be2 ie)
--     (allElements :: [InitialEdge])
--     )
--     && oneIndex be1 == oneIndex be2   


-- morphismFromBE :: InitialBasisElement -> Morphism
-- morphismFromBE basisElement =
--   oneIndexToMorphism (toCodomain (toObject . initialLabel basisElement))
--   $ oneIndex basisElement

-- oneIndexToMorphism :: Object -> Int -> Morphism
-- oneIndexToMorphism codomain0 n =
--   if multiplicity codomain0 one > 0
--   then morphism (toObject one) codomain0  $ \so ->
--            if so == one
--            then M.fromLists $
--                 (replicate n [0])
--                 ++ [[1]]
--                 ++ (replicate
--                     ((multiplicity codomain0 one) - 1 - n) [0])
--            else emptyMatrix
--   else error "One index for wrong object"




-- instance Finite InitialBasisElement where
--   allElements =  concat $ map (uncurry $ \il ms ->
--                                  [ InitialBasisElement il m
--                                  |  m <- ms
--                                  ]
--                              )
--                  [(il, morphismSet $ toCodomain $ toObject . il)
--                  | il <- allInitialLabels]
                        

-- ------------------------------------------------------
-- --  Initial labels
-- ------------------------------------------------------

morphismSet :: Object -> [Int]
morphismSet codomain0 =
  if multiplicity codomain0 one > 0
  then [0..(multiplicity codomain0 one - 1)]
  else []


-- finalMorphism :: InitialBasisElement -> Morphism
-- finalMorphism be =
--   let
--     initialCodomain = toCodomainSO $ initialLabel be
--     initialMorphism = oneIndexToMorphism
--       initialCodomain $ oneIndex be
--   in
--     substM (initialLabel be) initialMorphism finalMorphism
    
-- answer = map finalMorphism (allElements :: [InitialBasisElement])


-- Given a morphism and a choice of indexed simple object for each edge,
-- return the list of scalars corresponding to that subspace
-- component :: InitialBasisElement -> InitialBasisElement -> (InitialEdge -> (SimpleObject, Int)) -> [Scalar]
-- component m oTree oneIndex0 = 


-- multiplicityBE :: (InitialEdge -> Object) -> InitialBasisElement -> Int
-- multiplicityBE label0 be0 =
--   product 
--   [multiplicity (label0 initialEdge0) (initialLabel be0 initialEdge0)
--   | initialEdge0 <- allElements]

-- -- translate the final basis oneIndex into an index for the final object
-- decomposeH :: InitialBasisElement -> InitialBasisElement -> [Int]
-- decomposeH initialBe finalBe = 
--   let
--     label0 = (objectLabel $ finalSN initialBe) . newInitialEdge
--     beIndex = case (L.elemIndex finalBe allElements) of
--       Just i -> i
--       Nothing -> error "decomposeH impossible branch"
--     increment = multiplicity (codomain $ morphismFromBE finalBe) one
--     base = sum $ map (multiplicityBE label0)
--          (take beIndex (allElements :: [InitialBasisElement]))
--   in
--     [ base + increment*i
--     | i <- [0..(multiplicityBE label0 finalBe - 1)]]

    

-- decompose :: InitialBasisElement -> InitialBasisElement -> Scalar
-- decompose initialBe finalBe =
--   sum $ map (\i -> 
--                (subMatrix (finalMorphism initialBe) one) M.! (i + 1, 1)
--             )
--   $ decomposeH initialBe finalBe

-- decompose2 i j = decompose (allElements !! (i-1)) (allElements !! (j-1))

-- rmatrix :: M.Matrix Scalar
-- rmatrix =
--   let
--     size0 = length (allElements :: [InitialBasisElement])
--   in
--     M.matrix size0 size0
--     (\(i,j) -> decompose2 i j)


-- A basis element should really include labellings of internal edges
-- tensorTreeToIndex :: T.Tree (Object, SimpleObject, Int) -> SimpleObject -> Int
-- tensorTreeToIndex (Leaf (o, so, i)) so2 = if multiplicity o so2 > i
--                                           then (o, so, i)
--                                           else error "Index out of bounds"
-- tensorTreeToIndex (Node a b) =
--   let
--     (o1, so1, i1) = tensorTreeToIndex a
--     (o2, so2, i2) = tensorTreeToIndex b
--     so1s = map fst (tensorInv so)
--     so2s = map snd (tensorInv so)
--            zipWith (,) (map (tensorTreeToIndex a) so1s)
--                (map (tensorTreeToIndex b) so2s)
--   in
--     dropWhile (\(a,b) -> multiplicity )


edgeLabels :: TwoComplex -> [Edge -> SimpleObject]
edgeLabels tc =
  let
    labels = replicateM (length $ edges tc) allSimpleObjects
  in
    [ \e -> label !! TC.indexE e
    | label <- labels]

tensorSOList :: SimpleObject -> SimpleObject -> [SimpleObject]
tensorSOList so1 so2 =
  case (so1, so2) of
    (AE ae1, AE ae2) -> [AE $ ae1]
    (AE _  , M)      -> [M]
    (M     , AE _)   -> [M]
    (M     , M   )   -> map AE group

-- TODO: enumerate all the edge trees
tensorITree :: InternalTree -> InternalTree -> [InternalTree]
tensorITree it1 it2 =
    map (\so -> INode so it1 it2) $ tensorSOList (rootLabel it1) (rootLabel it2)
    
objectTrees :: (Edge -> SimpleObject) -> Tree Edge -> [InternalTree]
objectTrees label0 soTree =
  case soTree of
    Leaf e -> [ILeaf e (label0 e)]
    Node a b -> [ tensorITree ot1 ot2
                | ot1 <- objectTrees label0 a
                , ot2 <- objectTrees label0 b
                ]

vertexLabels :: TwoComplex -> (Edge -> SimpleObject) -> Vertex -> [InternalTree]
vertexLabels tc oLabel v =
  objectTrees oLabel $ fmap oLabel $ edgeTree tc v

basis :: TwoComplex -> [Stringnet]
basis tc = [ Stringnet
             { twoComplex = tc
             , colorCoeff = \c ->
                 if c == SimpleColoring
                    { objectLabel = objectLabel0
                    , objectTree = objectTree !! indexV tc
                    }
                 then 1
                 else 0
             }
           | objectLabel0 <- edgeLabels tc
           , objectTree0  <- map (vertexLabels tc objectLabel0)
             (TC.vertices tc)
           ]




-- Test: replacePlusH Phi (Node (Leaf (Reverse (IE
-- RightLoop))) (Node (Leaf (IE RightLeg)) (Leaf (IE RightLoop)))) (Leaf $ IE
-- RightLoop) (initialEdgeTree $ IV Main)
replacePlusH :: SimpleColoring -> Morphism -> Tree Edge -> Tree Edge -> Tree Edge -> (Tree Edge, Tree Morphism)
replacePlusH sn m oldSubTree newSubTree bigTree = 
  if bigTree == oldSubTree
  then (newSubTree, Leaf m)
  else case bigTree of
    Leaf x  -> (Leaf x, Leaf $ idMorphism $ objectLabel sn x)
    Node x y ->
      let
        (tex, tmx) = replacePlusH sn m oldSubTree newSubTree x
        (tey, tmy) = replacePlusH sn m oldSubTree newSubTree y
      in
        (Node tex tey, Node tmx tmy)


--TODO: replace these functions with a Foldable instance
tensorMTree :: Tree Morphism -> Morphism
tensorMTree (Leaf m) = m
tensorMTree (Node x y) = tensorM (tensorMTree x) (tensorMTree y)

tensorOTree :: Tree Object -> Object
tensorOTree (Leaf m) = m
tensorOTree (Node x y) = tensorO (tensorOTree x) (tensorOTree y)

replacePlus :: SimpleColoring -> Morphism -> Tree Edge -> Tree Edge -> Tree Edge -> (Tree Edge, Morphism)
replacePlus sn m oldSubTree newSubTree bigTree =
  let (eTree, mTree) = replacePlusH sn m oldSubTree newSubTree bigTree in
    (eTree, tensorMTree mTree)

associateL :: InteriorVertex -> Tree Edge -> State Stringnet (Tree Edge)
associateL v0 subTree@(Node x yz) =
  case yz of
    Node y z ->
      let newSubTree = (Node (Node x y) z) in
        state $ \sn ->
        (newSubTree,
         let
           (newEdgeTree, morphism) = replacePlus sn
               (alphaI (treeLabel (objectLabel sn) x) (treeLabel (objectLabel sn) y)
                           (treeLabel (objectLabel sn) z))
               subTree newSubTree $ edgeTree sn $ IV v0
         in
           sn
           { edgeTree = \v ->
               if v == IV v0
               then newEdgeTree
               else edgeTree sn v
                    
           , colorCoeff = undefined --(\sc ->
           }
        )


associateR :: InteriorVertex -> Tree Edge -> State Stringnet (Tree Edge)
associateR v0 subTree@(Node xy z) =
  case xy of
    Node x y ->
      let newSubTree = (Node x (Node y z)) in
        state $ \sn ->
                  (newSubTree,
                   let
                     (newEdgeTree, morphism) = replacePlus sn
                       (alpha
                        (treeLabel (objectLabel sn) x)
                        (treeLabel (objectLabel sn) y)
                        (treeLabel (objectLabel sn) z)
                       )
                       subTree newSubTree $ edgeTree sn $ IV v0
                   in
                     sn
                     { edgeTree = \v ->
                         if v == IV v0
                         then newEdgeTree
                         else edgeTree sn v
                              
                     , colorCoeff = undefined

                       -- morphismLabel = \v ->
                       --   if v == v0
                       --   then compose (morphism)
                       --        (morphismLabel sn v)
                       --   else morphismLabel sn v
                     }
                  )



isolateHelperR :: InteriorVertex ->  SimpleColoring -> SimpleColoring
isolateHelperR v sn =
  let t = edgeTree sn (IV v) in
    case t of
      Node _ (Leaf _) -> sn
      Node _ (Node _ _) -> isolateHelperR v
        $ execState (associateL v t) sn
  
isolateHelperL :: InteriorVertex ->  SimpleColoring -> SimpleColoring
isolateHelperL v sn =
  let t = edgeTree sn (IV v) in
    case t of
      Node (Leaf _) _ -> sn
      Node (Node _ _) _ -> isolateHelperL v
        $ execState (associateR v t) sn
  
     
-- Turns the far right leaf into a depth one leaf  
isolateR :: InteriorVertex -> State Stringnet ()
isolateR v0 = state $ \sn ->
  ((), isolateHelperR v0 sn)

isolateL :: InteriorVertex -> State Stringnet ()
isolateL v0 = state $ \sn ->
  ((), isolateHelperL v0 sn)

swap :: Tree a -> Tree a
swap (Node x y) = Node y x


zMorphism :: Object -> Object -> Morphism -> Morphism
zMorphism xl yl m =
  ((idMorphism xl) `tensorM`  (rho yl))
  <> ((idMorphism xl) `tensorM` ((idMorphism yl) `tensorM` (ev $ star xl))) -- X (Y 1)
  <> ((idMorphism xl) `tensorM` (alpha yl xl (star xl))) -- X (Y (X *X))
  <> ((idMorphism xl) `tensorM` (m `tensorM` (idMorphism $ star xl))) -- X 1 *X -> X ((Y X) *X)
  <> ((pivotalJI xl) `tensorM` (lambdaI $ star xl))       -- **X *X -> X (1 *X)
  <> (coev $ star xl)  -- 1 -> **X *X

-- rotation of the rightmost edge in v0's to the leftside
zRotate :: InteriorVertex -> State Stringnet ()
zRotate v0 =
  isolateR v0 >> 
  ( state $ \sn ->
      ((), sn
        { edgeTree = \v ->
            (
              if v == IV v0
              then swap 
              else id
            )
            $ edgeTree sn v
          
        , colorCoeff = undefined

          -- morphismLabel = \v ->
           --  if v == v0 
           --  then case (edgeTree sn (IV v0)) of
           --    Node y (Leaf x) ->
           --      zMorphism (objectLabel sn x) (treeLabel (objectLabel sn) y) (morphismLabel sn v)
           -- else morphismLabel sn v
        }
      )
  )


rotateToEndHelper :: Edge -> InteriorVertex -> SimpleColoring -> SimpleColoring
rotateToEndHelper e0 v0 sn = 
  let
    es = flatten $ edgeTree sn (IV v0)
  in
    if es !! (length es - 1) == e0
    then sn
    else rotateToEndHelper e0 v0 $ execState (zRotate v0) sn

rotateToEnd :: Edge -> InteriorVertex -> State Stringnet ()
rotateToEnd e0 v0 = (state $ \sn ->
  ((), rotateToEndHelper e0 v0 sn))  >> isolateR v0

elemT :: Eq a => a -> Tree a -> Bool
elemT u = (elem u) . flatten 

minimalSuperTree :: (Eq a) => a -> a -> Tree a -> Tree a
minimalSuperTree a1 a2 t@(Node x y) 
  | a1 `elemT` x && a2 `elemT` x = minimalSuperTree a1 a2 x
  | a1 `elemT` y && a2 `elemT` y = minimalSuperTree a1 a2 y
  | otherwise                    = t


-- Easy optimization: calculate t from previous t
isolate2Helper ::  Edge -> Edge -> InteriorVertex -> SimpleColoring -> SimpleColoring
isolate2Helper e1 e2 v0 sn0 =
  let
    t = minimalSuperTree e1 e2 (edgeTree sn0 $ IV v0)
  in
    case t of
      Node x y -> 
        case x of
          Node _ _ -> isolate2Helper e1 e2 v0 $ execState (associateR v0 t) sn0
          Leaf _ -> case y of
              Node _ _ -> isolate2Helper e1 e2 v0 $ execState (associateL v0 t) sn0
              Leaf _ -> sn0

-- Put (rev) e1 and e2 on same node
isolate2 :: Edge -> Edge -> InteriorVertex  -> State Stringnet ()
isolate2 e1 e2 v0 = state $ \sn0 ->
  let
    firstEdge = (flatten $ edgeTree sn0 $ IV v0) !! 0
    sn1 = if (e2 == firstEdge)
          then execState (zRotate v0) sn0
          else sn0
  in   
    ((), isolate2Helper e1 e2 v0 sn1)


-- The disk's perimeter should only have two edges
tensorHelper :: Disk -> State Stringnet Edge
tensorHelper d0 =
  state $ \sn0 ->
  let
    e1 = (perimeter sn0 d0) !! 0
    e2 = rev ((perimeter sn0 d0) !! 1)
    v0 = toIV ((endpoints e1 sn0) !! 0)
    v1 = toIV ((endpoints e1 sn0) !! 1)
    product = TensorE e1 e2
    edgeImage e = case () of
      _ | e `elem` [e1, e2] -> product
        | e `elem` [rev e1, rev e2] -> rev product
        | otherwise -> e

    sn =  execState (isolate2 e1 e2 v0
                     >> isolate2 (rev e2) (rev e1) v1
                    ) sn0
  in
    ( product
    , sn
      { edges = map edgeImage (edges sn)
      , disks = [d | d <- disks sn
                   , d /= d0]
      , perimeter = (map edgeImage) . (perimeter sn)
      , edgeTree =  (replace (Node (Leaf e1) (Leaf e2)) (Leaf product))
                    . (replace (Node (Leaf $ rev e2) (Leaf $ rev e1)) (Leaf $ rev product))
                    . (edgeTree sn)
      }
    )

tensorN :: Disk -> SimpleColoring -> SimpleColoring 
tensorN d0 sn0 =
  let
    e1 = (perimeter sn0 d0) !! 0
    e2 = rev ((perimeter sn0 d0) !! 1)
    v0 = toIV ((endpoints e1 sn0) !! 0)
    v1 = toIV ((endpoints e1 sn0) !! 1)
  in
    execState (isolate2 e1 e2 v0
              >> isolate2 (rev e2) (rev e1) v1
              >> tensorHelper d0 
              ) sn0


tensor :: Disk -> State Stringnet ()
tensor d = state $ \sn -> ((), tensorN d sn)

-- do
--   e1 <- fmap (!! 0) (perimeter d0)
--   e2 <- fmap rev $ fmap (!! 1) (perimeterM d0)
--   v0 <- fmap (!! 0) (endpointsM e1)
--   v1 <- fmap (!! 1) (endpointsM e1)
--   isolate2 e1 e2 v0
--   isolate2 (rev e2) (rev e1) v1
--  tensorHelper d0 


contract :: Edge -> State Stringnet InteriorVertex
contract e = do
  v0 <- fmap (toIV . (!! 0)) $ endpointsM e 
  v1 <- fmap (toIV . (!! 1)) $ endpointsM e 
  rotateToEnd e v0  
  rotateToEnd (rev e) v1
  zRotate v1
  isolateL v1
  contractHelper e

leftSubTree :: Tree a -> Tree a
leftSubTree (Node x _) = x

rightSubTree :: Tree a -> Tree a
rightSubTree (Node _ y) = y

contractHelper :: Edge -> State Stringnet InteriorVertex
contractHelper contractedEdge  = state $ \sn ->
  let
    v0 = toIV $ (endpoints contractedEdge sn) !! 0
    v1 = toIV $ (endpoints contractedEdge sn) !! 1
    composition =  Contraction contractedEdge
  in
  (composition, sn
                { vertices = [composition] ++
                             [v | v <- vertices sn
                                , not $ v `elem` [v0, v1]]

                , edges = [e | e <- edges sn
                             , e /= contractedEdge
                             , e /= rev contractedEdge]

                , imageVertex = (\v -> if v `elem` [IV v0, IV v1]
                                       then IV composition
                                       else v
                          ) . (imageVertex sn)

                , edgeTree = \v ->
                    if v == IV composition
                    then Node (leftSubTree $ edgeTree sn $ IV v0)
                         (rightSubTree $ edgeTree sn $ IV v1)
                    else edgeTree sn v


                , colorCoeff = undefined

                  -- morphismLabel = (\v -> if (v == composition) 
                  --                        then  compose ((idMorphism $ treeLabel (objectLabel sn) (leftSubTree $ edgeTree sn $ IV v0))
                  --                                      `tensorM`
                  --                                        (ev $ objectLabel sn contractedEdge)
                  --                                        `tensorM`
                  --                                       (idMorphism $ treeLabel (objectLabel sn) (rightSubTree $ edgeTree sn $ IV v1))
                  --                                      )
                  --                              (tensorM (morphismLabel sn v0)
                  --                               (morphismLabel sn v1))
                  --                        else morphismLabel sn v )

                , perimeter = \d -> [e | e <- perimeter sn d
                                       , e /= contractedEdge
                                       , e /= rev contractedEdge
                                       ]
                }
  )


-- Connect the starting point of the first edge to that of the second
-- through the disk The edges e1 and e2 should be distinct elements of
-- perimeter d.
connect :: Edge -> Edge -> Disk -> State Stringnet Edge
connect e1 e2 d = state $ \sn -> 
  let connection = Connector e1 e2 d in
  ( connection
  ,
    let
      (edgeTree1, morphism1) =
        replacePlus sn (rhoI $ objectLabel sn e1)
        (Leaf e1) (Node (Leaf e1) (Leaf $ connection))
        (edgeTree sn $ start e1 sn)

      (edgeTree2, morphism2) =
        replacePlus sn (rhoI $ objectLabel sn e2)
        (Leaf e2) (Node (Leaf e2) (Leaf $ rev connection))
        (edgeTree sn $ start e2 sn)
    in

      sn
      { edges = [connection] ++ edges sn
      
      , disks = [Cut connection, Cut $ rev connection]
                ++ [d2 | d2 <- disks sn
                       , d2 /= d]
        
      , edgeTree = \v -> case () of
          _ | v ==  (start e1 sn) -> edgeTree1
            | v ==  (start e2 sn) -> edgeTree2
            | otherwise           -> edgeTree sn v
      
      , perimeter = \d0 -> case () of
          _ | d0 == Cut connection -> [connection] ++
                           (takeWhile (/= e1) $ dropWhile (/= e2) $ cycle $ perimeter sn d)
            | d0 == Cut (rev connection) -> [rev connection] ++
                                            (takeWhile (/= e2) $ dropWhile  (/= e1) $ cycle $ perimeter sn d)
            | otherwise -> perimeter sn d0
      
        -- Find index of objectlabels
      , colorCoeff = undefined

        -- morphismLabel = \v -> case () of
        --   _ | v == toIV (start e1 sn) -> morphism1 <> morphismLabel sn v
        --     | v == toIV (start e2 sn) -> morphism2 <> morphismLabel sn v
        --     | otherwise               -> morphismLabel sn v
          
      }
  )
        
addCoev :: Edge -> State Stringnet (InteriorVertex, Edge, Edge)
addCoev e = state $ \sn ->
  let mp  = Midpoint e
      fh = FirstHalf e
      sh = SecondHalf e       
  in
  ((mp, fh, sh), sn 
                { vertices =  [mp] ++ vertices sn

                , edges = [fh, sh] ++ [f | f <- edges sn
                                         , f /= e
                                         , f /= rev e]

                , edgeTree = \v -> case () of
                    _ | v == IV mp -> Node (Leaf $ rev $ FirstHalf e) (Leaf $ SecondHalf e)
                      | otherwise ->  (replace (Leaf e) (Leaf fh)) 
                        . (replace (Leaf $ rev e) (Leaf $ rev sh))
                        $ edgeTree sn v

                , perimeter =  flip (>>=) (\es ->
                                             if es == [e]
                                             then [fh, sh]
                                             else if es == [rev e]
                                             then [rev sh, rev fh]
                                             else es
                                          ) . (map return) . perimeter sn

                , colorCoeff = undefined
                  -- morphismLabel = \v -> if v == mp
                  --                       then coev $ objectLabel sn e
                  --                       else morphismLabel sn v                
                }

  )

