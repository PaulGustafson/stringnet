-- This program calculates the TVBW representation of the braid
-- generator in terms of the structural morphisms of a spherical
-- category.  To do this, it follows Table 3 of the Finiteness for DW
-- MCG reps paper.
--
-- We encode a stringnet as a marked CW-complex.
-- For now, all duals are right duals.
--
--
-- TODO: Calculate an actual R-matrix of a simple TY category.
--
-- TODO: Style refactoring
--     - comment top-level (exported) functions
--     - consistent use of State TwoComplex
--     
-- TODO: Make all functions total
--       - Get rid of toIV type casts
--
-- TODO: unit tests
--
-- Ideas: Make a LocalMoves type.
--        Add left duals
--        Refactor using Simplex n
--

module Stringnet where

import           Control.Monad.State
import           Data.List
import           Data.Semigroup
import qualified Data.Tree as T
  

-- Left and right refer to positions before the braiding operation
data Puncture = LeftPuncture | RightPuncture
  deriving (Show, Eq)

data InteriorVertex = Main | Midpoint Edge | Contraction Edge
  deriving (Show, Eq)

data Vertex = Punc Puncture | IV InteriorVertex
  deriving (Show, Eq)

--initial edges
data InitialEdge = LeftLoop | RightLoop | LeftLeg | RightLeg
  deriving (Show, Eq)


-- Orientations of initial edges are given by arrows in the figures in
-- the paper
data Edge =
  -- initial edges
  IE InitialEdge

  -- result of adding coev vertex (--(e)--> (coev e) --(e)-->)
  | FirstHalf Edge | SecondHalf Edge

  -- connects the start of the two edges with a 1 in the disk
  | Connector Edge Edge Disk

   -- stick together parallel edges
  | TensorE Edge Edge

  -- don't use this constructor except to pattern match, use "rev"
  -- instead
  | Reverse Edge  
          deriving (Show, Eq)


data Disk =
  -- initial disks
  Outside | LeftDisk | RightDisk

  -- Edge should be of type Connect
  | Cut Edge          
          deriving (Show, Eq)


data Tree a = Leaf a | Node (Tree a) (Tree a)
            deriving (Eq, Show)


data Stringnet = Stringnet
                  { vertices      :: ![InteriorVertex]
                  , edges         :: ![Edge]
                  , disks         :: ![Disk]

                  -- The edges returned by perimeter should form a
                  -- cycle (the end point of an edge should be the the
                  -- starting point of the next edges).  Additionally,
                  -- the edges should either lie in the edges of the
                  -- Stringnet or be the reverse of such an edge.  CCW
                  -- ordering.
                  , perimeter     :: !(Disk -> [Edge])

                  -- image under contractions
                  , imageVertex    :: !(Vertex -> Vertex)     

                  -- TODO: Change to Tree based on tensor structure
                  , morphismLabel :: !(InteriorVertex -> Morphism)   

                  -- CCW ordering, outgoing orientation
                  , edgeTree      :: !(Vertex -> Tree Edge)  
                  }


data Object = OVar InitialEdge -- Object variable labeling edge
            | One
            | Star Object  -- Don't use this constructor except to
                           -- pattern match, use "star" instead
            | TensorO Object Object
            deriving (Show)  
                                                           
data Morphism = Phi
              | Id Object
              | Lambda Object -- 1 V -> V
              | LambdaI Object
              | Rho Object    -- V 1 -> V
              | RhoI Object
              | Alpha Object Object Object -- associator (xy)z = x(yz)
              | AlphaI Object Object Object -- inverse associator
              | Coev Object   --  right coev
              | Ev Object     -- right ev
              | TensorM Morphism Morphism
              | PivotalJ Object -- X -> X**
              | PivotalJI Object -- X** -> X
              | Compose Morphism Morphism
              deriving (Show)


-- domain :: Morphism -> Object
-- domain Phi = 

instance Semigroup Morphism where
  a <> b = Compose a b

toDataTree :: Tree a -> T.Tree (Maybe a)
toDataTree (Leaf x) = T.Node (Just x) []
toDataTree (Node x y) = T.Node Nothing [toDataTree x, toDataTree y]

-- Pretty print
pprint :: (Show a) => Tree a-> IO ()
pprint = putStr. T.drawTree . fmap (\x -> case x of
                                       Nothing -> "+"
                                       Just e -> show e
                                   )
                                   . toDataTree

-- type cast 
toIV :: Vertex -> InteriorVertex
toIV (IV v) = v

rev :: Edge -> Edge
rev (Reverse e) = e
-- TODO: (need to deal with Eq instance)
-- rev (TensorE a b) = TensorE (rev a) (rev b)
rev e = Reverse e

star :: Object -> Object
star (Star o) = o
star o = Star o

-- endpoints before finding the images of the vertices under
-- contractions
initialEndpoints :: Edge -> [Vertex]
initialEndpoints edge  = case edge of
  IE LeftLoop  -> [IV Main, IV Main]
  IE RightLoop -> [IV Main, IV Main]
  IE LeftLeg   -> [IV Main, Punc LeftPuncture]
  IE RightLeg  -> [IV Main, Punc RightPuncture]
  FirstHalf e -> [(initialEndpoints e) !! 0, IV $ Midpoint e]
  SecondHalf e -> [IV $ Midpoint e, (initialEndpoints e) !! 1]
  Connector e1 e2 _ -> [initialStart e1, initialStart e2]
  TensorE e1 _ -> initialEndpoints e1
  Reverse e -> reverse (initialEndpoints e)

initialStart :: Edge -> Vertex
initialStart e = (initialEndpoints e) !! 0

initialEnd :: Edge -> Vertex
initialEnd e = (initialEndpoints e) !! 1

-- TODO: maybe put this into Stringnet, to make parallel with
--       perimeter also, eliminate "image"
endpoints :: Edge -> Stringnet -> [Vertex]
endpoints e tc = map (imageVertex tc) (initialEndpoints e)

-- Monadic versions of methods
edgeTreeM :: Vertex -> State Stringnet (Tree Edge)
edgeTreeM v = state $ \tc -> (edgeTree tc v, tc)


endpointsM :: Edge -> State Stringnet [Vertex]
endpointsM e = state $ \tc -> (endpoints e tc, tc)

perimeterM :: Disk -> State Stringnet [Edge]
perimeterM d = state $ \tc -> (perimeter tc d, tc)

start :: Edge -> Stringnet -> Vertex
start e tc = (endpoints e tc) !! 0

end :: Edge -> Stringnet -> Vertex
end e tc = (endpoints e tc) !! 1


objectLabel :: Edge -> Object
objectLabel (IE e) = OVar e
objectLabel (FirstHalf e) = objectLabel e
objectLabel (SecondHalf e) = objectLabel e
objectLabel (Connector _ _ _) = One
objectLabel (TensorE e1 e2) = TensorO (objectLabel e1) (objectLabel e2)
objectLabel (Reverse e)  = star (objectLabel e)


treeLabel :: Tree Edge -> Object
treeLabel (Leaf e) = objectLabel e
treeLabel (Node x y) = TensorO (treeLabel x) (treeLabel y)


-- reverseEdge :: Edge -> State Stringnet Edge
-- reverseEdge e0 = state $ \tc ->
--   (rev e0
--   , tc
--        { edges = [rev e0] ++ [e | e <- edges tc
--                                     , e /= e0] })

flatten :: Tree a -> [a]
flatten (Leaf x) = [x] 
flatten (Node x y) = (flatten x) ++ (flatten y)

replace :: (Eq a) => Tree a -> Tree a -> Tree a -> Tree a
replace subTree1 subTree2 bigTree = 
  if bigTree == subTree1
  then subTree2
  else case bigTree of
    Leaf x  -> Leaf x
    Node x y -> Node (replace subTree1 subTree2 x)
                (replace subTree1 subTree2 y)

associateL :: InteriorVertex -> Tree Edge -> State Stringnet (Tree Edge)
associateL v0 subTree@(Node x yz) =
  case yz of
    Node y z ->
      let newSubTree = (Node (Node x y) z) in
        state $ \tc ->
        (newSubTree, 
         tc
         { edgeTree = \v ->
             if v == IV v0
             then replace subTree newSubTree $ edgeTree tc v
             else edgeTree tc v
                  
         , morphismLabel = \v ->
             if v == v0
             then Compose (AlphaI (treeLabel x) (treeLabel y)
                           (treeLabel z))
                  (morphismLabel tc v)
             else morphismLabel tc v
         }
        )

associateR :: InteriorVertex -> Tree Edge -> State Stringnet (Tree Edge)
associateR v0 subTree@(Node xy z) =
  case xy of
    Node x y ->
      let newSubTree = (Node x (Node y z)) in
        state $ \tc ->
                  (newSubTree,
                   tc
                    { edgeTree = \v ->
                        if v == IV v0
                        then replace subTree newSubTree $ edgeTree tc v
                        else edgeTree tc v
                         
                    , morphismLabel = \v ->
                        if v == v0
                        then Compose (Alpha (treeLabel x)
                                      (treeLabel y) (treeLabel z))
                             (morphismLabel tc v)
                        else morphismLabel tc v
                    }
                  )



isolateHelperR :: InteriorVertex ->  Stringnet -> Stringnet
isolateHelperR v tc =
  let t = edgeTree tc (IV v) in
    case t of
      Node _ (Leaf x) -> tc
      Node _ (Node x y) -> isolateHelperR v
        $ execState (associateL v t) tc
  
isolateHelperL :: InteriorVertex ->  Stringnet -> Stringnet
isolateHelperL v tc =
  let t = edgeTree tc (IV v) in
    case t of
      Node (Leaf x) _ -> tc
      Node (Node x y) _ -> isolateHelperL v
        $ execState (associateR v t) tc
  
     
-- Turns the far right leaf into a depth one leaf  
isolateR :: InteriorVertex -> State Stringnet ()
isolateR v0 = state $ \tc ->
  ((), isolateHelperR v0 tc)

isolateL :: InteriorVertex -> State Stringnet ()
isolateL v0 = state $ \tc ->
  ((), isolateHelperL v0 tc)

swap :: Tree a -> Tree a
swap (Node x y) = Node y x

-- 
zMorphism :: Object -> Object -> Morphism -> Morphism
zMorphism xl yl m =
  ((Id xl) `TensorM`  (Rho yl))
  <> ((Id xl) `TensorM` ((Id yl) `TensorM` (Ev $ star xl))) -- X (Y 1)
  <> ((Id xl) `TensorM` (Alpha yl xl (star xl))) -- X (Y (X *X))
  <> ((Id xl) `TensorM` (m `TensorM` (Id $ star xl))) -- X 1 *X -> X ((Y X) *X)
  <> ((PivotalJI xl) `TensorM` (LambdaI $ star xl))       -- **X *X -> X (1 *X)
  <> (Coev $ star xl)  -- 1 -> **X *X

-- rotation of the rightmost edge in v0's to the leftside
zRotate :: InteriorVertex -> State Stringnet ()
zRotate v0 =
  isolateR v0 >> 
  ( state $ \tc ->
      ((), tc
        { edgeTree = \v ->
            (
              if v == IV v0
              then swap 
              else id
            )
            $ edgeTree tc v
          
        ,  morphismLabel = \v ->
            if v == v0 
            then case (edgeTree tc (IV v0)) of
              Node y (Leaf x) ->
                zMorphism (objectLabel x) (treeLabel y) (morphismLabel tc v)
           else morphismLabel tc v
        }
      )
  )


rotateToEndHelper :: Edge -> InteriorVertex -> Stringnet -> Stringnet
rotateToEndHelper e0 v0 tc = 
  let
    es = flatten $ edgeTree tc (IV v0)
  in
    if es !! (length es - 1) == e0
    then tc
    else rotateToEndHelper e0 v0 $ execState (zRotate v0) tc

rotateToEnd :: Edge -> InteriorVertex -> State Stringnet ()
rotateToEnd e0 v0 = (state $ \tc ->
  ((), rotateToEndHelper e0 v0 tc))  >> isolateR v0

elemT u = (elem u) . flatten 

minimalSuperTree :: (Eq a) => a -> a -> Tree a -> Tree a
minimalSuperTree a1 a2 t@(Node x y) 
  | a1 `elemT` x && a2 `elemT` x = minimalSuperTree a1 a2 x
  | a1 `elemT` y && a2 `elemT` y = minimalSuperTree a1 a2 y
  | otherwise                    = t


-- Easy optimization: calculate t from previous t
isolate2Helper ::  Edge -> Edge -> InteriorVertex -> Stringnet -> Stringnet
isolate2Helper e1 e2 v0 tc0 =
  let
    t = minimalSuperTree e1 e2 (edgeTree tc0 $ IV v0)
  in
    case t of
      Node x y -> 
        case x of
          Node x1 x2 -> isolate2Helper e1 e2 v0 $ execState (associateR v0 t) tc0
          Leaf x0 -> case y of
              Node y1 y2 -> isolate2Helper e1 e2 v0 $ execState (associateL v0 t) tc0
              Leaf y0 -> tc0

-- Put (rev) e1 and e2 on same node
isolate2 :: Edge -> Edge -> InteriorVertex  -> State Stringnet ()
isolate2 e1 e2 v0 = state $ \tc0 ->
  let
    firstEdge = (flatten $ edgeTree tc0 $ IV v0) !! 0
    tc1 = if (e2 == firstEdge)
          then execState (zRotate v0) tc0
          else tc0
  in   
    ((), isolate2Helper e1 e2 v0 tc1)


-- The disk's perimeter should only have two edges
tensorHelper :: Disk -> State Stringnet Edge
tensorHelper d0 =
  state $ \tc0 ->
  let
    e1 = (perimeter tc0 d0) !! 0
    e2 = rev ((perimeter tc0 d0) !! 1)
    v0 = toIV ((endpoints e1 tc0) !! 0)
    v1 = toIV ((endpoints e1 tc0) !! 1)
    product = TensorE e1 e2
    edgeImage e = case () of
      _ | e `elem` [e1, e2] -> product
        | e `elem` [rev e1, rev e2] -> rev product
        | otherwise -> e

    tc =  execState (isolate2 e1 e2 v0
                     >> isolate2 (rev e2) (rev e1) v1
                    ) tc0
  in
    ( product
    , tc
      { edges = map edgeImage (edges tc)
      , disks = [d | d <- disks tc
                   , d /= d0]
      , perimeter = (map edgeImage) . (perimeter tc)
      , edgeTree =  (replace (Node (Leaf e1) (Leaf e2)) (Leaf product))
                    . (replace (Node (Leaf $ rev e2) (Leaf $ rev e1)) (Leaf $ rev product))
                    . (edgeTree tc)
      }
    )

tensorN :: Disk -> Stringnet -> Stringnet 
tensorN d0 tc0 =
  let
    e1 = (perimeter tc0 d0) !! 0
    e2 = rev ((perimeter tc0 d0) !! 1)
    v0 = toIV ((endpoints e1 tc0) !! 0)
    v1 = toIV ((endpoints e1 tc0) !! 1)
  in
    execState (isolate2 e1 e2 v0
              >> isolate2 (rev e2) (rev e1) v1
              >> tensorHelper d0 
              ) tc0


tensor :: Disk -> State Stringnet ()
tensor d = state $ \tc -> ((), tensorN d tc)

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
leftSubTree (Node x y) = x

rightSubTree :: Tree a -> Tree a
rightSubTree (Node x y) = y

contractHelper :: Edge -> State Stringnet InteriorVertex
contractHelper contractedEdge  = state $ \tc ->
  let
    v0 = toIV $ (endpoints contractedEdge tc) !! 0
    v1 = toIV $ (endpoints contractedEdge tc) !! 1
    composition =  Contraction contractedEdge
  in
  (composition, tc
                { vertices = [composition] ++
                             [v | v <- vertices tc
                                , not $ v `elem` [v0, v1]]

                , edges = [e | e <- edges tc
                             , e /= contractedEdge
                             , e /= rev contractedEdge]

                , imageVertex = (\v -> if v `elem` [IV v0, IV v1]
                                       then IV composition
                                       else v
                          ) . (imageVertex tc)

                , edgeTree = \v ->
                    if v == IV composition
                    then Node (leftSubTree $ edgeTree tc $ IV v0)
                         (rightSubTree $ edgeTree tc $ IV v1)
                    else edgeTree tc v


                , morphismLabel = (\v -> if (v == composition) 
                                         then  Compose (Ev $ objectLabel contractedEdge)
                                               (TensorM (morphismLabel tc v0)
                                                (morphismLabel tc v1))
                                         else morphismLabel tc v )

                , perimeter = \d -> [e | e <- perimeter tc d
                                       , e /= contractedEdge
                                       , e /= rev contractedEdge
                                       ]
                }
  )


-- Connect the starting point of the first edge to that of the second
-- through the disk The edges e1 and e2 should be distinct elements of
-- perimeter d.
connect :: Edge -> Edge -> Disk -> State Stringnet Edge
connect e1 e2 d = state $ \tc -> 
  let connection = Connector e1 e2 d in
  ( connection
  , tc
      { edges = [connection] ++ edges tc

      , disks = [Cut connection, Cut $ rev connection]
                ++ [d2 | d2 <- disks tc
                       , d2 /= d]

      , edgeTree = \v -> case () of
        _ | v ==  (start e1 tc) -> replace (Leaf e1)
                                (Node (Leaf e1) (Leaf $ connection))
                                $ edgeTree tc v
          | v ==  (start e2 tc) -> replace (Leaf e2)
                                (Node (Leaf e2) (Leaf $ rev connection))
                                $ edgeTree tc v
          | otherwise        -> edgeTree tc v

      , perimeter = \d0 -> case () of
          _ | d0 == Cut connection -> [connection] ++
              (takeWhile (/= e1) $ dropWhile (/= e2) $ cycle $ perimeter tc d)
            | d0 == Cut (rev connection) -> [rev connection] ++
              (takeWhile (/= e2) $ dropWhile  (/= e1) $ cycle $ perimeter tc d)
            | otherwise -> perimeter tc d0

      , morphismLabel = \v -> case () of
        _ | v == toIV (start e1 tc) -> (RhoI $ objectLabel e1) <> morphismLabel tc v
          | v == toIV (start e2 tc) -> (RhoI $ objectLabel e2) <> morphismLabel tc v
          | otherwise        -> morphismLabel tc v
          
      }
  )
        
addCoev :: Edge -> State Stringnet (InteriorVertex, Edge, Edge)
addCoev e = state $ \tc ->
  let mp  = Midpoint e
      fh = FirstHalf e
      sh = SecondHalf e
      v0 = (endpoints e tc) !! 0
      v1 = (endpoints e tc) !! 1
  in
  ((mp, fh, sh), tc 
                { vertices =  [mp] ++ vertices tc

                , edges = [fh, sh] ++ [f | f <- edges tc
                                         , f /= e
                                         , f /= rev e]

                , edgeTree = \v -> case () of
                    _ | v == IV mp -> Node (Leaf $ rev $ FirstHalf e) (Leaf $ SecondHalf e)
                      | otherwise ->  (replace (Leaf e) (Leaf fh)) 
                        . (replace (Leaf $ rev e) (Leaf $ rev sh))
                        $ edgeTree tc v

                , perimeter =  flip (>>=) (\es ->
                                             if es == [e]
                                             then [fh, sh]
                                             else if es == [rev e]
                                             then [rev sh, rev fh]
                                             else es
                                          ) . (map return) . perimeter tc

                , morphismLabel = \v -> if v == mp
                                        then Coev $ objectLabel e
                                        else morphismLabel tc v

                
                }

  )


-- perimeter before contractions
initialPerimeter :: Disk -> [Edge]
initialPerimeter Outside    = [IE LeftLoop, IE RightLoop]
initialPerimeter LeftDisk   =
  [Reverse $ IE LeftLoop, IE LeftLeg, Reverse $ IE LeftLeg]
initialPerimeter RightDisk  =
  [Reverse $ IE RightLoop, IE RightLeg, Reverse $ IE RightLeg]


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


-- tcX corresponds to figure number X from the braid figure in the paper
initialTC = Stringnet { vertices = [Main]
                       , edges    = map IE [LeftLoop, RightLoop, LeftLeg, RightLeg]
                       , disks    = [Outside, LeftDisk, RightDisk]
                       , imageVertex    = id
                       , perimeter = initialPerimeter
                       , morphismLabel  =  (\m -> case m of Main -> Phi)
                       , edgeTree = initialEdgeTree
                       }

            
braid = do
  (top1,l1,r1) <- addCoev $ IE LeftLoop
  (top2,l2,r2) <- addCoev $ IE LeftLeg
  (top3,r13,l3) <- addCoev r1
  (top4,l4,r4) <- addCoev $ IE RightLoop
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


finalTC = execState braid initialTC
finalVertex = vertices finalTC !! 0
finalMorphism = morphismLabel finalTC finalVertex


-- testDisk = evalState braid initialTC
-- testPerim = perimeter finalTC testDisk
-- testE1 = testPerim !! 0
-- testE2 = rev (testPerim !! 1)
-- testV0 = toIV $ (endpoints testE1 finalTC) !! 0
-- testV1 = toIV $ (endpoints testE1 finalTC) !! 1

-- testIndex tc e v = elemIndex e $ flatten $ edgeTree tc $ IV v

-- ti1 = testIndex finalTC testE1 testV0
-- ti2 = testIndex finalTC testE2 testV0

-- TESTS

-- PASS
-- testTC = execState (isolate2 LeftLoop LeftLeg Main) initialTC
-- pprint $ edgeTree testTC Main

-- PASS
-- test =  execState (isolate2 (rev RightLoop) LeftLoop  Main) initialTC
-- p =  pprint $ edgeTree testTC2 Main

-- PASS
-- testTC3 = execState  (zRotate Main) initialTC

-- PASS
-- test = execState (rotateToEnd RightLoop Main) initialTC

-- test = execState (
--   do
--     zRotate Main
--     zRotate Main
--     zRotate Main
--     isolateR Main
--   )
--   initialTC

-- p x =  pprint $ edgeTree x $ IV Main


