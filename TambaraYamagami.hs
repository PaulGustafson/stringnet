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
-- TODO: Do everything wrt two complexes
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
import           Control.Monad.State
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


-----------------------------------
-- Stringnet copy-paste 
----------------------------------

-- Left and right refer to positions before the braiding operation
data Puncture = LeftPuncture | RightPuncture
  deriving (Show, Eq)

data InteriorVertex = Main | Midpoint Edge | Contraction Edge
  deriving (Show, Eq)

data Vertex = Punc Puncture | IV InteriorVertex
  deriving (Show, Eq)

--initial edges
data InitialEdge = LeftLoop | RightLoop | LeftLeg | RightLeg
  deriving (Show, Eq, Enum)

toInitialEdge :: Edge -> InitialEdge
toInitialEdge (IE ie) = ie
toInitialEdge e = error  $ "Failed to cast " ++ (show e) ++ " to InitialEdge"

instance Finite InitialEdge where
  allElements = [LeftLoop, RightLoop, LeftLeg, RightLeg]


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

instance Functor Tree where
  fmap f (Leaf l) = Leaf $ f l
  fmap f (Node a b) = Node (fmap f a) (fmap f b)

instance Foldable Tree where
  foldMap f (Leaf x) = f x
  foldMap f (Node a b) = (foldMap f a) `mappend` (foldMap f b)


data ColoredGraph = ColoredGraph
                  { vertices      :: ![InteriorVertex]
                  , edges         :: ![Edge]
                  , disks         :: ![Disk]

                  -- The edges returned by perimeter should form a
                  -- cycle (the end point of an edge should be the the
                  -- starting point of the next edges).  Additionally,
                  -- the edges should either lie in the edges of the
                  -- ColoredGraph or be the reverse of such an edge.
                  -- CCW ordering.
                  , perimeter     :: !(Disk -> [Edge])

                  -- image under contractions
                  , imageVertex    :: !(Vertex -> Vertex)     

                  , morphismLabel :: !(InteriorVertex -> Morphism)

                  -- CCW ordering, outgoing orientation
                  , edgeTree      :: !(Vertex -> Tree Edge)

                  , objectLabel   :: !(Edge -> Object)
                  }



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

-- type cast 
toIV :: Vertex -> InteriorVertex
toIV (IV v) = v

rev :: Edge -> Edge
rev (Reverse e) = e
-- MAYBE: (need to deal with Eq instance)
-- rev (TensorE a b) = TensorE (rev a) (rev b)
rev e = Reverse e


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

-- TODO: maybe put this into ColoredGraph, to make parallel with
--       perimeter also, eliminate "image"
endpoints :: Edge -> ColoredGraph -> [Vertex]
endpoints e tc = map (imageVertex tc) (initialEndpoints e)

-- Monadic versions of methods
edgeTreeM :: Vertex -> State ColoredGraph (Tree Edge)
edgeTreeM v = state $ \tc -> (edgeTree tc v, tc)


endpointsM :: Edge -> State ColoredGraph [Vertex]
endpointsM e = state $ \tc -> (endpoints e tc, tc)

perimeterM :: Disk -> State ColoredGraph [Edge]
perimeterM d = state $ \tc -> (perimeter tc d, tc)

start :: Edge -> ColoredGraph -> Vertex
start e tc = (endpoints e tc) !! 0

end :: Edge -> ColoredGraph -> Vertex
end e tc = (endpoints e tc) !! 1


treeLabel :: (Edge -> Object) -> Tree Edge -> Object
treeLabel label (Leaf e) = label e
treeLabel label (Node x y) =
  tensorO (treeLabel label x) (treeLabel label y)


-- reverseEdge :: Edge -> State ColoredGraph Edge
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


-- Test: replacePlusH Phi (Node (Leaf (Reverse (IE
-- RightLoop))) (Node (Leaf (IE RightLeg)) (Leaf (IE RightLoop)))) (Leaf $ IE
-- RightLoop) (initialEdgeTree $ IV Main)
replacePlusH :: ColoredGraph -> Morphism -> Tree Edge -> Tree Edge -> Tree Edge -> (Tree Edge, Tree Morphism)
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

tensorMTree :: Tree Morphism -> Morphism
tensorMTree (Leaf m) = m
tensorMTree (Node x y) = tensorM (tensorMTree x) (tensorMTree y)

replacePlus :: ColoredGraph -> Morphism -> Tree Edge -> Tree Edge -> Tree Edge -> (Tree Edge, Morphism)
replacePlus sn m oldSubTree newSubTree bigTree =
  let (eTree, mTree) = replacePlusH sn m oldSubTree newSubTree bigTree in
    (eTree, tensorMTree mTree)

-- TODO: debug the following 
--
-- data Side = Left | Right
--
-- associate :: Side -> InteriorVertex -> Tree Edge -> State ColoredGraph (Tree Edge)
-- associate side v0 subTree@(Node x y) =
--   let
--     (newSubTree, unaugmentedMorphism) = case side of
--       Left -> case y of
--         Node y0 y1 -> (Node x (Node y0 y1),
--                         AlphaI (treeLabel x) (treeLabel y0) (treeLabel y1))
--       Right -> case x of
--         Node x0 x1 -> (Node (Node x0 x1) y,
--                        Alpha (treeLabel x0) (treeLabel x1) (treeLabel y))
--   in      
--     state $ \tc ->
--     (newSubTree,
--          let
--             (newEdgeTree, morphism) = replacePlus
--               unaugmentedMorphism
--               subTree newSubTree $ edgeTree tc $ IV v0
--          in
--            tc
--            { edgeTree = \v ->
--                if v == IV v0
--                then newEdgeTree
--                else edgeTree tc v
                      
--            , morphismLabel = \v ->
--                if v == v0
--                then Compose morphism
--                     (morphismLabel tc v)
--                else morphismLabel tc v
--            }
--         )

-- associateL :: InteriorVertex -> Tree Edge -> State ColoredGraph (Tree Edge)
-- associateL = associate Left 

-- associateR :: InteriorVertex -> Tree Edge -> State ColoredGraph (Tree Edge)
-- associateR = associate Right



--  Test: 
--  let a = associateL Main (Node (Leaf (Reverse (IE RightLoop))) (Node (Leaf (IE RightLeg)) (Leaf (IE RightLoop)))) 
--  let tc2 = execState a initialTC
--  edgeTree tc2 $ IV Main

associateL :: InteriorVertex -> Tree Edge -> State ColoredGraph (Tree Edge)
associateL v0 subTree@(Node x yz) =
  case yz of
    Node y z ->
      let newSubTree = (Node (Node x y) z) in
        state $ \tc ->
        (newSubTree,
         let
           (newEdgeTree, morphism) = replacePlus tc
               (alphaI (treeLabel (objectLabel tc) x) (treeLabel (objectLabel tc) y)
                           (treeLabel (objectLabel tc) z))
               subTree newSubTree $ edgeTree tc $ IV v0
         in
           tc
           { edgeTree = \v ->
               if v == IV v0
               then newEdgeTree
               else edgeTree tc v
                    
           , morphismLabel = \v ->
               if v == v0
               then compose morphism
                    (morphismLabel tc v)
               else morphismLabel tc v
           }
        )


associateR :: InteriorVertex -> Tree Edge -> State ColoredGraph (Tree Edge)
associateR v0 subTree@(Node xy z) =
  case xy of
    Node x y ->
      let newSubTree = (Node x (Node y z)) in
        state $ \tc ->
                  (newSubTree,
                   let
                     (newEdgeTree, morphism) = replacePlus tc
                       (alpha
                        (treeLabel (objectLabel tc) x)
                        (treeLabel (objectLabel tc) y)
                        (treeLabel (objectLabel tc) z)
                       )
                       subTree newSubTree $ edgeTree tc $ IV v0
                   in
                     tc
                     { edgeTree = \v ->
                         if v == IV v0
                         then newEdgeTree
                         else edgeTree tc v
                              
                     , morphismLabel = \v ->
                         if v == v0
                         then compose (morphism)
                              (morphismLabel tc v)
                         else morphismLabel tc v
                     }
                  )



isolateHelperR :: InteriorVertex ->  ColoredGraph -> ColoredGraph
isolateHelperR v tc =
  let t = edgeTree tc (IV v) in
    case t of
      Node _ (Leaf _) -> tc
      Node _ (Node _ _) -> isolateHelperR v
        $ execState (associateL v t) tc
  
isolateHelperL :: InteriorVertex ->  ColoredGraph -> ColoredGraph
isolateHelperL v tc =
  let t = edgeTree tc (IV v) in
    case t of
      Node (Leaf _) _ -> tc
      Node (Node _ _) _ -> isolateHelperL v
        $ execState (associateR v t) tc
  
     
-- Turns the far right leaf into a depth one leaf  
isolateR :: InteriorVertex -> State ColoredGraph ()
isolateR v0 = state $ \tc ->
  ((), isolateHelperR v0 tc)

isolateL :: InteriorVertex -> State ColoredGraph ()
isolateL v0 = state $ \tc ->
  ((), isolateHelperL v0 tc)

swap :: Tree a -> Tree a
swap (Node x y) = Node y x

-- 
zMorphism :: Object -> Object -> Morphism -> Morphism
zMorphism xl yl m =
  ((idMorphism xl) `tensorM`  (rho yl))
  <> ((idMorphism xl) `tensorM` ((idMorphism yl) `tensorM` (ev $ star xl))) -- X (Y 1)
  <> ((idMorphism xl) `tensorM` (alpha yl xl (star xl))) -- X (Y (X *X))
  <> ((idMorphism xl) `tensorM` (m `tensorM` (idMorphism $ star xl))) -- X 1 *X -> X ((Y X) *X)
  <> ((pivotalJI xl) `tensorM` (lambdaI $ star xl))       -- **X *X -> X (1 *X)
  <> (coev $ star xl)  -- 1 -> **X *X

-- rotation of the rightmost edge in v0's to the leftside
zRotate :: InteriorVertex -> State ColoredGraph ()
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
                zMorphism (objectLabel tc x) (treeLabel (objectLabel tc) y) (morphismLabel tc v)
           else morphismLabel tc v
        }
      )
  )


rotateToEndHelper :: Edge -> InteriorVertex -> ColoredGraph -> ColoredGraph
rotateToEndHelper e0 v0 tc = 
  let
    es = flatten $ edgeTree tc (IV v0)
  in
    if es !! (length es - 1) == e0
    then tc
    else rotateToEndHelper e0 v0 $ execState (zRotate v0) tc

rotateToEnd :: Edge -> InteriorVertex -> State ColoredGraph ()
rotateToEnd e0 v0 = (state $ \tc ->
  ((), rotateToEndHelper e0 v0 tc))  >> isolateR v0

elemT :: Eq a => a -> Tree a -> Bool
elemT u = (elem u) . flatten 

minimalSuperTree :: (Eq a) => a -> a -> Tree a -> Tree a
minimalSuperTree a1 a2 t@(Node x y) 
  | a1 `elemT` x && a2 `elemT` x = minimalSuperTree a1 a2 x
  | a1 `elemT` y && a2 `elemT` y = minimalSuperTree a1 a2 y
  | otherwise                    = t


-- Easy optimization: calculate t from previous t
isolate2Helper ::  Edge -> Edge -> InteriorVertex -> ColoredGraph -> ColoredGraph
isolate2Helper e1 e2 v0 tc0 =
  let
    t = minimalSuperTree e1 e2 (edgeTree tc0 $ IV v0)
  in
    case t of
      Node x y -> 
        case x of
          Node _ _ -> isolate2Helper e1 e2 v0 $ execState (associateR v0 t) tc0
          Leaf _ -> case y of
              Node _ _ -> isolate2Helper e1 e2 v0 $ execState (associateL v0 t) tc0
              Leaf _ -> tc0

-- Put (rev) e1 and e2 on same node
isolate2 :: Edge -> Edge -> InteriorVertex  -> State ColoredGraph ()
isolate2 e1 e2 v0 = state $ \tc0 ->
  let
    firstEdge = (flatten $ edgeTree tc0 $ IV v0) !! 0
    tc1 = if (e2 == firstEdge)
          then execState (zRotate v0) tc0
          else tc0
  in   
    ((), isolate2Helper e1 e2 v0 tc1)


-- The disk's perimeter should only have two edges
tensorHelper :: Disk -> State ColoredGraph Edge
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

tensorN :: Disk -> ColoredGraph -> ColoredGraph 
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


tensor :: Disk -> State ColoredGraph ()
tensor d = state $ \tc -> ((), tensorN d tc)

-- do
--   e1 <- fmap (!! 0) (perimeter d0)
--   e2 <- fmap rev $ fmap (!! 1) (perimeterM d0)
--   v0 <- fmap (!! 0) (endpointsM e1)
--   v1 <- fmap (!! 1) (endpointsM e1)
--   isolate2 e1 e2 v0
--   isolate2 (rev e2) (rev e1) v1
--  tensorHelper d0 


contract :: Edge -> State ColoredGraph InteriorVertex
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

contractHelper :: Edge -> State ColoredGraph InteriorVertex
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
                                         then  compose ((idMorphism $ treeLabel (objectLabel tc) (leftSubTree $ edgeTree tc $ IV v0))
                                                       `tensorM`
                                                         (ev $ objectLabel tc contractedEdge)
                                                         `tensorM`
                                                        (idMorphism $ treeLabel (objectLabel tc) (rightSubTree $ edgeTree tc $ IV v1))
                                                       )
                                               (tensorM (morphismLabel tc v0)
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
connect :: Edge -> Edge -> Disk -> State ColoredGraph Edge
connect e1 e2 d = state $ \tc -> 
  let connection = Connector e1 e2 d in
  ( connection
  ,
    let
      (edgeTree1, morphism1) =
        replacePlus tc (rhoI $ objectLabel tc e1)
        (Leaf e1) (Node (Leaf e1) (Leaf $ connection))
        (edgeTree tc $ start e1 tc)

      (edgeTree2, morphism2) =
        replacePlus tc (rhoI $ objectLabel tc e2)
        (Leaf e2) (Node (Leaf e2) (Leaf $ rev connection))
        (edgeTree tc $ start e2 tc)
    in

      tc
      { edges = [connection] ++ edges tc
      
      , disks = [Cut connection, Cut $ rev connection]
                ++ [d2 | d2 <- disks tc
                       , d2 /= d]
        
      , edgeTree = \v -> case () of
          _ | v ==  (start e1 tc) -> edgeTree1
            | v ==  (start e2 tc) -> edgeTree2
            | otherwise           -> edgeTree tc v
      
      , perimeter = \d0 -> case () of
          _ | d0 == Cut connection -> [connection] ++
                           (takeWhile (/= e1) $ dropWhile (/= e2) $ cycle $ perimeter tc d)
            | d0 == Cut (rev connection) -> [rev connection] ++
                                            (takeWhile (/= e2) $ dropWhile  (/= e1) $ cycle $ perimeter tc d)
            | otherwise -> perimeter tc d0
      
        -- Find index of objectlabels
      , morphismLabel = \v -> case () of
          _ | v == toIV (start e1 tc) -> morphism1 <> morphismLabel tc v
            | v == toIV (start e2 tc) -> morphism2 <> morphismLabel tc v
            | otherwise               -> morphismLabel tc v
          
      }
  )
        
addCoev :: Edge -> State ColoredGraph (InteriorVertex, Edge, Edge)
addCoev e = state $ \tc ->
  let mp  = Midpoint e
      fh = FirstHalf e
      sh = SecondHalf e       
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
                                        then coev $ objectLabel tc e
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

objectLabel0 :: BasisElement -> Edge -> Object
objectLabel0 be (IE e) = toObject $ initialLabel be e
objectLabel0 be (FirstHalf e) = objectLabel0 be e
objectLabel0 be (SecondHalf e) = objectLabel0 be e
objectLabel0 be (Connector _ _ _) = toObject one
objectLabel0 be (TensorE e1 e2)
  = tensorO (objectLabel0 be e1) (objectLabel0 be e2)
objectLabel0 be (Reverse e)  = star (objectLabel0 be e)

initialColoredGraph :: BasisElement -> ColoredGraph
initialColoredGraph basisElement =
  ColoredGraph { vertices = [Main]
               , edges    = map IE [LeftLoop, RightLoop, LeftLeg, RightLeg]
               , disks    = [Outside, LeftDisk, RightDisk]
               , imageVertex    = id
               , perimeter = initialPerimeter
               , morphismLabel =  \m ->
                   case m of Main
                               -> morphismFromBE basisElement
               , edgeTree = initialEdgeTree
               , objectLabel = objectLabel0 basisElement
               }

braid :: State ColoredGraph ()            
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
midMorphism :: BasisElement -> State ColoredGraph () -> Morphism
midMorphism be st =
  let
    cg = (execState st . initialColoredGraph) be
  in
    morphismLabel cg (vertices cg !! 0) 

finalSN :: BasisElement -> ColoredGraph
finalSN = execState braid . initialColoredGraph

finalVertex :: BasisElement -> InteriorVertex
finalVertex be = vertices (finalSN be) !! 0

finalMorphism :: BasisElement -> Morphism
finalMorphism be = morphismLabel (finalSN be) (finalVertex be)

-- finalEdgeTree :: Tree Edge
-- finalEdgeTree = edgeTree finalSN $ IV finalVertex


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

  --  , stringnet :: Stringnet -- keep track of edge labels after every morphism 
  
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
--     len = length $ summandsO $ substO $ treeLabel
--       $ initialEdgeTree $ IV Main
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
tensorInv2 :: (Num a) =>  (SimpleObject -> SimpleObject -> a) -> SimpleObject -> [a]
tensorInv2 f so = map (uncurry f) $ tensorInv so


tensorO :: Object -> Object -> Object
tensorO o1 o2 = object $
     let jointMultiplicity a b
           = (multiplicity o1 a) * (multiplicity o2 b)
     in
       sum . tensorInv2 jointMultiplicity


-- Go through the direct sum of simple objects in the domain and range
-- and check if each pair is (M,M)
tensorM :: Morphism -> Morphism -> Morphism
tensorM m1 m2 =
  let kron so1 so2 = kronecker (subMatrix m1 so1) (subMatrix m2 so2)
  in
    morphism (tensorO (domain m1) (domain m2))
    (tensorO (codomain m1) (codomain m2))
    (foldl directSum emptyMatrix . (tensorInv2 kron))


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
-- substO :: (InitialEdge -> SimpleObject) -> Object -> Object
-- substO il o0 =  case o0 of
--   OVar ie -> toObject $ il ie
--   One -> toObject $ AE (AElement 0)
--   Star o -> star $ substO il o
--   TensorO o1 o2 -> (substO il o1) `tensorO` (substO il o2)

    

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
        -- other components are 0, so get killed during composition
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

type InitialData = (InitialEdge -> SimpleObject, Morphism)

-- standard (nondiagrammatic) order
compose :: Morphism -> Morphism -> Morphism
compose m1 m2 =
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
         ++ (show m2) ++ " has codomain: "
         ++ (show $ codomain m2) ++ ". "
         ++ (show m1) ++ " has domain: " ++ (show $ domain m1)

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
--   substO il $ treeLabel (objectLabel initialColoredGraph) (initialEdgeTree $ IV Main)

-- TODO: modify other functions to take non-simpleObject labels
-- and remove this function
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
data BasisElement = BasisElement
  { initialLabel :: InitialEdge -> SimpleObject
  , oneIndex :: Int
  }

morphismFromBE :: BasisElement -> Morphism
morphismFromBE basisElement =
  oneIndexToMorphism (toCodomain (toObject . initialLabel basisElement))
  $ oneIndex basisElement

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




instance Finite BasisElement where
  allElements =  concat $ map (uncurry $ \il ms ->
                                 [ BasisElement il m
                                 |  m <- ms
                                 ]
                             )
                 [(il, morphismSet $ toCodomain $ toObject . il)
                 | il <- allInitialLabels]
                        

-- ------------------------------------------------------
-- --  Initial labels
-- ------------------------------------------------------

morphismSet :: Object -> [Int]
morphismSet codomain0 =
  if multiplicity codomain0 one > 0
  then [0..(multiplicity codomain0 one)]
  else []


-- finalMorphism :: BasisElement -> Morphism
-- finalMorphism be =
--   let
--     initialCodomain = toCodomainSO $ initialLabel be
--     initialMorphism = oneIndexToMorphism
--       initialCodomain $ oneIndex be
--   in
--     substM (initialLabel be) initialMorphism finalMorphism
    
answer = map finalMorphism (allElements :: [BasisElement])



