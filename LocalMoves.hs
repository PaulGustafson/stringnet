module LocalMoves where

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

-- Test: replacePlusH Phi (Node (Leaf (Reverse (IE
-- RightLoop))) (Node (Leaf (IE RightLeg)) (Leaf (IE RightLoop)))) (Leaf $ IE
-- RightLoop) (initialEdgeTree $ IV Main)
replacePlusH :: Coloring -> Morphism -> Tree Edge -> Tree Edge -> Tree Edge -> (Tree Edge, Tree Morphism)
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

replacePlus :: Coloring -> Morphism -> Tree Edge -> Tree Edge -> Tree Edge -> (Tree Edge, Morphism)
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
                    
           , morphismLabel = \v ->
               if v == v0
               then compose morphism
                    (morphismLabel sn v)
               else morphismLabel sn v
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
                              
                     , morphismLabel = \v ->
                         if v == v0
                         then compose (morphism)
                              (morphismLabel sn v)
                         else morphismLabel sn v
                     }
                  )



isolateHelperR :: InteriorVertex ->  Coloring -> Coloring
isolateHelperR v sn =
  let t = edgeTree sn (IV v) in
    case t of
      Node _ (Leaf _) -> sn
      Node _ (Node _ _) -> isolateHelperR v
        $ execState (associateL v t) sn
  
isolateHelperL :: InteriorVertex ->  Coloring -> Coloring
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
          
        ,  morphismLabel = \v ->
            if v == v0 
            then case (edgeTree sn (IV v0)) of
              Node y (Leaf x) ->
                zMorphism (objectLabel sn x) (treeLabel (objectLabel sn) y) (morphismLabel sn v)
           else morphismLabel sn v
        }
      )
  )


rotateToEndHelper :: Edge -> InteriorVertex -> Coloring -> Coloring
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
isolate2Helper ::  Edge -> Edge -> InteriorVertex -> Coloring -> Coloring
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

tensorN :: Disk -> Coloring -> Coloring 
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


                , morphismLabel = (\v -> if (v == composition) 
                                         then  compose ((idMorphism $ treeLabel (objectLabel sn) (leftSubTree $ edgeTree sn $ IV v0))
                                                       `tensorM`
                                                         (ev $ objectLabel sn contractedEdge)
                                                         `tensorM`
                                                        (idMorphism $ treeLabel (objectLabel sn) (rightSubTree $ edgeTree sn $ IV v1))
                                                       )
                                               (tensorM (morphismLabel sn v0)
                                                (morphismLabel sn v1))
                                         else morphismLabel sn v )

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
      , morphismLabel = \v -> case () of
          _ | v == toIV (start e1 sn) -> morphism1 <> morphismLabel sn v
            | v == toIV (start e2 sn) -> morphism2 <> morphismLabel sn v
            | otherwise               -> morphismLabel sn v
          
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

                , morphismLabel = \v -> if v == mp
                                        then coev $ objectLabel sn e
                                        else morphismLabel sn v

                
                }

  )

