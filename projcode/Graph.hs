module Graph where

import           Data.Map                       ( Map )
import qualified Data.Map                      as Map
import           Heap                           ( Heap )
import qualified Heap

type Weight = Int
type Node = String
type Graph = Map Node (Map Node Weight)

data Distance = R Int | I deriving (Show, Eq)

data Assoc a b = Assoc a b
    deriving (Show, Eq)

instance Ord Distance where
    _     <= I     = True
    I     <= _     = False
    (R i) <= (R j) = i <= j

instance (Ord b, Eq a) => Ord (Assoc a b) where
    Assoc _ y1 <= Assoc _ y2 = y1 <= y2

graph :: [(Node, Node, Weight)] -> Graph
graph xs = ins xs Map.empty
  where
    ins []               g = g
    ins ((u, v, w) : xs) g = ins xs
        $ Map.alter (Just . maybe (Map.singleton v w) (Map.insert v w)) u g

edge :: Graph -> Node -> Node -> Maybe Weight
edge g u v = Map.lookup u g >>= Map.lookup v

dijkstra :: Graph -> Node -> [Assoc Node Distance]
dijkstra g src = go (prepare g src) []
  where
    prepare g src =
        Heap.fromList
            $ map (\(n, _) -> Assoc n (if n == src then R 0 else I))
            $ Map.toList g
    go q res = case Heap.extractMin q of
        Nothing                           -> res
        Just (Assoc _              I, _ ) -> error "this should not happen"
        Just (h@(   Assoc nd (R ds)), tl) -> go
            (Heap.fromList . map f . Heap.toList $ tl)  -- this conjugation looks weird
            (h : res)
          where
            Just adjs = Map.lookup nd g
            f e@(Assoc nd w) = case (Map.lookup nd adjs, w) of
                (Nothing, _) -> e
                (Just w', I) -> Assoc nd (R $ ds + w')
                (Just w', R w) ->
                    Assoc nd (R $ if ds + w' < w then ds + w' else w)

-- a-a 0, a-b 10, a-c 5, a-d 9, a-e 7
test :: Graph
test = graph
    [ ("a", "b", 10)
    , ("a", "c", 5)
    , ("b", "c", 2)
    , ("c", "b", 3)
    , ("b", "d", 1)
    , ("c", "d", 9)
    , ("c", "e", 2)
    , ("d", "e", 4)
    , ("e", "d", 6)
    , ("e", "a", 7)
    ]
