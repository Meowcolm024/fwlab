module Graph where

import           Data.Map                       ( Map )
import qualified Data.Map                      as Map
import           Heap                           ( Heap )
import qualified Heap


type Node = String
type Graph = Map Node (Map Node Distance)

data Distance = R Int | I deriving (Show, Eq)

data Assoc a b = Assoc a b
    deriving (Show, Eq)

instance Ord Distance where
    _     <= I     = True
    I     <= _     = False
    (R i) <= (R j) = i <= j

infixl 6 |+|
(|+|) :: Distance -> Distance -> Distance
(|+|) I     _     = I
(|+|) _     I     = I
(|+|) (R n) (R m) = R (n + m)

instance (Ord b, Eq a) => Ord (Assoc a b) where
    Assoc _ y1 <= Assoc _ y2 = y1 <= y2

graph :: [(Node, Node, Distance)] -> Graph
graph xs = ins xs Map.empty
  where
    ins []               g = g
    ins ((u, v, w) : xs) g = ins xs
        $ Map.alter (Just . maybe (Map.singleton v w) (Map.insert v w)) u g

edge :: Graph -> Node -> Node -> Maybe Distance
edge g u v = Map.lookup u g >>= Map.lookup v

dijkstra :: Graph -> Node -> [Assoc Node Distance]
dijkstra g src =
    go []
        $ Heap.fromList
        $ map (\n -> Assoc n (if n == src then R 0 else I))
        $ Map.keys g
  where
    go res q = case Heap.extractMin q of
        Nothing -> res
        Just (h@(Assoc nu du), tl) ->
            go (h : res) . Heap.fromList . map f . Heap.forget $ tl
          where
            f e@(Assoc nv dv) = case Map.lookup nu g >>= Map.lookup nv of
                Nothing -> e
                Just w  -> Assoc nv (if du |+| w < dv then du |+| w else dv)

-- a-a 0, a-b 8, a-c 5, a-d 9, a-e 7
test :: Graph
test = graph $ map
    (\(a, b, c) -> (a, b, R c))
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
