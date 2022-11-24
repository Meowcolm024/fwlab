module Heap where

data Heap a = Empty | Heap a [Heap a] deriving Show

merge :: Ord a => Heap a -> Heap a -> Heap a
merge Empty h     = h
merge h     Empty = h
merge h1@(Heap x hs1) h2@(Heap y hs2) | x < y     = Heap x (h2 : hs1)
                                      | otherwise = Heap y (h1 : hs2)

insHeap :: Ord a => Heap a -> [Heap a] -> Heap a
insHeap h hs = foldl merge h hs

insert :: Ord a => a -> Heap a -> Heap a
insert x = merge (Heap x [])

extractMin :: Ord a => Heap a -> Maybe (a, Heap a)
extractMin Empty             = Nothing
extractMin (Heap x []      ) = Just (x, Empty)
extractMin (Heap x (h : hs)) = Just (x, insHeap h hs)

fromList :: Ord a => [a] -> Heap a
fromList xs = foldr insert Empty xs

toList :: Ord a => Heap a -> [a]
toList h = case extractMin h of
    Nothing     -> []
    Just (h, t) -> h : toList t

forget :: Ord a => Heap a -> [a]
forget Empty = []
forget (Heap h t) = h : (t >>= forget)
