module Utilities
(   mergeSortBy,
    mergeSort,
    removeDuplicatesBy,
    removeDuplicates,
) where


------------------------------------------------------------------------------------------------------
----------------------- My implementation on basic Haskell functions and types------------------------
------------------------------------------------------------------------------------------------------


removeDuplicatesInner :: (a -> a -> Bool) -> [a] -> Maybe a -> [a]
removeDuplicatesInner cmp_eq [] _ = [] 
removeDuplicatesInner cmp_eq (x:xs) Nothing =  x:removeDuplicatesInner cmp_eq xs (Just x)
removeDuplicatesInner cmp_eq (x:xs) (Just last_elem)
    | cmp_eq x last_elem = cont
    | otherwise = x : cont
    where cont = removeDuplicatesInner cmp_eq xs (Just x)

removeDuplicatesBy :: (a -> a -> Bool) -> [a] -> [a]
removeDuplicatesBy cmp_eq l = removeDuplicatesInner cmp_eq l Nothing

removeDuplicates :: Eq a => [a] -> [a]
removeDuplicates = removeDuplicatesBy (==) 

-- MergeSort implementation

mergeSortBy :: (a -> a -> Ordering) -> [a] -> [a]
mergeSortBy f [] = []
mergeSortBy f [x] = [x]
mergeSortBy f l = mergeSortedListsBy f l1_sorted l2_sorted
        where   (l1, l2) = splitList l
                [l1_sorted, l2_sorted] = map (mergeSortBy f) [l1,l2]

mergeSortedListsBy :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
mergeSortedListsBy _ [] xs = xs
mergeSortedListsBy _ xs [] = xs
mergeSortedListsBy f (x:xs) (y:ys) = if f x y == GT then  y : mergeSortedListsBy f (x:xs) ys else x : mergeSortedListsBy f xs (y:ys)

splitList :: [a] -> ([a], [a])
splitList [] = ([],[])
splitList [x] = ([x],[])
splitList (x:y:xs) = (x:l1, y:l2) where (l1,l2) = splitList xs

mergeSort :: Ord a => [a] -> [a]
mergeSort = mergeSortBy compare