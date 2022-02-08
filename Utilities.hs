module Utilities
(   myMap,
    myFoldl,
    myFoldr,
    myDropWhile,
    myTakeWhile,
    mySpan,
    myConcat,
    myElem,
    myFst,
    mySnd,
    mergeSortBy,
    mergeSort,
    removeDuplicates,
    MyOrdering(..),
    MyMaybe(..)
) where

data MyMaybe a = MyNothing | MyJust a

data MyOrdering = MyLT | MyEQ | MyGT

myCompare :: Ord a => a -> a -> MyOrdering
myCompare x y
    | x < y  = MyLT
    | x == y = MyEQ
    | otherwise  = MyGT 

myMap :: (a -> b) -> [a] -> [b]
myMap _ [] = []
myMap f (x:xs) = f x : myMap f xs

myFoldl :: (b -> a -> b) -> b -> [a] -> b
myFoldl _ acc [] = acc
myFoldl f acc (x:xs) = myFoldl f (f acc x) xs

myFoldr :: (a -> b -> b) -> b -> [a] -> b
myFoldr _ acc [] = acc
myFoldr f acc (x:xs) = f x (myFoldr f acc xs)

myDropWhile :: (a -> Bool) -> [a] -> [a]
myDropWhile _ [] = []
myDropWhile p (x:xs)
    | p x = myDropWhile p xs
    | otherwise = x:xs

myTakeWhile :: (a -> Bool) -> [a] -> [a]
myTakeWhile _ [] = []
myTakeWhile p (x:xs)
    | p x = x : myTakeWhile p xs
    | otherwise = []

mySpan :: (a -> Bool) -> [a] -> ([a], [a])
mySpan _ [] = ([], [])
mySpan p (x:xs) 
    | p x = let (l1, l2) = mySpan p xs in (x:l1, l2)
    | otherwise = ([], x:xs) 

myConcat :: [[a]] -> [a]
myConcat [] = []
myConcat (l:ll) = l ++ myConcat ll

myElem :: (Eq a) => a -> [a] -> Bool
myElem _ [] = False
myElem a (x:xs)
    | a == x = True
    | otherwise = myElem a xs

myFst :: (a, b) -> a
myFst (a,_) = a

mySnd :: (a, b) -> b
mySnd (_,b) = b


removeDuplicatesInner :: (Eq a) => (a -> a -> Bool) -> [a] -> MyMaybe a -> [a]
removeDuplicatesInner cmp_eq [] _ = [] 
removeDuplicatesInner cmp_eq (x:xs) MyNothing =  x:removeDuplicatesInner cmp_eq xs (MyJust x)
removeDuplicatesInner cmp_eq (x:xs) (MyJust last_elem)
    | cmp_eq x last_elem = cont
    | otherwise = x : cont
    where cont = removeDuplicatesInner cmp_eq xs (MyJust x)

removeDuplicates :: (Eq a) => (a -> a -> Bool) -> [a] -> [a]
removeDuplicates cmp_eq l = removeDuplicatesInner cmp_eq l MyNothing

-- MergeSort implementation

mergeSortBy :: (a -> a -> MyOrdering) -> [a] -> [a]
mergeSortBy f [] = []
mergeSortBy f [x] = [x]
mergeSortBy f l = mergeSortedListsBy f l1_sorted l2_sorted
        where   (l1, l2) = splitList l
                [l1_sorted, l2_sorted] = myMap (mergeSortBy f) [l1,l2]

mergeSortedListsBy :: (a -> a -> MyOrdering) -> [a] -> [a] -> [a]
mergeSortedListsBy _ [] xs = xs
mergeSortedListsBy _ xs [] = xs
mergeSortedListsBy f (x:xs) (y:ys) = case f x y of
    MyGT  -> y : mergeSortedListsBy f (x:xs) ys
    _     -> x : mergeSortedListsBy f xs (y:ys)

splitList :: [a] -> ([a], [a])
splitList [] = ([],[])
splitList [x] = ([x],[])
splitList (x:y:xs) = (x:l1, y:l2) where (l1,l2) = splitList xs


mergeSort :: Ord a => [a] -> [a]
mergeSort = mergeSortBy myCompare