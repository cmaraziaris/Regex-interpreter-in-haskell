module DictSet (
 dictEmpty,
 dictNull,
 dictSingleton,
 dictInsert,
 dictLookup,
 dictFromList,
 dictFlatten,
 dictDelete,
 --dictHasValidBalance
 setEmpty,
 setNull,
 setSingleton,
 setInsert,
 setLookup,
 setFromList,
 setFlatten,
 setDelete,
 setPruneDuplicates
)
where

-- A haskell implementation of balanced Binary Search Trees and the implementation of balanced,ordered set from those trees

import Utilities ( myFoldr, myFoldl, MyMaybe(..), myFst, myZip, myMap )

type Height = Int
type Balance = Int -- Balance value of a node is in {-1,0,+1}
data Dict k a = DictNil | DictNode Height k a (Dict k a) (Dict k a) deriving (Eq, Show)

--Create an empty Dictionary
dictEmpty :: Dict k a
dictEmpty = DictNil

dictNull :: Dict k a -> Bool
dictNull DictNil = True
dictNull _ = False

dictSingleton :: (k,a) -> Dict k a
dictSingleton (k,a) = DictNode 1 k a DictNil DictNil

dictHeight :: Dict k a -> Height
dictHeight DictNil = 0
dictHeight (DictNode h _ _ _ _) = h

node :: (k,a) -> Dict k a -> Dict k a -> Dict k a
node (k,a) tree1 tree2 = DictNode (1 + max (dictHeight tree1) (dictHeight tree2)) k a tree1 tree2

dictInsert :: Ord k => (k,a) -> Dict k a -> Dict k a

dictInsert (k,a) DictNil = dictSingleton (k,a)

dictInsert (k,a) dictnode@(DictNode h k1 a1 tree1 tree2)
    | k < k1 = dictRotate $  node (k1,a1) (dictInsert (k,a) tree1) tree2
    | k > k1 = dictRotate $  node (k1,a1) tree1 (dictInsert (k,a) tree2)
    | otherwise = DictNode h k a tree1 tree2

dictLookup :: Ord k => k -> Dict k a -> MyMaybe a
dictLookup _ DictNil = MyNothing
dictLookup k (DictNode _ k1 a tree1 tree2)
    | k < k1 = dictLookup k tree1
    | k > k1 = dictLookup k tree2
    | otherwise = MyJust a

--dictRangeLookup :: Ord k -> k -> k -> Dict k a -> [(k,a)]
--dictRangeLookup _ _ DictNil = []
--dictRangeLookup k1 k2 (DictNode _ k a tree1 tree2)
--    | k1 =< k && k =< k2 = dictRangeLookup k tree1
--    | k >  k2 =
--    | otherwise 
--    where 

dictFromList :: Ord k => [(k,a)] -> Dict k a
dictFromList = myFoldr dictInsert dictEmpty

dictFlatten :: Dict k a -> [(k,a)]

dictFlatten dict = dictFlatten' dict []

dictFlatten' :: Dict k a -> [(k,a)] -> [(k,a)]

dictFlatten' DictNil l = l
dictFlatten' (DictNode _ k a tree1 tree2) l = l2
    where   l1 = dictFlatten' tree2 l
            l2 = dictFlatten' tree1 ((k,a):l1)

dictLeftMost :: Dict k a -> MyMaybe (k,a)

dictLeftMost DictNil = MyNothing
dictLeftMost (DictNode _ k a tree1 tree2) = case tree1 of
            DictNil -> MyJust (k,a)
            _ -> dictLeftMost tree1

dictGetDeleteLeftMost :: Ord k => Dict k a -> (MyMaybe (k,a), Dict k a)

dictGetDeleteLeftMost DictNil = (MyNothing, DictNil)
dictGetDeleteLeftMost (DictNode _ k a tree1 tree2) =  case r of
                                MyJust (k1,a1) -> (MyJust (k1,a1), dictRotate $ node (k,a) newDict tree2)
                                _ -> (MyJust (k,a), tree2)
        where (r, newDict) = dictGetDeleteLeftMost tree1

dictDelete :: Ord k => k -> Dict k a -> Dict k a

dictDelete _ DictNil = DictNil
dictDelete k1 (DictNode h k a tree1 tree2)
    | k1 < k = dictRotate $ node (k,a) (dictDelete k1 tree1) tree2
    | k1 > k = dictRotate $ node (k,a) tree1 (dictDelete k1 tree2)
    | otherwise = case r of
                MyJust (k1,a1) -> dictRotate $ node (k1,a1) tree1 newDict
                _ -> dictRotate tree2
    where (r, newDict) = dictGetDeleteLeftMost tree2

dictBal :: Dict k a -> Balance
dictBal DictNil = 0
dictBal (DictNode _ _ _ tree1 tree2) = dictHeight tree2 - dictHeight tree1

dictHasValidBalance :: Dict k a -> Bool

dictHasValidBalance DictNil = True
dictHasValidBalance dictnode@(DictNode _ _ _ tree1 tree2) = (abs (dictBal dictnode) <= 1) && result
    where result = dictHasValidBalance tree1 && dictHasValidBalance tree2

dictRotate :: Ord k => Dict k a -> Dict k a

dictRotate DictNil = DictNil
dictRotate dictnode@(DictNode h k a tree1 tree2)
    | abs bal <= 1 = dictnode
    | bal == 2  = if bal2 == -1 then node (k21,a21) (node (k,a) tree1 tree211) (node (k2,a2) tree212 tree22) else
                    node (k2,a2) (node (k,a) tree1 tree21) tree22
    | otherwise = if bal1 ==  1 then node (k12,a12) (node (k1,a1) tree11 tree121) (node (k,a) tree122 tree2) else
                    node (k1,a1) tree11 (node (k,a) tree12 tree2)
    where   bal = dictBal dictnode
            bal1 = dictBal tree1
            bal2 = dictBal tree2
            DictNode _ k1 a1 tree11 tree12 = tree1
            DictNode _ k2 a2 tree21 tree22 = tree2
            DictNode _ k21 a21 tree211 tree212 = tree21
            DictNode _ k12 a12 tree121 tree122 = tree12


perms :: [a] -> [[a]]
perms = myFoldr permsInsert [[]]

permsInsert :: a -> [[a]] -> [[a]]

permsInsert a = myFoldr (++) [] . myMap (permsInsert' a) 

permsInsert' :: a -> [a] -> [[a]]

permsInsert' a [] = [[a]]
permsInsert' a (x:xs) = (a:x:xs) : myMap (x :) (permsInsert' a xs) 

dictCheckValidity :: Ord a => [a] -> Bool
dictCheckValidity  = and . myMap (dictHasValidBalance . dictFromList. (\l -> myZip l l)) . perms

type Set k = Dict k k

setEmpty :: Set k
setEmpty = dictEmpty

setNull :: Set k  -> Bool
setNull = dictNull

setSingleton :: k -> Set k
setSingleton k = dictSingleton (k,k)

setInsert :: Ord k => k -> Set k -> Set k
setInsert k = dictInsert (k,k)

setLookup :: (Ord k) => k -> Set k -> Bool
setLookup k set =  dictLookup k set /= MyNothing

setFromList :: Ord k => [k] -> Set k
setFromList = dictFromList . (\l -> myZip l l)

setFlatten ::  Set k -> [k]
setFlatten = myMap myFst . dictFlatten

setDelete :: Ord k => k -> Set k -> Set k
setDelete = dictDelete 

setPruneDuplicates :: Ord k => [k] -> [k]
setPruneDuplicates = setFlatten. setFromList 
