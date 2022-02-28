module DictSet (
 Dict(..),
 dictEmpty,
 dictNull,
 dictSingleton,
 dictInsert,
 dictLookup,
 dictFromList,
 dictFlatten,
 dictDelete,
 dictUpdate,
 --dictHasValidBalance
 Set(..),
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
import Data.Maybe ( isJust )
import Data.Foldable ( Foldable(foldl') )
-- A haskell implementation of balanced Binary Search Trees and the implementation of balanced,ordered set from those trees
-- Dictionary and Set are used for optimal search since their complexity operations are O(log(n)) which is much better
-- than the operations on lists which have linear compexity
-- Of course, there is the cost of the creation of these data structures which is O(n log(n)) but the benefits are worth more

-- Since the dictionary and Set are balanced vinary search trees, it is necessary for the keys to beling to the Ord typeclass
-- in order for the structures to be able to work properly



type Height = Int
type Balance = Int -- Balance value of a node is in {-1,0,+1} in a balanced binary sarch tree
data Dict k a = DictNil | DictNode Height k a (Dict k a) (Dict k a) deriving (Eq, Show)

--Create an empty Dictionary
dictEmpty :: Dict k a
dictEmpty = DictNil

--Checks if dictionary is empty
dictNull :: Dict k a -> Bool
dictNull DictNil = True
dictNull _ = False

--Create a dictionary which contains only one (key,value)
dictSingleton :: (k,a) -> Dict k a
dictSingleton (k,a) = DictNode 1 k a DictNil DictNil

dictHeight :: Dict k a -> Height
dictHeight DictNil = 0
dictHeight (DictNode h _ _ _ _) = h

node :: (k,a) -> Dict k a -> Dict k a -> Dict k a
node (k,a) tree1 tree2 = DictNode (1 + max (dictHeight tree1) (dictHeight tree2)) k a tree1 tree2

--Insert a (key,value) to dictionary. If the key already exists, replace the current value by the value of (key,value)
dictInsert :: Ord k => (k,a) -> Dict k a -> Dict k a

dictInsert (k,a) DictNil = dictSingleton (k,a)

dictInsert (k,a) dictnode@(DictNode h k1 a1 tree1 tree2)
    | k < k1 = dictRotate $  node (k1,a1) (dictInsert (k,a) tree1) tree2
    | k > k1 = dictRotate $  node (k1,a1) tree1 (dictInsert (k,a) tree2)
    | otherwise = DictNode h k a tree1 tree2

-- Checks if a key exists in the dictionary. If it exists, return a "MyJust a" where a is the value of the key. Otherwise return MyNothing 
dictLookup :: Ord k => k -> Dict k a -> Maybe a
dictLookup _ DictNil = Nothing
dictLookup k (DictNode _ k1 a tree1 tree2)
    | k < k1 = dictLookup k tree1
    | k > k1 = dictLookup k tree2
    | otherwise = Just a

-- Given a key, apply a function on the value of that key  and return a new value. If the key does not exist, do nothing to the dictionary
dictUpdate :: Ord k => k -> (a -> a) -> Dict k a -> Dict k a

dictUpdate _ _ DictNil = DictNil

dictUpdate k f dictnode@(DictNode h k1 a1 tree1 tree2)
    | k < k1 = DictNode h k1 a1 (dictUpdate k f tree1) tree2
    | k > k1 = DictNode h k1 a1 tree1 (dictUpdate k f tree2)
    | otherwise = DictNode h k (f a1) tree1 tree2

--dictRangeLookup :: Ord k -> k -> k -> Dict k a -> [(k,a)]
--dictRangeLookup _ _ DictNil = []
--dictRangeLookup k1 k2 (DictNode _ k a tree1 tree2)
--    | k1 =< k && k =< k2 = dictRangeLookup k tree1
--    | k >  k2 =
--    | otherwise 
--    where 

--Convert a list into a dictionary
dictFromList :: Ord k => [(k,a)] -> Dict k a
dictFromList = foldl' (flip dictInsert) dictEmpty

--Unfold a dictionary into a list
dictFlatten :: Dict k a -> [(k,a)]

dictFlatten dict = dictFlatten' dict []

dictFlatten' :: Dict k a -> [(k,a)] -> [(k,a)]

dictFlatten' DictNil l = l
dictFlatten' (DictNode _ k a tree1 tree2) l = l2
    where   l1 = dictFlatten' tree2 l
            l2 = dictFlatten' tree1 ((k,a):l1)

dictLeftMost :: Dict k a -> Maybe (k,a)

dictLeftMost DictNil = Nothing
dictLeftMost (DictNode _ k a tree1 tree2) = case tree1 of
            DictNil -> Just (k,a)
            _ -> dictLeftMost tree1

dictGetDeleteLeftMost :: Ord k => Dict k a -> (Maybe (k,a), Dict k a)

dictGetDeleteLeftMost DictNil = (Nothing, DictNil)
dictGetDeleteLeftMost (DictNode _ k a tree1 tree2) =  case r of
                                Just (k1,a1) -> (Just (k1,a1), dictRotate $ node (k,a) newDict tree2)
                                _ -> (Just (k,a), tree2)
        where (r, newDict) = dictGetDeleteLeftMost tree1

--Delete the key (and its value) from the dictionary. If the key does not exist in the dictinary, change nothing
dictDelete :: Ord k => k -> Dict k a -> Dict k a

dictDelete _ DictNil = DictNil
dictDelete k1 (DictNode h k a tree1 tree2)
    | k1 < k = dictRotate $ node (k,a) (dictDelete k1 tree1) tree2
    | k1 > k = dictRotate $ node (k,a) tree1 (dictDelete k1 tree2)
    | otherwise = case r of
                Just (k1,a1) -> dictRotate $ node (k1,a1) tree1 newDict
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
perms = foldr permsInsert [[]]

permsInsert :: a -> [[a]] -> [[a]]

permsInsert a = concatMap (permsInsert' a) 

permsInsert' :: a -> [a] -> [[a]]

permsInsert' a [] = [[a]]
permsInsert' a (x:xs) = (a:x:xs) : map (x :) (permsInsert' a xs) 

dictCheckValidity :: Ord a => [a] -> Bool
dictCheckValidity  = all (dictHasValidBalance . dictFromList. (\l -> zip l l)) . perms

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
setLookup k set =  Data.Maybe.isJust (dictLookup k set )

setFromList :: Ord k => [k] -> Set k
setFromList = dictFromList . (\l -> zip l l)

setFlatten ::  Set k -> [k]
setFlatten = map fst . dictFlatten

setDelete :: Ord k => k -> Set k -> Set k
setDelete = dictDelete 

--Transform the list into a set so that duplicates are extinguished and then convert it back into a list
setPruneDuplicates :: Ord k => [k] -> [k]
setPruneDuplicates = setFlatten. setFromList 
