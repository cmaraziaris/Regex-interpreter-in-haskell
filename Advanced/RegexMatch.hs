module RegexMatch (regexFullMatch, regexPartMatch, test_all) where

import MakeNFA
import NFAtoDFA
import Types

import Data.Foldable ( Foldable(foldl') )
import Control.Monad ( MonadPlus(mplus) )
import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap.Lazy as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Maybe 
import Data.Char (ord, chr)

--makeDfa constructs a dfa using the natural tactic. Construct an equivalent nfa and then transform it into an dfa
makeDfa :: [Char] -> Fsa
makeDfa = nfaToDfa . makeNfa


-- Regex matching will use the dictionary and set types and functions provided ny the module DictSet
-- The dictionary has type TransDict (defined directly below). The goal is that instead of traversing the list of transitions to find the next State
-- which has a cost proportional to the number of transitions (#transitions), the dictionary structure will allow for a cost proportional to 
-- log(#states) + log(#transCharacter) which is significantly less
-- Of course, the conversion from the list to the dictionary has a cost O(n*log(n)) where n = #transitions, so fro very small string inputs
-- the conversion has a bigger cost, however, for longer inputs to the dfa, the benefits of the dictionary outweight the contruction cost

-- type TransDict = Dict StateId (Dict TransChar StateId)
type StatePosMap = IntMap (IntMap StateId)  -- For each state currState in the transitions of the form (currState, nextState, transChar),
                                                        -- keep in a dictionary all the transition characters of those transitions and in 
                                                        -- which nextState they point to


--For the implementation of the wildcard, it is important for the current state currState and input character c 
-- whether there is a transition of the form (currState, newState, c). If there is, the new state is newState. Otherwise, search for a transition
-- of the form (currState, newState, '.') (the WildCard).
-- This works because of how nfatoDfa works (explained in the nfatoDfa module)

regexFullMatch :: ([Char], [Char]) -> Bool
regexFullMatch (regStr, strPat) = searchFull dict set strPat firstState
    where
      (_,_,transitions, firstState, finalStates) = makeDfa regStr
      dict = transDict transitions
      set = IntSet.fromList finalStates



searchFull :: StatePosMap -> IntSet -> String -> StateId-> Bool
searchFull dict setFinal [] currState = IntSet.member currState setFinal
searchFull dict setFinal (c:str) currState = maybe False (searchFull dict setFinal str) nextState

  where 
    nextState = findNextState dict c currState
    isFinalState = IntSet.member currState setFinal


-- Bonus: Partial Matching (Also compatible with the WildCard bonus)

regexPartMatch :: ([Char], [Char]) -> [[Char]]
regexPartMatch (regStr, strPat) = searchPart dict set strPat firstState
    where
      (_,_,transitions, firstState, finalStates) = makeDfa regStr
      dict = transDict transitions
      set = IntSet.fromList finalStates


--regexPartMatch1 :: ([Char], [Char]) -> [[Char]]
--regexPartMatch1 (regStr, strPat) = searchPart transitions finalStates strPat firstState
--    where
--      (_,_,transitions, firstState, finalStates) = makeDfa1 regStr

findNextState :: StatePosMap -> TransChar -> StateId -> Maybe StateId
findNextState dict chr currState = IntMap.lookup currState  dict >>= (\chrDict -> mplus (IntMap.lookup (ord chr) chrDict) (IntMap.lookup (ord '.') chrDict))

searchPart :: StatePosMap -> IntSet -> String -> StateId -> [String]
searchPart dict setFinal [] currState = ["" | IntSet.member currState setFinal]
searchPart dict setFinal (c:str) currState = newString ++ maybe [] (map (c :) . searchPart dict setFinal str) nextState

  where 
    nextState = findNextState dict c currState
    isFinalState = IntSet.member currState setFinal
    newString = ["" | isFinalState]

transDictFoldl :: StatePosMap -> Transition -> StatePosMap
transDictFoldl dict (id1, id2, chr) = IntMap.insertWith (\_ y -> IntMap.insert (ord chr) id2 y) id1 (IntMap.singleton (ord chr) id2) dict

transDict :: Transitions -> StatePosMap
transDict = foldl' transDictFoldl IntMap.empty



------------------------ Testing ---------------------------------------------------------


inputsPart = [("(ab)*", "abababde"), ("(ac|dd)*", "acacddeff")]
outputsPart = [["", "ab","abab","ababab"], ["","ac","acac","acacdd"]]

test_full :: Bool
test_full = map regexFullMatch inputsFull == outputsFull

test_part :: Bool
test_part = map regexPartMatch inputsPart == outputsPart

test_all :: Bool
test_all = test_full && test_part




inputsFull = [
    ("ab|c","ab"),
    ("ab|.","abd"),
    ("(ab|.)*","abd"),
    ("((ab)*c|c*a(ab)*)*","c"),
    ("((ab)*c|c*a(ab)*)*",""),
    ("((ab)*c|c*a(ab)*)*","a"),
    ("((ab)*c|c*a(ab)*)*","cccccccccccababcccccca"),
    ("((ab)*c|c*a(ab)*)*","ccccc"),
    ("((ab)*c|c*a(ab)*)*","aaaaaaaaaaaaaaa"),
    ("((ab)*c|c*a(ab)*)*","aaaaaaaaaaaaaaa"),
    ("((ab)*c|c*a(ab)*)*","ccccccccccaccca"),
    ("(((((((ab)*c|c*a(ab)*)*)*)*)*)*)*","cacacacaccccaab"),
    ("(((((((ab)*c|c*a(ab)*)*)*)*)*)*)*","cacacacaccccab"),
    ("((ab)*c|c*a(ab)*)*","cacacacaccccaab"),
    ("((ab)*c|c*a(ab)*)*","cacacacaccccab"),
    ("(((a|bcd(.(d*|_).)*a*)ba(e(f|_)|_)*)|_((a|_).e)*((_)*)*(_))|((d.e)*c)", "bcd4ddddoaabaeeefeefefe"), --True
    ("(((a|bcd(.(d*|_).)*a*)ba(e(f|_)|_)*)|_((a|_).e)*((_)*)*(_))|((d.e)*c)", "bcd4oaabaeeefeefefe"),     --True
    ("(((a|bcd(.(d*|_).)*a*)ba(e(f|_)|_)*)|_((a|_).e)*((_)*)*(_))|((d.e)*c)", "bcd4ddddoaabaeeefeeffefe"), --False
    ("(((a|bcd(.(d*|_).)*a*)ba(e(f|_)|_)*)|_((a|_).e)*((_)*)*(_))|((d.e)*c)", "abaeeefeefefe"),           --True
    ("(((a|bcd(.(d*|_).)*a*)ba(e(f|_)|_)*)|_((a|_).e)*((_)*)*(_))|((d.e)*c)", "7e5ea5e3e"),               --True
    ("(((a|bcd(.(d*|_).)*a*)ba(e(f|_)|_)*)|_((a|_).e)*((_)*)*(_))|((d.e)*c)", "c")]                       --True

outputsFull = [
    True, 
    False, 
    True,
    True,
    True,
    True,
    True,
    True,
    True,
    True,
    True,
    True,
    False,
    True,
    False,
    True,
    True,
    False,
    True,
    True,
    True]

{- 
-- Comparisons with thompon's construction and the new improved construction
-- It has been seen that with small regexes, as was expected, there is no big difference
-- However, with the use of larger regexes, there is a significant difference.
-- test_all, using the new nfa construction, in my computer, it finished on average in 0.48 seconds while using around 202.800.000 bytes
-- test_all, using the classical nfa construction, in my computer, it finished on average in 7 seconds while using around 3.000.000.000 bytes

-- The consclusion is that the new nfa construction shows significantly better results

regexFullMatch1 :: ([Char], [Char]) -> Bool
regexFullMatch1 (regStr, strPat) = searchFull dict set strPat firstState
    where
      (_,_,transitions, firstState, finalStates) = makeDfa1 regStr
      dict = transDict transitions
      set = setFromList finalStates

regexPartMatch1 :: ([Char], [Char]) -> [[Char]]
regexPartMatch1 (regStr, strPat) = myMap myReverse $ searchPart dict set strPat firstState ""
    where
      (_,_,transitions, firstState, finalStates) = makeDfa1 regStr
      dict = transDict transitions
      set = setFromList finalStates



-- compare stats from thompon's nfa and ε-free Nfa (number of states and transitions)
compareStats :: [Char] -> String
compareStats str = "Num of States = " ++ show (length a1) ++ " " ++ show (length b1) ++ " " ++  "Num of Transitions = " ++ show (length a3) ++ " " ++ show (length b3)
    where   (a1,a2,a3,a4,a5) = makeDfa str
            (b1,b2,b3,b4,b5) = makeDfa1 str
-- Tests // TODO : RM before sending

makeDfa1 :: [Char] -> Fsa
makeDfa1 = nfaToDfa1 . makeNfa1

test_full1 :: Bool
test_full1 = map regexFullMatch1 inputsFull == outputsFull

test_part1 :: Bool
test_part1 = map regexPartMatch1 inputsPart == outputsPart

test_all1 :: Bool
test_all1 = test_full1 && test_part1

-}