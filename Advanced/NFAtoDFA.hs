-- Then conversion algorithm will not use ε-closure of states since the nfa construction (from the paper) from the given regex constructs an ε-free NFA

-- Also, for the implementation of the bonus "WildCard", there is a slight modification of the algorithm
-- Specifically, from a set-state from the subset construction, the next set-state from a tansition character c is constructed like the algorithm
-- specifies but the nfa transitions which are taken into account are not just the ones with transition character c, but also the ones with transition
-- character '.'. This is done since it is desired that '.' can be used as the transition character c regardless of what character it is.
-- This has a cost in the construction of the DFA. For example for the regex "(((a|bcd(.(d*|_).)*a*)ba(e(f|_)|_)*)|_((a|_).e)*((_)*)*(_))|((d.e)*c)":
-- nfatoDfa Without treating '.' as the WildCard: The dfa from the nfa of Thompson's construction has 60 states and 318 transitions
--                                                The dfa from the ε-free Nfa with few transitions has 20 states and 34 transitions

-- nfatoDfa while treating '.' as the WildCard:   The dfa from the nfa of Thompson's construction has 156 states and 2226 transitions
--                                                The dfa from the ε-free Nfa with few transitions has 77 states and 430 transitions

-- As it is shown, there is a visible cost with treating '.' as the wildcard in the construction
-- However, if this was not done, the implementation of the bonus "WildCard" would have to be implemented in the regex matching by
-- using backtracking because it would not be clear whether the use of the transition with transition character c or with the transition character 
-- '.' must be used whenever such a choice can be made. However, backtracking can have an exponential cost if the choice has to be made lots of times

-- Because of this, the nfatodfa implementation treating '.' as the wildcard was chosen

module NFAtoDFA (nfaToDfa) where

import Types
import RegParser (parseRegexpr, RegExpr(..))
import Utilities
import MakeNFA (makeNfa)

--Sorting the transitions will not be useful since the regex matching will use the directory structure which does not need an initial sorting
{- 
sortTransitions :: Transition -> Transition -> MyOrdering
sortTransitions (stateId1, stateId2, char1 ) (stateId3, stateId4, char2) = case comp1 of
  MyEQ -> case comp2 of
          MyEQ -> comp3
          _ -> comp2
  _ -> comp1
  where comp1 = myCompare stateId1 stateId3
        comp2 
          | char1 == char2 = MyEQ
          | char1 == '.' = MyGT
          | char2 == '.' = MyLT
          | otherwise = myCompare char1 char2
        comp3 = myCompare stateId2 stateId4
-}
type SetTransition = (States, States, TransChar)

nfaToDfa :: Fsa -> Fsa
nfaToDfa (states', inputs', transitions', firstState', lastStates) = (states, inputs', {- mergeSortBy sortTransitions -}transitions, firstState, finalStates)
  where 
    initSetState = [firstState'] -- the nfa constructed from makeNfa with the used from the algorithm from the paper does not have ε-transitions
    (setStates, setTrans) = convertToSetDFA transitions' inputs' initSetState
    (states, transitions, firstState, finalStates) = translateSetsToInts lastStates setStates setTrans initSetState

------------------------------------------------------------------------------------------------------
-- Steps 5,6

translateSetsToInts :: States -> [States] -> [SetTransition] -> States -> (States, Transitions, FirstState, LastStates)
translateSetsToInts finalNFAStates setStates setTransitions initSetState = (intStates, intTransitions, intInitState, intFinalStates)
  where
    totalSetStates = length setStates
    intStates = [1..totalSetStates]
    mapping = myZip setStates intStates
    convertSetTransToInt (srcSet, destSet, char) = ( getSetToIntMapping mapping srcSet, getSetToIntMapping mapping destSet, char )
    intTransitions = map convertSetTransToInt setTransitions
    intInitState = getSetToIntMapping mapping initSetState
    intFinalStates = getFinalIntStates mapping finalNFAStates


getSetToIntMapping :: [(States, StateId)] -> States -> StateId
getSetToIntMapping ((set,int):restMappings) setToMap = if set == setToMap then int else getSetToIntMapping restMappings setToMap
getSetToIntMapping [] setToMap = error "getSetToIntMapping : Got [] as first argument"


getFinalIntStates :: [(States, StateId)] -> States -> [StateId]
getFinalIntStates [] _ = []
getFinalIntStates ((set,int):restMapping) finalNFAStates 
    | myAny  (`myMember` finalNFAStates) set= int : checkRest
    | otherwise = checkRest
    where
      checkRest = getFinalIntStates restMapping finalNFAStates

------------------------------------------------------------------------------------------------------
-- Step 4

convertToSetDFA :: Transitions -> Inputs -> States -> ([States],[SetTransition])
convertToSetDFA transitions inputs initState = convertToSetDFAInner transitions inputs [initState] [initState] []

-- Perform a DFS search until no new set transitions are left to be visited. Return the final Set States and Set Transitions of the DFA.
convertToSetDFAInner :: Transitions -> Inputs -> [States] -> [States] -> [SetTransition] -> ([States],[SetTransition])
convertToSetDFAInner _ _ [] finalSetStates finalTrans = (finalSetStates, finalTrans)
convertToSetDFAInner transitions inputs (stateToExpand:restToVisit) setStatesSoFar transSoFar = convertToSetDFAInner transitions inputs newToVisit newSetStates newTrans
  where 
    (newTransAdded, newReachableStates) = expandState stateToExpand transitions inputs setStatesSoFar
    newToVisit = newReachableStates ++ restToVisit
    newSetStates = newReachableStates ++ setStatesSoFar
    newTrans = newTransAdded ++ transSoFar

------------------------------------------------------------------------------------------------------
-- Step 3: From a set-state S, given input character a, get the new reachable set-state S'

-- For a given state, for every symbol find the new reachable states. Finally, accumulate and return all of these transitions and new states found.
expandState :: States -> Transitions -> Inputs -> [States] -> ([SetTransition], [States])
expandState stateToExpand transitions inputs setStates = (newTrans, newReachableStates)
  where 
    newTrans = filter (\(x,y,z) -> y /= [] && x /= []) [ getSetTransitionsReachedWithCharEps symbol transitions stateToExpand | symbol <- inputs ]
    newReachableStates = filter (\x -> not $ myMember x setStates) . map (\(x,y,z) -> y) $ newTrans

-- Given a set of states `states` and transition character `char`, find all the states that can be reached from the set by consuming `char`
-- and a number of epsilon transitions.
getSetTransitionsReachedWithCharEps :: TransChar -> Transitions -> States -> SetTransition
getSetTransitionsReachedWithCharEps symbol transitions initStates = (initStates, reachedWithChar, symbol)
              where reachedWithChar = getStatesReachedWithChar transitions symbol initStates

-- Given a set of states `states` and transition character `char`, find all the states that can be reached from the set by consuming `char`.
getStatesReachedWithChar :: Transitions -> TransChar -> States -> States
getStatesReachedWithChar transitions char states =  map (\(x,y,z) -> y) . filter (\(x,y,z) -> (z == char || z == '.') && myMember x states) $ transitions
