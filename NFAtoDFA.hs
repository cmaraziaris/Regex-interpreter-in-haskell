
module NFAtoDFA (nfaToDfa, makeDfa) where

import Types
import RegParser (parseRegexpr, RegExpr(..))
import Utilities
import MakeNFA (makeNfa)


type SetTransition = (States, States, TransChar)

nfaToDfa :: Fsa -> Fsa
nfaToDfa (states', inputs', transitions', firstState', lastStates) = (states, inputs', transitions, firstState, finalStates)
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
getStatesReachedWithChar transitions char states =  map (\(x,y,z) -> y) . filter (\(x,y,z) -> z == char && myMember x states) $ transitions

makeDfa :: [Char] -> Fsa
makeDfa = nfaToDfa . makeNfa


