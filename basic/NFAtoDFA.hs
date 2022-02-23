
module NFAtoDFA (nfaToDfa) where

import Types
import RegParser (parseRegexpr, RegExpr(..))

type SetTransition = (States, States, TransChar)

nfaToDfa :: Fsa -> Fsa
nfaToDfa (states', inputs', transitions', firstState', [lastState']) = (states, inputs', transitions, firstState, finalStates)
  where 
    initSetState = getEpsilonClosure transitions' [firstState']
    (setStates, setTrans) = convertToSetDFA transitions' inputs' initSetState
    (states, transitions, firstState, finalStates) = translateSetsToInts lastState' setStates setTrans initSetState

------------------------------------------------------------------------------------------------------
-- Steps 5,6

translateSetsToInts :: StateId -> [States] -> [SetTransition] -> States -> (States, Transitions, FirstState, LastStates)
translateSetsToInts lastNFAState setStates setTransitions initSetState = (intStates, intTransitions, intInitState, intFinalStates)
  where
    totalSetStates = length setStates
    intStates = [1..totalSetStates]
    mapping = myZip setStates intStates
    convertSetTransToInt (srcSet, destSet, char) = ( getSetToIntMapping mapping srcSet, getSetToIntMapping mapping destSet, char )
    intTransitions = map convertSetTransToInt setTransitions
    intInitState = getSetToIntMapping mapping initSetState
    intFinalStates = getFinalIntStates mapping lastNFAState


getSetToIntMapping :: [(States, StateId)] -> States -> StateId
getSetToIntMapping ((set,int):restMappings) setToMap = if set == setToMap then int else getSetToIntMapping restMappings setToMap
-- getSetToIntMapping [] setToMap = 0


getFinalIntStates :: [(States, StateId)] -> StateId -> [StateId]
getFinalIntStates [] _ = []
getFinalIntStates ((set,int):restMapping) finalNFAState 
    | isMember finalNFAState set = int : checkRest
    | otherwise = checkRest
    where
      checkRest = getFinalIntStates restMapping finalNFAState

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
    newReachableStates = filter (\x -> not $ isMember x setStates) . map (\(x,y,z) -> y) $ newTrans

-- Given a set of states `states` and transition character `char`, find all the states that can be reached from the set by consuming `char`
-- and a number of epsilon transitions.
getSetTransitionsReachedWithCharEps :: TransChar -> Transitions -> States -> SetTransition
getSetTransitionsReachedWithCharEps symbol transitions initStates = (initStates, reachedWithCharAndEps, symbol)
              where reachedWithChar = getStatesReachedWithChar transitions symbol initStates
                    reachedWithCharAndEps = getEpsilonClosure transitions reachedWithChar

-- Given a set of states `states` and transition character `char`, find all the states that can be reached from the set by consuming `char`.
getStatesReachedWithChar :: Transitions -> TransChar -> States -> States
getStatesReachedWithChar transitions char states =  map (\(x,y,z) -> y) . filter (\(x,y,z) -> z == char && isMember x states) $ transitions


------------------------------------------------------------------------------------------------------
-- Step 2: Get ε-closure of a given list of states

getEpsilonClosure :: Transitions -> States -> States
getEpsilonClosure trans initStates = getEpsilonClosureInner trans initStates []

-- If a state is already in the closure, don't explore it.
-- Otherwise, add it in the so-far closure and also add its reachable states in the states-to-check list.
getEpsilonClosureInner :: Transitions -> States -> States -> States
getEpsilonClosureInner _ [] closure = closure
getEpsilonClosureInner transitions (t:ts) closureSoFar
    | isMember t closureSoFar = getEpsilonClosureInner transitions ts closureSoFar
    | otherwise = getEpsilonClosureInner transitions (epsNeighbors ++ ts) (t:closureSoFar)
    where
      epsNeighbors = map (\(x,y,z) -> y) . filter (\(x,y,z) -> x == t && z == '_') $ transitions
------------------------------------------------------------------------------------------------------

-- Auxiliary
isMember :: Eq t => t -> [t] -> Bool
isMember x [] = False
isMember x (y:xs) = (x == y) || isMember x xs

myZip :: [a] -> [b] -> [(a,b)] 
myZip [] [] = []
myZip (x:xs) (y:ys) = (x,y) : (myZip xs ys)
