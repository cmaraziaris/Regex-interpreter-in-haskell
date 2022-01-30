
module NFAtoDFA (nfaToDfa) where

import RegParser
import Types

-- import MakeNFA -- TODO : rm 
-- import Debug.Trace

-- type Fsa = (States, Inputs, Transitions, FirstState, LastStates)
-- type Transition = (StateId, StateId, TransChar)

type SetTransition = (States, States, TransChar)

nfaToDfa :: Fsa -> Fsa
nfaToDfa (states', inputs', transitions', firstState', [lastState']) = (states, inputs', transitions, firstState, finalStates)
        where initState = get_epsilon_closure transitions' [firstState'] [firstState']
              unmarked = [initState]
              setStates = [initState]
              (finalSetStates, trans) = convert transitions' inputs' unmarked setStates []
              l = length(finalSetStates)
              states = [l,l-1..1]
              mapping = myZip finalSetStates states
              transitions = convert_setTrans_toIntTrans mapping trans finalSetStates
              finalStates = get_final mapping lastState'
              firstState = get_mapping mapping initState

check_symbol :: TransChar -> Transitions -> States -> SetTransition
check_symbol symbol transitions tState = (tState, uState, symbol)
              where move = get_states_move_letter transitions symbol tState
                    uState = get_epsilon_closure transitions move move

check_tState :: States -> Transitions -> Inputs -> [States] -> [States] -> ([SetTransition], [States], [States])
check_tState tState transitions inputs unmarked setStates = (newTrans, newUnmarked, newSetStates)
  where newTrans = filter (\(x,y,z) -> y /= [] && x /= []) [ check_symbol symbol transitions tState | symbol <- inputs ]
        newUs = map (\(x,y,z) -> y) newTrans
        newUnique = filter (\x -> member_list x setStates == False)  newUs
        newUnmarked = newUnique ++ unmarked
        newSetStates = newUnique ++ setStates


convert :: Transitions -> Inputs -> [States] -> [States] -> [SetTransition] -> ([States],[SetTransition])
convert _ _ [] finalSetStates transSoFar = (finalSetStates, transSoFar)
convert transitions inputs (tState:ts) setStates transSoFar = convert transitions inputs newUnmarked newSetStates finalTrans
  where (newTrans, newUnmarked, newSetStates) = check_tState tState transitions inputs ts setStates
        finalTrans = newTrans ++ transSoFar


get_mapping :: [(States, StateId)] -> States -> StateId
get_mapping [] x = 0
get_mapping ((set,int):ms) x = if set == x then int else get_mapping ms x

convert_setTrans_toIntTrans :: [(States, StateId)] -> [SetTransition] -> [States] -> Transitions
convert_setTrans_toIntTrans mapping setTrans setStates = map (\(x,y,z) -> ( (get_mapping mapping x), (get_mapping mapping y), z) ) setTrans

get_final :: [(States, StateId)] -> StateId -> [StateId]
get_final [] _ = []
get_final ((set,int):mp) finalState = if member_list finalState set then int : (get_final mp finalState) else get_final mp finalState


member_list x [] = False
member_list x (y:xs) = if x == y then True else member_list x xs

get_epsilon_closure :: Transitions -> States -> States -> States
get_epsilon_closure transitions [] closure = closure
get_epsilon_closure transitions (t:ts) closureSoFar = get_epsilon_closure transitions (found ++ ts) (found ++ closureSoFar) 
                where us = map (\(x,y,z) -> y) (filter (\(x,y,z) -> x == t && z == '_') transitions)
                      found = [ u | u <- us, (member_list u closureSoFar) == False ]

get_states_move_letter :: Transitions -> TransChar -> States -> States
get_states_move_letter transitions c states =  map (\(x,y,z) -> y) (filter (\(x,y,z) -> z == c && member_list x states) transitions)


myZip [] [] = []
myZip (x:xs) (y:ys) = (x,y) : (myZip xs ys)
