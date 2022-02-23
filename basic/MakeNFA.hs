
module MakeNFA (makeNfa) where

import Types
import RegParser (parseRegexpr, RegExpr(..))
import Utilities (removeDuplicates)

type AvailableState = StateId

createNfaRec :: AvailableState -> RegExpr -> (Fsa, AvailableState)

-- ε-transition : nfa with just one state, that is also final
createNfaRec n EmptyChar = ( ([n], [], [], n, [n]), n+1 )

createNfaRec n AnyLetter = (fsa, nextAvailState)
    where
      fsa = ([src,dest], ['.'], [(src,dest,'.')], src, [dest]) 
      (src,dest,nextAvailState) = (n,n+1,n+2)

createNfaRec n (Letter c) = (fsa, nextAvailState)
    where
      fsa = ([src,dest], [c], [(src,dest,c)], src, [dest])
      (src,dest,nextAvailState) = (n,n+1,n+2)

createNfaRec n (Kleene reg) = (fsa, nextAvailState)
    where 
      fsa = ([], [], transitions, src, [dest])
      ((_, _, transitions', firstState', [lastState']), availState) = createNfaRec n reg
      (src,dest,nextAvailState) = (availState, availState+1, availState+2)
      transitions = (src,dest,'_') : (src,firstState','_') : (lastState',dest,'_') : (lastState',firstState','_') : transitions'

createNfaRec n (Concat (reg1, reg2)) = (fsa, availState2)
    where 
      fsa = ([], [], transitions, firstState1, [lastState2])
      ((_, _, transitions1, firstState1, [lastState1]), availState1) = createNfaRec n reg1
      ((_, _, transitions2, firstState2, [lastState2]), availState2) = createNfaRec availState1 reg2
      transitions = (lastState1,firstState2,'_') : (transitions1 ++ transitions2)

createNfaRec n (Union (reg1, reg2)) = (fsa, nextAvailState)
    where 
      fsa = ([], [], transitions, src, [dest])
      ((_,_, transitions1, firstState1, [lastState1]), availState1) = createNfaRec n reg1
      ((_,_, transitions2, firstState2, [lastState2]), availState2) = createNfaRec availState1 reg2
      (src,dest,nextAvailState) = (availState2, availState2+1, availState2+2)
      transitions = (src,firstState1,'_') : (src,firstState2,'_') : (lastState1,dest,'_') : (lastState2,dest,'_') : (transitions1 ++ transitions2)

createNfaRec _ _ = error "createNfaRec: Not a regex given"


makeNfa :: [Char] -> Fsa
makeNfa str = (states, inputs, transitions, firstState, lastStates)
    where 
      ((_, _, transitions, firstState, lastStates), nextAvailState) = createNfaRec 1 (parseRegexpr str)
      states = [1..nextAvailState-1]
      inputs = removeDuplicates . filter isValidInput $ str
      isValidInput c = not ( c == '_' || c == '|' || c == '(' || c == ')' || c == '*' || c == ' ' )