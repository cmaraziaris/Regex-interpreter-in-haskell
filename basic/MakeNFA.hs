
module MakeNFA (makeNfa) where

import RegParser
import Types

-- type Fsa = (States, Inputs, Transitions, FirstState, LastStates)

type AvailableState = StateId

-- TODO: Replace with merge-sort
quicksort1 :: (Ord a) => [a] -> [a]
quicksort1 [] = []
quicksort1 (x:xs) =
  let smallerSorted = quicksort1 [a | a <- xs, a < x]
      biggerSorted = quicksort1 [a | a <- xs, a > x]  -- !! Don't keep equals
  in  smallerSorted ++ [x] ++ biggerSorted


createNfaRec :: AvailableState -> RegExpr -> (Fsa, AvailableState)

createNfaRec n EmptyChar = ( ([x,y], [], [(x,y,'_')], x, [y]), n+2 )
                        where (x,y) = (n,n+1)

createNfaRec n AnyLetter = ( ([x,y], ['.'], [(x,y,'.')], x, [y]), n+2 )
                        where (x,y) = (n,n+1)

createNfaRec n (Letter c) = ( ([x,y], [c], [(x,y,c)], x, [y]), n+2 )
                        where (x,y) = (n,n+1)

createNfaRec n (Kleene reg) = ( (states, inputs', transitions, x, [y]), availableState+2 )
        where ((states', inputs', transitions', firstState', [lastState']), availableState) = createNfaRec n reg
              (x,y) = (availableState, availableState+1)
              states = [1..availableState+1] -- no need to update state in createNfaRec
              transitions = (x,y,'_') : (x,firstState','_') : (lastState',y,'_') : (lastState',firstState','_') : transitions'

createNfaRec n (Concat (reg1, reg2)) = ( (states, inputs, transitions, firstState1, [lastState2]), availableState2 )
        where ((states1, inputs1, transitions1, firstState1, [lastState1]), availableState1) = createNfaRec n reg1
              ((states2, inputs2, transitions2, firstState2, [lastState2]), availableState2) = createNfaRec availableState1 reg2
              states = [1..availableState2-1]
              inputs = inputs1 ++ inputs2
              transitions = (lastState1,firstState2,'_') : (transitions1 ++ transitions2)

createNfaRec n (Union (reg1, reg2)) = ( (states, inputs, transitions, x, [y]), availableState2+2 )
        where ((states1, inputs1, transitions1, firstState1, [lastState1]), availableState1) = createNfaRec n reg1
              ((states2, inputs2, transitions2, firstState2, [lastState2]), availableState2) = createNfaRec availableState1 reg2
              (x,y) = (availableState2, availableState2+1)
              states = [1..availableState2+1]
              inputs = inputs1 ++ inputs2  -- not needed, can find inputs by initial str via sort + rm dupl + rm ()|* ' '
              transitions = (x,firstState1,'_') : (x,firstState2,'_') : (lastState1,y,'_') : (lastState2,y,'_') : (transitions1 ++ transitions2)

makeNfa :: [Char] -> Fsa
makeNfa str = (states, inputs, t, f, [l])
        where ((s, inputs', t, f, [l]), n) = createNfaRec 1 (parseRegexpr str)
              inputs = quicksort1 inputs'
              states = [1..n-1]