
module Types
(
  StateId,
  TransChar,
  Inputs,
  Transition,
  States,
  Transitions,
  FirstState,
  LastStates,
  Fsa
)
where

type StateId = Int
type TransChar = Char
type Inputs = [TransChar]
type Transition = (StateId, StateId, TransChar)
type States = [StateId]
type Transitions = [Transition]
type FirstState = StateId
type LastStates = States
type Fsa = (States, Inputs, Transitions, FirstState, LastStates)
