import Control.Monad.State

update : (stateType -> stateType) -> State stateType ()
update func =
  do
    currState <- get
    put (func currState)

increase : Nat -> State Nat ()
increase diff = update (+diff)