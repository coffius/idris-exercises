data State : (stateType : Type) -> Type -> Type where
  Get : State stateType stateType
  Put : stateType -> State stateType ()
  Pure : ty -> State stateType ty
  Bind : State stateType a -> (a -> State stateType b) -> State stateType b

get : State stateType stateType
get = Get

put : stateType -> State stateType ()
put = Put

pure : ty -> State stateType ty
pure = Pure

(>>=) : State stateType a -> (a -> State stateType b) -> State stateType b
(>>=) = Bind

runState : State stateType a -> (st: stateType) -> (a, stateType)
runState Get             st = (st, st)
runState (Put newState)  _  = ((), newState)
runState (Pure x)        st = (x, st)
runState (Bind cmd prog) st =
  let
    (val, nextState) = runState cmd st
  in
    runState (prog val) nextState

implementation Functor (State stateType) where
  map func stA = Bind stA (\valA => Pure (func valA))

implementation Applicative (State stateType) where
  pure  x   = Pure x
  (<*>) x y = Bind x (\func => map func y)

implementation Monad (State stateType) where
  (>>=) = Bind

addIfPositive : Integer -> State Integer Bool
addIfPositive x =
  let
    isPositive = x > 0
  in 
    do when isPositive (
        do current <- get
           put (current + x)
       )
       pure isPositive

addPositives : List Integer -> State Integer Nat
addPositives xs = do added <- traverse addIfPositive xs
                     pure (length (filter id added))

data Tree a = Empty | Node (Tree a) a (Tree a)

testTree : Tree String
testTree = Node (Node (Node Empty "Jim" Empty) "Fred" (Node Empty "Sheila" Empty)) "Alice" (Node Empty "Bob" (Node Empty "Eve" Empty))

labelTreeWith2 : Tree a -> State (Stream label) (Tree (label, a))
labelTreeWith2 Empty                  = pure Empty
labelTreeWith2 (Node left elem right) =
  do
    lbldLeft <- labelTreeWith2 left
    (this :: rest) <- get
    put rest
    lbldRight <- labelTreeWith2 right
    pure (Node lbldLeft (this, elem) lbldRight)

flatten : Tree a -> List a
flatten Empty = []
flatten (Node left val right) = flatten left ++ (val :: flatten right)

deepFirst : Tree elem -> Tree (Int, elem)
deepFirst tree = fst (runState (labelTreeWith2 tree) [1..])

