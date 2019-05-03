import Control.Monad.State

data Tree a = Empty | Node (Tree a) a (Tree a)

testTree : Tree String
testTree = Node (Node (Node Empty "Jim" Empty) "Fred" (Node Empty "Sheila" Empty)) "Alice" (Node Empty "Bob" (Node Empty "Eve" Empty))

testStream : Stream Int
testStream = [1..]

flatten : Tree a -> List a
flatten Empty = []
flatten (Node left val right) = flatten left ++ (val :: flatten right)

labelTreeWith : Stream label -> Tree elem -> (Stream label, Tree (label, elem))
labelTreeWith lbls Empty        = (lbls, Empty)
labelTreeWith lbls (Node l e r) = 
  let
    (forThis :: forRight, lbldLeft) = labelTreeWith lbls l
    (forNext, lbldRight) = labelTreeWith forRight r
  in
    (forNext, Node lbldLeft (forThis, e) lbldRight)

labelTreeWith2 : Tree a -> State (Stream label) (Tree (label, a))
labelTreeWith2 Empty                  = pure Empty
labelTreeWith2 (Node left elem right) =
  do
    lbldLeft <- labelTreeWith2 left
    (this :: rest) <- get
    put rest
    lbldRight <- labelTreeWith2 right
    pure (Node lbldLeft (this, elem) lbldRight)

deepFirst : Tree elem -> Tree (Int, elem)
deepFirst tree = snd (labelTreeWith testStream tree)

deepFirst2 : Tree elem -> Tree (Int, elem)
deepFirst2 tree = evalState (labelTreeWith2 tree) [1..]

countEmpty : Tree elem -> State Nat ()
countEmpty Empty =
  do
    curr <- get
    put (S curr)
countEmpty (Node left _ right) =
  do
    countEmpty left
    countEmpty right

countEmptyNode : Tree elem -> State (Nat, Nat) ()
countEmptyNode Empty =
  do
    (currEmpties, currFull) <- get
    put (S currEmpties, currFull)
countEmptyNode (Node left _ right) =
  do
    countEmptyNode left
    countEmptyNode right
    (currEmpties, currFull) <- get
    put (currEmpties, S currFull)
