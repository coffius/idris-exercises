data BSTree elem = Empty
                 | Node (BSTree elem) elem (BSTree elem)

Eq elem => Eq (BSTree elem) where
  (==) Empty Empty = True
  (==) (Node left e right) (Node left' e' right') =
    left == left' && e == e' && right == right'
  (==) _ _ = False

Functor BSTree where
  map func Empty = Empty
  map func (Node left e right) = Node(map func left) (func e) (map func right)

Foldable BSTree where
  foldr func acc Empty = acc
  foldr func acc (Node left e right) =
    let
      leftFold = foldr func acc left
      rightFold = foldr func leftFold right
    in
      func e rightFold
