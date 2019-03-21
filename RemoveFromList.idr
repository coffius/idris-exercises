removeFromList: Eq a => (elem: a) -> List a -> List a
removeFromList elem [] = []
removeFromList elem (head :: tail) =
  if   elem == head
  then removeFromList elem tail
  else head :: (removeFromList elem tail)

example1: List Int
example1 = [1,2,3,1,2,3]
