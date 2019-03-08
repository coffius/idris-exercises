data ListLast: List a -> Type where
  Empty: ListLast []
  NonEmpty: (xs: List a) -> (x: a) -> ListLast (xs ++ [x])

total listLast: (xs: List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) = case listLast xs of
  Empty => NonEmpty [] x
  (NonEmpty ys y) => NonEmpty (x :: ys) y  

total describeHelper: (input: List Int) -> (form: ListLast input) -> String
describeHelper []          Empty           = "Empty"
describeHelper (xs ++ [x]) (NonEmpty xs x) = "NonEmpty - All but one: " ++ show xs

total describeListEnd: List Int -> String
describeListEnd xs with (listLast xs)
  describeListEnd []          | Empty           = "Empty!"
  describeListEnd (ys ++ [x]) | (NonEmpty ys x) = "Non-empty :) All but last: " ++ show ys

list1: List Int
list1 = [1,2,3]

