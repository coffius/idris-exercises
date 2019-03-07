import Data.Vect

proofNil : Vect n elem -> Vect (n + 0) elem
proofNil {n} xs = rewrite plusZeroRightNeutral n in xs

proofNext : Vect (1 + n + k) elem -> Vect (n + (1 + k)) elem
proofNext {n} {k} xs =
  let hypothesis = sym $ plusSuccRightSucc n k 
  in rewrite hypothesis 
  in xs

go : Vect n elem -> Vect m elem -> Vect (n+m) elem
go acc []        = proofNil acc
go acc (x :: xs) = proofNext (go (x::acc) xs)

total myReverse : Vect len elem -> Vect len elem
myReverse xs = go [] xs

-- total invalidReverseList : List a -> List a
-- invalidReverseList input = []

example: Vect 4 String
example = ["1", "2", "3", "4"]

result: Vect 4 String
result = myReverse example