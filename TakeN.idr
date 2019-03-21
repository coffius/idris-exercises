data TakeN: List a -> Type where
     Fewer: TakeN xs
     Exact: (nXs: List a) -> TakeN (nXs ++ rest)

total takeN: (n: Nat) -> (xs: List a) -> TakeN xs
takeN Z xs = Exact []
takeN (S k) [] = Fewer
takeN (S k) (x :: xs) = case takeN k xs of
  Fewer     => Fewer
  Exact nXs => Exact (x :: nXs)

groupByN: (n: Nat) -> (xs: List a) -> List (List a)
groupByN n xs with (takeN n xs)
  groupByN n xs            | Fewer     = [xs]
  groupByN n (nXs ++ rest) | Exact nXs = nXs :: groupByN n rest

halves: List a -> (List a, List a)
halves xs =
  let
    halfLen = div (length xs) 2
  in
    splitInHalf halfLen xs
  where
    splitInHalf: Nat -> List a -> (List a, List a)
    splitInHalf n xs with (takeN n xs)
      splitInHalf n xs            | Fewer     = ([], xs)
      splitInHalf n (nXs ++ rest) | Exact nXs = (nXs, rest)

example: List Int
example = [1,2,3,4,5,6,7,8,9]

emptyList: List Int
emptyList = []
