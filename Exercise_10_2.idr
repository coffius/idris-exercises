import Data.List.Views
import Data.Vect
import Data.Vect.Views
import Data.Nat.Views

total equalSuffixHelper: Eq a => List a -> List a -> List a
equalSuffixHelper input1 input2 with (snocList input1)
  equalSuffixHelper [] input2          | Empty = []
  equalSuffixHelper (xs ++ [x]) input2 | (Snoc xs_rec) with (snocList input2)
    equalSuffixHelper (xs ++ [x]) []          | (Snoc xs_rec) | Empty      = []
    equalSuffixHelper (xs ++ [x]) (ys ++ [y]) | (Snoc xs_rec) | (Snoc ys_rec) =
      if x == y
      then x :: (equalSuffixHelper xs ys | xs_rec | ys_rec)
      else []

total equalSuffix: Eq a => List a -> List a -> List a
equalSuffix xs ys = reverse (equalSuffixHelper xs ys)

total mergeSort: Ord a => Vect n a -> Vect n a
mergeSort input with (splitRec input)
  mergeSort []  | SplitRecNil = []
  mergeSort [x] | SplitRecOne = [x]
  mergeSort (lefts ++ rights) | (SplitRecPair lrec rrec) =
    merge (mergeSort lefts  | lrec)
          (mergeSort rights | rrec)

total toBinary: Nat -> String
toBinary input with (halfRec input)
  toBinary Z           | HalfRecZ          = ""
  toBinary (n + n)     | (HalfRecEven rec) = (toBinary n | rec) ++ "0"
  toBinary (S (n + n)) | (HalfRecOdd rec)  = (toBinary n | rec) ++ "1"

total palindrome: Eq a => List a -> Bool
palindrome input with (vList input)
  palindrome []  | VNil = True
  palindrome [x] | VOne = True
  palindrome (first :: (mid ++ [last])) | (VCons rec) =
    if first == last
    then palindrome mid | rec
    else False

list : List Int
list = [1..5]

test1 : List Int
test1 = [1,2,4,5]

vect1 : Vect 10 Integer
vect1 = [1,2,3,4,5,6,7,8,9,0]
