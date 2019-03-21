data SnocList: List a -> Type where
  Empty: SnocList []
  Snoc: (rec: SnocList xs) -> SnocList (xs ++ [x])

snocListHelp: (snoc: SnocList input) -> (rest: List a) -> SnocList (input ++ rest)
snocListHelp {input} snoc [] = rewrite appendNilRightNeutral input in snoc
snocListHelp {input} snoc (x :: xs) =
  rewrite appendAssociative input [x] xs in
          snocListHelp (Snoc snoc) xs
-- snocListHelp {input} snoc [] = ?noRewrite1 snoc
-- snocListHelp {input} snoc (x :: xs) = ?noRewrite2 (snocListHelp (Snoc snoc {x}) xs)

snocList: (xs: List a) -> SnocList xs
snocList xs = snocListHelp Empty xs

total myReverseHelper: (input: List a) -> SnocList input -> List a
myReverseHelper []          Empty      = []
myReverseHelper (xs ++ [x]) (Snoc rec) = x :: myReverseHelper xs rec

total myReverse: List a -> List a
myReverse input with (snocList input)
  myReverse []          | Empty       = []
  myReverse (xs ++ [x]) | (Snoc rec)  = x :: myReverse xs | rec

total isSuffix: Eq a => List a -> List a -> Bool
isSuffix input1 input2 with (snocList input1)
  isSuffix []          input2 | Empty      = True
  isSuffix (xs ++ [x]) input2 | (Snoc xsrec) with (snocList input2)
    isSuffix (xs ++ [x]) []          | (Snoc xsrec) | Empty        = False
    isSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc xsrec) | (Snoc ysrec) =
      if x == y
      then isSuffix xs ys | xsrec | ysrec
      else False

list100: List Int
list100 = [1..100]

suffix: List Int
suffix = [90..100]

notSuffix: List Int
notSuffix = [1..10]
