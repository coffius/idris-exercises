import Data.List.Views

list1: List Int
list1 = [1,2,3]

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

myReverse: List a -> List a
myReverse input with (listLast input)
  myReverse [] | Empty = []
  myReverse (xs ++ [x]) | (NonEmpty xs x) = x :: myReverse xs

data SplitList: List a -> Type where
  SplitNil:  SplitList []
  SplitOne:  SplitList [x]
  SplitPair: (lefts: List a) -> (rights: List a) -> SplitList (lefts ++ rights)

total splitList: (input: List a) -> SplitList input
splitList input = splitListHelp input input
  where
    splitListHelp: List a -> (input: List a) -> SplitList input
    splitListHelp _  []  = SplitNil
    splitListHelp _  [x] = SplitOne
    splitListHelp (_ :: _ :: counter) (item :: items) =
      case splitListHelp counter items of
        SplitNil               => SplitOne
        SplitOne {x}           => SplitPair [item] [x]
        SplitPair lefts rights => SplitPair (item :: lefts) rights
    splitListHelp _ items = SplitPair [] items

mergeSort: Ord a => List a -> List a
mergeSort input with (splitList input)
  mergeSort [] | SplitNil = []
  mergeSort [x] | SplitOne = [x]
  mergeSort (lefts ++ rights) | (SplitPair lefts rights) =
    merge (mergeSort lefts) (mergeSort rights)

total mergeSort2: Ord a => List a -> List a
mergeSort2 input with (splitRec input)
  mergeSort2 []   | SplitRecNil = []
  mergeSort2 [x]  | SplitRecOne = [x]
  mergeSort2 (lefts ++ rights) | (SplitRecPair lrec rrec) =
    merge (mergeSort2 lefts  | lrec)
          (mergeSort2 rights | rrec)


example: List Int
example = [6,5,4,3,3,1,3,7,3,4,5,1,2,1,2,4,6,9,6]
