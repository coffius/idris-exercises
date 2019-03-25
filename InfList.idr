module InfList

public export
data InfList : Type -> Type where
  (::) : (value: elem) -> Inf (InfList elem) -> InfList elem

%name InfList xs, ys, zs

public export
total countFrom : Integer -> InfList Integer
countFrom x = x :: countFrom (x + 1)

public export
total labelFrom : InfList k -> List a -> List (k, a)
labelFrom (key :: xs) []        = []
labelFrom (key :: xs) (y :: ys) = (key, y) :: labelFrom xs ys

public export
total labelWith : Stream labelType -> List a -> List (labelType, a)
labelWith xs [] = []
labelWith (lbl :: lbls) (x :: xs) = (lbl, x) :: labelWith lbls xs

public export
total label : List a -> List (Integer, a)
label = labelWith (iterate (+1) 0)

public export
total getPrefix : (count: Nat) -> InfList ty -> List ty
getPrefix Z     (value :: xs) = []
getPrefix (S k) (value :: xs) = value :: (getPrefix k xs)
