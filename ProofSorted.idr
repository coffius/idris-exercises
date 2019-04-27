module ProofSorted

checkSorted: Ord ty => List ty -> Bool
checkSorted []  = True
checkSorted [x] = True
checkSorted (x :: xs) =
    case xs of
        []       => True
        (y :: _) => if x <= y 
            then checkSorted xs
            else False

data IsLte : (smaller: ty) -> (bigger: ty) -> Type where
    Lte: IsLte smaller bigger

proveLessThen: Ord ty => (smaller: ty) -> (bigger: ty) -> Dec (IsLte smaller bigger)
proveLessThen smaller bigger =
    case smaller <= bigger of
        False => No  fails
        True  => Yes holds
    where
        fails: IsLte smaller bigger -> Void
        fails prf = believe_me {b = Void} ()
        holds: IsLte smaller bigger
        holds = really_believe_me (Lte {smaller = smaller} {bigger = bigger})


data Sorted : List ty -> Type where
    SortedNil: Sorted []
    SortedOne: (head: ty) -> Sorted [head]
    SortedMany: {tl: List ty} -> (elem: ty) -> Sorted (hd :: tl) -> (prf: IsLte elem hd) -> Sorted (elem :: hd :: tl)

keepsUnsorted : (tailUnsorted : Sorted (second :: tail) -> Void) -> Sorted (first :: (second :: tail)) -> Void
keepsUnsorted tailUnsorted (SortedMany _ tailSort _) = tailUnsorted tailSort

prependUnsorted : (unsorted : IsLte first second -> Void) -> Sorted (first :: (second :: tail)) -> Void
prependUnsorted unsorted (SortedMany _ _ fsSorted) = unsorted fsSorted

proveSorted: Ord ty => (input: List ty) -> Dec(Sorted input)
proveSorted []    = Yes SortedNil
proveSorted [one] = Yes (SortedOne one)
proveSorted (first :: second :: tail) = case proveLessThen first second of
    (Yes fsSorted)  => case proveSorted (second :: tail) of
        (Yes tailSorted)   => Yes (SortedMany first tailSorted fsSorted)
        (No  tailUnsorted) => No  (keepsUnsorted tailUnsorted)
    (No fsUnsorted) => No (prependUnsorted fsUnsorted)
