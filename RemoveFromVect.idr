import Data.Vect

notInNil : Elem value [] -> Void
notInNil Here impossible
notInNil (There _) impossible

notInTail : (notHere : (value = x) -> Void) -> (notThere : Elem value xs -> Void) -> Elem value (x :: xs) -> Void
notInTail notHere notThere Here = notHere Refl
notInTail notHere notThere (There later) = notThere later

myIsElem: DecEq a => (value: a) -> (xs: Vect n a) -> Dec(Elem value xs)
myIsElem value [] = No notInNil
myIsElem value (x :: xs) = case decEq value x of
  (Yes Refl)    => Yes Here
  (No  notHere) => case myIsElem value xs of
    (Yes prf) => Yes (There prf)
    (No notThere) => No (notInTail notHere notThere)

removeElem: (value: a) -> (xs: Vect (S n) a) -> (prf: Elem value xs) -> Vect n a
removeElem             value (value :: ys) Here         = ys
removeElem {n = Z}     value (y     :: []) (There later) = absurd later
removeElem {n = (S k)} value (y     :: ys) (There later) = y :: removeElem value ys later

maryInVector: Elem "Mary" ["Peter", "Paul", "Mary"]
maryInVector =  There (There Here)

data Last: List a -> a -> Type where
  LastOne: Last [value] value
  LastCons: (prf: Last xs value) -> Last (x :: xs) value

last123: Last [1, 2, 3] 3
last123 = LastCons (LastCons LastOne)

notInEmpty : Last [] value -> Void
notInEmpty LastOne impossible
notInEmpty (LastCons _) impossible

notTheLastOne : (notLast : (x = value) -> Void) -> Last [x] value -> Void
notTheLastOne notLast LastOne = notLast Refl
notTheLastOne _ (LastCons LastOne) impossible
notTheLastOne _ (LastCons (LastCons _)) impossible

notInListTail : (notInTail : Last (mid :: tail) value -> Void) -> Last (x :: (mid :: tail)) value -> Void
notInListTail notInTail (LastCons prf) = notInTail prf

total isLast: DecEq a => (xs: List a) -> (value: a) -> Dec(Last xs value)
isLast [] value = No notInEmpty
isLast (last :: []) value = case decEq last value of
  (Yes Refl) => Yes LastOne
  (No contra) => No (notTheLastOne contra)
isLast (head :: mid :: tail) value = case isLast (mid :: tail) value of
  (Yes prf) => Yes (LastCons prf)
  (No notInTail) => No (notInListTail notInTail)
