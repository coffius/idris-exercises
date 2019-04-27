data MyVect : (len: Nat) -> (elem: Type) -> Type where
  Nil  : MyVect 0 elem
  (::) : (e: elem) -> (tail: MyVect len elem) -> MyVect (S len) elem

Eq elem => Eq (MyVect n elem) where
  (==) Nil Nil = True
  (==) (head :: tail) (head' :: tail') = head == head' && tail == tail'

Foldable (MyVect n) where
  foldr func acc Nil = acc
  foldr func acc (e :: tail) =
    let
      foldedTail = foldr func acc tail
    in
      func e foldedTail

data EqNat: (num1: Nat) -> (num2: Nat) -> Type where
  Same: (num: Nat) -> EqNat num num

sameS : (k: Nat) -> (j: Nat) -> (eq : EqNat k j) -> EqNat (S k) (S j)
sameS j j (Same j) = Same (S j)

-- checkEqNat: (num1: Nat) -> (num2: Nat) -> Maybe (num1 = num2)
-- checkEqNat Z Z = Just Refl
-- checkEqNat Z (S k) = Nothing
-- checkEqNat (S k) Z = Nothing
-- checkEqNat (S k) (S j) =
--   case checkEqNat k j of
--     Nothing => Nothing
--     Just prf => Just (cong prf)

total zeroNotSuc : (0 = S k) -> Void
zeroNotSuc Refl impossible

total sucNotZero : (S k = 0) -> Void
sucNotZero Refl impossible

noRec : (contra : (k = j) -> Void) -> (S k = S j) -> Void
noRec contra Refl = contra Refl

checkEqNat: (num1: Nat) -> (num2: Nat) -> Dec (num1 = num2)
checkEqNat Z Z = Yes Refl
checkEqNat Z (S k) = No zeroNotSuc
checkEqNat (S k) Z = No sucNotZero
checkEqNat (S k) (S j) = case checkEqNat k j of
  Yes prf => Yes (cong prf)
  No contra => No (noRec contra)

exactLength: (len: Nat) -> (input: MyVect m a) -> Maybe (MyVect len a)
exactLength {m} len input =
  case decEq m len of
    Yes Refl  => Just input
    No contra => Nothing

total headUnequal: {xs: MyVect n a} -> {ys: MyVect n a} -> (contra: (x = y) -> Void) -> ((x :: xs) = (y :: ys)) -> Void
headUnequal contra Refl = contra Refl

total tailUnequal: {xs: MyVect n a} -> {ys: MyVect n a} -> (contra: (xs = ys) -> Void) -> ((x :: xs) = (y :: ys)) -> Void
tailUnequal contra Refl = contra Refl

DecEq a => DecEq (MyVect n a) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) (y :: ys) = case decEq x y of
    Yes Refl => case decEq xs ys of
      Yes Refl  => Yes Refl
      No contra => No (tailUnequal contra)
    No contra => No (headUnequal contra)

example1: MyVect 4 Integer
example1 = 1 :: 2 :: 3 :: 4 :: Nil

example1': MyVect 4 Integer
example1' = 1 :: 2 :: 3 :: 4 :: Nil

example2: MyVect 3 Integer
example2 = 1 :: 2 :: 3 :: Nil

example3: MyVect 4 Integer
example3 = 4 :: 3 :: 2 :: 1 :: Nil

natEqual: (x: Nat) -> (y: Nat) -> Maybe(x = y)
natEqual Z Z = Just Refl
natEqual Z (S k) = Nothing
natEqual (S k) Z = Nothing
natEqual (S k) (S j) = case natEqual k j of
  Nothing => Nothing
  (Just prf) => Just (cong prf)
