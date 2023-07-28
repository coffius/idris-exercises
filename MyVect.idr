module MyVect

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

reverse : MyVect len elem -> MyVect len elem
reverse xs = go [] xs
  where go : MyVect n elem -> MyVect m elem -> MyVect (n+m) elem
        go {n}         acc []        = rewrite plusZeroRightNeutral n in acc
        go {n} {m=S m} acc (x :: xs) = rewrite sym $ plusSuccRightSucc n m
                                       in go (x::acc) xs

(++) : (xs : MyVect m elem) -> (ys : MyVect n elem) -> MyVect (m + n) elem
(++) []      ys = ys
(++) (x::xs) ys = x :: xs ++ ys                                       


-- Refl - short for reflexivity(or Reflexive relation)
-- It means that x = x, a = a and so on. In broad terms it means that a value is equal to itself
sameLen: (first: MyVect n a) -> (second: MyVect m a) -> (first = second) -> (n = m)
sameLen second second Refl = Refl

-- To Show:
-- 1. sameLen example1 example2 correctProof
-- 2. sameLen example1 example3 correctProof
-- 3. sameLen example1 example3
-- 4. sameLen example1 example3 Refl

example1: MyVect 4 Integer
example1 = 1 :: 2 :: 3 :: 4 :: Nil

example2: MyVect 4 Integer
example2 = 1 :: 2 :: 3 :: 4 :: Nil

example3: MyVect 4 Integer
example3 = 1 :: 2 :: 3 :: 4 :: Nil

-- One number less
example4: MyVect 3 Integer
example4 = 1 :: 2 :: 3 :: Nil

example5: MyVect 4 Integer
example5 = 1 :: 2 :: 3 :: 5 :: Nil

correctProof: (MyVect.example1 = MyVect.example2)
correctProof = case decEq MyVect.example1 MyVect.example2 of 
  Yes Refl => Refl

-- incorrectProof: (MyVect.example1 = MyVect.example2)
-- incorrectProof = case decEq MyVect.example1 MyVect.example2 of 
--   Yes Refl => Refl

-- incorrectProof2: (MyVect.example1 = MyVect.example3)
-- incorrectProof2 = case decEq MyVect.example1 MyVect.example3 of 
--   Yes Refl => Refl

