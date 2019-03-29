import InfList
import Data.Primitives.Views
import Data.Nat.Views

-- exercise #1
every_other : Stream a -> Stream a
every_other (first :: second :: tail) = second :: every_other tail

-- Exercise #2
Functor InfList where
  map func (value :: tail) = (func value) :: (map func tail)

infListFunctorTest: List Integer
infListFunctorTest = getPrefix 10 (map (*2) (countFrom 1))

-- Exercise #3
data Face = Heads | Tails

getFace : Int -> Face
getFace number with (divides number 2)
  getFace ((2 * div) + rem) | (DivBy prf) = if rem <= 0 then Heads else Tails

randoms : Int -> Stream Int
randoms seed =
  let seed' = 1664525 * seed + 1013904223 in
      (seed' `shiftR` 2) :: randoms seed'

coinFlips : Nat -> Stream Int -> List Face
coinFlips count stream = map getFace (take count stream)

flipsTest : List Face
flipsTest = coinFlips 6 (randoms 12345)

-- Exercise #4
calcNext: (number: Double) -> (approx: Double) -> Double
calcNext number approx = (approx + (number / approx)) / 2

square_root_approx : (number: Double) -> (approx: Double) -> Stream Double
square_root_approx number approx = approx :: square_root_approx number (calcNext number approx)

sqrtTest1 : List Double
sqrtTest1 = take 3 $ square_root_approx 10 10

sqrtTest2 : List Double
sqrtTest2 = take 10 $ square_root_approx 100 25

-- Exercise #5
square_root_bound : (max: Nat) -> (number: Double) -> (bound : Double) -> (approxs: Stream Double) -> Double
square_root_bound  Z    number bound (value :: xs) = value
square_root_bound (S k) number bound (apprx :: xs) =
  if isBoundReached
  then apprx
  else square_root_bound k number bound xs
  where
    isBoundReached : Bool
    isBoundReached = (apprx * apprx - number) < bound

square_root : Double -> Double
square_root value = square_root_bound 100 value 0.00000000001 (square_root_approx value value)

boundedSqrtTest1: Double
boundedSqrtTest1 = square_root 6

boundedSqrtTest2: Double
boundedSqrtTest2 = square_root 2500

boundedSqrtTest3: Double
boundedSqrtTest3 = square_root 2501
