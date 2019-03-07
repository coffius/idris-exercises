module Main

import Data.Vect

StringOrInt: (x: Bool) -> Type
StringOrInt x = case x of
    True => Int
    False => String

getStringOrInt : (x : Bool) -> StringOrInt x
getStringOrInt x = case x of
    True => 94
    False => "Ninety four"

average: (str: String) -> Double
average str = let numWords = wordCount str
                  totalLenght = sum(allLengths (words str)) in
                  cast totalLenght / cast numWords
    where
        wordCount :  String -> Nat
        wordCount str = length (words str)

        allLengths : List String -> List Nat
        allLengths strs = map length strs 

double: Num input => input -> input
double input = input + input

twice: (f: a -> a) -> (x: a) -> a
twice f x = f (f x)

palindrome2: String -> Bool
palindrome2 x = toLower x == toLower (reverse x)

palindrome4: Nat -> String -> Bool
palindrome4 len str = if length str > len then palindrome2 str else False

palindrome3: String -> Bool
palindrome3 x = palindrome4 10 x

counts: String -> (Nat, Nat)
counts str = let numOfWords = length (words str)
                 numOfChars = length str in
                    (numOfWords, numOfChars)

top_ten: Ord a => List a -> List a
top_ten list = let sorted = reverse (sort list)
                   topTen = take 10 sorted in
                     topTen

over_length: Nat -> List String -> Nat
over_length len list = length (filter (\x => length(x) > len) list)

allLengths: Vect len String -> Vect len Nat
allLengths [] = []
allLengths (x :: xs) = length x :: allLengths xs

insertList: Ord elem => elem -> (xsSorted : Vect len elem) -> Vect (S len) elem
insertList x [] = [x]
insertList x (y :: xs) = if x < y
    then x :: y :: xs
    else y :: insertList x xs

insSort: Ord elem => Vect n elem -> Vect n elem
insSort [] = []
insSort (x :: tail) =
    let
        sortedTail = insSort tail
        in
            insertList x sortedTail

total my_length: List a -> Nat
my_length [] = 0
my_length (x :: xs) = 1 + my_length xs

total pushToEnd : a -> List a -> List a
pushToEnd x [] = [x]
pushToEnd x (y :: ys) = y :: pushToEnd x ys

total my_reverse: List a -> List a
my_reverse [] = []
my_reverse (x :: xs) =
    let reversed = my_reverse xs
    in pushToEnd x reversed

total my_map: (a -> b) -> List a -> List b
my_map f [] = []
my_map f (x :: xs) = f x :: my_map f xs

total my_vect_map: (a -> b) -> Vect n a -> Vect n b
my_vect_map f [] = []
my_vect_map f (x :: xs) = f x :: my_vect_map f xs

total createEmpties : Vect n (Vect 0 elem)
createEmpties = replicate _ []

total transposeHelper : (x : Vect n elem) -> (xsTrans : Vect n (Vect len elem)) -> Vect n (Vect (S len) elem)
transposeHelper [] [] = []
transposeHelper (x :: xs) (y :: ys) = (x :: y) :: transposeHelper xs ys

total transposeMat: Vect m (Vect n elem) -> Vect n (Vect m elem)
transposeMat [] = createEmpties
transposeMat (x :: xs) =
    let xsTrans = transposeMat xs
    in transposeHelper x xsTrans

data Direction = North | East | South | West

turnClockwise: Direction -> Direction
turnClockwise North = East
turnClockwise East = South
turnClockwise South = West
turnClockwise West = North

data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

area: Shape -> Double
area (Triangle base height) = 0.5 * base * height
area (Rectangle length height) = length * height
area (Circle radius) = pi * radius * radius

data BSTree : Type -> Type where
    Leaf : Ord elem => BSTree elem
    Node : Ord elem => (left: BSTree elem) -> (val: elem) -> (right: BSTree elem) -> BSTree elem

total insertTree: elem -> BSTree elem -> BSTree elem
insertTree x Leaf = Node Leaf x Leaf
insertTree x orig@(Node left val right) =
    case compare x val of
        LT => Node (insertTree x left) val right
        EQ => orig
        GT => Node left val (insertTree x right)

listToTree: Ord a => List a -> BSTree a
listToTree [] = Leaf
listToTree (x :: xs) =
    let tailAsTree = listToTree xs
    in insertTree x tailAsTree

treeToList: BSTree a -> List a
treeToList Leaf = []
treeToList (Node left val right) =
    let leftPart = treeToList left
        rightPart = val :: treeToList right
    in leftPart ++ rightPart

data Expr = Val Int 
          | Add Expr Expr
          | Sub Expr Expr
          | Mult Expr Expr

total evaluate: Expr -> Int
evaluate (Val value) = value
evaluate (Add l r) = evaluate l + evaluate r
evaluate (Sub l r) = evaluate l - evaluate r
evaluate (Mult l r) = evaluate l * evaluate r

total maxMaybe: Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe Nothing Nothing = Nothing
maxMaybe Nothing (Just x) = Just x
maxMaybe (Just x) Nothing = Just x
maxMaybe (Just x) (Just y) =
    let max = if x > y then x else y
    in Just max

data Picture = Primitive Shape
             | Combine Picture Picture
             | Rotate Double Picture
             | Translate Double Double Picture

total biggestTriangle: Picture -> Maybe Double
biggestTriangle (Primitive shape@(Triangle x y)) = Just(area shape)
biggestTriangle (Primitive (Rectangle x y)) = Nothing
biggestTriangle (Primitive (Circle x)) = Nothing
biggestTriangle (Combine left right) =
    let maybeLeft  = biggestTriangle left
        maybeRight = biggestTriangle right 
    in maxMaybe maybeLeft maybeRight
biggestTriangle (Rotate _ pic) = biggestTriangle pic
biggestTriangle (Translate _ _ pic) = biggestTriangle pic

data PowerSource = Petrol | Pedal
data Vehicle : PowerSource -> Type where
    Bicycle: Vehicle Pedal
    Car : (fuel: Nat) -> Vehicle Petrol
    Bus : (fuel: Nat) -> Vehicle Petrol

wheels : Vehicle _ -> Nat
wheels Bicycle = 2
wheels Car = 4
wheels Bus = 4

refuel: Vehicle Petrol -> Vehicle Petrol
refuel (Car _) = Car 100
refuel (Bus _) = Bus 200
refuel Bicycle impossible

append_nil : Vect m elem -> Vect (plus m 0) elem
append_nil {m} xs = rewrite plusZeroRightNeutral m in xs

append_xs : Vect (S (m + len)) elem -> Vect (plus m (S len)) elem
append_xs {m} {len} xs = rewrite sym (plusSuccRightSucc m len) in xs

append : Vect n elem -> Vect m elem -> Vect (m + n) elem
append [] ys = append_nil ys
append (x :: xs) ys = append_xs (x :: append xs ys)

total my_zip : Vect n a -> Vect n b -> Vect n (a, b)
my_zip [] [] = []
my_zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys

tryIndex : Integer -> Vect n a -> Maybe a
tryIndex {n} i vector =
    case integerToFin i n of
        Nothing => Nothing
        (Just idx) => Just (index idx vector)

vectTake: (n: Nat) -> Vect (n + m) elem -> Vect n elem
vectTake Z xs = []
vectTake (S k) (x :: xs) = x :: vectTake k xs

total sumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries {n} pos left right =
    case integerToFin pos n of
        Nothing => Nothing
        (Just x) => let leftVal = index x left 
                        rightVal = index x right
                    in Just (leftVal + rightVal)
                    

main : IO ()
main = repl "\n> " reverse

