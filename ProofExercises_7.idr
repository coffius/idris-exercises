total sameCons: {xs: List a} -> {ys: List a} -> xs = ys -> x :: xs = x :: ys
sameCons Refl = Refl

total sameLists: {xs: List a} -> {ys: List a} -> x = y -> xs = ys -> x :: xs = y :: ys
sameLists Refl Refl = Refl

data ThreeEq: Nat -> Nat -> Nat -> Type where
  Same: (x:Nat) -> ThreeEq x x x

total allSameS: (x, y, z: Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS x x x (Same x) = Same (S x)