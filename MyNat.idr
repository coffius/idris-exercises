module MyNat

data MyNat = Z | S MyNat

total plus : (n, m : MyNat) -> MyNat
plus Z right        = right
plus (S left) right = S (plus left right)

total minus : MyNat -> MyNat -> MyNat
minus Z        right     = Z
minus left     Z         = left
minus (S left) (S right) = minus left right


-- Custom implementation of `nat1 = nat2`
-- We are going to see it below
data EqNat: (num1: MyNat) -> (num2: MyNat) -> Type where
    Same: (num: MyNat) -> EqNat num num

-- Given 
--   one nat k and and another nat j               // Premise 1
-- if
--   we know that k and j are equal                // Premise 2
-- then
--   we know that k+1 and j+1 are equal as well    // Conclusion
sameS : (k: MyNat) -> (j: MyNat) -> (eq : EqNat k j) -> EqNat (S k) (S j)
sameS j j (Same j) = Same (S j)

total zeroNotSuc : (MyNat.Z = MyNat.S k) -> Void
zeroNotSuc Refl impossible

total sucNotZero : (MyNat.S k = MyNat.Z) -> Void
sucNotZero Refl impossible

noRec : (contra : (k = j) -> Void) -> (MyNat.S k = MyNat.S j) -> Void
noRec contra Refl = contra Refl

checkEqNat: (num1: MyNat) -> (num2: MyNat) -> Dec (num1 = num2)
checkEqNat  MyNat.Z     MyNat.Z    = Yes Refl
checkEqNat  MyNat.Z    (MyNat.S k) = No zeroNotSuc
checkEqNat (MyNat.S k)  MyNat.Z    = No sucNotZero
checkEqNat (MyNat.S k) (MyNat.S j) = case checkEqNat k j of
    Yes prf => Yes (cong prf)
    No contra => No (noRec contra)

natEqual: (x: MyNat) -> (y: MyNat) -> Maybe(x = y)
natEqual  MyNat.Z     MyNat.Z    = Just Refl
natEqual  MyNat.Z    (MyNat.S k) = Nothing
natEqual (MyNat.S k)  MyNat.Z    = Nothing
natEqual (MyNat.S k) (MyNat.S j) = 
    case natEqual k j of
        Nothing => Nothing
        (Just prf) => Just (cong prf)