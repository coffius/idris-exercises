myPlusCommutes: (left: Nat) -> (right: Nat) -> left + right = right + left
myPlusCommutes Z right = rewrite plusZeroRightNeutral right in Refl
myPlusCommutes (S left) right = 
  rewrite myPlusCommutes left right in 
  rewrite plusSuccRightSucc right left in Refl
