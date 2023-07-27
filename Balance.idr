import Prelude.Nat

withdraw: (balance: Nat) -> (amount: Nat) -> (prf: LTE amount balance) -> Nat
withdraw balance amount _ = balance - amount

doWithdraw: (balance: Nat) -> (amount: Nat) -> Either String Nat
doWithdraw balance amount = case isLTE amount balance of
    (Yes prf) => Right(withdraw balance amount prf)
    (No _)    => Left("balance too low")
