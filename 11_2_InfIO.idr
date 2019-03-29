data InfIO: Type where
  Do: IO a -> (a -> Inf InfIO) -> InfIO

(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

forever: Fuel
forever = More forever

tank: Nat -> Fuel
tank Z = Dry
tank (S k) = More (tank k)

printLoop: String -> InfIO
printLoop msg =
  do
    putStrLn msg
    printLoop msg

run: InfIO -> IO()
run (Do action cont) =
  do
    res <- action
    run (cont res)

runFuel: Fuel -> InfIO -> IO()
runFuel Dry         y                = putStrLn "Out of fuel"
runFuel (More fuel) (Do action cont) =
  do
    res <- action
    runFuel fuel (cont res)
