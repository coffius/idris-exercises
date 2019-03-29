data InfIO: Type where
  Do: IO a -> (a -> Inf InfIO) -> InfIO

(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

partial
forever: Fuel
forever = More forever

total
run: Fuel -> InfIO -> IO()
run Dry         y                = putStrLn "Out of fuel"
run (More fuel) (Do action cont) =
  do
    res <- action
    run fuel (cont res)

total
totalRepl : (prompt: String) -> (action: String -> String) -> InfIO
totalRepl prompt action =
  do
    input <- getLine
    putStr ((action input) ++ prompt)
    totalRepl prompt action

partial
main : IO()
main = run forever (totalRepl "\n: " toUpper)
