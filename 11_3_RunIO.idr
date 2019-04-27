data RunIO : Type -> Type where
  Quit: a -> RunIO a
  Do: IO a -> (a -> Inf(RunIO b)) -> RunIO b

(>>=) : IO a -> (a -> Inf(RunIO b)) -> RunIO b
(>>=) = Do

greet : RunIO ()
greet =
  do
    putStrLn "Enter your name: "
    name <- getLine
    if name == ""
      then Quit ()
      else
        do
          putStrLn ("Your name is " ++ name)
          greet

data Fuel = Dry | More (Lazy Fuel)

forever : Fuel
forever = More forever

run: Fuel -> RunIO a -> IO (Maybe a)
run Dry         y             = pure Nothing
run (More fuel) (Quit result) = pure (Just result)
run (More fuel) (Do io func)  =
  do
    result <- io
    run fuel (func result)

main : IO()
main =
  do
    run forever greet
    pure ()
