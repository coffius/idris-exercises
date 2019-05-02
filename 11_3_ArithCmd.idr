module ArithCmd

import Data.Primitives.Views
import System

%default total

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

data Command : Type -> Type where
  PutStr  : String -> Command ()
  GetLine : Command String
  Bind : Command a -> (a -> Command b) -> Command b
  Pure : a -> Command a

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do   : Command a -> (a -> Inf(ConsoleIO b)) -> ConsoleIO b

data Input = Answer Int | QuitCmd

namespace CommandDo
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind

namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf(ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do


readInput: (prompt: String) -> Command Input
readInput prompt =
  do
    PutStr prompt
    answer <- GetLine
    if toLower answer == "quit"
      then Pure QuitCmd
      else Pure (Answer (cast answer))

runCommand : Command ty -> IO ty
runCommand (PutStr x)       = putStr x
runCommand GetLine          = getLine
runCommand (Bind cmdA func) =
  do
    res <- runCommand cmdA
    runCommand (func res)
runCommand (Pure x)       = pure x

run : Fuel -> ConsoleIO a -> IO (Maybe a)
run Dry      _                = pure Nothing
run (More fuel) (Quit res)    = pure (Just res)
run (More fuel) (Do cmd func) =
  do
    cmdRes <- runCommand cmd
    let res = func cmdRes
    run fuel res

quiz : Stream Int -> (score: Nat) -> ConsoleIO Nat
quiz (num1 :: num2 :: nums) score =
  do
    PutStr ("Score so far: " ++ show score ++ "\n")
    input <- readInput (show num1 ++ " * " ++ show num2 ++ " = ? ")
    case input of
      Answer answer => 
        if answer == num1 * num2
          then do PutStr ("Correct!")
                  quiz nums (score + 1)
          else do PutStr ("Wrong! The answer is " ++ show (num1 * num2) ++ "\n")
                  quiz nums score
      QuitCmd  => Quit score


randoms : Int -> Stream Int
randoms seed =
  let seed' = 1664525 * seed + 1013904223 in
      (seed' `shiftR` 2) :: randoms seed'

arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
  where
    bound : Int -> Int
    bound num with (divides num 12)
      bound ((12 * div) + rem) | (DivBy prf) = rem + 1

partial
main: IO ()
main =
  do
    seed       <- time
    Just score <- run forever (quiz (arithInputs(fromInteger seed)) 0)
        | Nothing => putStrLn "Run out of fuel"
    putStrLn ("Final score = " ++ show score)
