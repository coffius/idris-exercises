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
  ReadFile: (filepath: String) -> Command (Either FileError String)
  WriteFile: (filepath: String) -> (content: String) -> Command (Either FileError ())
  Bind : Command a -> (a -> Command b) -> Command b
  Pure : a -> Command a

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do   : Command a -> (a -> Inf(ConsoleIO b)) -> ConsoleIO b

data Input = Answer Int | QuitCmd
data ShellCmd = Cat String | Copy String String | ExitCmd

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

splitBySpace : String -> List String
splitBySpace str = split (==' ') str

parseShellCmd : List String -> Either String ShellCmd
parseShellCmd []                 = Left "Pls input a command"
parseShellCmd ["exit"]           = Right ExitCmd
parseShellCmd ["cat",  filename] = Right (Cat filename)
parseShellCmd ["copy", src, dst] = Right (Copy src dst)
parseShellCmd (unsupported :: t) = Left ("Cmd [" ++ unsupported ++ "] is unsupported")

-- execShellCmd : ShellCmd -> ConsoleIO ()
-- execShellCmd (Cat file) =
  -- do
  --   result <- ReadFile file
  --   case result of
  --     (Left err)      => PutStr (show err)
  --     (Right content) => PutStr content
-- execShellCmd (Copy src dst) =
  -- do
  --   Right content <- ReadFile src          | Left err => PutStr (show err)
  --   Right _       <- WriteFile dst content | Left err => PutStr (show err)
  --   PutStr "file has been copied successfully"
-- execShellCmd ExitCmd = ?execShellCmd_rhs_3

readShellInput: (prompt: String) -> Command (Either String ShellCmd)
readShellInput prompt =
  do
    PutStr prompt
    cmdStr <- GetLine
    case parseShellCmd(splitBySpace(cmdStr)) of
      (Left err) => Pure (Left err)
      (Right cmd) => Pure (Right cmd)

runCommand : Command ty -> IO ty
runCommand (PutStr x)       = putStr x
runCommand GetLine          = getLine
runCommand (Bind cmdA func) =
  do
    res <- runCommand cmdA
    runCommand (func res)
runCommand (Pure x)         = pure x
runCommand (ReadFile path)  = readFile path
runCommand (WriteFile path cnt) = writeFile path cnt

run : Fuel -> ConsoleIO a -> IO (Maybe a)
run Dry      _                = pure Nothing
run (More fuel) (Quit res)    = pure (Just res)
run (More fuel) (Do cmd func) =
  do
    cmdRes <- runCommand cmd
    let res = func cmdRes
    run fuel res

scoreStr: (score: Nat) -> (attempts: Nat) -> String
scoreStr score attempts =
  "Score so far: " ++ show score ++ "/" ++ show attempts ++ "\n"

quiz : Stream Int -> (score: Nat) -> (attempts: Nat) -> ConsoleIO Nat
quiz (num1 :: num2 :: nums) score attempts =
  do
    PutStr (scoreStr score attempts)
    input <- readInput (show num1 ++ " * " ++ show num2 ++ " = ? ")
    case input of
      Answer answer =>
        if answer == num1 * num2
          then do PutStr ("Correct! ")
                  quiz nums (score + 1) (attempts + 1)
          else do PutStr ("Wrong! The answer is " ++ show (num1 * num2) ++ "\n")
                  quiz nums score (attempts + 1)
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

-- partial
-- main: IO ()
-- main =
--   do
--     seed       <- time
--     Just score <- run forever (quiz (arithInputs(fromInteger seed)) 0 0)
--         | Nothing => putStrLn "Run out of fuel"
--     putStrLn ("Final score = " ++ show score)

shell : ConsoleIO ()
shell =
  do
    cmdOrErr <- readShellInput ":> "
    case cmdOrErr of
      (Left err)  => do PutStr err
                        shell
      (Right (Cat file)) => do result <- ReadFile file
                               case result of
                                  (Left err)      => PutStr (show err)
                                  (Right content) => PutStr content
                               shell
      (Right (Copy src dst)) => do readResult <- ReadFile src
                                   case readResult of
                                     (Left err) => PutStr (show err)
                                     (Right content) => do writeResult <- WriteFile dst content
                                                           case writeResult of
                                                            (Left err) => PutStr (show err)
                                                            (Right ()) => PutStr "file copied"
                                   shell
      (Right ExitCmd) => Quit ()

partial
main: IO ()
main =
  do
    Just val <- run forever shell
        | Nothing => putStrLn "Run out of fuel"
    putStrLn "Bye!"