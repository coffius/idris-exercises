module Main

import System
import Data.Vect

printLenght: IO ()
printLenght = do
  putStr "Input a string: "
  input <- getLine
  let len = length input
  putStrLn(show len)

printLonger: IO ()
printLonger = do
  putStr "Input the first string: "
  first <- getLine
  putStr "Input the second string: "
  second <- getLine
  let firstLen  = length first
  let secondLen = length second
  let longest = max firstLen secondLen
  putStrLn ("The longest: " ++ (show longest))

readNumber: IO (Maybe Nat)
readNumber = do
  input <- getLine
  if all isDigit (unpack input)
    then pure (Just(cast input))
    else pure Nothing

total readNumbers: IO (Maybe (Nat, Nat))
readNumbers = do
  Just num1_ok <- readNumber | Nothing => pure Nothing
  Just num2_ok <- readNumber | Nothing => pure Nothing
  pure (Just (num1_ok, num2_ok))

total stringToNat: String -> Maybe Integer
stringToNat input = 
  if all isDigit (unpack input)
    then Just(cast input)
    else Nothing

guess: Integer -> Nat -> IO()
guess target guesses = do
  userInput <- getLine
  let parsed = stringToNat userInput
  case parsed of
    Nothing => putStrLn ("Invalid input: " ++ userInput)
    (Just number) => case compare number target of
      LT => putStrLn ("too low. Guess #" ++ (show guesses)) >>= \_ => guess target (guesses + 1)
      EQ => putStrLn "Correct!!!"
      GT => putStrLn ("too high. Guess #" ++ (show guesses)) >>= \_ => guess target (guesses + 1)

randomGuess: IO()
randomGuess = do
  rndNum <- time
  putStrLn ("Guess me: " ++ (show rndNum))
  guess rndNum 1
  
readVectLen: (len: Nat) -> IO (Vect len String)
readVectLen Z = pure []
readVectLen (S k) = do
  x <- getLine
  xs <- readVectLen k
  pure (x :: xs)

readVect: IO(len ** Vect len String)
readVect = do
  x <- getLine
  if (x == "")
    then pure(_ ** [])
    else do (_ ** xs) <- readVect
            pure (_ ** (x :: xs))

maybeZipVects: Vect n a -> Vect m b -> Maybe(Vect n (a, b))
maybeZipVects {n} left right = case exactLength n right of 
  Just right' => Just(zip left right')
  Nothing => Nothing

zipInputs: IO()
zipInputs = do
  putStrLn "Enter the first vector:"
  (_ ** firstVect) <- readVect
  putStrLn "Enter the second vector:"
  (_ ** secondVect) <- readVect
  case maybeZipVects firstVect secondVect of
    Nothing => putStrLn "Vectors are different"
    Just zipped => printLn zipped

readToBlank: IO(List String)
readToBlank = do
  line  <- getLine
  if line == ""
    then pure []
    else do lines <- readToBlank
            pure (line :: lines)

readAndSave: IO()
readAndSave = do
  putStrLn "Enter lines:"
  lines <- readToBlank
  let oneString = unlines lines
  putStrLn "Enter filename:"
  fileName <- getLine
  result <- writeFile fileName oneString
  case result of 
    (Left _) => pure ()
    (Right err) => printLn err

readLinesFrom : (file : File) -> IO (n: Nat ** Vect n String)
readLinesFrom file = do
  isEOF <- fEOF file
  case isEOF of
    True => pure (_ ** [])
    False => do
      Right line <- fGetLine file
                 | Left err => pure (_ ** [])
      (_ ** nextLines) <- readLinesFrom file
      pure (_ ** trim line :: nextLines)           

readVectFile: (filename: String) -> IO (n ** Vect n String)
readVectFile filename = do
  Right file <- openFile filename Read
             | Left err => pure (_ ** [])
  readLinesFrom file

main : IO ()
main = do
  _ <- putStr "Enter your name: "
  x <- getLine
  putStrLn ("Hi there, " ++ x)
