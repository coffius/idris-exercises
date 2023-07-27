import Data.Vect

data WordState: (guesses_remaining: Nat) -> (letters: Nat) -> Type where
  MkWordState: (word: String) -> (missing: Vect letters Char) -> WordState guesses_remaining letters

data Finished: Type where
  Lost: (game: WordState 0 (S letters))   -> Finished
  Won:  (game: WordState (S remaining) 0) -> Finished

data ValidInput: List Char -> Type where
  Letter: (c: Char) -> ValidInput [c]

total emptyNotValidInput : ValidInput [] -> Void
emptyNotValidInput (Letter _) impossible

total tooManyChars : ValidInput (x :: (y :: xs)) -> Void
tooManyChars (Letter _) impossible

total isValidInput: (chars: List Char) -> Dec (ValidInput chars)
isValidInput [] = No emptyNotValidInput
isValidInput (x :: []) = Yes(Letter x)
isValidInput (x :: (y :: xs)) = No tooManyChars

isValidString: (s: String) -> Dec(ValidInput(unpack s))
isValidString s = isValidInput (unpack s)

readGuess: IO (x ** ValidInput x)
readGuess = do
  putStr "Guess: "
  userGuess <- getLine
  case isValidString (toUpper userGuess) of
    (Yes prf) => pure (_ ** prf)
    (No contra) => do
      putStrLn ("Invalid guess = [" ++ userGuess ++"]")
      readGuess

removeElem: (value: a) -> (xs: Vect (S n) a) -> {auto prf: Elem value xs} -> Vect n a
removeElem             value (value :: ys) {prf = Here}          = ys
removeElem {n = Z}     value (y     :: []) {prf = (There later)} = absurd later
removeElem {n = (S k)} value (y     :: ys) {prf = (There later)} = y :: removeElem value ys

processGuess: (letter: Char) ->
              WordState (S guesses) (S letters) ->
              Either (WordState guesses (S letters))
                     (WordState (S guesses) letters)
processGuess letter (MkWordState word missing) = case isElem letter missing of
  (Yes prf) => Right (MkWordState word (removeElem letter missing))
  (No contra) => Left (MkWordState word missing)

game: (state: WordState (S guesses) (S letters)) -> IO Finished
game {guesses} {letters} state = do
  ([input] ** Letter input) <- readGuess
  case processGuess input state of
    (Left l) => do
      putStrLn "Wrong!"
      case guesses of
        Z   => pure (Lost l)
        S k => game l
    (Right r) => do
      putStrLn "Right!"
      case letters of
        Z => pure (Won r)
        (S k) => game r

main: IO ()
main = 
  let
    wordToGuess = MkWordState "Test" ['T', 'E', 'S']
  in
    do
      result <- game {guesses=2} wordToGuess
      case result of
        (Lost (MkWordState word missing)) => putStrLn ("You lost. The word was " ++ word)
        (Won game) => putStrLn "You win"
