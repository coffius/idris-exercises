module Main

import Data.Vect

data DataStore: Type where
    MkData: (size: Nat) -> (items: Vect size String) -> DataStore

size: DataStore -> Nat
size (MkData size' items') = size'

items: (store: DataStore) -> Vect (size store) String
items (MkData size' items') = items'

addToStore: DataStore -> String -> DataStore
addToStore (MkData size items) newItem = MkData _ (addToData items)
    where
        addToData: Vect old String -> Vect (S old) String
        addToData [] = [newItem]
        addToData (x :: xs) = x :: addToData xs

data Command = Add String
						 | Get Integer
						 | Size
             | Quit

parseCommand : (cmd : String) -> (args : String) -> Maybe Command
parseCommand "add" str = Just (Add str)
parseCommand "get" val = case all isDigit (unpack val) of
	True  => Just(Get(cast val))
	False => Nothing
parseCommand "size" "" = Just Size
parseCommand "quit" "" = Just Quit
parseCommand _ _ = Nothing

parse: String -> Maybe Command             
parse input = case span (/= ' ') input of 
    (cmd, args) => parseCommand cmd (ltrim args)
        
getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store =
	let
		currItems = items store
	in 
		case integerToFin pos (size store) of
			Nothing => Just("Out of range\n", store)
			Just id => Just((index id currItems) ++ "\n", store)

total processCommand : (cmd : Command) -> (store : DataStore) -> Maybe (String, DataStore)
processCommand (Add item) store =
	let 
		newStore = addToStore store item
		newId = show (size store)
	in 
		Just("ID: " ++ newId ++ "\n", newStore)
processCommand (Get pos) store = getEntry pos store
processCommand Size store = Just("Size: " ++ show (size store) ++ "\n", store)
processCommand Quit store = Nothing

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input = case parse input of
    Nothing => Just("Invalid command\n", store)
    Just cmd => processCommand cmd store

main : IO ()
main = replWith (MkData _ []) ":>> " processInput
