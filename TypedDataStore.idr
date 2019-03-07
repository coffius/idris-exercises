import Data.Vect

infixr 5 .+.

data Schema = SString
            | SInt
            | (.+.) Schema Schema

SchemaType: Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

data Command: Schema -> Type where
  -- SetSchema: (newSchema: Schema) -> Command schema
  Add: SchemaType schema -> Command schema
  Get: Integer -> Command schema
  Size: Command schema
  Quit: Command schema

record DataStore where
  constructor MkData
  schema: Schema
  size: Nat
  items: Vect size (SchemaType schema)

addToStore: (store: DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData schema size items) newItem = MkData schema _ (addToData items)
  where
    addToData: Vect old (SchemaType schema) -> Vect (S old) (SchemaType schema)
    addToData [] = [newItem]
    addToData (x :: xs) = x :: addToData xs
  
display: SchemaType schema -> String
display {schema = SString} item = item
display {schema = SInt} item = show item
display {schema = (x .+. y)} (iteml, itemr) = display iteml ++ ", " ++ display itemr

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store =
  let
    currItems = items store
  in 
    case integerToFin pos (size store) of
      Nothing => Just("Out of range\n", store)
      Just id => Just(display (index id currItems) ++ "\n", store)

parsePrefix: (schema: Schema) -> String -> Maybe (SchemaType schema, String)
parsePrefix SString item = getQuoted(unpack item)
  where
    getQuoted: List Char -> Maybe (String, String)
    getQuoted ('"' :: xs) = case span (/= '"') xs of
      (quoted, '"' :: rest) => Just(pack quoted, ltrim (pack rest))
      _ => Nothing
    getQuoted _ = Nothing
    
parsePrefix SInt item =
  case span isDigit item of
    ("", rest)  => Nothing
    (num, rest) => Just (cast num, ltrim rest)
parsePrefix (schemal .+. schemar) item =
  case parsePrefix schemal item of
    Nothing => Nothing
    Just(leftVal, input') => 
      case parsePrefix schemar input' of
        Nothing => Nothing
        Just (rightVal, input'') => Just ((leftVal, rightVal), input'')

parseBySchema : (schema : Schema) -> String -> Maybe(SchemaType schema)
parseBySchema schema input = case parsePrefix schema input of
  Just (res, "") => Just res
  Just _         => Nothing
  Nothing        => Nothing

parseCommand: (schema: Schema) -> String -> String -> Maybe(Command schema)
parseCommand schema "add" rest = case parseBySchema schema rest of
  Nothing         => Nothing
  Just    restok  => Just (Add restok)
parseCommand schema "get" val =
  case all isDigit (unpack val) of
    True  => Just(Get(cast val))
    False => Nothing
parseCommand schema "size" "" = Just Size
parseCommand schema "quit" "" = Just Quit
parseCommand _ _ _ = Nothing

parse: (schema: Schema) -> (input:String) -> Maybe(Command schema)
parse schema input = case span (/= ' ') input of 
    (cmd, args) => parseCommand schema cmd (ltrim args)

total processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input =
  let
    storeSchema = schema store
    invalid = parse storeSchema input
    parsed = parse (schema store) input
  in 
    case parsed of
      Nothing => Just("Invalid command\n", store)
      Just (Add item) => Just("ID: " ++ show (size store) ++ "\n", addToStore store item)
      Just (Get pos) => getEntry pos store
      Just Size => Just("Size: " ++ show (size store) ++ "\n", store)
      Just Quit => Nothing

main: IO()
main = replWith (MkData (SString .+. SString .+. SInt) _ [])
                "Command: " processInput