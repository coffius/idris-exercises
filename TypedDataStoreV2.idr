module DataStore

import Data.Vect

infixr 5 .+.

public export
data Schema = SString
            | SInt
            | (.+.) Schema Schema

public export
SchemaType: Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

export
record DataStore(schema: Schema) where
  constructor MkData
  size: Nat
  items: Vect size (SchemaType schema)

export
empty: DataStore schema
empty = MkData 0 []

export
addToStore : (value: SchemaType schema) -> (store: DataStore schema) -> DataStore schema
addToStore value (MkData size items) = MkData _ (value :: items)

public export
data StoreView : DataStore schema -> Type where
  SNil : StoreView empty
  SAdd: (rec: StoreView store) -> StoreView (addToStore value store)

storeViewHelp : (items: Vect size (SchemaType schema)) -> StoreView (MkData size items)
storeViewHelp [] = SNil
storeViewHelp (val :: xs) = SAdd (storeViewHelp xs)

export
storeView : (store : DataStore schema) -> StoreView store
storeView (MkData size items) = storeViewHelp items

listItems : DataStore schema -> List (SchemaType schema)
listItems input with (storeView input)
  listItems empty                    |  SNil      = []
  listItems (addToStore value store) | (SAdd rec) = value :: (listItems store | rec)

filterKeys : (test : SchemaType schema -> Bool) -> DataStore (SString .+. schema) -> List String
filterKeys test input with (storeView input)
  filterKeys test empty                           |  SNil      = []
  filterKeys test (addToStore (key, value) store) | (SAdd rec) =
    if test value
    then key :: (filterKeys test store | rec)
    else filterKeys test store | rec

getValues : DataStore (SString .+. schema) -> List (SchemaType schema)
getValues input with (storeView input)
  getValues input                       |  SNil      = []
  getValues (addToStore (_, val) store) | (SAdd rec) = val :: (getValues store | rec)

testStore : DataStore (SString .+. SString .+. SInt)
testStore = addToStore ("Mercury", "Mariner 10",  1974) $
            addToStore ("Venus",   "Venera",      1961) $
            addToStore ("Uranus",  "Voyager 2",   1986) $
            addToStore ("Pluto",   "New Horizons",2015) $
            empty
