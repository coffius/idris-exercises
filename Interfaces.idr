maybeAdd: Num a => Maybe a -> Maybe a -> Maybe a
maybeAdd x y = do
  xVal <- x
  yVal <- y
  Just (xVal + yVal)
      
occurrences: Eq ty => (item: ty) -> (values: List ty) -> Nat
occurrences item [] = 0
occurrences item (value :: values) =
  case value == item of
    False => occurrences item values
    True  => 1 + occurrences item values

data Matter = Solid | Liquid | Gas

Eq Matter where
  (==) Solid  Solid   = True
  (==) Liquid Liquid  = True
  (==) Gas    Gas     = True
  (==) _      _       = False
  
data Tree elem = Empty
               | Node (Tree elem) elem (Tree elem)

Eq elem => Eq (Tree elem) where
  (==) Empty Empty = True
  (==) (Node left e right) (Node left' e' right') =
    left == left' && e == e' && right == right'
  (==) _ _ = False

record Album where
  constructor MkAlbum
  artist: String
  title: String
  year: Integer

help: Album
help = MkAlbum "The Beatles" "Help" 1965

rubbersoul: Album
rubbersoul = MkAlbum "The Beatles" "Rubber Soul" 1965

clouds: Album
clouds = MkAlbum "Joni Mitchell" "Clouds" 1969

honkydory: Album
honkydory = MkAlbum "David Bowie" "Hunky Dory" 1971

heroes: Album
heroes = MkAlbum "David Bowie" "Heroes" 1977

collection: List Album
collection = [help, rubbersoul, clouds, honkydory, heroes]

Eq Album where
  (==) (MkAlbum artist title year) (MkAlbum artist' title' year') =
    artist == artist' && title == title' && year == year'

Ord Album where
  compare (MkAlbum artist title year) (MkAlbum artist' title' year') =
    case compare artist artist' of
      EQ => case compare year year' of
        EQ => compare title title'
        diffYear => diffYear
      diffArtist => diffArtist

Show Album where
  show (MkAlbum artist title year) =
    title ++ " by " ++ artist ++ " (released " ++ show year ++ ")"

data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

Eq Shape where           
  (==) (Triangle x z) (Triangle x' z') = x == x' && z == z'
  (==) (Rectangle x z) (Rectangle x' z') = x == x' && z == z'
  (==) (Circle x) (Circle x') = x == x'
  (==) _ _ = False

area: Shape -> Double
area (Triangle base height) = 0.5 * base * height
area (Rectangle length height) = length * height
area (Circle radius) = pi * radius * radius

Ord Shape where
  compare x y = let
    xArea = area x
    yArea = area y
  in
    compare xArea yArea

testShapes: List Shape
testShapes = [Circle 3, Triangle 3 9, Rectangle 2 6, Circle 4, Rectangle 2 7]