import Data.List

%default total

data WareAction = CreateNew | UpdateExist | RemoveExist | GetWareInfo

implementation Eq WareAction where
  (==) CreateNew   CreateNew   = True
  (==) UpdateExist UpdateExist = True
  (==) RemoveExist RemoveExist = True
  (==) GetWareInfo GetWareInfo = True
  (==) _           _           = False

implementation DecEq WareAction where
  decEq wa1 wa2 =
    case wa1 == wa2 of
      False => Yes theyEqual
      True  => No theyNotEqual
    where
      theyEqual : wa1 = wa2
      theyEqual = really_believe_me (Refl {x = wa1})
      theyNotEqual : wa1 = wa2 -> Void
      theyNotEqual prf = believe_me {b = Void} ()

record Ware where
  constructor MkWare
  name: String
  price: Double

data Role = SuperUser | Operator | Guest

roleToActions : Role -> List WareAction
roleToActions SuperUser = CreateNew :: UpdateExist :: RemoveExist :: GetWareInfo :: Nil
roleToActions Operator  = CreateNew :: UpdateExist :: GetWareInfo :: Nil
roleToActions Guest     = GetWareInfo :: Nil

record User where
  constructor MkUser
  firstName: String
  secondName: String
  role: Role

userActions : User -> List WareAction
userActions = roleToActions . role

checkUserRights: (user: User) -> (reqAction: WareAction) -> Bool
checkUserRights user reqAction =
  let
    userActions = roleToActions(role user)
  in
    any (\action => action == reqAction) userActions

ActionResult: Type
ActionResult = Either String Ware

-- Runtime check that a user has a right (CreateNew) to create a new ware
-- In this case we are not sure if the user has the needed right
-- So it is necessary to check that explicitly 
createNewWare: (name: String) -> (price: Double) -> (user: User) -> ActionResult
createNewWare name price user = case checkUserRights user CreateNew of
  False => Left  ("Have no rights")
  True  => Right (MkWare name price)

HasAccess : (user: User) -> (action: WareAction) -> Type
HasAccess user action = Elem action (userActions user)

data ContainsAccess: User -> WareAction -> Type where
  Positive: (user: User) -> (action: WareAction) -> Elem action (userActions user) -> ContainsAccess user action


proveNegative : (contra : Elem req (userActions user) -> Void) -> ContainsAccess user req -> Void
proveNegative contra (Positive user req prf) = contra prf

proveContainsAccess: (user: User) -> (req: WareAction) -> Dec (ContainsAccess user req)
proveContainsAccess user req =
  case isElem req (userActions user) of
    (Yes prf) => Yes (Positive user req prf)
    (No contra) => No (proveNegative contra)

proveUserRights: (userActions: List WareAction) -> (req: WareAction) -> Dec(Elem req userActions)
proveUserRights userActions req = isElem req userActions

proveUserAccess: (user: User) -> (req: WareAction) -> Dec (HasAccess user req)
proveUserAccess user req = proveUserRights (roleToActions(role user)) req

-- Compile time check that a user has a right (CreateNew) to create a new ware
-- In this case that proof guards the function from being called from an arbitrary place
-- It is possible to call it only if a caller has a proof that the user has the right 
createProved: (name: String) -> (price: Double) -> (user: User) -> (prf: ContainsAccess user CreateNew) -> Ware
createProved name price user {prf} = MkWare name price


testGuest: User
testGuest = MkUser "Test" "Guest" Guest

testSuperUser: User
testSuperUser = MkUser "Test" "SuperUser" SuperUser

-- Compile-time proof that `Main.testSuperUser` has the `CreateNew` right
superUserCanCreate: ContainsAccess Main.testSuperUser CreateNew
superUserCanCreate = Positive Main.testSuperUser CreateNew Here

-- Show: createProved "test_ware" 1.0 testSuperUser superUserCanCreate

guestCreatesWare: ActionResult
guestCreatesWare = createNewWare "Test Ware" 10.0 testGuest

superUserCreatesWare: ActionResult
superUserCreatesWare = createNewWare "Test Ware" 10.0 testSuperUser
