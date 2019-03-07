data Expr num = Val num 
              | Add (Expr num) (Expr num)
              | Sub (Expr num) (Expr num)
              | Mul (Expr num) (Expr num)
              | Div (Expr num) (Expr num)
              | Abs (Expr num)

Num ty => Num (Expr ty) where
  (+) = Add
  (*) = Mul
  fromInteger = Val . fromInteger

Neg ty => Neg (Expr ty) where
  negate x = 0 - x
  (-) = Sub

Abs ty => Abs (Expr ty) where
  abs = Abs


eval: (Abs num, Neg num, Integral num) => Expr num -> num
eval (Val x) = x
eval (Add x y) = eval x + eval y
eval (Sub x y) = eval x - eval y
eval (Mul x y) = eval x * eval y
eval (Div x y) = div (eval x) (eval y)
eval (Abs x)   = abs (eval x)

exprShowHelper: Show ty => (left: ty) -> (symb: Char) -> (right: ty) -> String
exprShowHelper left symb right =
  "(" ++ show left ++ " " ++ cast symb ++ " " ++ show right ++ ")"
  
Show ty => Show (Expr ty) where
  show (Val x) = show x
  show (Add x y) = exprShowHelper x '+' y
  show (Sub x y) = exprShowHelper x '-' y
  show (Mul x y) = exprShowHelper x '*' y
  show (Div x y) = exprShowHelper x '/' y
  show (Abs x) = "|"++ show x ++"|"

(Abs ty, Neg ty, Integral ty, Eq ty) => Eq (Expr ty) where
  (==) x y = eval x == eval y

(Abs ty, Neg ty, Integral ty) => Cast (Expr ty) ty where
  cast = eval

Functor Expr where
  map func (Val x) = Val (func x)
  map func (Add x y) = Add (map func x)(map func y)
  map func (Sub x y) = Sub (map func x)(map func y)
  map func (Mul x y) = Mul (map func x)(map func y)
  map func (Div x y) = Div (map func x)(map func y)
  map func (Abs x) = Abs (map func x)
  
example1: Expr Integer
example1 = Add (Val 6) (Mul (Val 3) (Abs(Val (-12))))

example2: Expr Integer
example2 = 6 + 3 * 12

example3: Expr Integer
example3 = 6 * 3 + 12

example4: Expr Integer
example4 = 1 + 2 * 3