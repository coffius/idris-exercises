AdderType: (numargs: Nat) -> Type -> Type
AdderType Z numType = numType
AdderType (S k) numType = (next: numType) -> AdderType k numType

adder: Num numType => (numargs: Nat) -> numType -> AdderType numargs numType
adder Z acc = acc
adder (S k) acc = \next => adder k (next + acc)
----------------------------------------------------------------------------
data Format = Number Format
            | Str Format
            | Character Format
            | FNumber Format
            | Lit String Format
            | End
----------------------------------------------------------------------------
PrintfType: Format -> Type
PrintfType (Number fmt) = (i: Int) -> PrintfType fmt
PrintfType (Str fmt) = (str: String) -> PrintfType fmt
PrintfType (Character fmt) = (str: Char) -> PrintfType fmt
PrintfType (FNumber fmt) = (str: Double) -> PrintfType fmt
PrintfType (Lit str fmt) = PrintfType fmt
PrintfType End = String
----------------------------------------------------------------------------
printfFmt: (fmt: Format) -> (acc: String) -> PrintfType fmt
printfFmt (Number fmt) acc = \i => printfFmt fmt (acc ++ show i)
printfFmt (Str fmt) acc = \str => printfFmt fmt (acc ++ str)
printfFmt (Character fmt) acc = \char => printfFmt fmt (acc ++ show char)
printfFmt (FNumber fmt) acc = \fnum => printfFmt fmt (acc ++ show fnum)
printfFmt (Lit lit fmt) acc = printfFmt fmt (acc ++ lit)
printfFmt End acc = acc
----------------------------------------------------------------------------
toFormat: (xs: List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: chars) = Number (toFormat chars)
toFormat ('%' :: 's' :: chars) = Str (toFormat chars)
toFormat ('%' :: 'c' :: chars) = Character (toFormat chars)
toFormat ('%' :: 'f' :: chars) = FNumber (toFormat chars)
toFormat ('%' :: chars) = Lit "%" (toFormat chars)
toFormat (c :: chars) = case toFormat chars of
  Lit lit fmt => Lit (strCons c lit) fmt
  fmt => Lit (strCons c "") fmt
----------------------------------------------------------------------------
printf: (fmt: String) -> PrintfType (toFormat (unpack fmt))
printf fmt = printfFmt _ ""
----------------------------------------------------------------------------
TupleVect: (len: Nat) -> (elemType: Type) -> Type
TupleVect Z elemType = ()
TupleVect (S k) elemType = (elemType, TupleVect k elemType)

