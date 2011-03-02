datatype dec = FunctionDec of string list | TypeDec of string list | VarDec of string

fun newdec [] = []
  | newdec (d::l) =
      (case d 
         of FunctionDec(_) => fdec ([],d::l)
         |  TypeDec(_) => tdec ([],d::l)
         |  VarDec(_) => d::(newdec l))

and fdec (fs,[])   = [FunctionDec(fs)]
  | fdec (fs,d::l) =
      (case d
         of FunctionDec(fr) => fdec((hd fr)::fs,l)
         |  _ => FunctionDec(fs)::(newdec (d::l)))

and tdec (ts,[])   = [TypeDec(ts)]
  | tdec (ts,d::l) =
      (case d
         of TypeDec(tr) => tdec((hd tr)::ts,l)
         |  _ => TypeDec(ts)::(newdec (d::l)))
