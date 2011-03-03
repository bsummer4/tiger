datatype dec = FUN_DEC of string list | TYPE_DEC of string list | VAR_DEC of string

fun newdec [] = []
  | newdec (d::l) =
      (case d 
         of FUN_DEC(_)  => fdec ([],d::l)
         |  TYPE_DEC(_) => tdec ([],d::l)
         |  VAR_DEC(_)  => d::(newdec l))

and fdec (fs,[])   = [FUN_DEC(fs)]
  | fdec (fs,d::l) =
      (case d
         of FUN_DEC(fr) => fdec((hd fr)::fs,l)
         |  _ => FUN_DEC(fs)::(newdec (d::l)))

and tdec (ts,[])   = [TYPE_DEC(ts)]
  | tdec (ts,d::l) =
      (case d
         of TYPE_DEC(tr) => tdec((hd tr)::ts,l)
         |  _ => TYPE_DEC(ts)::(newdec (d::l)))
