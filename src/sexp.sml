(*
	This is a quick approximation of of an s-expression library. Needs
	a lot of work.
*)

structure Sexp = struct
 datatype sexp = SEQ of sexp list | BOOL of bool | SYM of string
               | STR of string | INT of int

 local
  fun w s = TextIO.output (TextIO.stdOut,s)
  fun indent 0 = ()
    | indent n = (w " "; indent (n-1))
  fun newline d = (w "\n"; indent d)

  fun printSeq j d [] = ()
    | printSeq j d (x::[]) = print' j d x
    | printSeq j d (x::xs) = (print' j d x; w " "; printSeq false d xs)
  and print' j d (SEQ l) = ( if not j then newline d else ()
                           ; w "("; printSeq true (1+d) l; w ")")
    | print' _ d (BOOL true) = w "#t"
    | print' _ d (BOOL false) = w "#f"
    | print' _ d (SYM s) = w s
    | print' _ d (STR s) = (w "\""; w s; w "\"")
    | print' _ d (INT i) = w (Int.toString i)
 in
  fun printSexp s = (print' true 0 s; w "\n"; TextIO.flushOut TextIO.stdOut)
 end
end
