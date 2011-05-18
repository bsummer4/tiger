structure Lex = TigerLexFun(structure Tokens = struct
 type svalue = int
 type pos = int
 type ('a,'b) token = string

 fun String (v,_,_) = "String\t\"" ^ v ^ "\""
 fun Integer (v,_,_) = "Integer\t" ^ (Int.toString v)
 fun Id (v,_,_) = "Id\t" ^ v

 define(`V',`
  fun $1 (_,_) = "$1"')
 V(Eof) V(Comma) V(Colon) V(Semi) V(Lparen) V(Rparen) V(Lbrak) V(Rbrak)
 V(Lbrace) V(Rbrace) V(Dot) V(Add) V(Sub) V(Mul) V(Div) V(Eq) V(Neq)
 V(Lt) V(Le) V(Gt) V(Ge) V(And) V(Or) V(Assign) V(Array) V(If) V(Then)
 V(Else) V(While) V(For) V(To) V(Do) V(Let) V(In) V(End) V(Of) V(Break)
 V(Nil) V(Fun) V(Var) V(Type) V(Umin)
 undefine(`V')
end)

open TextIO
fun println x = (print x; print "\n")
fun get _ = input stdIn
val lexer = Lex.makeLexer get
fun loop () =
 case lexer () of t =>
  (println t; if t="Eof" then () else loop())

;loop ();
