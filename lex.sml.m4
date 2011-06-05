open TextIO
fun println x = (print x; print "\n")
fun intersperse t [] = []
  | intersperse t (x::xs) = rev (foldl (fn(e,a)=>(e::t::a)) [x] xs)
fun join xs = String.concat (intersperse " " xs)
fun stringLex s =
 let val ss = ref (Substring.full s)
     fun get n =
      case Substring.getc (!ss)
       of NONE => ""
        | SOME (x,ss') => (ss := ss'; str x)
 in get
 end

define(`toks',`
 V(Eof) V(Comma) V(Colon) V(Semi) V(Lparen) V(Rparen) V(Lbrak) V(Rbrak)
 V(Lbrace) V(Rbrace) V(Dot) V(Add) V(Sub) V(Mul) V(Div) V(Eq) V(Neq)
 V(Lt) V(Le) V(Gt) V(Ge) V(And) V(Or) V(Assign) V(Array) V(If) V(Then)
 V(Else) V(While) V(For) V(To) V(Do) V(Let) V(In) V(End) V(Of) V(Break)
 V(Nil) V(Fun) V(Var) V(Type) V(Umin)')

structure T = struct
 define(`V',`
  | $1')
 datatype token
  = String of string
  | Id of string
  | Integer of int
  toks
 undefine(`V')
end

structure Lex = TigerLexFun(structure Tokens = struct
 type svalue = int
 type pos = int
 type ('a,'b) token = T.token

 fun String (v,_,_) = T.String v
 fun Integer (v,_,_) = T.Integer v
 fun Id (n,_,_) = T.Id n

 define(`V',`
  fun $1 (_,_) = T.$1')
 toks
 undefine(`V')
end)

fun tokList str =
 let val lex = Lex.makeLexer(stringLex str)
     fun loop a =
      case lex() of T.Eof => rev a | t => loop(t::a)
 in loop []
 end

val tokens =
 case (CommandLine.name(),CommandLine.arguments())
  of (_,x::xs) => SOME(x::xs)
   | (_,[]) => NONE

open QCheck infix ==>

fun toString n =
 (if n>=0 then Int.toString n else "-"^toString(~n)
 ) handle General.Overflow => "OVERFLOW"

val int = (Gen.Int.int, SOME toString)
fun intTest x =
 (if x<0 then raise Fail "intTest is not defined for negative integers."
  else case tokList(toString x)
        of [T.Integer n] => n=x
         | _ => false
 ) handle General.Overflow => false

;
checkGen int ("integers", (fn x=>(x>=0)) ==> intTest);
