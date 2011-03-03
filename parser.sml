structure Tiger =
struct

local 

exception Parse
structure TigerLrVals = TigerLrValsFun (structure Token = LrParser.Token)
structure TigerLex = TigerLexFun (structure Tokens = TigerLrVals.Tokens)
structure TigerParser =
 Join
  (structure ParserData = TigerLrVals.ParserData
   structure Lex = TigerLex
   structure LrParser = LrParser)

fun get n = TextIO.inputN(TextIO.stdIn,n)
fun eof tok = TigerParser.sameToken(tok,TigerLrVals.Tokens.Eof(0,0))
fun parse lexer = TigerParser.parse(0,lexer,(fn _=>raise Parse),())
val more = TigerParser.Stream.get
val lexer = TigerParser.makeLexer get

fun go' f =
 let fun loop lex =
      let val (r,lex') = parse lex
          val (tok,lex'') = more lex'
      in f r; if eof tok then () else loop lex''
      end
 in loop lexer
 end

in

fun go s = (go' (Sexp.printSexp o ASTSexp.toSexp)
             handle Parse => print "\nRejected!\n")

end
end
