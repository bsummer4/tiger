structure TigerLrVals = TigerLrValsFun (structure Token = LrParser.Token)
structure TigerLex = TigerLexFun (structure Tokens = TigerLrVals.Tokens)
structure TigerParser =
 Join
  (structure ParserData = TigerLrVals.ParserData
   structure Lex = TigerLex
   structure LrParser = LrParser)

exception Parse

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

fun go () = go' (CIRPrint.printProg o ToC.IRtoCIR.convertIR o LL.rewriteCalls o Semantic.toIR)

;
go();
