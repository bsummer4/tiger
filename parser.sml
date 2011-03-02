(* tiger.sml *)

(* This file provides glue code for building the calculator using the
 * parser and lexer specified in tiger.lex and tiger.grm.
*)

structure Tiger : sig
	           val parse : unit -> unit
                 end = 
struct

(* 
 * We apply the functors generated from tiger.lex and tiger.grm to produce
 * the TigerParser structure.
 *)

  structure TigerLrVals =
    TigerLrValsFun(structure Token = LrParser.Token)

  structure TigerLex =
    TigerLexFun(structure Tokens = TigerLrVals.Tokens)

  structure TigerParser =
    Join(structure LrParser = LrParser
	 structure ParserData = TigerLrVals.ParserData
	 structure Lex = TigerLex)

(* 
 * We need a function which given a lexer invokes the parser. The
 * function invoke does this.
 *)

  fun invoke lexstream =
      let fun print_error (s,i:int,_) =
	      TextIO.output(TextIO.stdOut,
			    "Error, line " ^ (Int.toString i) ^ ", " ^ s ^ "\n")
       in TigerParser.parse(0,lexstream,print_error,())
      end

(* 
 * Finally, we need a driver function that reads one or more expressions
 * from the standard input. The function parse, shown below, does
 * this. It runs the calculator on the standard input and terminates when
 * an end-of-file is encountered.
 *)

  fun parse () = 
      let
          local
            val getStdIn = fn _ => Option.valOf (TextIO.inputLine TextIO.stdIn)
          in
            val lexer = TigerParser.makeLexer getStdIn
          end
	  val dummyEOF = TigerLrVals.Tokens.EOF(0,0)
	  val dummySEMI = TigerLrVals.Tokens.SEMI(0,0)
	  fun loop lexer =
	      let val (result,lexer) = invoke lexer
		  val (nextToken,lexer) = TigerParser.Stream.get lexer
		  (* val _ = case result
                  (* HERE IS WHERE WE PRINT RESULT *)
			    of SOME r =>
				TextIO.output(TextIO.stdOut,
				       "result = " ^ (Int.toString r) ^ "\n")
			     | NONE => ()
                   *)
	       in if TigerParser.sameToken(nextToken,dummyEOF) then ()
		  else loop lexer
	      end
       in loop lexer
      end

end (* structure Tiger *)
