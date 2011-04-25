(*
	This defines the program representation for programs used inside
	the compiler.
*)

structure IR = struct
 type sym = Symbol.symbol

 structure Type = struct
  datatype ty
   = NIL | INT | STRING | UNIT | REC of sym | ARR of sym | FUN of sym

  type arrays = ty SymTable.table
  type records = (sym * ty) list SymTable.table
  type procs = {res:ty,args:ty list} SymTable.table

  fun compatible (a,b) =
   if a=b then true else case (a,b)
    of (ARR _,NIL) => true
     | (REC _,NIL) => true
     | (NIL,ARR _) => true
     | (NIL,REC _) => true
     | _ => false
 end

 datatype exp
  = ARR of {size:texp, init:texp} (* ADDED arr:sym *)
  | ASSIGN of {var:var, exp:texp}
  | BREAK
  | CALL of {func:sym, args:texp list}
  | IF of {test:texp, then':texp}
  | IFELSE of {test:texp, then':texp, else':texp}
  | INT of int
  | NIL
  | OP of {left:texp, oper:oper, right:texp}
  | REC of (sym * texp) list
  | SEQ of texp list
  | STR of string
  | SEQ of texp list 
  | VAR of var
  | WHILE of {test:texp, body:texp}
 and oper = ADD | SUB | MUL | DIV | EQ | NEQ | LT | LE | GT | GE | AND | OR
 and var = SIMPLE of sym | FIELD of var * sym | INDEX of var * exp
 withtype texp = {e:exp, ty:Type.ty}

 (*
 	The `block' field in `vars' refers to where the block where a
 	variable is defined or the block defined by a function depending
	on what type of variable it is. Note that `args' and `vars'
	are disjoint sets and that the order of `args' is significant.
 *)
 type block = {args:sym list, vars:sym list, subBlocks:sym list, up:sym option, body:texp} 
 type vars = {typ:Type.ty, block:sym} SymTable.table
 type blocks = block SymTable.table
 type program =
  { main:sym
  , blocks:blocks
  , procs:Type.procs
  , arrays:Type.arrays
  , records:Type.records
  , vars:vars
  }
end

signature IR_PRINT = sig
 val print : IR.program -> unit
end

(*
	- The IR may not have any nested blocks.

	If these are not true, an TODO exception will be thrown.

	:TODO: Expressions and Statements
		We don't have to worry about the expression/statement
		distinction in C. Explain why.

	x := foo>bar
	%%
	x = ((strcmp(foo,bar)<0):1?0);	
*)
(*
structure IRPrintC:> IR_PRINT = struct
 (* decArray decRec decProc ; defArray defRec defProc *)

 fun id x = x
 fun appFmt f s e [] = print e
   | appFmt f s e (x::xs) =
      (f x; if xs=[] then () else print s; appFmt f s e xs)

 fun appAlt f g [] = ()
   | appAlt f g (x::xs) = (f x; appAlt g f xs)

 fun opname oper = case oper
    of ADD => "+"  | SUB => "-" | MUL => "*" | DIV => "/" | EQ => "=="
	 | NEQ => "!=" | LT => "<"  | LE => "<=" | GT => ">"  | GE => ">="
	 | AND => "&&" | OR => "||" 

 fun typeStr ty =
  case ty 
   of NIL => "void *"
    | INT => "int"
	| STRING => "char *"
	| UNIT => "void"
	| REC s => Symbol.unique s
	| ARR s => Symbol.unique s

 fun decStruct _ s =
  let val s = Symbol.unique s
   in app print ["struct ", s, ";\ntypedef struct ", s, " ", s, ";\n"]
  end

 val (decArray,decRec) = (decStruct,decStruct);

 fun decProc {procs,...} s = 
  case SymTable.look(procs,s) of {res,args} =>
   ( app print [typeStr res, " ", Symbol.unique s, "("]
   ; appFmt (print o typeStr) ", " ");\n" args
   )  

 fun printDecs p as {vars,...} s
  case SymTable.lookup (vars,s) 
   of {REC r,_} => decRec p r
    | {ARR a,_} => decArray p r
	| {FUN f,_} => decProc p f
   
 fun defRec p as {records,...} s = 
   case SymTab.look(records,x) of rec
   ( app print ["struct ", Symbol.unique s, " {"]
   ; appFmt (fn (ty,name) => app print [typeStr ty, " ", Symbol.unique name])
      "; " ";};\n" (ListPair.map id (#ty (#1 rec)) (#1 rec))
   )
   
 fun defArray p as {arrays,...} s =
   case SymTable.look(arrays,s) of {init,...} =>
    app print ["struct ", Symbol.unique s, " { int size; ", Symbol.unique (#2 init), " *elmts;};\n"]

 fun defProc p as {blocks,procs,...} s =
  case (SymTable.look(blocks,s), SymTable.look(procs,s)) of (b,{res,args}) =>
   (* Print return type and function name *)
   ( app print [Symbol.unique res, " ", Symbol.unique s, " ("]
   (* Print argument list *)
   ; appFmt (fn (ty,name) => app print [(typeStr ty), " ", (Symbol.unique name)])
      "," ")\n" (ListPair.map id (args (#args b)))
   (* Print function body *)
   ; print "{\n"
   (* Print variable declarations *)
   ; decVars p (exhaust (#args b) (#vars b)) 
   (* Print statements *)
   ; printExps p (#body b)
   (* How to get return value ???? *)
   ; print "}\n"
   )

 fun decVar p as {vars,...} s = 
  case SymTable.look(vars, s) of {typ,_} => 
   app print [(typeStr typ), " ", (Symbol.unique s), ";\n"]

 fun decVars p [] = print "\n"
   | decVars p s::ss = (decVar p s; decVars p ss)

 fun printTExp p is_stmt te as {typ, e} = 
  case e
   of ARR{size, init} => 
      ( app print ["(", typeStr typ, ".size = "] 
	  ; printTExp p 0 size
	  ; app print [", ", typeStr typ, ".elmt
	  typeStr p, ".elmts[

 (* fl is a semicolon flag. If set, then if it needs to, the expression may print a semicolon *)
 (*
 fun printExp p fl e = 
  case e 
   of ARR{size,init} => TODO() (* arr_name.elements[exp] *)
    | (ASSIGN{var, exp}) => (printVar var; print " = "; printExp p 0 exp; print ";") 
    | BREAK => print "break;\n" 
    | (CALL{func, args}) => 
	   (* app print [(Symbol.unique func), "("]
	   ; appFmt (fn (p',fl',e') => printExp p' fl' e') ", " ")"  
	   *)
	(* func_name(arg1_exp,...argN_exp) , need "parent" exp to know whether or not to print semicolon *)
    | (IF{test, then'}) => 
  	   appAlt print (fn (p',fl',e') => printExp p' fl' e') ["if (", (p, 0, (#e test)), 
	     ") {\n", (p, 0, (#e then')), "}\n"]
    | (IFELSE{test, then', else'}) =>
	   appAlt print (fn (p' fl' e') => printExp p' fl' e') ["if (", (p, 0, (#e test)), ") {\n", 
	     (p, 0, (#e then')), "}\nelse {", (p, 0, (#e else')), "}\n"]
    | (INT i) => app print [" ", (Int.toString i), " "]
    | NIL => print "null"
    | (OP{left, oper, right}) => 
	   case (left, right) 
	    of (INT i1, INT i2) => 
	       app print [" ", (Int.toString left), (opname oper), (Int.toString right), " "]
         | (STR s1, STR s2) => 
		   app print [" (strcmp(\"", s1, "\",\"", s2, "\")", (opname oper), "0 ? 1:0) "]
         | (VAR v2, VAR v2) => TODO() (* find type of v1,v2 then print appropriate expression *)
		 | (INT i, VAR v) => (app print [" ", (Int.toString i), (opname oper)]; printVar v; print " ")
	     | (VAR v, INT i) => (print " "; printVar v; app print [(opname oper), (Int.toString i), " "])
	     | (STR s, VAR v) => 
		    ( app print [" (strcmp(\"", s, "\","]
			; printVar v
			; app print [")", (opname oper), "0 ? 1:0) "]
			) 
		 | (VAR v, STR s) =>  
		    ( print " (strcmp("
			; printVar v
			; app print [",\"", s, "\")", (opname oper), "0 ? 1:0) "]
			)
	     | (* FUNCS *)
		 | (_ , _) => raise Bad_op_exp "Invalid operation expression"
    | (REC fs) => TODO()
    | (STR s) => app print ["\"", s, "\""]
    | (VAR v) => printVar v
    | (WHILE{test,body}) => 
	   appAlt print (fn (p',fl',e') => printExp p' fl' e') ["while (", (p, 0, (#e test)), 
	     ") {\n", (p, 0, (# e body)), "}\n"]
 *)

 fun printVar v
  case v
   of SIMPLE s => print (Symbol.unique s)
    | FIELD (v',s) => (printVar v'; print "."; print (Symbol.unique s))
    | INDEX (v',e) => (printVar v'; print ".elts["; printExp e; print "]")

 fun print p = 
  case (SymTable.look (#blocks p, #main p)) of b => 
   ( print "#include <stdio.h>\n#include <stdlib.h>\n"
   (* print arrays, record, function declarations *)
   ; SymTable.app (decProc p) (#procs p)
   ; SymTable.app (decRec p) (#records p)
   ; SymTable.app (decArr p) (#arrays p)
   ; SymTable.app (defProc p) (#procs p)
   ; SymTable.app (defRec p) (#records p)
   ; SymTable.app (defArr p) (#arrays p)
   (* Print main *)
   ; app print ["int main () {\n", (Symbol.unique (#main p)),  
   ) 

end


(*
struct foo_234 { int size; struct bar *elements; }
struct bar_23 { struct foo a; }

typedef struct foo_234 foo_234;
typedef struct bar_23 bar_23;
*)


(*
	- print type declarations
	- print function prototypes
	- print all functions
		- print variable declarations;
		- print all expressions.

	typedef struct { int size; int *elements; } bar_9;
	typedef struct { int size; struct bar_9 *elements; } foo_23;
end 
*)

*)
