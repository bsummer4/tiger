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
  = ARR of {size:texp, init:texp}
  | ASSIGN of {var:var, exp:texp}
  | BREAK
  | CALL of {func:sym, args:texp list}
  | IF of {test:texp, then':texp}
  | IFELSE of {test:texp, then':texp, else':texp}
  | INT of int
  | NIL
  | OP of {left:texp, oper:oper, right:texp}
  | REC of (sym * texp) list
  | STR of string
  | VAR of var
  | WHILE of {test:texp, body:texp}

 and oper = ADD | SUB | MUL | DIV | EQ | NEQ | LT | LE | GT | GE | AND | OR
 and var = SIMPLE of sym | FIELD of var * sym | INDEX of var * exp
 withtype texp = {e:exp, ty:ty}

 (*
 	The `block' field in `vars' refers to where the block where a
 	variable is defined or the block defined by a function depending
	on what type of variable it is. Note that `args' and `vars'
	are disjoint sets and that the order of `args' is significant.
 *)
 type block = {args:sym list, vars:sym list, subBlocks:sym list, up:sym option, body:exp}
 type vars = {typ:sym, block:sym} SymTable.table
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
structure IRPrintC:> IR_PRINT = struct
 (* decArray decRec decProc ; defArray defRec defProc *)

 fun id x = x
 fun appFmt f s e [] = print e
   | appFmt f s e (x::xs) =
      (f x; if xs=[] then () else print s; appFmt f s e xs)

 fun typeStr ty =
  case ty 
   of NIL => "void *"
    | INT => "int"
	| STRING => "char *"
	| UNIT => "void"
	| REC s => Symbol.unique s
	| ARR s => Symbol.unique s
	| FUN s => raise Unsupported "First-class functions"

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

 fun defRec p as {records,...} s = 
   case SymTab.look(records,x) of rec
   ( app print ["struct ", Symbol.unique s, " {"]
   ; appFmt (fn (ty,name) => app print [typeStr ty, " ", Symbol.unique name])
      "; " ";};\n" (ListPair.map id (#ty (#1 rec)) (#1 rec))
   )
   
 fun defArray p as {arrays,...} s =
   case SymTable.look(arrays,s) of {init,...} =>
    app print ["struct ", Symbol.unique s, " { int size; ", Symbol.unique (#2 init), " *elmts;};\n"]

 fun printBlock p e = TODO()

 fun defProc p as {blocks,procs,...} s =
  case (SymTable.look(blocks,s), SymTable.look(procs,s)) of (b,{res,args}) =>
   ( app print [Symbol.unique res, " ", Symbol.unique s, " ("]
   ; appFmt (fn (ty,name) => app print [typeStr ty, " ", Symbol.unique name])
      "," ")\n" (ListPair.map id args (#args b))
   ; print "{\n"
   ; printBlock p (#body b)
   ; print "}\n"
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

