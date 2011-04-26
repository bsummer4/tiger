(*
	This defines the program representation for programs used inside
	the compiler.
*)

structure C = struct
 type sym = Symbol.symbol

 structure Type = struct
  datatype ty
   = VOID_PTR | INT | STRING | VOID | REC of sym | ARR of sym

  type arrays = ty SymTable.table
  type records = (sym * ty) list SymTable.table
  type procs = {res:ty,args:ty list} SymTable.table

  fun compatible (a,b) =
   if a=b then true else case (a,b)
    of (ARR _,VOID_PTR) => true
     | (REC _,VOID_PTR) => true
     | (VOID_PTR,ARR _) => true
     | (VOID_PTR,REC _) => true
     | _ => false
 end

 datatype stmt
  = ASSIGN of {var:var, exp:texp}
  | IF of {test:texp, then':stmt list, else':stmt list}
  | EXP of texp
  | RETURN of texp
  | LABEL of sym
  | GOTO of sym

 and exp
  = ARR of texp
  | REC
  | CALL of {func:sym, args:texp list}
  | INT of int
  | STR of string
  | OP of {left:texp, oper:oper, right:texp}
  | VAR of var
  | NULL

 and oper = ADD | SUB | MUL | DIV | EQ | NEQ | LT | LE | GT | GE | AND | OR
 and var = SIMPLE of sym | FIELD of var * sym | INDEX of var * exp
 withtype texp = {e:exp, ty:Type.ty}

 (*
 	The `block' field in `vars' refers to where the block where a
 	variable is defined or the block defined by a function depending
	on what type of variable it is. Note that `args' and `vars'
	are disjoint sets and that the order of `args' is significant.
 *)
 type block = {args:sym list, vars:sym list, body:stmt list}
 type vars = Type.ty SymTable.table
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
	If these are not true, an TODO exception will be thrown.
*)
structure IRPrintC:> IR_PRINT = struct
 (* decArray decRec decProc ; defArray defRec defProc *)

 fun id x = x

 fun exhaust [] [] = []
   | exhaust x [] = [] 
   | exhaust [] y = y
   | exhaust (x::xs) (y::ys) = exhaust xs ys

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
   of VOID_PTR => "void *"
    | INT => "int"
	| STRING => "char *"
	| UNIT => "void"
	| REC s => Symbol.unique s
	| ARR s => Symbol.unique s

 fun unique' s = Symbol.unique (Symbol.mk s)

 fun printStdLib = app print 
  [(* print *)
   "void ", unique' "print", "(char *str) {\n", 
   "  printf(\"%s\", str);\n",
   "}\n\n", 
   (* printi *)
   "void ", unique' "printi", "(int i) {\n",
   "  printf(\"%d\", i);\n",
   "}\n\n",
   (* flush *)
   "void ", unique' "flush", "() {\n",
   "  fflush();\n",
   "}\n\n",
   (* getchar *)
   "char *", unique' "getchar", "() {\n",
   "  char *str=(char *)malloc(sizeof(char) * 2);\n",
   "  if(str == NULL) {\n",
   "    fprintf(stderr,\"no memory\n\");\n",
   "    exit(1);\n",
   "  }\n",
   "  str[0] = getchar();\n",
   "  str[1] = '\0';\n", 
   "  return str;\n",
   "}\n\n",
   (* ord *)
   "int ", unique' "ord", "(char *str) {\n",
   "  if (strlen(str) == 0)\n",
   "    return -1;\n",
   "  else\n",
   "    return (int)str[0];\n",
   "}\n\n",
   (* chr *)
   "char *", unique' "char", "(int i) {\n",
   "  char *str = (char *)malloc(sizeof(char) * 2);\n",
   "  if (str == NULL) {\n",
   "    fprintf(stderr,\"no memory\");\n",
   "    exit(1);\n",
   "  }\n",
   "  if (i > 255) exit(0);\n",
   "  else {\n",
   "    str[0] = (char)i;\n",
   "    str[1] = '\0';\n",
   "  }\n",
   "  return str;\n",
   "}\n\n",
   (* size *)
   "int ", unique' "size", "(char *str) {\n",
   "  return strlen(str);\n",
   "}\n\n",
   (* substring *)
   "char *", unique' "substring", "(char *str, int start, int n) {\n",
   "  char *sub = (char *)malloc(sizeof(char) * (n+1));\n",
   "  if (sub == NULL) {\n",
   "    fprintf(stderr,\"no memory\");\n",
   "    exit(1);\n",
   "  }\n",
   "  strncpy(sub, &str[start], n);\n",
   "  return sub;\n",
   "}\n\n",
   (* concat *)
   "char *", unique' "concat", "(char *str1, char *str2) {\n",
   "  int length = strlen(str1) + strlen(str2) + 1;\n",
   "  char new_str = (char *)malloc(sizeof(char) * length);\n",
   "  if (new_str == NULL) {\n",
   "    fprintf(stderr,\"no memory\");\n",
   "    exit(1);\n",
   "  }\n", 
   "  strcpy(new_str, str1);\n",
   "  strcat(new_str, str2);\n",
   "}\n\n",
   (* not *)
   "int ", unique' "not", "(int i) {\n",
   "  return (i == 0 ? 1 : 0);\n",
   "}\n\n",
   (* exit *)   
   "void ", unique' "exit", "(int i) {\n",
   "  exit(i);\n",
   "}\n\n",
  ] 

 fun decStruct _ s =
  let val s = Symbol.unique s
   in app print ["struct ", s, ";\ntypedef struct ", s, " *", s, ";\n"]
  end

 val (decArray,decRec) = (decStruct,decStruct);

 fun decProc p as {procs,...} s = 
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

 fun defProc p as {blocks,procs,...} s =
  case (SymTable.look(blocks,s), SymTable.look(procs,s)) of (b,{res,args}) =>
   ( app print [Symbol.unique res, " ", Symbol.unique s, " ("]
   ; appFmt (fn (ty,name) => app print [(typeStr ty), " ", (Symbol.unique name)])
      "," ")\n" (ListPair.map id (args (#args b)))
   ; print "{\n"
   ; app (decVar p) (exhaust (#args b) (#vars b))
   ; app printTExps (#body b)
   ; print "}\n"
   )

 fun decVar p as {vars,...} s = 
  case SymTable.look(vars, s) of {typ,_} => 
   app print [(typeStr typ), " ", (Symbol.unique s), ";\n"]

 fun printStmt stmt = 
  case stmt 
   of ASSIGN {var, texp} = case texp
      of {STRING, _} => 
          ( appAlt print printVar ["strdup(", var, ", "]
          ; appAlt printTExp print [texp, ");\n"]
          )
       | {_,_} => appAlt print printTExp ["=", texp, ";\n"]
    | IF {test, then', else'} = 
       ( appAlt print printTExp ["if (", test, ") {\n"] 
       ; appAlt printStmt print [then', "}\n else {\n", else', "}\n"]
       )
	| EXP te = appAlt printTExp print [te, ";\n"]
	| RETURN te = appAlt print printTExp ["return ", te, ";\n"]
	| LABEL s = app print [Symbol.unique s, ":\n"]
	| GOTO s = app print ["goto ", Symbol.unique s, ";\n"]

 fun malloc ty exp =
   ( app print
      ["(", typeStr typ, ")malloc(sizeof(struct ", typeStr typ, ") * ("]
   ; (case exp of NONE => print "1" | (SOME x) => printTexp exp)
   ; print "))"
   )

 fun printTExp p te as {typ, e} = 
  case e
   of ARR size = malloc typ SOME size
    | REC = malloc typ NONE
    | CALL {func, args} = 
       ( app print [Symbol.unique func, "("] 
       ; appFmt printTExp ", " ")" args
       ) 
    | INT i = print (Int.toString i)
    | STR str = app print ["\"", str, "\""]
    | OP of {left, op, right} = case left 
       of {STRING,_} => 
           ( appAlt print printTExp ["(strcmp(", left, ", ", right, ")"] 
           ; app print [opname op, "0?1:0)"]
           ) 
        | {_,_} => appAlt print (printTExp p) ["(", left, opname op, right,")"]
    | VAR v = printVar v
    | NULL = print "NULL"
 
 
 fun printVar v = case v
    of SIMPLE s => print (Symbol.unique s)
     | FIELD (v',s) => (printVar v'; print "."; print (Symbol.unique s))
     | INDEX (v',e) => (printVar v'; print ".elts["; printTExp e; print "]")

 fun print p as {main, procs, arrays, records,...} = 
   ( print "#include <stdio.h>\n#include <stdlib.h>\n"
   ; printStdLib
   ; SymTable.app (decRec p) (#records p)
   ; SymTable.app (decArr p) (#arrays p)
   ; SymTable.app (decProc p) (#procs p)
   ; SymTable.app (defRec p) (#records p)
   ; SymTable.app (defArr p) (#arrays p)
   ; SymTable.app (defProc p) (#procs p)
   ; app print ["int main () {\n", (Symbol.unique (#main p))]
   ; print "()}\n"
   ) 

end


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
