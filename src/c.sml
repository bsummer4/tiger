(*
    This defines the program representation for programs used inside
    the compiler.
*)

structure C = struct
 type sym = Symbol.symbol

 structure Type = struct
  datatype ty
   = VOID_PTR | INT | STR | VOID | REC of sym | ARR of sym

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
 and var = SIMPLE of sym | FIELD of var * sym | INDEX of var * texp
 withtype texp = {e:exp, ty:Type.ty}

 (*
 	The `block' field in `vars' refers to where the block where a
 	variable is defined or the block defined by a function depending
	on what type of variable it is. Note that `args' and `vars'
	are disjoint sets and that the order of `args' is significant.
 *)
 type block = {args:sym list, vars:sym list, body:stmt list}
 type vars = {ty:Type.ty,isRef:bool} SymTable.table
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

signature C_PRINT = sig
 val printProg : C.program -> unit
end

(*
	If these are not true, an TODO exception will be thrown.
*)
structure CPrint (*:> C_PRINT *) = struct
 open Util C
 structure ST = SymTable
 structure Sym = Symbol

 (* decArray decRec decProc ; defArray defRec defProc *)

 fun id x = x

 fun exhaust [] [] = []
   | exhaust x [] = [] 
   | exhaust [] y = y
   | exhaust (x::xs) (y::ys) = exhaust xs ys

 fun appFmt f s e [] = print e
   | appFmt f s e (x::xs) =
      (f x; if xs=[] then () else print s; appFmt f s e xs)

 fun opname oper = case oper
    of ADD => "+"  | SUB => "-" | MUL => "*" | DIV => "/" | EQ => "=="
     | NEQ => "!=" | LT => "<"  | LE => "<=" | GT => ">"  | GE => ">="
     | AND => "&&" | OR => "||" 

 fun typeStr ty =
  let open Type in
   case ty 
    of Type.VOID_PTR => "void *"
     | Type.INT => "int"
     | Type.STR => "char *"
     | Type.VOID => "void"
     | Type.REC s => Sym.unique s
     | Type.ARR s => Sym.unique s
  end

 fun unique' s = Sym.unique (Sym.mk s)

 fun printStdLib() = app print 
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
   "  fflush(stdout);\n",
   "}\n\n",
   (* getchar *)
   "char *", unique' "getchar", "() {\n",
   "  char *str=(char *)malloc(sizeof(char) * 2);\n",
   "  if(str == NULL) {\n",
   "    fprintf(stderr,\"no memory\\n\");\n",
   "    exit(1);\n",
   "  }\n",
   "  str[0] = getchar();\n",
   "  str[1] = '\\0';\n", 
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
   "    str[1] = '\\0';\n",
   "  }\n",
   "  return str;\n",
   "}\n\n",
   (* size *)
   "int ", unique' "size", "(char *str) {\n",
   "  return strlen(str);\n",
   "}\n\n",
   (* substring *)
   "char *", unique' "substring", "(char *str, int start, int n) {\n",
   "  char *sub = malloc(n+1);\n",
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
   "  char *new_str = malloc(length);\n",
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
   "}\n\n"
  ] 

 fun decStruct _ s =
  let val s = Sym.unique s
   in app print ["struct ", s, ";\ntypedef struct ", s, " *", s, ";\n"]
  end

 val (decArr,decRec) = (decStruct,decStruct)

(*
 ====
 = For calls
 =====
 the argument expressions, the var to be created
 is the argument that we are creating a reference? { return false; }
  if the thing we are passing is not a simple variable, then complain.
  otherwise grab the name of the simple variable
 is it a reference?
  if yes then return false
  else return true

 =====
 = For declarations
 =====
 The variable to be created.
*)

 fun varDecPrint (p:program) var = 
  case ST.look(#vars p,var) of {ty, isRef} =>
   app print [typeStr ty, if isRef then "* " else " ", Sym.unique var]
   
 fun decProc (p:program as {procs,blocks,vars,...}) s =
  let val ({args,...}, {res,...}) = (ST.look(blocks,s), ST.look(procs,s))
  in app print [typeStr res, " ", Sym.unique s, "("]
   ; appFmt (varDecPrint p) ", " ");\n" args
  end

 fun defRec (p:program as {records,...}) s = 
   case ST.look(records,s) of rec' =>
   ( app print ["struct ", Sym.unique s, " {"]
   ; appFmt (fn (name, ty) => app print [typeStr ty, " ", Sym.unique name])
      "; " ";};\n" rec'
     (* ListPair.map id (#ty (#1 rec')) (#1 rec')) *)
   )
   
 fun defArr (p:program as {arrays,...}) s =
   case ST.look(arrays,s) of ty =>
    app print ["struct ", Sym.unique s, " { ", typeStr ty, " *elmts;};\n"]

 fun decVar (p:program as {vars,...}) s = 
  case ST.look(vars, s)
   of {ty,isRef=false} => app print [typeStr ty, " ", (Sym.unique s), ";\n"]
    | _ => fuck()

 fun defProc (p:program as {blocks,procs,...}) s =
  case (ST.look(blocks,s), ST.look(procs,s)) of (b as {args,...},{res,...}) =>
   ( app print [typeStr res, " ", Sym.unique s, " ("]
   ; appFmt (varDecPrint p) "," ")\n" args
   ; print "{\n"
   ; app (decVar p) (#vars b)
   ; app (printStmt p) (#body b)
   ; print "}\n"
   )

 and malloc p ty exp =
   ( app print
      ["(", typeStr ty, ")malloc(sizeof(struct ", typeStr ty, ") * ("]
   ; (case exp of NONE => print "1" | SOME x => (printTExp p) x)
   ; print "))"
   )

 and printVar p v = case v
    of SIMPLE s => app print 
        ["(", if #isRef(ST.look(#vars p,s)) then "*" else "", Sym.unique s, ")"]
     | FIELD (v',s) => (printVar p v'; print "."; print (Sym.unique s))
     | INDEX (v',e) => (printVar p v'; print ".elts["; (printTExp p) e; print "]")

 and printStmt p stmt = 
  case stmt 
   of ASSIGN {var, exp} =>
     (case exp
       of {ty=Type.STR,...} => 
           ( print "strdup(";  printVar p var; print ", "
           ; (printTExp p) exp; print ");\n"
           )
        | _ => (print "="; (printTExp p) exp; print ";\n")
     )
    | IF {test, then', else'} =>
       ( print "if ("; (printTExp p) test; print ") {\n"
       ; app (printStmt p) then'; print "}\n else {\n"; app (printStmt p) else'; print "}\n"
       )
    | EXP te => ((printTExp p) te; print ";\n")
    | RETURN te => (print "return "; (printTExp p) te; print ";\n")
    | LABEL s => app print [Sym.unique s, ":\n"]
    | GOTO s => app print ["goto ", Sym.unique s, ";\n"]

 and isRef p v = #isRef(ST.look(#vars p,v))
 and printTExp p (te as {e, ty}) = 
  let fun printArg (exp,var) =
       case (exp, isRef p var)
        of ({ty,e=VAR(SIMPLE sv)},true) => if isRef p sv then printTExp p exp
                                                  else (print "&"; printTExp p exp)
         | (_,false) => printTExp p exp
         | (_,true) => shit()
  in
   case e
    of ARR size => malloc p ty (SOME size)
     | REC => malloc p ty NONE
     | CALL {func, args} => 
        let val {args=argVars,...} = ST.look(#blocks p,func)
        in app print [Sym.unique func, "("]
         ; appFmt printArg ", " ")" (ListPair.zipEq (args,argVars))
        end
     | INT i => print (Int.toString i)
     | STR str => app print ["\"", str, "\""]
     | OP {left, oper, right} => 
        ( case left
           of {ty=Type.STR,e} => 
               ( print "(strcmp("; (printTExp p) left; print ", "; (printTExp p) right; print ")"
               ; app print [opname oper, "0?1:0)"]
               ) 
            | _ => (print "("; (printTExp p) left; print (opname oper); (printTExp p) right; print ")")
        )
     | VAR v => printVar p v
     | NULL => print "NULL"
  end

 fun printProg (p as {main, procs, arrays, records,...}) = 
   ( print "#include <stdio.h>\n#include <stdlib.h>\n#include <string>\n"
   ; printStdLib
   ; ST.appi ((decRec p) o #1) records
   ; ST.appi ((decArr p) o #1) arrays
   ; ST.appi ((decProc p) o #1) procs
   ; ST.appi ((defRec p) o #1) records
   ; ST.appi ((defArr p) o #1) arrays
   ; ST.appi ((defProc p) o #1) procs
   ; app print ["int main () {\n", Sym.unique main]
   ; print "()}\n"
   ) 

end
