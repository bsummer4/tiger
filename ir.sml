(*
	This defines the intermediate representation.  This is mostly
	a subset of the AST that can be easily translated to C.

	- All objects are fully typed.
	- All symbols are replaced with references to data structures.
*)
fun range n =
 let fun r sofar i = if i<0 then sofar else r (i::sofar) (i-1)
 in r [] (n-1) end

structure Type = struct
 datatype t = VOID | INT | STRING | RECORD of t list | ARRAY of t
            | PROC of proc
 withtype proc = t * t list
end

signature IR = sig
 type proc and var
 datatype varExp = LOCAL of int | GLOBAL of int | FIELD of varExp * int
                 | INDEX of varExp * exp
 and oper = ADD | SUB | MUL | DIV | EQ | NEQ | LT | LE | GT | GE
 and stmt = ASSIGN of var * exp | IF of exp * exp * exp
          | WHILE of exp * exp list | FOR of (exp * exp * exp) * exp list
          | BREAK | RETURN of exp option | EXP of exp | NIL
 and exp = VAR of var | INT of int | STR of string
         | CALL of int * exp list | OP of exp * oper * exp
 type program and code = stmt list and procData = Type.t list * code
 val decVar: program -> Type.t -> (program * var)
 val decProc: program -> Type.proc -> (program * proc)
 val defProc: program -> (proc * procData) -> program
end

structure IR : IR = struct
 type unique = unit ref * int
 structure Map = BinaryMapFn (struct
  type ord_key=unique
  fun compare ((x',x),(y',y)) = Int.compare(x,y)
 end)

 type proc = unique and var = unique
 datatype varExp = LOCAL of int | GLOBAL of int | FIELD of varExp * int
                 | INDEX of varExp * exp
 and oper = ADD | SUB | MUL | DIV | EQ | NEQ | LT | LE | GT | GE
 and stmt = ASSIGN of var * exp | IF of exp * exp * exp
          | WHILE of exp * exp list | FOR of (exp * exp * exp) * exp list
          | BREAK | RETURN of exp option | EXP of exp | NIL
 and exp = VAR of var | INT of int | STR of string
         | CALL of int * exp list | OP of exp * oper * exp

 type code = stmt list
 type procData = Type.t list * code
 type 'a map = 'a Map.map
 type program = { procs: (Type.proc * procData option) map
                , globals: Type.t map
                , next: int }

 fun decVar {globals,next,procs} ty =
  let val v = (ref(),next)
  in ({globals=Map.insert (globals,v,ty), next=next+1, procs=procs},v)
  end

 fun decProc {globals,next,procs} ty =
  let val p = (ref(),next)
  in ({globals=globals, next=next+1, procs=Map.insert(procs,p,(ty,NONE))}, p)
  end

 fun defProc {globals,next,procs} (proc,data) =
  case Map.find (procs,proc)
   of NONE => raise Fail "You must declare procedures before defining them"
    | (SOME(ty,NONE)) => { globals=globals, next=next+1
                         , procs=Map.insert(procs,proc,(ty,SOME data)) }
    | (SOME _) => raise Fail "You may only define procedures once"
end

structure CG = struct
 exception WTF
 open IR
 open Type
 fun w s = TextIO.output (TextIO.stdOut, s)

 val letters = "abcdefghijklmnopqrstuvwxyz";
 fun name i =
  let val n = size letters
  in case (i div n, i mod n) of (tag,idx) =>
      str(String.sub(letters,idx)) ^ (if 0=tag then "" else Int.toString tag)
  end

 fun decl pre (ty,id) = (dumpType ty; w " "; w pre; w (name id))
 and decls (pre,sep) vars =
  ListPair.app (fn(t,i)=>(decl pre (t,i); w sep)) (vars, range(length vars))
 and dumpType t =
  case t
   of VOID => w "void" | INT => w "int" | STRING => w "char*"
    | RECORD(slots) => (w "struct {"; decls ("",";") slots; w "}")
    | (ARRAY t) => (dumpType t; w "*")

 val dumpArgs = decls ("a_",",")
 val dumpVars = decls ("l_",";")
 val dumpGlobs = decls ("g_",";")

 fun renderStmt s = ( case s of BREAK => w "break" | _ => (); w ";" )
 fun renderBlock stmts = ( w "{"; app renderStmt stmts; w "}" )

 fun renderFun ty id args vars code =
  ( dumpType ty; w " "; w ("f_"^(name id)); w "("; dumpArgs args
  ; renderBlock code )
end
