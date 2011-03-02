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
 datatype varExp = LOCAL of int | GLOBAL of var | FIELD of varExp * int
                 | INDEX of varExp * exp
 and oper = ADD | SUB | MUL | DIV | EQ | NEQ | LT | LE | GT | GE
 and stmt = ASSIGN of varExp * exp | IF of exp * block * block
          | WHILE of exp * block | FOR of (exp * exp * exp) * block
          | BREAK | RETURN of exp option | EXP of exp | NIL
 and exp = VAR of varExp | INT of int | STR of string
         | CALL of proc * exp list | OP of exp * oper * exp
 withtype block = stmt list
 type program and procData = Type.t list * block
 val empty: program
 val decVar: program -> Type.t -> (program * var)
 val decProc: program -> Type.proc -> (program * proc)
 val defProc: program -> (proc * procData) -> program
 val vars: program -> var list
 val var: program -> var -> Type.t
 val varNum: program -> var -> int
 val procs: program -> proc list
 val proc: program -> proc -> Type.proc * procData option
 val procNum: program -> proc -> int
end

structure IR : IR = struct
 type unique = unit ref * int
 structure Map = BinaryMapFn (struct
  type ord_key=unique
  fun compare ((x',x),(y',y)) = Int.compare(x,y)
 end)

 type proc = unique and var = unique
 datatype varExp = LOCAL of int | GLOBAL of var | FIELD of varExp * int
                 | INDEX of varExp * exp
 and oper = ADD | SUB | MUL | DIV | EQ | NEQ | LT | LE | GT | GE
 and stmt = ASSIGN of varExp * exp | IF of exp * block * block
          | WHILE of exp * block | FOR of (exp * exp * exp) * block
          | BREAK | RETURN of exp option | EXP of exp | NIL
 and exp = VAR of varExp | INT of int | STR of string
         | CALL of proc * exp list | OP of exp * oper * exp

 withtype block = stmt list
 type procData = Type.t list * block
 type 'a map = 'a Map.map
 type program = { procs: (Type.proc * procData option) map
                , globals: Type.t map
                , next: int }

 val empty = {procs=Map.empty, globals=Map.empty, next=0}

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

 fun procs (p:program) = map #1 (Map.listItemsi (#procs p))
 fun vars (p:program) = map #1 (Map.listItemsi (#globals p))
 fun proc (p:program) f = valOf (Map.find(#procs p,f))
 fun var (p:program) v = valOf (Map.find(#globals p,v))
 fun varNum p (_,i) = i
 fun procNum p (_,i) = i
end

structure CG = struct
 exception WTF
 open TextIO
 open IR
 fun w s = output(stdOut,s)

 fun TODO() = raise Fail "Not Implemented"

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
  let open Type
  in case t
      of VOID => w "void" | INT => w "int" | STRING => w "char*"
       | RECORD slots => (w "struct {"; decls ("",";") slots; w "}")
       | ARRAY t => (dumpType t; w "*")
       | PROC (r,args) => TODO()
  end

 val dumpArgs = decls ("a_",",")
 val dumpVars = decls ("l_",";")
 val dumpGlobs = decls ("g_",";")

 fun block stmts = ( w "{"; app stmt stmts; w "}" )

 and exp (INT i) = w (Int.toString i)
   | exp (STR s) = (w "\""; w s; w "\"")
   | exp _ = TODO()
 and var a = TODO()
 and stmt s =
  case s of BREAK => w "break;"
          | RETURN NONE => w "return;"
          | RETURN(SOME e) => (w "return "; exp e; w ";")
          | EXP e => (exp e; w ";")
          | ASSIGN(v,e) => (var v; w "="; exp; w ";")
          | IF (i,t,e) => (w "if ("; exp i; w ")"; block t; block e)
          | WHILE (i,b) => (w "while ("; exp i; w ")"; block b)
          | FOR ((i,c,n),b) =>
             (w "for ("; exp i; w ";"; exp c; w ";"; exp n; w ")"; block b)
          | NIL => ()

 fun renderFun ty id args vars code =
  ( dumpType ty; w " "; w ("f_"^(name id)); w "("; dumpArgs args; w ")"
  ; w "{" ; dumpVars vars; block code ; w "}"
  )

 fun renderProc p proc =
  let val id = IR.procNum p proc
      val ((ty,args),SOME (vars,code)) = IR.proc p proc
  in renderFun ty id args vars code
  end

 fun generate p main =
  ( dumpGlobs (map (IR.var p) (IR.vars p)); w "\n"
  ; renderProc p main; w "\n"
  ; app w ["int main(){f_", name (IR.procNum p main), "();}\n"]
  ; flushOut stdOut
  )
end
