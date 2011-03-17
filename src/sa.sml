(* :TODO: Move these toplevel definitions to 'util.sml'. *)

(* Is 'e' a member of 'l'? *)
fun mem e l = case List.find (fn x=>x=e) l of NONE=>false | _=>true

(* This is like valOf except the caller chooses what exception is thrown. *)
fun protect e NONE = raise e
  | protect _ (SOME x) = x

(* This lets us compare objects by identity instead of by value. *)
type unique = unit ref

fun last [] = raise Match
  | last (x::[]) = x
  | last (x::xs) = last xs

structure Semantic = struct
 structure ST = SymTable
 structure Type = struct
  datatype t = NIL | INT | STRING | UNIT
             | RECORD of (Symbol.symbol * t) list * unique
             | ARRAY of t * unique
             | NAME of Symbol.symbol * t option ref
 end

 structure Value = struct
  datatype t = VAR of Type.t | FUN of {result:Type.t, formals:Type.t list}
 end

 structure Context = struct
  type t = {type':Type.t ST.table, var:Value.t ST.table}
  val empty = {type'=ST.empty, var=ST.empty}: t
  (* :TODO: Add all the default bindings to 'default'. *)
  val default = empty
 end

 exception TypeError
 exception UndefinedVariable of Symbol.symbol
 val TODO = Type.NIL

 datatype operClass = INT_OP | CMP_OP
 fun operClassify oper =
  if mem oper [AST.ADD,AST.SUB,AST.MUL,AST.DIV]
  then INT_OP else CMP_OP
 fun valueType (Value.FUN {result,...}) = result
   | valueType (Value.VAR t) = t
 fun varLookup (env: Context.t) sym =
  protect (UndefinedVariable sym) (ST.look (#var env,sym))

 fun expect env t exp =
  if t = (expType env exp) then () else raise TypeError

 and expectMatch env (a,b) =
  case expType env a
   of Type.NIL => raise TypeError
    | aType => expect env aType b

 and varType (env: Context.t) var : Type.t =
  case var
   of AST.SIMPLE(sym,pos) => valueType (varLookup env sym)
    | AST.FIELD(var,sym,pos) =>
       (case varType env var
         of Type.RECORD(flist,u) =>
             (case List.find (fn (field,_) => field=sym) flist
               of SOME(_,ty) => ty
                | NONE => raise TypeError)
          | _ => raise TypeError)
    | AST.INDEX(var,exp,pos) =>
       ( expect env Type.INT exp
       ; case varType env var of Type.ARRAY (ty,u) => ty | _ => raise TypeError
       )

 and operType env {left,right,oper,pos} =
  ( case operClassify oper
     of INT_OP => app (expect env Type.INT) [left,right]
      | CMP_OP => expectMatch env (left,right)
  ; Type.INT
  )

 and ifType env {test,then',else',pos} =
  let val rtype = expType env then'
  in expect env Type.INT test
   ; case  else' of (SOME elseExp) => (expect env rtype elseExp; rtype)
                 | NONE => Type.NIL
  end

 and expType (env: Context.t) exp =
  case exp
   of AST.NIL => Type.NIL
    | AST.BREAK _ => Type.NIL
    | AST.ASSIGN {var,exp,pos} => (expect env (varType env var) exp; Type.NIL)
    | AST.SEQ [] => Type.NIL
    | AST.SEQ el => last (map ((expType env) o #1) el)
    | AST.INT _ => Type.INT
    | AST.STR _ => Type.STRING
    | AST.LET {decs,body,pos} => TODO
    | AST.VAR v => varType env v
    | AST.IF e => ifType env e
    | AST.REC r => TODO
    | AST.ARRAY a => TODO
    | AST.WHILE w => TODO
    | AST.FOR f => TODO
    | AST.OP oper => operType env oper
    | AST.CALL c => TODO
end
