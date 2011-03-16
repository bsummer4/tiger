(* :TODO: Move these toplevel definitions to 'util.sml'. *)

(* Is 'e' a member of 'l'? *)
fun mem e l = case List.find (fn x=>x=e) l of NONE=>false | _=>true

(* This is like valOf except the caller chooses what exception is thrown. *)
fun protect e NONE = raise e
  | protect _ (SOME x) = x

(* This lets us compare objects by identity instead of by value. *)
type unique = unit ref

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

 datatype operType = INT_OP | CMP_OP
 fun operType oper =
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

 and varType (env: Context.t) var =
  case var
   of AST.SIMPLE(sym,pos) => valueType (varLookup env sym)
    | AST.FIELD(var,sym,pos) => TODO
    | AST.INDEX(var,exp,pos) => TODO

 and expType (env: Context.t) exp =
  case exp
   of AST.OP{left,right,oper,pos} =>
       ( case operType oper
          of INT_OP => app (expect env Type.INT) [left,right]
           | CMP_OP => expectMatch env (left,right)
       ; Type.INT )
    | AST.VAR v => varType env v
    | _ => TODO
end
