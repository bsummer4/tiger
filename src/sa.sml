(*
	For now, this just does type-checking of expressions.
*)

structure Semantic = struct
 open Util
 structure ST = SymTable
 structure Type = struct
  datatype t = NIL | INT | STRING | UNIT
             | RECORD of (Symbol.symbol * t) list * unique
             | ARRAY of t * unique
             | NAME of Symbol.symbol * t option ref
  fun compatible _ = TODO();
 end

 structure Value = struct
  datatype t = VAR of Type.t | FUN of {result:Type.t, formals:Type.t list}
 end

 structure Context = struct
  type t = {ty:Type.t ST.table, var:Value.t ST.table}
  val empty = {ty=ST.empty, var=ST.empty}: t
  (* :TODO: Add all the default bindings to 'default'. *)
  val default = empty
  fun bindType {ty,var} name v = {ty=ST.enter(ty,name,v),var=var}
  fun bindVal {ty,var} name v = {ty=ty,var=ST.enter(var,name,v)}
  fun getType {ty,var} sym = ST.look(ty,sym)
  fun getVar {ty,var} sym = ST.look(var,sym)
 end

 exception TypeError
 exception UndefinedVariable of Symbol.symbol
 exception UndefinedType of Symbol.symbol

 datatype operClass = INT_OP | CMP_OP
 fun operClassify oper =
  if mem oper [AST.ADD,AST.SUB,AST.MUL,AST.DIV]
  then INT_OP else CMP_OP

 fun valueType (Value.FUN {result,...}) = result
   | valueType (Value.VAR t) = t

 fun varLookup e n = protect (UndefinedVariable n) (Context.getVar e n)
 fun typeLookup e n = protect (UndefinedVariable n) (Context.getType e n)

 fun expect env ty exp =
  if Type.compatible (ty,expType env exp) then ()
  else raise TypeError

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


 and recType env {fields, typ, pos} =
  let fun names ((a,_),(b,_)) = (a,b)
      val sort = insertionSort (Symbol.compare o names)
      fun match ab bc = sort ab = sort bc
      val ty = typeLookup env typ
      fun extractFields (Type.RECORD(fields,_)) = fields
        | extractFields _ = raise TypeError
  in
   if match (map (fn(sym,e,_)=>(sym,expType env e)) fields)
       (extractFields ty)
   then ty
   else raise TypeError
  end

 and arrType env {typ,size,init,pos} =
  case typeLookup env typ of ty =>
   ( expect env Type.INT size
   ; expect env (case ty of Type.ARRAY(t,_)=>t | _=>raise TypeError) init
   ; ty )

 and expType (env: Context.t) exp =
  case exp
   of AST.NIL => Type.NIL
    | AST.BREAK _ => Type.NIL
    | AST.ASSIGN {var,exp,pos} => (expect env (varType env var) exp; Type.NIL)
    | AST.SEQ [] => Type.NIL
    | AST.SEQ el => last (map ((expType env) o #1) el)
    | AST.INT _ => Type.INT
    | AST.STR _ => Type.STRING
    | AST.LET {decs,body,pos} => TODO()
    | AST.VAR v => varType env v
    | AST.IF e => ifType env e
    | AST.REC r => recType env r
    | AST.ARRAY a => arrType env a
    | AST.WHILE w => TODO()
    | AST.FOR f => TODO()
    | AST.OP oper => operType env oper
    | AST.CALL c => TODO()
end
