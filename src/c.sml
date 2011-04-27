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
  = ARR of {size:texp}
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
