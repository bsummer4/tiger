(*
	This defines the program representation for programs used inside
	the compiler.
*)

structure IR = struct
 type sym = Symbol.symbol

 structure Type = struct
  datatype ty
   = NIL | INT | STR | UNIT | REC of sym | ARR of sym | FUN of sym

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
  = ARR of {size:texp, init:texp option}
  | ASSIGN of {var:var, exp:texp}
  | BREAK
  | CALL of {func:sym, args:texp list ref}
  | IF of {test:texp, then':texp}
  | IFELSE of {test:texp, then':texp, else':texp}
  | INT of int
  | NIL
  | OP of {left:texp, oper:oper, right:texp}
  | REC of (sym * texp) list option
  | SEQ of texp list
  | STR of string
  | VAR of var
  | WHILE of {test:texp, body:texp}
 and oper = ADD | SUB | MUL | DIV | EQ | NEQ | LT | LE | GT | GE | AND | OR
 and var = SIMPLE of sym | FIELD of var * sym | INDEX of var * texp
 withtype texp = {e:exp, ty:Type.ty}

 (*
 	The `block' field in `vars' refers to where the block where a
 	variable is defined or the block defined by a function depending
	on what type of variable it is. Note that `args' and `vars'
	are disjoint sets and that the order of `args' is significant.
 *)
 type block
  = { args:sym list
    , vars:sym list
    , subBlocks:sym list
    , up:sym option
    , body:texp
    }

 type vars = {typ:Type.ty, block:sym, ref':bool} SymTable.table
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
