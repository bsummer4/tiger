(*
	This file defines the code to implement the static analysis
	phase of the complier. The function `Semantic.translate' takes
	a AST representation of a program (`AST.exp') and produces an
	IR representation of the same program (`IR.program'). Exceptions
	will be thrown if there is a type error, or an undefined reference
	to a symbol or value.

	One of the things that happens in this pass is that all names
	are made globally unique using the `Symbol.gensym' procedure. From
	here on, we will use the word `uname' to refer to such names.

	While walking the tree, we need to keep track of quite a bit of
	information:

		- The uname of the current block.
		- The uname of the parent block if any.
		- A set unames for all variables defined so far in the
		  current block.
		- A set unames for all sub-blocks defined so far within
		  the current block.
		- A mapping from variable names in the current lexical scope to their
		  unames.
		- A mapping from type names in the current lexical scope to their
		  values.
		- Everything in IR.program except `#main'. We just set main to
		  Symbol.empty until we are done.
*)

structure Semantic = struct
 local open Util in

  type sym = Symbol.symbol
  structure ST = SymTable
  type sm = sym ST.table
  exception TypeError

  structure State = struct
   type scope = { ty:IR.Type.ty ST.table, var:sym ST.table }
   type blockState = { name:sym, parent:sym option, vars:sym list
                     , subBlocks:sym list }
   type state = blockState * scope * IR.program

   fun mkBlock s p =
    { name=Symbol.gensym s, parent=p, vars=[], subBlocks=[] } : blockState

   val emptyScope =
    {ty=ST.empty,var=ST.empty} : scope

   val emptyProgram =
    { main=Symbol.empty, blocks=ST.empty, arrays=ST.empty, records=ST.empty
    , vars=ST.empty } : IR.program
  end

  (* Convenience Functions *)
  fun bindType (b,{ty,var},p) name v = (b,{ty=ST.enter(ty,name,v),var=var},p)
  fun bindVal (b,{ty,var},p) name v = (b,{ty=ty,var=ST.enter(var,name,v)},p)
  fun getType (_,{ty,var},_) sym = ST.look(ty,sym)
  fun getVar (_,{ty,var},_) sym = ST.look(var,sym)
  type s=State.state;

  datatype operClass = INT_OP | CMP_OP
  fun operClassify oper =
   if mem oper [AST.ADD,AST.SUB,AST.MUL,AST.DIV]
   then INT_OP else CMP_OP

  fun cvt (s:s,exp) =
   let fun rec' {fields,typ,pos} = TODO()
       fun arr {typ,size,init,pos} = TODO()
       fun seq es = TODO()
   in case exp
       of AST.NIL => (s,{ty=IR.Type.NIL,e=IR.NIL})
        | AST.BREAK _ => (s,{ty=IR.Type.UNIT,e=IR.BREAK})
        | AST.INT i => (s,{ty=IR.Type.INT,e=IR.INT i})
        | AST.STR (str,p) => (s,{ty=IR.Type.STRING,e=IR.STR str})
        | AST.SEQ es => seq (map #1 es)
        | AST.REC r => rec' r
        | AST.ARRAY a => arr a
        | _ => TODO()
   end
 end
end

(*
 fun expect (s:s) ty exp =
  if Type.compatible (ty,expType env exp) then ()
  else raise TypeError

 and expectMatch (s:s) (a,b) =
  case expType env a
   of Type.UNIT => raise TypeError
    | aType => expect env aType b

 and varType (s:s) var =
  case var
   of AST.SIMPLE(sym,pos) => getVar env sym
    | AST.FIELD(var,sym,pos) =>
       (case varType env var
         of Type.REC(flist,u) =>
             (case List.find (fn (field,_) => field=sym) flist
               of SOME(_,ty) => ty
                | NONE => raise TypeError)
          | _ => raise TypeError)
    | AST.INDEX(var,exp,pos) =>
       ( expect env Type.INT exp
       ; case varType env var of Type.ARR (ty,u) => ty | _ => raise TypeError
       )

 and operType (s:s) {left,right,oper,pos} =
  ( case operClassify oper
     of INT_OP => app (expect env Type.INT) [left,right]
      | CMP_OP => expectMatch env (left,right)
  ; Type.INT
  )

 and ifType (s:s) {test,then',else',pos} =
  let val rtype = expType env then'
  in expect env Type.INT test
   ; case  else' of (SOME elseExp) => (expect env rtype elseExp; rtype)
                 | NONE => Type.NIL
  end

 and recType (s:s) {fields, typ, pos} =
  let fun names ((a,_),(b,_)) = (a,b)
      val sort = insertionSort (Symbol.compare o names)
      fun match ab bc = sort ab = sort bc
      val ty = getType env typ
      fun extractFields (Type.RECORD(fields,_)) = fields
        | extractFields _ = raise TypeError
  in
   if match (map (fn(sym,e,_)=>(sym,expType env e)) fields)
       (extractFields ty)
   then ty
   else raise TypeError
  end

 and arrType (s:s) {typ,size,init,pos} =
  case getType env typ of ty =>
   ( expect env Type.INT size
   ; expect env (case ty of Type.ARR(t,_)=>t | _=>raise TypeError) init
   ; ty )

 and expType (s:s) exp =
  case exp
   of
    | AST.ASSIGN {var,exp,pos} => (expect env (varType env var) exp; Type.NIL)
    | AST.SEQ [] => Type.NIL
    | AST.SEQ el => last (map ((expType env) o #1) el)
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
*)
