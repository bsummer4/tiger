(*
	This file defines the code to implement the static analysis
	phase of the complier. The function `Semantic.translate' takes
	a AST expression (`AST.exp') and produces an IR representation
	of the same program (`IR.program'). Exceptions will be thrown
	if there is a type error, or an undefined reference to a symbol
	or value.

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
		- A mapping from variable names in the current lexical
		  scope to their unames.
		- A mapping from type names in the current lexical scope
		  to their values.
		- Everything in IR.program except `#main'. We just set main to
		  Symbol.empty until we are done.
*)

structure Semantic = struct
 local open Util in
  structure A = AST
  structure I = IR
  structure T = IR.Type

  type sym = Symbol.symbol
  structure ST = SymTable
  type sm = sym ST.map
  exception TypeError

  structure State = struct
   type scope = { ty:T.ty ST.map, var:sym ST.map }
   type blockState = { name:sym, parent:sym option, vars:sym list
                     , subBlocks:sym list }
   type state = blockState * scope * I.program

   fun mkBlock s p =
    { name=Symbol.gensym s, parent=p, vars=[], subBlocks=[] } : blockState

   val emptyScope =
    {ty=ST.empty,var=ST.empty} : scope

   val emptyProgram =
    { main=Symbol.empty, blocks=ST.empty, arrays=ST.empty, records=ST.empty
    , vars=ST.empty, procs=ST.empty } : I.program
  end

  (* Convenience Functions *)
  fun bindType (b,{ty,var},p) name v = (b,{ty=ST.insert(ty,name,v),var=var},p)
  fun bindVal (b,{ty,var},p) name v = (b,{ty=ty,var=ST.insert(var,name,v)},p)
  fun getType (_,{ty,var},_) sym = ST.lookup(ty,sym)
  fun getVar (_,{ty,var},_) sym = ST.lookup(var,sym)
  type s=State.state

  datatype operClass = INT_OP | CMP_OP | EQ_OP
  fun operClassify oper =
   let val (i,e,c) = (INT_OP,EQ_OP,CMP_OP)
   in case oper of A.ADD=>i | A.SUB=>i | A.MUL=>i | A.DIV=>i | A.AND=>i
                 | A.OR=>i | A.LT=>c | A.LE=>c | A.GT=>e | A.GE=>e
                 | A.EQ=>e | A.NEQ=>e
   end

  fun irop op' = case op'
   of A.ADD=>I.ADD | A.SUB=>I.SUB | A.MUL=>I.MUL | A.DIV=>I.DIV
    | A.AND=>I.AND | A.OR=>I.OR   | A.LT=>I.LT   | A.LE=>I.LE
    | A.GT=>I.GT   | A.GE=>I.GE   | A.EQ=>I.EQ   | A.NEQ=>I.NEQ

  fun assertTy t t' = if T.compatible(t,t') then () else raise TypeError
  fun assertTy' [] t' = raise TypeError
    | assertTy' (t::ts) t' =
       if T.compatible(t,t') then () else assertTy' ts t'

  fun smap f (s:s) al =
   let fun r acc [] = acc
         | r (s,x'l) (x::xs) =
            case f (s,x) of (s',x') =>
             r (s',x'::x'l) xs
   in r (s,[]) al
   end

  (* cvt :: (s,exp) -> (s,exp) *)
  fun cvt (state:s as (blocks,scope,program), exp) =
   let

    val (getType,getVar) = (getType state,getVar state)

    fun rec' {fields,typ,pos} =
     let val rty = case getType typ of T.REC r => r | _ => raise TypeError
         val etys = ST.lookup (#arrays program,rty)
     in TODO()
        (*case smap (fn ... => cvt ...) state fields of (s,fields') => TODO()*)
     end

    fun arr {typ,size,init,pos} =
     let val aty = case getType typ of T.ARR a => a | _ => raise TypeError
         val ety = ST.lookup (#arrays program,aty)
     in case smap cvt state [size,init]
         of (s',[s as{ty=tys,e=es}, i as{ty=tyi,e=ei}]) =>
             if tys<>T.INT orelse tyi<>ety then raise TypeError
             else (s',{ty=T.ARR aty,e=I.ARR{size=s,init=i}})
          | _ => raise Match
     end

    fun op' (op',l,r) = case smap cvt state [l,r]
     of (s,[l' as{ty=lty,e=le}, r' as{ty=rty,e=re}]) =>
         ( assertTy lty rty
         ; case operClassify op'
            of INT_OP => assertTy T.INT lty
             | CMP_OP => assertTy' [T.INT,T.STR] lty
             | EQ_OP => ()
         ; (s,{ty=T.INT,e=I.OP{oper=irop op',left=l',right=r'}})
         )
      | _ => raise Match

    fun seq es = case smap cvt state es
     of (s,[]) => (s,{ty=T.UNIT,e=I.SEQ[]})
      | (s,el) => case last el of {ty,e} =>
         (s,{ty=ty,e=I.SEQ el})

   in case exp
       of A.NIL => (state,{ty=T.NIL,e=I.NIL})
        | A.BREAK _ => (state,{ty=T.UNIT,e=I.BREAK})
        | A.INT i => (state,{ty=T.INT,e=I.INT i})
        | A.STR (str,p) => (state,{ty=T.STR,e=I.STR str})
        | A.SEQ es => seq (map #1 es)
        | A.REC r => rec' r
        | A.ARRAY a => arr a
        | A.OP {left,oper,right,pos} => op' (oper,left,right)
        | A.VAR var => TODO()
        | A.CALL {func,args,pos} => TODO()
        | A.ASSIGN {var,exp,pos} => TODO()
        | A.IF {test,then',else',pos} => TODO()
        | A.WHILE {test,body,pos} => TODO()
        | A.FOR {var,lo,hi,body,pos} => TODO()
        | A.LET {decs,body,pos} => TODO()
   end
 end
end

(*
    fun ifthen' (s:s) (c,t) =
     let val rtype = expType env then'
     in expect env T.INT test
      ; case else' of (SOME elseExp) => (expect env rtype elseExp; rtype)
                    | NONE => T.NIL
     end

    fun oper (o',l,r) =
     let val (s',[(lty,le),(rty,re)]) = cvts s [l,r]
     in assertTy lty rty
      ; case operClass o'
         of INT_OP => assertTy INT lty
          | CMP_OP => assertTy' [T.INT,T.STR] lty
          | EQ_OP => ()
      ; (s',{ty=INT,e=OP{oper=cvtop o',left=l,right=r}})
     end

 fun expect (s:s) ty exp =
  if T.compatible (ty,expType env exp) then ()
  else raise TypeError

 and expectMatch (s:s) (a,b) =
  case expType env a
   of T.UNIT => raise TypeError
    | aType => expect env aType b

 and varType (s:s) var =
  case var
   of A.SIMPLE(sym,pos) => getVar env sym
    | A.FIELD(var,sym,pos) =>
       (case varType env var
         of T.REC(flist,u) =>
             (case List.find (fn (field,_) => field=sym) flist
               of SOME(_,ty) => ty
                | NONE => raise TypeError)
          | _ => raise TypeError)
    | A.INDEX(var,exp,pos) =>
       ( expect env T.INT exp
       ; case varType env var of T.ARR (ty,u) => ty | _ => raise TypeError
       )

 and operType {left,right,oper,pos} =
  ( case operClassify oper
     of INT_OP => app (expect env T.INT) [left,right]
      | CMP_OP => expectMatch env (left,right)
  ; T.INT
  )

 and recType (s:s) {fields,typ,pos} =
  let fun names ((a,_),(b,_)) = (a,b)
      val sort = insertionSort (Symbol.compare o names)
      fun match ab bc = sort ab = sort bc
      val ty = getType env typ
      fun extractFields (T.RECORD(fields,_)) = fields
        | extractFields _ = raise TypeError
  in
   if match (map (fn(sym,e,_)=>(sym,expType env e)) fields)
       (extractFields ty)
   then ty
   else raise TypeError
  end

 and arrType (s:s) {typ,size,init,pos} =
  case getType env typ of ty =>
   ( expect env T.INT size
   ; expect env (case ty of T.ARR(t,_)=>t | _=>raise TypeError) init
   ; ty )

 and expType (s:s) exp =
  case exp
   of
    | A.ASSIGN {var,exp,pos} => (expect env (varType env var) exp; T.NIL)
    | A.SEQ [] => T.NIL
    | A.SEQ el => last (map ((expType env) o #1) el)
    | A.LET {decs,body,pos} => TODO()
    | A.VAR v => varType env v
    | A.IF e => ifType env e
    | A.REC r => recType env r
    | A.ARRAY a => arrType env a
    | A.WHILE w => TODO()
    | A.FOR f => TODO()
    | A.OP oper => operType env oper
    | A.CALL c => TODO()
end
*)
