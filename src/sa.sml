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

  (* smap :: (s*'a -> s*'b) -> s > 'a list *)
  fun smap f (s:s) al =
   let fun r acc [] = acc
         | r (s,x'l) (x::xs) =
            case f (s,x) of (s',x') =>
             r (s',x'::x'l) xs
   in r (s,[]) al
   end

(*
	A couple of utillity functions for dealing with symbol->value
	maps. In `STcombine' we assume that both tables have idential
	sets of keys.
*)
  fun fromAlist l = foldl (fn((k,v),t)=>ST.insert(t,k,v)) ST.empty l
  fun STcombine t t' = ST.mapi (fn (k,v) => (v,ST.lookup(t',k))) t

  (* cvt :: s*A.exp -> s*I.exp *)
  fun cvt (state:s as (blocks,scope,program), exp) =
   let

    val (getType,getVar) = (getType state,getVar state)

    fun rec' {fields,typ,pos} =
     let val rty = case getType typ of T.REC r => r | _ => raise TypeError
         val etys = fromAlist (ST.lookup(#records program,rty))
         val (state',exps) = (smap
                              (fn (s,(n,e,p)) =>
                               (case cvt(s,e)of(s',e')=>(s',(n,e'))))
                              state
                              fields)
         val exps' = fromAlist exps
         val init = STcombine etys exps'
         fun combine (k,(fty,{e,ty})) = (assertTy ty fty; {e=e,ty=ty})
     in (state',{ty=T.REC rty,e=I.REC(ST.mapi combine init)})
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

    fun var (A.SIMPLE(n,_)) = (state,TODO(),I.SIMPLE(getVar n))
      | var (A.FIELD(v,n,_)) = (case var v of (s,ty,v') =>
                                (s,TODO(),I.FIELD(v',n)))
      | var (A.INDEX(v,i,_)) = (case var v of (s,ty,v') =>
                                (case cvt (s,i) of (s',i') =>
                                 (s',TODO(),I.INDEX(v',i'))))

    fun varExp v = case var v of (s,ty,v') => (s,{ty=ty,e=I.VAR v'})

   in case exp
       of A.NIL => (state,{ty=T.NIL,e=I.NIL})
        | A.BREAK _ => (state,{ty=T.UNIT,e=I.BREAK})
        | A.INT i => (state,{ty=T.INT,e=I.INT i})
        | A.STR (str,p) => (state,{ty=T.STR,e=I.STR str})
        | A.SEQ es => seq (map #1 es)
        | A.REC r => rec' r
        | A.ARRAY a => arr a
        | A.OP {left,oper,right,pos} => op' (oper,left,right)
        | A.VAR v => varExp v
        | A.CALL {func,args,pos} => TODO()
        | A.ASSIGN {var,exp,pos} => TODO()
        | A.IF {test,then',else',pos} => TODO()
        | A.WHILE {test,body,pos} => TODO()
        | A.FOR {var,lo,hi,body,pos} => TODO()
        | A.LET {decs,body,pos} => TODO()
   end
 end
end
