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
  fun bindType (b,{ty,var},p) name t = (b,{ty=ST.insert(ty,name,t),var=var},p)
  fun bindVal (b,{ty,var},p) name u = (b,{ty=ty,var=ST.insert(var,name,u)},p)
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

  (* smap :: (s*'a -> s*'b) -> s -> 'a list -> (s,'b list) *)
  (* Accumulate a new state while mapping over a list *)
  fun smap f (s:s) al =
   let fun r acc [] = acc
         | r (s,x'l) (x::xs) =
            case f (s,x) of (s',x') =>
             r (s',x'::x'l) xs
   in r (s,[]) al
   end

  fun elementType (_,_,program) (T.ARR r) = TODO()
    | elementType _ _ = raise TypeError
  fun fieldType (_,_,program) (T.REC r) n = TODO()
    | fieldType _ _ _ = raise TypeError

(*
 A couple of utillity functions for dealing with symbol->value maps. In
 `STcombine' we assume that both tables have identical sets of keys.
fromAlist :: (sym * 'a) list -> 'a ST.map
 STcombine :: 'a ST.map -> 'b ST.map -> ('a * 'b) ST.map
 newVar :: s -> sym -> (State.scope,s)
*)

(* type scope = { ty:T.ty ST.map, var:sym ST.map }
   type blockState = { name:sym, parent:sym option, vars:sym list
                     , subBlocks:sym list }
   type state = blockState * scope * I.program *)

  fun fromAlist l = foldl (fn((k,v),t)=>ST.insert(t,k,v)) ST.empty l
  fun STcombine t t' = ST.mapi (fn (k,v) => (v,ST.lookup(t',k))) t

  fun newVar (st:s as (bs,{ty,var},pgm)) v = 
   let val unq = Symbol.gensym v
       val scp = {ty=ty,var=ST.insert(var,v,unq)}
       val st  = bindVal st v unq
   in (scp,st)
   end
  
  (* fun wrapVar s = I.SIMPLE s *)
  fun texp e ty = {e=e,ty=ty}

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
     in (state',{ty=T.REC rty,e=I.REC(SOME(ST.mapi combine init))})
     end

    fun arr {typ,size,init,pos} =
     let val aty = case getType typ of T.ARR a => a | _ => raise TypeError
         val ety = ST.lookup (#arrays program,aty)
     in case smap cvt state [size,init]
         of (s',[s as{ty=tys,e=es}, i as{ty=tyi,e=ei}]) =>
             if tys<>T.INT orelse tyi<>ety then raise TypeError
             else (s',{ty=T.ARR aty,e=I.ARR{size=s,init=SOME i}})
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

    fun seq es =
     case smap cvt state es
      of (s,[]) => (s,{ty=T.UNIT,e=I.SEQ[]})
       | (s,el) => case last el of {ty,e} =>
                    (s,{ty=ty,e=I.SEQ el})

    fun var (A.SIMPLE(n,_)) =
         let val n' = getVar n
             val ty = #typ(ST.lookup(#vars program,n'))
         in (state,ty,I.SIMPLE n')
         end
      | var (A.FIELD(v,n,_)) =
         let val (s,rty,v') = var v
             val fty = (fieldType s rty n)
         in (s,fty,I.FIELD(v',n))
         end
      | var (A.INDEX(v,i,_)) =
         let val (s,aty,v') = var v
             val (s',i') = cvt (s,i)
             val ety = (elementType s' aty)
         in (s',ety,I.INDEX(v',i'))
         end

    fun varExp v = case var v of (s,ty,v') => (s,{ty=ty,e=I.VAR v'})

    fun call (f,e) =
     let val f = getVar f
         val proc  = ST.lookup(#procs program,f)
         val (s,l) = (smap cvt state e)
         fun cur f (a,b) = f a b
     in ListPair.app (cur assertTy) (map #ty l,#args proc);
        (s,{ty=(#res proc),e=I.CALL{func=f,args=ref l}})
     end
   
    (* Evaluate loop bounds before binding loop variable *)
    fun for (v,lo,hi,body) =
     let val iv = I.SIMPLE v
         val (s,l) = smap cvt state [lo,hi]
         val (scp,s) = newVar s v
         val ((bs,_,pgm),b) = cvt(s,body)

         val assn = {e=I.ASSIGN{var=iv,exp=hd l},ty=T.UNIT}
         val left = {e=I.VAR iv,ty=T.INT}
         val test = {e=I.OP{left=left,right=(last l),oper=I.LT},ty=T.INT}
         val incr = { e=I.OP{left=left,right={e=I.INT 1,ty=T.INT},oper=I.ADD}
                    , ty=T.INT}
         val body = {e=I.SEQ[b,incr],ty=T.UNIT}
         val whl  = {e=I.WHILE{test=test,body=body},ty=T.UNIT}
     in app (assertTy T.INT) (map #ty l);
        assertTy T.UNIT (#ty b);
        ((bs,scp,pgm),{e=I.SEQ[assn,whl],ty=T.UNIT})
     end

   fun while' (test,body) =
    let val (s,l) = smap cvt state [test,body]
        val (t,b) = (hd l,last l)
    in assertTy T.INT  (#ty t);
       assertTy T.UNIT (#ty b);
       (s,{e=I.WHILE{test=t,body=b},ty=T.UNIT})
    end

   fun if' (test,then',NONE) =
        let val (s,l) = smap cvt state [test,then']
            val (t,th) = (hd l, last l)
        in assertTy T.INT (#ty t);
           assertTy T.UNIT (#ty th);
           (s,{e=I.IF{test=t,then'=th},ty=T.UNIT})
        end
     | if' (test,then',SOME else') =
        let val (s,l) = smap cvt state [test,then',else']
            val (t,th,e) = (hd l, hd (tl l), last l)
        in assertTy T.INT (#ty t);
           assertTy (#ty th) (#ty e);
           (s,{e=I.IFELSE{test=t,then'=th,else'=e},ty=(#ty e)})
        end
    
   in case exp
       of A.NIL => (state,{ty=T.NIL,e=I.NIL})
        | A.BREAK _ => (state,{ty=T.UNIT,e=I.BREAK})
        | A.INT i => (state,{ty=T.INT,e=I.INT i})
        | A.STR (str,_) => (state,{ty=T.STR,e=I.STR str})
        | A.SEQ es => seq (map #1 es)
        | A.REC r => rec' r
        | A.ARRAY a => arr a
        | A.OP {left,oper,right,pos} => op' (oper,left,right)
        | A.VAR v => varExp v
        | A.CALL {func,args,pos} => call(func,args)
        | A.ASSIGN {var,exp,pos} => TODO()
        | A.IF {test,then',else',pos} => if'(test,then',else')
        | A.WHILE {test,body,pos} => while' (test,body)
        | A.FOR {var,lo,hi,body,pos} => for (var,lo,hi,body)
        | A.LET {decs,body,pos} => TODO()
   end
 end
end
