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
  structure S = Symbol

  type sym = S.symbol
  structure ST = SymTable
  type sm = sym ST.map
  exception TypeError
  exception TypeLoop
  exception DuplicateTypes

  structure State = struct
   type scope = { ty:T.ty ST.map, var:sym ST.map }
   type blockState = { name:sym,  vars:sym list }
   type state = blockState * scope * I.program

   val emptyScope =
    {ty=ST.empty,var=ST.empty} : scope

   val emptyProgram =
    { main=S.empty, blocks=ST.empty, arrays=ST.empty, records=ST.empty
    , vars=ST.empty, procs=ST.empty } : I.program
  end

  (* Convenience Functions *)
  fun bindType (b,{ty,var},p) name t = (b,{ty=ST.insert(ty,name,t),var=var},p)
  fun bindVal (b,{ty,var},p) name u = (b,{ty=ty,var=ST.insert(var,name,u)},p)
  fun getType' (_,{ty,var},_) sym = ST.lookup(ty,sym)
  fun getVar' (_,{ty,var},_) sym = ST.lookup(var,sym)
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
  fun smap f s xs =
   case foldl (fn (x,(s,xs)) => case f(s,x) of (s',x') =>
               (s',x'::xs))
         (s,[]) xs
    of (s',ys) => (s',rev ys)

  fun elementType (_,_,p:I.program) (T.ARR r) =
       ST.lookup(#arrays p,r)
    | elementType _ _ = raise TypeError
  fun fieldType (_,_,p:I.program)(T.REC r) n =
       ST.lookup (ST.lookup(#records p,r),n)
    | fieldType _ _ _ = raise TypeError

  fun foobar s {ty,var} =
   let val () = app print ["==== ", s, " ====", "\n"]
       val () = app print ["---- ", "types" , " ----", "\n"]
       val () = ST.appi (fn (k,v) => (print(Symbol.unique k);print "\n")) ty
       val () = app print ["---- ", "values" , " ----", "\n"]
       val () = ST.appi (fn (k,v) => (print(Symbol.unique k);print "\n")) var
   in ()
   end

(*
 A couple of utillity functions for dealing with symbol->value maps. In
 `STcombine' we assume that both tables have identical sets of keys.
  fromAlist :: (sym * 'a) list -> 'a ST.map
  STcombine :: 'a ST.map -> 'b ST.map -> ('a * 'b) ST.map
  newVar :: s -> sym -> (sym,s)
*)

  fun fromAlist l = foldl (fn((k,v),t)=>ST.insert(t,k,v)) ST.empty l
  fun STcombine t t' = ST.mapi (fn (k,v) => (v,ST.lookup(t',k))) t

  fun newVar (st:s as (bs as {name,vars},{ty,var},pgm)) (v,typ:T.ty) : sym*s =
   let val unq = S.gensym v
       val pgm' = pgmWithVars pgm
                   (ST.insert (#vars pgm, unq, {typ=typ,block=(#name bs),ref'=false} ))
       val bs' = {name=name,vars=unq::vars}
       val st' = bindVal (bs',{ty=ty,var=var},pgm') v unq
   in (unq,st')
   end

  (* setup state for convert *)
  (* replace new scope with stashed scope *)
  (* insert block into program, return new state *)
  fun mkFun ({name,args,result,body,pos}:A.fundec,s:s as (bs,{ty=tyscope,var=varscope},pgm as {procs,vars,...})) : s =
   let val realName = getVar' s name
       val realArgNames = map (S.gensym o #name) args
       val realType = case result of SOME (ty,_) => getType' s ty | NONE => T.UNIT
       fun mkPgmVar (realName,arg:A.field,vars) =
        ST.insert( vars, realName
                , {block=realName,typ=getType' s (#typ arg), ref'=false} )
       val vars' = ListPair.foldl mkPgmVar vars (realArgNames,args)

       val bsForBody = {name=realName,vars=[]}
       fun bindVar (realName,arg:A.field,scp) = ST.insert(scp,#name arg,realName)
       val varForBody = ListPair.foldl bindVar varscope (realArgNames,args)
       val stateForBody = (bsForBody,{ty=tyscope,var=varForBody},pgmWithVars pgm vars')

       val ((bs',_,pgm'),l as {e,ty}) = cvt(stateForBody,body)
       val pgm'' = pgmWithBlocks pgm'
                    (ST.insert( #blocks pgm', realName
                              , {args=realArgNames,vars=(#vars bs'),body=l} ))

   in assertTy ty realType
    ; (bs,{ty=tyscope,var=varscope},pgm'')
   end

  (* cvt :: s*A.exp -> s*I.texp *)
  and cvt (state:s as (blocks,scope,program), exp:A.exp) : s*I.texp =
   let

    val (getType,getVar) = (getType' state,getVar' state)

    (* type scope = { ty:T.ty ST.map, var:sym ST.map }
       type blockState = { name:sym, vars:sym list }
       type state = blockState * scope * I.program     *)

    (* fold onto map of (sym * sym list) *)
    (* create new blockstate with crap *)
    (* change program to make new environment for crap *)
    (* change scope to allow new variable bindings *)

    fun fdec (s:s as (bs,{ty,var},pgm),dl) =
     let fun mkBind ({name,args,...}:A.fundec,acc) = ST.insert(acc,name,S.gensym(name))
         val var' = foldl mkBind var dl
         fun mkProcs ({name,result,args,...}:A.fundec,acc) =
          ST.insert(acc,ST.lookup(var',name),
                   { res=(case result of SOME (t,_) => getType' s t | NONE => T.UNIT)
                   , args=map ((getType' s) o #typ) args })
         val pgm' = pgmWithProcs pgm (foldl mkProcs (#procs pgm) dl)
         val s' = (bs,{ty=ty,var=var'},pgm')
     in (foldl mkFun s' dl,NONE)
     end

    fun rec' {fields,typ,pos} =
     let val rty = case getType typ of T.REC r => r | _ => raise TypeError
         val etys = ST.lookup(#records program,rty)
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

     (* mkTDefs :: sym -> {defs:ty ST, seen:unit ST} -> ty * ty ST *)
    fun mkTDefs s dm n {defs,seen} =
     case (ST.find(seen,n),ST.find(dm,n))
      of (SOME _,_) => raise TypeLoop
       | (_,NONE) => (getType' s n,defs)
       | (_,SOME(A.NAME_TY (n',_))) =>
          (case mkTDefs s dm n' {seen=ST.insert(seen,n,()),defs=defs}
            of (ty,defs') => (ty,ST.insert(defs',n,ty)))
       | (_,SOME(A.REC_TY _)) =>
          (case T.REC(S.gensym n) of x => (x,ST.insert(defs,n,x)))
       | (_,SOME(A.ARRAY_TY (n',_))) =>
          (case ( T.ARR(S.gensym n)
                , mkTDefs s dm n' {seen=ST.insert(seen,n,()),defs=defs})
            of (ty,(_,defs')) => (ty,ST.insert(defs',n,ty)))

    (* TODO use functional record update *)
    (* tdec :: state * {name:sym,ty:ty,pos:int} list -> state * exp option *)
    fun tdec (s:s as (bs,{ty=tyscope,var=varscope},program),dl) =
     let fun safeInsert ({name,ty,pos},t) =
          if ST.inDomain(t,name) then raise DuplicateTypes
                                 else ST.insert(t,name,ty)
         val dm = foldl safeInsert ST.empty dl
         val defs = ST.foldli
          (fn (n,ty,a) => #2(mkTDefs s dm n {defs=a,seen=ST.empty}))
          ST.empty dm
         val tyscope' = ST.unionWith (fn(a,_)=>a) (defs,tyscope)
         val () = foobar "tdec" {var=varscope,ty=tyscope'}
         fun mkRecTy fl =
          fromAlist (map (fn {name,typ,pos} =>
                          (name,ST.lookup(tyscope',typ))) fl)

         fun mkType n (p:I.program as {arrays=a,records=r,...})=
          case (ST.lookup(dm,n),ST.lookup(defs,n))
           of (A.NAME_TY _,_) => p
            | (A.REC_TY fl,T.REC tn) =>
               pgmWithRecords p (ST.insert(r,tn,mkRecTy fl))
            | (A.ARRAY_TY(et,_),T.ARR tn) =>
               pgmWithArrays p (ST.insert(a,tn,ST.lookup(tyscope',et)))
            | (A.REC_TY _,_) => ohwell()
            | (A.ARRAY_TY _,_) => ohwell()
         val p' = ST.foldli (fn(k,v,a)=>mkType k a) program defs

     in ((bs,{ty=tyscope',var=varscope},p'),NONE)
     end

    fun vdec (state,n,t,i) =
     let val (s,i') = cvt (state,i)
         val (u,s') = newVar s (n,#ty i')
         val () = foobar "vdec" (#2 s')
     in (case t of SOME (t,_) => assertTy (getType' state t) (#ty i')
                 | NONE       => ());
        (s',SOME{e=I.ASSIGN{var=I.SIMPLE u,exp=i'},ty=T.UNIT})
     end

    fun seq es =
     case smap cvt state es
      of (s,[]) => (s,{ty=T.UNIT,e=I.SEQ[]})
       | (s,el) => case last el of {ty,e} =>
                    (s,{ty=ty,e=I.SEQ el})

    fun varExp v = case var v of (s,ty,v') => (s,{ty=ty,e=I.VAR v'})
    and var (A.SIMPLE(n,_)) = let val n' = getVar n
                                  val ty = #typ(ST.lookup(#vars program,n'))
                              in (state,ty,I.SIMPLE n') end
      | var (A.FIELD(v,n,_)) = let val (s,rty,v') = var v
                                   val fty = (fieldType s rty n)
                               in (s,fty,I.FIELD(v',n)) end
      | var (A.INDEX(v,i,_)) = let val (s,aty,v') = var v
                                   val (s',i') = cvt (s,i)
                                   val ety = (elementType s' aty)
                               in (s',ety,I.INDEX(v',i')) end

    fun assign (v,e) =
     (case var v of (s,vty,v') =>
      (case cvt (s,e) of (s',e' as {ty=ety,e=ee}) =>
       ((assertTy vty ety);
        (s',{ty=T.UNIT,e=I.ASSIGN{var=v',exp=e'}}))))

    fun call (f,e) =
     let val f = getVar f
         val proc  = ST.lookup(#procs program,f)
         val (s,l) = (smap cvt state e)
         fun cur f (a,b) = f a b
     in ListPair.app (cur assertTy) (map #ty l,#args proc);
        (s,{ty=(#res proc),e=I.CALL{func=f,args=ref l}})
     end

    fun if' (test,then',NONE) =
         let val (s,(t,th)) = (case smap cvt state [test,then'] of (s,[a,b])=>(s,(a,b)) | _ => fuck())
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

    fun while' (test,body) =
     let val (s,l) = smap cvt state [test,body]
         val (t,b) = (hd l,last l)
     in assertTy T.INT  (#ty t);
        assertTy T.UNIT (#ty b);
        (s,{e=I.WHILE{test=t,body=b},ty=T.UNIT})
     end

    (* Evaluate loop bounds before binding loop variable *)
    fun for (v,lo,hi,body) =
     let val scp = (#2 state)
         val (s',l) = smap cvt state [lo,hi]
         val (uv,s) = newVar s' (v,T.INT)
         val iv = I.SIMPLE uv
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

    fun let' (decs,body) =
     let fun r (st,dec) =
          case dec
           of A.VAR_DEC {name,typ,init,...} => vdec (st,name,typ,init)
            | A.TYPE_DEC l => tdec (st,l)
            | A.FUN_DEC l => fdec (st,l)
         val (_,scp,_) = state
         val (s,assignOpts) = smap r state decs
         val assign = List.mapPartial id assignOpts
         val (s',body' as {e,ty}) = cvt(s,body)
     in (s',{e=I.SEQ (List.concat [assign,[body']]),ty=ty})
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
        | A.ASSIGN {var,exp,pos} => assign(var,exp)
        | A.CALL {func,args,pos} => call(func,args)
        | A.IF {test,then',else',pos} => if'(test,then',else')
        | A.WHILE {test,body,pos} => while'(test,body)
        | A.FOR {var,lo,hi,body,pos} => for (var,lo,hi,body)
        | A.LET {decs,body,pos} => let' (decs,body)
   end
 end

 local
  open Symbol
 in
  val stdTypes = [ (mk "int",T.INT), (mk "string",T.STR) ]
  val stdLib   = [ (mk "print"    ,{res=T.UNIT,args=[T.STR]})
                 , (mk "printi"   ,{res=T.UNIT,args=[T.INT]})
                 , (mk "flush"    ,{res=T.UNIT,args=[T.UNIT]})
                 , (mk "getchar"  ,{res=T.STR ,args=[T.UNIT]})
                 , (mk "ord"      ,{res=T.INT ,args=[T.STR]})
                 , (mk "chr"      ,{res=T.STR ,args=[T.INT]})
                 , (mk "size"     ,{res=T.INT ,args=[T.STR]})
                 , (mk "substring",{res=T.STR ,args=[T.STR,T.INT,T.INT]})
                 , (mk "concat"   ,{res=T.STR ,args=[T.STR,T.STR]})
                 , (mk "not"      ,{res=T.INT ,args=[T.INT]})
                 , (mk "exit"     ,{res=T.UNIT,args=[T.INT]})
                 ]
  val stdScope : State.scope = {ty=fromAlist stdTypes,var=fromAlist (map(fn(a,b)=>(a,a)) stdLib)}
  val stdProgram : I.program = pgmWithProcs State.emptyProgram (fromAlist stdLib)
 end

 (* create basic state, bind stdlib *)
 (* toIR :: A.exp -> I.program *)
 fun toIR e : I.program =
  let val bs  = {name=S.mk "TopLevel",vars=[]}
      val scp = stdScope
      val pgm = stdProgram
      val ((bs',_,pgm'),body) = cvt((bs,scp,pgm),e)
      val pgm'' = pgmWithBlocks pgm'
                   (ST.insert( #blocks pgm', #name bs'
                             , {args=[],vars=(#vars bs'),body=body} ))
  in pgmWithMain pgm'' (S.mk "TopLevel")
  end
end
