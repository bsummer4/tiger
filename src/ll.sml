(*
signature LL = sig
 structure ST
 structure S
 val keys: 'a ST.map -> sym list
 val foldExp: (exp * 'a -> 'a) -> 'a -> IR.exp -> 'a
 val foldCalls f acc exp
 val foldVars f acc exp
 val getTigerBlocks ({blocks,...}:program)
 val addCall (exp * {func:sym,args:sym list} list -> 
             {func:sym,args:sym list} ST.map 
 val mkCallMap (p:program)
 val freeVars : (program -> sym -> unit ST.map)
 val allFreeVars : (program -> unit ST.map ST.map)
 val rewriteCalls p cm fvs
 val lambdaLift IR.program -> IR.program
end
*)

structure LL = struct
 local
  open IR
  open Util
  open IRUtil
  structure ST = SymTable
  structure S = Symbol

  fun keys t = ST.foldli (fn(k,v,acc) => k::acc) [] t

  (*

  1) Build a map of function names to function call sites
  2) Iterate through each block
     i)  replace each occurence of a free variable within a block with
         a new bound refernece variable and add that to argument list
         as a reference
     ii) replace call sites with updated bound arguments

     If any call sites were modified, do another pass
  *)

  fun foldExp f acc exp =
   let
    fun varr acc v =
     case v
      of SIMPLE _ => acc
       | FIELD (v,_) => varr acc v
       | INDEX (v,{ty,e}) => varr (expr(e,acc)) v
    and expr (e,acc) =
     ( (*print("foldExp.expr\n");*)
     f (e, (case e
      of (ARR {init=SOME i,size=s}) => foldl expr acc [#e s,#e i]
       | (ARR {init=NONE,size=s}) => foldl expr acc [#e s]
       | (ASSIGN {var=v,exp=e}) => varr (foldl expr acc [#e e]) v
       | (BREAK) => acc
       | (IF {test=t,then'=th}) => foldl expr acc [#e th,#e t]
       | (IFELSE {test=t,then'=th,else'=e}) =>
  	     foldl expr acc [#e e,#e th,#e t]
       | (INT _) => acc
       | (NIL) => acc
       | (OP {left=l,right=r,...}) => foldl expr acc [#e r,#e l]
       | (STR _) => acc
       | (VAR vd) => varr acc vd
       | (WHILE {test=t,body=b}) => foldl expr acc [#e b,#e t]
       | (SEQ l) => foldl expr acc (map #e l)
       | (REC (SOME t)) =>
  	     foldl expr acc (map #e (ST.listItems t))
       | (REC NONE) => acc
       | (CALL {args=a,...}) =>
  	     foldl expr acc ((map #e (!a)):IR.exp list)
     )))
   in expr(exp,acc)
   end

  fun foldCalls f acc exp =
   let fun r(exp,acc) =
        case exp
         of c as CALL _ => f(c,acc)
          | _ => acc
   in foldExp r acc exp
   end

  fun foldVars f acc exp =
   let (*val () = print "foldVars\n"*)
       fun getName v =
        case v
         of SIMPLE s => s
          | FIELD (v,s) => getName v
          | INDEX (v,e) => getName v
       fun r (exp,acc) =
        ( (*print "foldVars\n"*)()
        ; case exp
           of VAR v => f(getName v,acc)
            | ASSIGN{var,exp} => f(getName var,acc)
            | _ => acc
       )
   in foldExp r acc exp
   end

  (* Get non-foreign blocks *)
  (* program -> exp tigerBlock *)
  fun tigerBlocks ({blocks,...}:program) =
    ST.mapPartiali (fn (k,b) =>
               case b of FOREIGN => NONE
                       | TIGER (b) => SOME(b))
     blocks

  (* get a list of call sites *)
  fun callSites (p:program) =
    let
     fun addCall blockName ((CALL {func,args}),acc) =
          (case ST.lookup(acc,func) of sites =>
            ST.insert(acc,func,(blockName,args)::sites))
       | addCall _ (_,_) = raise Match
     fun r (k,block:tigerBlock,acc) =
          foldCalls (addCall k) acc ((#e o #body) block)
    in ST.foldli r (ST.map (fn _ =>[]) (#blocks p)) (tigerBlocks(p))
    end

  fun freeVars (p:program) (blkName,blk:tigerBlock) =
    let fun r(nm,vars) = if (#block (ST.lookup(#vars p,nm))) = blkName
                         then vars else ST.insert(vars,nm,())
    in foldVars r ST.empty ((#e o #body) blk)
    end

  fun allFreeVars p =
   ST.mapPartiali (fn (k,v) =>
                    case freeVars p (k,v) of m =>
                     if ST.isEmpty m then NONE else SOME m)
    (tigerBlocks p)

  (* rewrite call sites with unbound variables *)
  fun rewriteBody p (vn,vn') body =
   let fun rewriteVarName (v as SIMPLE s) =
            if s<>vn then v else (SIMPLE vn')
         | rewriteVarName v = v
       fun rewriteVars (texp as {ty,e=VAR v}) =
            {ty=ty,e=VAR(mapVar rewriteVarName v)}
         | rewriteVars (texp as {ty,e=ASSIGN{var,exp}}) =
            {ty=ty,e=ASSIGN{var=mapVar rewriteVarName var,exp=exp}}
         | rewriteVars (texp) =
            texp
   in mapExp rewriteVars body
   end

  fun fixVar (p:program) callSites (bnm,vnm) =
   let fun tb (TIGER t) = t
         | tb FOREIGN = wtf "fixVar should only be passed TIGER blocks"
       val ty  = #typ (ST.lookup(#vars p,vnm))
       val {args=argVars,vars,body} = tb(ST.lookup(#blocks p,bnm))
       val {args=argTypes,res} = (ST.lookup(#procs p,bnm))
       val vnm' = S.gensym vnm
       val p = pgmWithVars p (ST.insert(#vars p,vnm',{typ=ty,block=bnm,ref'=true}))
       (*val _ = app print ["\n(fixing-block ",Symbol.unique bnm," "]*)
       val p = pgmWithBlocks p
                  (ST.insert( #blocks p,bnm
                            , TIGER { args=vnm'::argVars
                                    , vars=vars
                                    , body=rewriteBody p (vnm,vnm') body}))
       (*val _ = print ")\n"*)
       val p = pgmWithProcs p
                   (ST.insert(#procs p,bnm,{res=res,args=ty::argTypes}))
   in (*print "fixVar"*) 
      app (fn (callLoc,c) =>
           case if callLoc=bnm then vnm' else vnm of varToAdd =>
            (c:=({ty=ty,e=VAR(SIMPLE varToAdd)}::(!c))))
       (ST.lookup(callSites,bnm))
    ; p
   end

  (* Fold over two nested maps. *)
  fun foldli2 f acc m =
   ST.foldli
    (fn (key1,insideMap,acc2) =>
     ST.foldli
      (fn (key2,v,acc3) => f (key1,key2,v,acc3))
      acc2 insideMap)
    acc m

  (*
  # Lambda Lifting
  - find free vars
  - find call sites
  	- for all blocks
  	- for all free vars
  		- repeat until nothing changed
  *)
  fun lambdaLift (p:program as {vars,...}) =
   let
    val cs = callSites p
    fun fixVar' (blockName,varName,(),p) = fixVar p cs (blockName,varName)
    fun r p =
     case allFreeVars p of fvs =>
      if ST.isEmpty fvs then p else r (foldli2 fixVar' p fvs )
   in r p
   end

 in
  val lift : (IR.program -> IR.program) = lambdaLift
 end
end
