structure LL = struct

open IR;
structure ST = SymTable;

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
     | INDEX (v,{ty,e}) => varr (expr acc e) v
  and expr acc e =
   case e
    of (a as ARR {init=SOME i,size=s}) => foldl f acc [a,#e s,#e i]
     | (a as ARR {init=NONE,size=s}) => foldl f acc [a,#e s]
     | (a as ASSIGN {var=v,exp=e}) => varr (foldl f acc [a,#e e]) v
     | (b as BREAK) => f(b,acc)
     | (i as IF {test=t,then'=th}) => foldl f acc [i,#e th,#e t]
     | (i as IFELSE {test=t,then'=th,else'=e}) => 
	     foldl f acc [i,#e e,#e th,#e t]
     | (i as INT _) => f(i,acc)
     | (n as NIL) => f(n,acc)
     | (o' as OP {left=l,right=r,...}) => foldl f acc [o',#e r,#e l]
     | (s as STR _) => f(s,acc)
     | (v as VAR vd) => varr (f(v,acc)) vd
     | (w as WHILE {test=t,body=b}) => foldl f acc [w,#e b,#e t]
     | (s as SEQ l) => foldl f acc (s::(map #e l))
     | (r as REC (SOME t)) => 
	     foldl f acc (r::(map (#e) (ST.listItems t)))
     | (r as REC NONE) => f(r,acc)
     | (c as CALL {args=a,...}) =>
	     foldl f acc (c::((map #e (!a)):IR.exp list))
 in expr acc exp
 end

fun foldCalls f acc exp =
 let fun r(exp,acc) =
      case exp
       of c as CALL _ => f(c,acc)
        | _ => acc
 in foldExp r acc exp
 end

fun foldVars f acc exp =
 let fun r(exp,acc) =
      case exp
      of VAR v => f(v,acc)
       | _ => acc
 in foldExp r acc exp
 end

(* Get non-foreign blocks *)
fun getTigerBlocks ({blocks,...}:program) =
  ST.foldli (fn (k,b,a) =>
             case b of FOREIGN => a
                     | TIGER (b) => ((k,((#e o #body) b))::a))
   [] blocks

(* get a list of call sites *)
fun addCall ((CALL {func,args}),acc) =
  (case ST.find(acc,func)
   of SOME sites => ST.insert(acc,func,args::sites)
    | NONE       => ST.insert(acc,func,[args]))
    | addCall (_,_) = raise Match

fun createCallMap  (p:program) = let
  fun createCallMap' (exp,acc) = foldCalls addCall acc exp
  in foldl (createCallMap' o (fn((k,b),a)=>(b,a))) ST.empty (getTigerBlocks(p)) end

(* find all unbound variables *)
fun addFreeVar (vt:vars) cb (v,acc) =
  let fun r v =
       (case v
        of SIMPLE s => s
         | FIELD (v,s) => r v
         | INDEX (v,e) => r v)
      val s = r v
      val t = {e=VAR(SIMPLE(s)),ty=(#typ (ST.lookup(vt,s)))}
  in case ST.find(vt,s)
      of SOME {block=b,...} => if b = cb then acc else ST.insert(acc,s,t)
       | NONE               => raise Match
  end

fun findFreeVars (p as {blocks,vars,...}:program) =
  let fun wrap ((id,bod),acc) =
       (id,ST.listItems (foldVars (addFreeVar vars id) ST.empty bod))::acc
  in foldl wrap [] (getTigerBlocks p)
  end

(* rewrite call sites with unbound variables *)
fun rewriteCalls p =
  let val cm  = createCallMap p
      val fvs = findFreeVars p
      fun rewrite (id,vs) = 
	   app (fn c => c := List.concat[vs,!c]) (ST.lookup(cm,id))
  in app rewrite fvs
   ; p
  end
end
