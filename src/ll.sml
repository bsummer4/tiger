(* structure LL = struct
  open IR;
end *)

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

foo {

  int x;
  bar {
     x := y
  }

*)

fun foldExp f acc exp =
  let
    fun hack f (a,b) = f a b
    fun varr acc v =
     case v
      of SIMPLE _ => acc
       | FIELD (v,_) => varr acc v
       | INDEX (v,e) => varr (expr acc e) v
    and expr acc e =
      case e
      of (a as ARR {init=i,size=s}) => f (f (f acc a) (#e s)) (#e i)
       | (a as ASSIGN {var=v,exp=e}) => varr (f (f acc a) (#e e)) v
       | (b as BREAK) => f acc b
       | (i as IF {test=t,then'=th}) => f (f (f acc i) (#e th)) (#e t)
       | (i as IFELSE {test=t,then'=th,else'=e}) => f (f (f (f acc i) (#e e)) (#e th)) (#e t)
       | (i as INT _) => f acc i
       | (n as NIL) => f acc n
       | (o' as OP {left=l,right=r,...}) => f (f (f acc o') (#e r)) (#e l)
       | (s as STR _) => f acc s
       | (v as VAR vd) => varr (f acc v) vd
       | (w as WHILE {test=t,body=b}) => f (f (f acc w) (#e b)) (#e t)
       | (s as SEQ l) => foldl (hack f) (f acc s) (map #e l)
       | (r as REC l) => foldl (hack f) (f acc r) (map (#e o #2) l)
       | (c as CALL {args=a,...}) => foldl (hack f) (f acc c) ((map #e (!a)):IR.exp list)
  in expr acc exp
  end

fun foldCalls f acc exp = 
  let 
    fun r f acc exp =
      case exp
      of c as CALL _ => f acc c
       | _ => acc
  in r f acc exp
  end

fun foldVars f acc exp = 
  let 
    fun r f acc exp =
      case exp
      of VAR v => f acc v
       | _ => acc
  in r f acc exp
  end

(* get a list of call sites *)
type callSite = texp list ref
type callMap = callSite list ST.map

(* get block bodies *)
fun getBlockBodies ({blocks,vars,...}:program) =
  let fun cur f t s = f(t,s)
  in map (#e o #body o (cur ST.lookup blocks)) (keys blocks)
  end

fun addCall acc (CALL {func,args}) = 
  (case ST.find(acc,func)
  of SOME sites => ST.insert(acc,func,args::sites)
   | NONE       => ST.insert(acc,func,[args]))
   | addCall acc _ = raise Match

fun createCallMap' (exp,acc) = foldCalls addCall acc exp
fun createCallMap  (p:program) =
   foldl createCallMap' ST.empty (getBlockBodies(p))

(* find all unbound variables *)
type freeList = (sym * sym list)
fun addFreeVar (vt:vars) cb acc v = 
  let
    fun r v = 
      (case v
      of SIMPLE s => s
       | FIELD (v,s) => r v
       | INDEX (v,e) => r v)
  in
    case ST.find(vt,(r v))
     of SOME {block=b,...} => if b = cb then acc else v::acc
      | NONE      => raise Match
  end

fun findFreeVars (p as {blocks,vars,...}:program) =
  let
    val bods = getBlockBodies(p)
    fun wrap (id,bod,acc) = (id,(foldVars (addFreeVar vars id) [] bod))::acc
  in
    ListPair.foldlEq wrap [] ((keys blocks),bods)
  end

(* rewrite call sites with unbound variables *)
fun rewriteCalls p =
  let
    val cm  = createCallMap p
    val fvs = findFreeVars p
    fun rewriteCall' vs c = c := List.concat [vs,!c]
    (*fun rewriteCall cm (id,vs) = app (rewriteCall' vs) ST.lookup(cm,id)*)
  in
    ()(*app (rewriteCall cm) fvs*)
  end
