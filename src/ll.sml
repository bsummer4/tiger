(* structure LL = struct
  open IR;
end *)

open IR;
structure ST = SymTable;

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
      of CALL c => f acc c
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

(* get a list of call sites -- Yay 
   I will delete this later -- Yay *)

type callSite = texp list ref
type callMap = callSite list ST.table

fun addCall acc {func,args} = 
  case ST.find(acc,func)
  of SOME sites => ST.enter (acc,func,args::sites)
   | NONE       => ST.enter (acc,func,[args])

fun createCallMap exp = foldCalls addCall ST.empty exp

(* find all unbound variables *)
