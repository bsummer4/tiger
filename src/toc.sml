open IR
open Util
structure T=Type
structure S=Symbol

val tmp = Symbol.mk "tmp"

fun unit e = {ty=T.UNIT,e=e}
fun seq el = unit(SEQ(el))

fun splitForLast l =
 let fun r _ [] = fuck()
       | r acc (x::[]) = (rev acc,x)
       | r acc (x::xs) = r (x::acc) xs
 in r [] l
 end

datatype expClass = EXP | STMT | BAD
fun okStmt e = BAD<>(expClass e)
and okExp e = (EXP=(expClass e))
and expClass (texp as {ty,e}) = case e
 of STR _ => EXP
  | VAR _ => EXP
  | INT _ => EXP
  | NIL => EXP
  | BREAK => STMT
  | ARR {size,init=NONE} => if okExp size then EXP else BAD
  | ARR _ => BAD
  | REC NONE => EXP
  | REC (SOME l) => BAD
  | ASSIGN {var,exp} => if okExp exp then STMT else BAD
  | CALL {func,args=ref args} => if List.all okExp args then EXP else BAD
  | IF {test,then'} =>
     if okExp test andalso okStmt then' then STMT else BAD
  | IFELSE {test,then',else'} =>
     if okExp test andalso List.all okStmt [then',else']
     then STMT else BAD
  | OP {left,oper,right} =>
     if List.all okExp [left,right] then EXP else BAD
  | SEQ l =>
     if List.all okStmt l then STMT else BAD
  | WHILE {test,body} =>
     if okExp test andalso okStmt body then STMT else BAD

fun push vl e = vl:=(e::(!vl))

(* fix :: (sym*ty) list ref -> (program * texp) -> (program * texp) *)
fun fix vl p (te as {e=exp,ty=typ}) =
 let val fix = fix vl p
     fun tmpVar ty =
      let val sym = Symbol.gensym tmp
          val () = push vl (sym,ty)
      in SIMPLE sym
      end
 in case exp

  of WHILE {test=test,body=body} =>
      if okExp test then unit(WHILE{test=test,body=(fix body)})
      else let val t = tmpVar T.INT
               val updateTest = fix(unit(ASSIGN{var=t,exp=test}))
           in seq[ updateTest
                 , unit(WHILE{ test={ty=T.INT,e=VAR t}
                             , body=seq[fix body, updateTest]
                             })]
           end

   | SEQ l => {ty=typ,e=SEQ (map fix l)}

   | ASSIGN {var,exp as {ty,e}} =>
      (case e
       of (SEQ el) =>
           (case splitForLast el of (prefix,last) =>
             fix({ty=ty,e=SEQ(List.concat
                               [prefix,
                                [{ ty=ty
                                 , e=ASSIGN{var=var,exp=last}
                                 }]])}))
        | (IFELSE{test,then',else'}) =>
           fix(unit(IFELSE{ test=test
                          , then'=unit(ASSIGN{var=var, exp=then'})
                          , else'=unit(ASSIGN{var=var, exp=else'})
                          }))
        | _ => if okExp exp then te else fix(unit((ASSIGN{var=var, exp=(fix exp)}))))

   | CALL {func, args=(ref args)} =>
      let val tmps = map (fn{ty,e}=>(ty,e,tmpVar ty)) args
          val args = map (fn(ty,_,v)=>{ty=ty,e=VAR v}) tmps
          val setup = map (fn(ty,e,v)=>unit(ASSIGN{var=v,exp={e=e,ty=ty}}))
                       tmps
      in {ty=typ,e=SEQ
          [ seq setup
          , {ty=typ,e=CALL{func=func,args=ref args}}
          ]}
      end

   | IF {test, then'} =>
      fix(unit(IFELSE{test=test, then'=then', else'=(unit (SEQ []))}))

   | IFELSE {test, then', else'} =>
      let val t = tmpVar T.INT
      in {ty=typ, e=SEQ[ fix(unit(ASSIGN{var=t, exp=test}))
                       , {ty=typ, e=IFELSE{ test={ty=T.INT, e=VAR t}
                                          , then'=fix(then')
                                          , else'=fix(else')}}]}
      end

   | OP {left, oper, right} =>
      (case left of {ty, e} =>
        let val t1 = tmpVar ty
            val t2 = tmpVar ty
        in {ty=typ, e=SEQ
            [ fix(unit(ASSIGN{var=t1, exp=left}))
            , fix(unit(ASSIGN{var=t2, exp=right}))
            , { ty=typ, e=OP{ left={ty=ty, e=VAR t1}
                            , oper=oper
                            , right={ty=ty, e=VAR t2}}}]}
        end)

   | ARR {size, init=SOME init} =>
      let val t1 = tmpVar T.INT
          val t2 = tmpVar typ
          val t3 = tmpVar T.INT
      in {ty=typ, e=SEQ
          [ fix(unit(ASSIGN{var=t1, exp=size}))
          , unit(ASSIGN{ var=t2
                       , exp={ty=typ
                           , e=ARR{ size={ty=T.INT, e=VAR t1}
                                  , init=NONE}}})
          , unit(WHILE{ test={ ty=T.INT
                             , e=OP{ left={ty=T.INT,e=VAR t3}
                                   , oper=LT
                                   , right={ty=T.INT,e=VAR t1}}}
                      , body=fix(unit(ASSIGN{ var=INDEX(t2, { ty=T.INT
                                                            , e=VAR t3})
                                            , exp=init}))})
           , {ty=typ, e=VAR t2}]}
      end

   | REC (SOME l) =>
      let val t = tmpVar typ
          fun foo (sym,{ty,e}) =
               fix(unit(ASSIGN{var=(FIELD(t,sym)),exp={ty=ty,e=e}}))
          val inits = ST.listItems (ST.mapi foo l)
      in { ty=typ
         , e=SEQ(List.concat[ [unit(ASSIGN{var=t, exp={ty=typ, e=REC NONE}})]
                            , inits
                            , [{ty=typ, e=VAR t}]])
         }
      end

   | _ => te
 end

(* transform :: (program * blockname) -> program *)
fun fromAlist l = foldl (fn((k,v),t)=>ST.insert(t,k,v)) ST.empty l
fun transform (program:program,blockname:S.symbol):program =
 let val vl = ref ([]:(S.symbol*T.ty)list)
     val {main,blocks,procs,arrays,records,vars=pvars} = program
     val {body,vars,args} = ST.lookup(#blocks program, blockname)
     val body' = fix vl program body
     val block' = {body=body',vars=List.concat[map #1 (!vl),vars],args=args}
     val newvars =
      fromAlist (map (fn(n,ty)=>(n,{typ=ty,block=blockname,ref'=false}))
                 (!vl))
     val vars' = ST.unionWith (fn _=>fuck()) (newvars,pvars)
     val blocks' = ST.insert(blocks,blockname,block')
 in {main=main,blocks=blocks',procs=procs,arrays=arrays,records=records,vars=vars'}
 end

(*
while (bad) do exp
--------------------
tmp1 := fix(bad)
while (tmp1) do
 ( fix(exp)
 ; tmp1 := fix(bad)
 )

seq(a, ...)
--------------------
seq(fix a, ...)

x := (bad;...;exp)
--------------------
fix(bad; ...; x:=exp)

x := if exp1 then exp2 else exp3
--------------------
fix(if exp1 then x:=exp2 else x:=exp3)

x := bad
--------------------
fix(x := fix(bad))

f(exp1,...,expN)
--------------------
( fix(tmp1=exp1)
; ...
; f(tmp1,...)
)

if(exp1) then exp2
--------------------
fix(if(exp1) then exp2 else ())

if(exp1) then exp2 else exp3
--------------------
fix(tmp1 := exp1)
if(tmp1) then fix(exp2) else fix(exp3)

bad1 [op] bad2
--------------------
fix(tmp1 := bad1)
fix(tmp2 := bad2)
tmp1 [op] tmp2

arr(size, init)
--------------------
( fix(tmp1 := size)
; tmp2 := arr[tmp1]
; tmp3 := 0
; while (tmp3 < tmp1) do
;  fix(tmp2[tmp3] := init)
; tmp2
)

rec(field1:=init1,...,fieldN:=init2)
--------------------
( tmp1 := rec
; fix(field1:=init1
; ...
; fix(fieldN:=initN
; tmp1
)

while (exp1) do exp2
--------------------
start:
 if (not(exp)) goto end
 exp 2
 goto start
end: ...

*)
