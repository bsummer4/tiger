structure TigerDefs = 
struct

open AST;
open Symbol;

datatype tvars = TFIELD of sym * pos | TINDEX of exp * pos
type tvar = (sym * pos) * tvars list

fun newop      (e1,oper,e2,pos) = OP {left=e1, oper=oper, right=e2, pos=pos}
fun newwhile   (t,b,pos) = WHILE {test=t, body=b, pos=pos}
fun newif      (c,t,e,pos) = IF {test=c, then'=t, else'=e, pos=pos}
fun newrec     (t,f,pos) = REC {typ=t, fields=f, pos=pos}
fun newcall    (f,a,pos) = CALL {func=f, args=a, pos=pos}
fun newarray   (t,s,i,pos) = ARRAY {typ=t, size=s, init=i, pos=pos}
fun newassign  (v,e,pos) = ASSIGN {var=v, exp=e, pos=pos}
fun newlet     (d,b,pos) = LET {decs=d, body=b, pos=pos}
fun newfield   (n,t,pos) = {name=n, esc=ref false, typ=t, pos=pos}
fun newtypedec (n,t,pos) = TYPE_DEC [{name=n, ty=t, pos=pos}]

fun newfor     (v,l,h,b,pos) =
  FOR {var=v,esc=ref false,lo=l,hi=h,body=b,pos=pos}
fun newvardec  (n,t,i,pos) =
  VAR_DEC {name=n, esc=ref false, typ=t, init=i, pos=pos}
fun newfundec  (n,a,r,b,pos) =
  FUN_DEC [{name=n, args=a, result=r, body=b, pos=pos}]

fun newvar    ((s,p),ts) =
  let
    fun r (acc, []) = acc
      | r (acc, t::ts) =
          case t
          of TFIELD(s,pos) => r (FIELD(acc,s,pos),ts)
          |  TINDEX(e,pos) => r (INDEX(acc,e,pos),ts)
  in
    r (SIMPLE(s,p),ts)
  end

fun newdec [] = []
  | newdec (d::l) =
      (case d
         of FUN_DEC(_)  => fdec ([],d::l)
         |  TYPE_DEC(_) => tdec ([],d::l)
         |  VAR_DEC(_)  => d::(newdec l))

and fdec (fs,[])   = [FUN_DEC(fs)]
  | fdec (fs,d::l) =
      (case d
         of FUN_DEC(fr) => fdec((hd fr)::fs,l)
         |  _ => FUN_DEC(fs)::(newdec (d::l)))

and tdec (ts,[])   = [TYPE_DEC(ts)]
  | tdec (ts,d::l) =
      (case d
         of TYPE_DEC(tr) => tdec((hd tr)::ts,l)
         |  _ => TYPE_DEC(ts)::(newdec (d::l)))

end
