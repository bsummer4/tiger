structure ParseUtils = struct
 local open AST open Util in
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
  fun newfield   (n,t,pos) = {name=n, typ=t, pos=pos}
  fun newtypedec (n,t,pos) = TYPE_DEC [{name=n, ty=t, pos=pos}]

  fun newfor (v,l,h,b,pos) =
    FOR {var=v,lo=l,hi=h,body=b,pos=pos}
  fun newvardec (n,t,i,pos) =
    VAR_DEC {name=n, typ=t, init=i, pos=pos}
  fun newfundec (n,a,r,b,pos) =
    FUN_DEC [{name=n, args=a, result=r, body=b, pos=pos}]

  fun newvar ((s,p),ts) =
   let fun r (acc, []) = acc
         | r (acc, t::ts) =
            case t of TFIELD(s,pos) => r (FIELD(acc,s,pos),ts)
                    | TINDEX(e,pos) => r (INDEX(acc,e,pos),ts)
   in r (SIMPLE(s,p),ts)
   end

 (*
	All 'FUN_DEC's and 'TYPE_DEC's in 'decs' must contain exactly one
	definition.
 *)
 fun newdec decs =
  let fun loop acc [] = rev acc
        | loop acc remain =
           (case hd remain
             of FUN_DEC _ => fdec acc [] remain
              | TYPE_DEC _ => tdec acc [] remain
              | VAR_DEC _ => loop (hd remain::acc) (tl remain))
      and fdec acc fs ((FUN_DEC[f])::ds) = fdec acc (f::fs) ds
        | fdec _ _ ((FUN_DEC _)::_) = raise FAIL
        | fdec acc fs ds = loop ((FUN_DEC(rev fs))::acc) ds
      and tdec acc ts ((TYPE_DEC[t])::ds) = tdec acc (t::ts) ds
        | tdec _ _ ((TYPE_DEC _)::_) = raise FAIL
        | tdec acc ts ds = loop ((TYPE_DEC (rev ts))::acc) ds
  in loop [] decs
  end
 end
end
