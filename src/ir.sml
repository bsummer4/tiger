(*
	This defines the program representation for programs used inside
	the compiler.
*)

structure IR = struct
 type sym = Symbol.symbol
 structure ST = SymTable

 structure Type = struct
  datatype ty
   = NIL | INT | STR | UNIT | REC of sym | ARR of sym 

  type arrays = ty ST.map
  type records = ty ST.map ST.map
  type procs = {res:ty,args:ty list} ST.map

  fun compatible (a,b) =
   if a=b then true else case (a,b)
    of (REC _,NIL) => true
     | (NIL,ARR _) => true
     | (NIL,REC _) => true
     | _ => false
 end

 datatype exp
  = ARR of {size:texp, init:texp option}
  | ASSIGN of {var:var, exp:texp}
  | BREAK
  | CALL of {func:sym, args:texp list ref}
  | IF of {test:texp, then':texp}
  | IFELSE of {test:texp, then':texp, else':texp}
  | INT of int
  | NIL
  | OP of {left:texp, oper:oper, right:texp}
  | REC of texp ST.map option
  | SEQ of texp list
  | STR of string
  | VAR of var
  | WHILE of {test:texp, body:texp}
 and oper = ADD | SUB | MUL | DIV | EQ | NEQ | LT | LE | GT | GE | AND | OR
 and var = SIMPLE of sym | FIELD of var * sym | INDEX of var * texp
 withtype texp = {e:exp, ty:Type.ty}

 (*
	The `block' field in `vars' refers to where the block where a
	variable is defined or the block defined by a function depending
	on what type of variable it is. Note that `args' and `vars'
	are disjoint sets and that the order of `args' is significant.
 *)
 type tigerBlock = {args:sym list, vars:sym list, body:texp}
 datatype block = TIGER of tigerBlock | FOREIGN

 type vars = {typ:Type.ty, block:sym, ref':bool} ST.map
 type blocks = block ST.map
 type program =
  { main:sym
  , blocks:blocks
  , procs:Type.procs
  , arrays:Type.arrays
  , records:Type.records
  , vars:vars
  }
end

structure IRSexp = struct
  open IR Util
  structure S = Sexp
  structure T = Type
  val name = Symbol.unique
  fun sym s = s
  val fix = S.SYM o name
  fun sexp s args = S.SEQ (S.SYM s::args)

  fun opname oper = case oper
     of ADD => "+"  | SUB => "-" | MUL => "*" | DIV => "/" | EQ => "="
      | NEQ => "<>" | LT => "<"  | LE => "<=" | GT => ">"  | GE => ">="
      | AND => "&"  | OR => "|"

  fun expSexp e = case e
   of ARR {size,init} => (case init
       of SOME init => sexp "array" [texpSexp size, texpSexp init]
        | NONE => S.SYM "array")
    | ASSIGN {var=v,exp=e'} => sexp "assign" (varSexp v::[texpSexp e'])
    | BREAK => sexp "break" []
    | CALL {func:Symbol.symbol, args:texp list ref} => sexp "call" (fix func::map texpSexp (!args))
    | IF {test,then'} => sexp "if" [texpSexp test, texpSexp then']
    | IFELSE {test,then',else'} => sexp "ifelse" (map texpSexp [test,then',else'])
    | INT i => sexp "int" [S.INT i]
    | NIL => sexp "nil" []
    | OP {left, oper, right} => sexp "op" (S.SYM(opname oper)::[texpSexp left, texpSexp right])
    | REC l => (case l
       of SOME l => sexp "rec"
           (map (fn (s, te) => S.SEQ [fix s,texpSexp te])
            (SymTable.listItemsi l))
        | NONE => S.SYM "rec")
    | SEQ l => sexp "seq" (map texpSexp l)
    | STR s => sexp "str" [S.STR s]
    | VAR v => varSexp v
    | WHILE {test,body} => sexp "while" [texpSexp test,texpSexp body]

  and varSexp v = case v
   of SIMPLE s => sexp "simple-var" [fix s]
    | FIELD (v,s) => sexp "field-var" [varSexp v,fix s]
    | INDEX (v,te) => sexp "index-var" [varSexp v,texpSexp te]

  and typSexp ty = case ty
   of T.INT => sexp "type" [S.SYM "INT"]
    | T.STR => sexp "type" [S.SYM "STR"]
    | T.NIL => sexp "type" [S.SYM "NIL"]
    | T.REC s => sexp "type" [S.SYM "record", fix s]
    | T.ARR s => sexp "type" [S.SYM "array", fix s]
    | T.UNIT => sexp "type" [S.SYM "UNIT"]

  and texpSexp (te as {e,ty}) = sexp "texp" [typSexp ty, expSexp e]

  and blockSexp (s,FOREIGN) = sexp "foreign-function" [fix s]
    | blockSexp (s,TIGER(b as {args,vars,body})) =
       sexp "block" [ fix s
                    , sexp "args" (map fix args)
                    , sexp "vars" (map fix vars)
                    , sexp "body" [texpSexp body]
                    ]

  and procSexp (s,(p as {res,args})) =
   sexp (name s) [typSexp res, sexp "args" (map typSexp args)]

  and arraySexp (s,a) = sexp (name s) [typSexp a]

  and recordSexp (s,r) =
   sexp (name s) (map (fn(s,typ)=>S.SEQ[fix s,typSexp typ])
                  (SymTable.listItemsi r))

  and varSexp' (s, (v as {typ,block:Symbol.symbol,ref'})) =
   sexp (name s) [typSexp typ, fix block, S.BOOL ref']

  fun programSexp (p:program as {main,blocks,procs,arrays,records,vars}) =
   sexp "program" [fix main
                  , sexp "blocks" (map blockSexp (SymTable.listItemsi blocks))
                  , sexp "procs" (map procSexp (SymTable.listItemsi procs))
                  , sexp "array" (map arraySexp (SymTable.listItemsi arrays))
                  , sexp "records" (map recordSexp(SymTable.listItemsi records))
                  , sexp "vars" (map varSexp' (SymTable.listItemsi vars))
                  ]

end

fun pgmWithMain {main=m,blocks=b,procs=p,arrays=a,records=r,vars=v} m' =
 {main=m',blocks=b,procs=p,arrays=a,records=r,vars=v}
fun pgmWithBlocks {main=m,blocks=b,procs=p,arrays=a,records=r,vars=v} b' =
 {main=m,blocks=b',procs=p,arrays=a,records=r,vars=v}
fun pgmWithProcs {main=m,blocks=b,procs=p,arrays=a,records=r,vars=v} p' =
 {main=m,blocks=b,procs=p',arrays=a,records=r,vars=v}
fun pgmWithArrays {main=m,blocks=b,procs=p,arrays=a,records=r,vars=v} a' =
 {main=m,blocks=b,procs=p,arrays=a',records=r,vars=v}
fun pgmWithRecords {main=m,blocks=b,procs=p,arrays=a,records=r,vars=v} r' =
 {main=m,blocks=b,procs=p,arrays=a,records=r',vars=v}
fun pgmWithVars {main=m,blocks=b,procs=p,arrays=a,records=r,vars=v} v' =
 {main=m,blocks=b,procs=p,arrays=a,records=r,vars=v'}

structure IRUtil = struct
 open IR
 structure T = Type
 fun unit e = {ty=T.UNIT,e=e}
 fun intType e = {ty=T.INT,e=e}
 fun add a b = {ty=T.INT,e=OP{oper=ADD,left=a, right=b}}
 fun inc v = unit(ASSIGN{var=v,exp=(add (intType (VAR v)) (intType (INT 1)))})
 fun seq el = unit(SEQ(el))
 fun mapVar f (SIMPLE s) = f (SIMPLE s)
   | mapVar f (FIELD(v,i)) = f (FIELD(f v,i))
   | mapVar f (INDEX(v,texp)) = f (INDEX(f v,texp))

 fun mapExp f texp =
  let
   fun varr v =
    case v
     of SIMPLE _ => v
      | FIELD (v,i) => FIELD (varr v,i)
      | INDEX (v,texp) => INDEX(varr v, expr texp)
   and expr {ty,e} =
    let val f = f o (fn e => {ty=ty,e=e}) in
     case e
      of BREAK => f e
       | INT _ => f e
       | NIL => f e
       | STR _ => f e
       | SEQ l => f (SEQ (map expr l))
       | REC (SOME t) => f (REC (SOME (ST.map expr t)))
       | REC NONE => f (REC NONE)
       | CALL {args,func} =>
        ( args := (map expr (!args))
        ; f (CALL{args=args,func=func})
        )
       | ARR {init=SOME i,size} => f(ARR{init=SOME (expr i), size=expr size})
       | ARR {init=NONE,size} => f(ARR{init=NONE, size=expr size})
       | ASSIGN {var,exp} => f(ASSIGN{var=varr var, exp=expr exp})
       | IF {test,then'} => f(IF{test=expr test, then'=expr then'})
       | IFELSE {test,then',else'} => 
          f(IFELSE{ test=expr test, then'=expr then', else'=expr else'})
       | OP {left,right,oper} => 
          f(OP{left=expr left, oper=oper, right=expr right})
       | VAR vd => f (VAR (varr vd))
       | WHILE {test,body} => f(WHILE{test=expr test, body=expr body})
    end
  in expr texp
  end
end
