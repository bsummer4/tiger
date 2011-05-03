(*
	This defines the program representation for programs used inside
	the compiler.
*)

structure IR = struct
 type sym = Symbol.symbol
 structure ST = SymTable

 structure Type = struct
  datatype ty
   = NIL | INT | STR | UNIT | REC of sym | ARR of sym | FUN of sym

  type arrays = ty ST.map
  type records = (sym * ty) list ST.map
  type procs = {res:ty,args:ty list} ST.map

  fun compatible (a,b) =
   if a=b then true else case (a,b)
    of (ARR _,NIL) => true
     | (REC _,NIL) => true
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
 type block
  = { args:sym list
    , vars:sym list
    , subBlocks:sym list
    , up:sym option
    , body:texp
    }

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
 local 
  structure S = Sexp
  open IR
  structure T = Type
  structure U = Util 
  val name = Symbol.unique
  fun sym s = s
  val fix = S.SYM o name
  fun sexp s args = S.SEQ (S.SYM s::args)
 
 in
 
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
      of SOME l => U.TODO()
       | NONE => U.TODO())
   | SEQ l => sexp "seq" (map texpSexp l)
   | STR s => sexp "str" [S.STR s]
   | VAR v => varSexp v
   | WHILE {test,body} => sexp "while" [texpSexp test,texpSexp body]

 and varSexp v = case v
  of SIMPLE s => sexp "simple-var" [fix s]
   | FIELD (v,s) => sexp "field-var" [varSexp v,fix s]
   | INDEX (v,te) => sexp "index-var" [varSexp v,texpSexp te]

 and typSexp ty =  case ty
  of T.INT => sexp "type" [S.SYM "INT"]
   | T.STR => sexp "type" [S.SYM "STR"]
   | T.NIL => sexp "type" [S.SYM "NIL"]
   | T.REC s => sexp "type" [S.SYM "record", fix s]
   | T.ARR s => sexp "type" [S.SYM "array", fix s]
 
 and texpSexp (te as {e,ty}) = sexp "texp" [typSexp ty, expSexp e]

 and blockSexp (s,(b as {args,vars,subBlocks,up,body})) =
  sexp "block" [ fix s
               , sexp "args" (map fix args)
               , sexp "vars" (map fix vars)
               , sexp "subBlocks" (map fix subBlocks)
               , sexp "up" [] (* TODO *)
               , sexp "body" [texpSexp body]
               ] 
 
 and procSexp (s,(p as {res,args})) = 
  sexp (name s) [typSexp res, sexp "args" (map typSexp args)]
 
 and arraySexp (s,a) = sexp (name s) [typSexp a]

 and recordSexp (s,r) = 
  sexp (name s) (map (fn(s,typ)=>S.SEQ[fix s,typSexp typ]) r)
 
 and varSexp' (s, (v as {typ,block:Symbol.symbol,ref'})) =
  sexp "var" [fix s, typSexp typ, fix block, S.BOOL ref'] 
 
 and programSexp (p:program as {main,blocks,procs,arrays,records,vars}) =
  sexp "program" [fix main
                 , sexp "blocks" (map blockSexp (SymTable.listItemsi blocks))
                 , sexp "procs" (map procSexp (SymTable.listItemsi procs))
                 , sexp "array" (map arraySexp (SymTable.listItemsi arrays))
                 , sexp "records" (map recordSexp(SymTable.listItemsi records))
                 , sexp "vars" (map varSexp' (SymTable.listItemsi vars))
                 ]

 val x = {ty=T.INT,e=OP{oper=ADD,left={ty=T.INT, e=STR "3"}, right={ty=T.INT,e=INT 4}}}
 val () = S.printSexp(texpSexp x);
 
(*
  fun prog p = 
   let val {main,blocks,procs,arrays,records,vars} = p
   in fix main
    ; listItemsi
   (* print main *)
    
   (* print blocks *)   
   (* print vars *) 
   (* print procs *)
   (* print arrays *)
   (* print records *)
  
  and block {args,vars,subBlocks,up,body} = 
  and var (SIMPLE s) = sexp "simple-var" [fix s]
    | var (FIELD(v,s)) = sexp "field-var" [var v, fix s]
    | var (INDEX(v,e)) = sexp "subscript-var" [var v, exp e]
 
  and exp (VAR v) = sexp "var" [var v]
    | exp NIL = S.SYM "nil"
    | exp (INT i) = sexp (name (Symbol.mk "int")) [S.INT i]
    | exp (STR s) = sexp (name (Symbol.mk "string")) [S.STR s]
    | exp (CALL{func,args}) =
       sexp "call" (fix func::map exp args)
    | exp (OP{left,oper,right}) =
      sexp "op" [S.SYM(opname oper), exp left, exp right]
    | exp (REC{fields,typ}) =
       let fun f (name,e,_) = S.SEQ[fix name, exp e]
       in sexp "record" (fix typ::map f fields)
       end
 
    | exp (SEQ l) = sexp "seq" (map (exp o #1) l)
    | exp (ASSIGN{var=v,exp=e}) = sexp "assign" [var v, exp e]
    | exp (IF{test,then',else'}) =
       (case else' of NONE => sexp "if" [exp test, exp then']
                    | (SOME e) => sexp "if" [exp test, exp then', exp e])
    | exp (WHILE{test,body}) = sexp "while" [exp test, exp body]
    | exp BREAK = S.SEQ [S.SYM "break"]
    | exp (ARRAY{typ,size,init}) =
       sexp "array" [fix typ, exp size, exp init]
 in
  val toSexp = prog
 end 
*) 
end  
end 
