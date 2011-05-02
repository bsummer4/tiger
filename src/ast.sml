(*
	This defines the AST representation and a utillity struct ASTPrint
	for printing ASTs.
*)

structure AST = struct
 type pos = int and sym = Symbol.symbol
 datatype oper
  = ADD | SUB | MUL | DIV | AND | OR | EQ | NEQ | LT | LE | GT | GE

 datatype exp
  = VAR of var
  | NIL
  | INT of int
  | STR of string * pos
  | CALL of {func:sym, args:exp list, pos:pos}
  | OP of {left:exp, oper:oper, right:exp, pos:pos}
  | REC of { fields:(sym * exp * pos) list, typ:sym, pos:pos}
  | SEQ of (exp * pos) list
  | ASSIGN of {var:var, exp:exp, pos:pos}
  | IF of {test:exp, then':exp, else':exp option, pos:pos}
  | WHILE of {test:exp, body:exp, pos:pos}
  | FOR of {var:sym, lo:exp, hi:exp, body:exp, pos:pos}
  | BREAK of pos
  | LET of {decs:dec list, body:exp, pos:pos}
  | ARRAY of {typ:sym, size:exp, init:exp, pos:pos}

 and var
  = SIMPLE of sym * pos
  | FIELD of var * sym * pos
  | INDEX of var * exp * pos

 and dec
  = TYPE_DEC of {name:sym, ty:ty, pos:pos} list
  | VAR_DEC of {name:sym, typ:(sym*pos) option, init:exp, pos:pos}
  | FUN_DEC of { name:sym, args:field list
               , result:(sym*pos)option, body:exp, pos:pos
               } list

 and ty = NAME_TY of sym*pos | REC_TY of field list | ARRAY_TY of sym*pos
 withtype field = {name:sym, typ:sym, pos:pos}
end

structure ASTSexp = struct
 local
  structure S = Sexp
  open AST
  val name = Symbol.unique

  fun sym s = s
  val fix = S.SYM o name
  fun sexp s args = S.SEQ (S.SYM s::args)
  fun opname oper = case oper
     of ADD => "+"  | SUB => "-" | MUL => "*" | DIV => "/" | EQ => "="
      | NEQ => "<>" | LT => "<"  | LE => "<=" | GT => ">"  | GE => ">="
      | AND => "&"  | OR => "|"

  fun var (SIMPLE(s,_)) = sexp "simple-var" [fix s]
    | var (FIELD(v,s,_)) = sexp "field-var" [var v, fix s]
    | var (INDEX(v,e,_)) = sexp "subscript-var" [var v, exp e]

  and exp (VAR v) = sexp "var" [var v]
    | exp NIL = S.SYM "nil"
    | exp (INT i) = sexp (name (Symbol.mk "int")) [S.INT i]
    | exp (STR(s,_)) = sexp (name (Symbol.mk "string")) [S.STR s]
    | exp (CALL{func,args,pos}) =
       sexp "call" (fix func::map exp args)
    | exp (OP{left,oper,right,pos}) =
      sexp "op" [S.SYM(opname oper), exp left, exp right]
    | exp (REC{fields,typ,pos}) =
       let fun f (name,e,_) = S.SEQ[fix name, exp e]
       in sexp "record" (fix typ::map f fields)
       end

    | exp (SEQ l) = sexp "seq" (map (exp o #1) l)
    | exp (ASSIGN{var=v,exp=e,pos}) = sexp "assign" [var v, exp e]
    | exp (IF{test,then',else',pos}) =
       (case else' of NONE => sexp "if" [exp test, exp then']
                    | (SOME e) => sexp "if" [exp test, exp then', exp e])
    | exp (WHILE{test,body,pos}) = sexp "while" [exp test, exp body]
    | exp (FOR{var=v,lo,hi,body,pos}) =
       sexp "for" [fix v, exp lo, exp hi, exp body]
    | exp (BREAK p) = S.SEQ [S.SYM "break"]
    | exp (LET{decs,body,pos}) =
       sexp "let" [S.SEQ(map dec decs), exp body]
    | exp (ARRAY{typ,size,init,pos}) =
       sexp "array" [fix typ, exp size, exp init]

   and dec (FUN_DEC l) =
        let fun field{name,typ,pos} =
             S.SEQ [fix name, fix typ]
            fun f{name,args,result,body,pos} =
             case result
              of NONE => S.SEQ [fix name, S.SEQ(map field args), exp body]
               | SOME(s,_) =>
                  S.SEQ [fix name, fix s, S.SEQ(map field args), exp body]
        in sexp "fun" (map f l) end
     | dec (VAR_DEC{name,typ,init,pos}) =
        (case typ
          of NONE => sexp "var" [fix name, exp init]
           | SOME (s,_) =>
              sexp "var" [fix name, fix s, exp init])
     | dec (TYPE_DEC l) =
        let fun tdec{name,ty=t,pos} = S.SEQ [fix name, ty t]
        in sexp "type" (map tdec l) end

   and ty (NAME_TY(s,p)) = sexp "name-type" [fix s]
     | ty (REC_TY l) =
        let fun f {name,typ,pos} =
             S.SEQ[fix name, fix typ]
        in sexp "record-type" (map f l) end
     | ty(ARRAY_TY(s,p)) = sexp "array-type" [fix s]

 in
  val toSexp = exp
 end
end

structure ASTUtils = struct
 fun varName v =
  case v
  of AST.SIMPLE (s,_) => s
   | AST.FIELD (v,s,_) => varName v
   | AST.INDEX (v,e,_) => varName v
end
