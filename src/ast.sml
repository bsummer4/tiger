(*
	This defines the representation of symbols and symbol tables,
	the AST representation for tiger code, and functions to output
	an AST (ASTSexp.toSexp).
*)

(* Symbols are just strings with constant time comparisons. *)
signature SYMBOL = sig
 eqtype symbol
 val mk: string -> symbol
 val name: symbol -> string
 val num: symbol -> int
 val compare: symbol * symbol -> order
end

structure Symbol:> SYMBOL = struct
 open Util
 structure H = HashTable
 val (nextsym, sizeHint) = (ref 0, 128)
 val forward : (string,int) H.hash_table =
  H.mkTable(HashString.hashString, op =) (sizeHint,FAIL)
 val backward : (int,string) H.hash_table =
  H.mkTable(Word.fromInt, op =) (sizeHint,FAIL)
 type symbol = int
 fun name n = H.lookup backward n
 fun num n = n
 val compare = Int.compare
 fun mk name =
  case H.find forward name
   of SOME i => i
    | NONE => let val i = !nextsym
              in nextsym := i+1
               ; H.insert forward (name,i)
               ; H.insert backward (i,name)
               ; i
              end
end

signature SYM_TABLE = sig
 type 'a table
 val empty: 'a table
 val enter: 'a table * Symbol.symbol * 'a -> 'a table
 val look: 'a table * Symbol.symbol -> 'a option
end

structure SymTable:> SYM_TABLE = struct
 type 'a table = 'a IntBinaryMap.map
 val empty = IntBinaryMap.empty
 fun enter(t,k,a) = IntBinaryMap.insert(t,Symbol.num k,a)
 fun look(t,k) = IntBinaryMap.find(t,Symbol.num k)
end

structure Common = struct
 type pos = int and sym = Symbol.symbol
 datatype oper = ADD | SUB | MUL | DIV | EQ | NEQ | LT | LE | GT | GE | AND | OR
 datatype 'exp var'
  = SIMPLE of sym * pos
  | FIELD of 'exp var' * sym * pos
  | INDEX of 'exp var' * 'exp * pos
end

structure AST = struct
 open Common
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

 and dec
  = TYPE_DEC of {name:sym, ty:ty, pos:pos} list
  | VAR_DEC of {name:sym, typ:(sym*pos) option, init:exp, pos:pos}
  | FUN_DEC of { name:sym, args:field list
               , result:(sym*pos)option, body:exp, pos:pos
               } list

 and ty = NAME_TY of sym*pos | REC_TY of field list | ARRAY_TY of sym*pos
 withtype var = exp var'
 and field = {name:sym, typ:sym, pos:pos}
end

structure IR = struct
 open Common
 datatype exp
  = ARRAY of {typ:sym, size:exp, init:exp}
  | ASSIGN of {var:var, exp:exp}
  | BREAK
  | CALL of {func:sym, args:exp list}
  | FOR of {var:sym, lo:exp, hi:exp, body:exp}
  | IF of {test:exp, then':exp}
  | IFELSE of {test:exp, then':exp, else':exp}
  | INT of int
  | NIL
  | OP of {left:exp, oper:oper, right:exp}
  | REC of {typ:sym, vals:exp list}
  | SEQ of exp list
  | STR of string
  | VAR of var
  | WHILE of {test:exp, body:exp}
 withtype var = exp var'

 structure Ty = struct
  datatype ty = NIL | INT | STRING | UNIT | RECORD of sym | ARRAY of sym
 end

 (*
 	The `block' field in `vars' refers to where the block where a
 	variable is defined or the block defined by a function depending
 	on what type of variable it is.
 *)
 type block = {vars:sym list, funcs:sym list, up:sym option, body:exp list}
 type vars = {typ:sym, block:sym} SymTable.table
 type types = Ty.ty SymTable.table
 type blocks = block SymTable.table
 type program = {main:sym, blocks:blocks, types:types, vars:vars}
end

(*
	This is a quick approximation of of an s-expression library.
	A real version of this library should have pretty-printing
	and parsing.
*)
structure Sexp = struct
 datatype sexp = SEQ of sexp list | BOOL of bool | SYM of string
               | STR of string | INT of int

 local
  fun w s = TextIO.output (TextIO.stdOut,s)
  fun indent 0 = ()
    | indent n = (w " "; indent (n-1))
  fun newline d = (w "\n"; indent d)

  fun printSeq j d [] = ()
    | printSeq j d (x::[]) = print' j d x
    | printSeq j d (x::xs) = (print' j d x; w " "; printSeq false d xs)
  and print' j d (SEQ l) = ( if not j then newline d else ()
                           ; w "("; printSeq true (1+d) l; w ")")
    | print' _ d (BOOL true) = w "#t"
    | print' _ d (BOOL false) = w "#f"
    | print' _ d (SYM s) = w s
    | print' _ d (STR s) = (w "\""; w s; w "\"")
    | print' _ d (INT i) = w (Int.toString i)
 in
  fun printSexp s = (print' true 0 s; w "\n"; TextIO.flushOut TextIO.stdOut)
 end
end

structure ASTSexp = struct
 local
  structure S = Sexp
  open AST
  val name = Symbol.name

  fun sym s = s
  val fix = S.SYM o Symbol.name
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
    | exp (INT i) = sexp "int" [S.INT i]
    | exp (STR(s,_)) = sexp "string" [S.STR s]
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
    | exp (WHILE{test,body,pos}) = sexp "while" [exp body]
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
