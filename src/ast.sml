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
end

structure Symbol:> SYMBOL = struct
 structure H = HashTable
 val (nextsym, sizeHint) = (ref 0, 128)
 val forward : (string,int) H.hash_table =
  H.mkTable(HashString.hashString, op =) (sizeHint,FAIL)
 val backward : (int,string) H.hash_table =
  H.mkTable(Word.fromInt, op =) (sizeHint,FAIL)
 type symbol = int
 fun name n = H.lookup backward n
 fun num n = n
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
  type field = {name: sym, esc: bool ref, typ: sym, pos: pos}
  datatype ty = NAME_TY of sym * pos | REC_TY of field list | ARRAY_TY of sym * pos
  datatype oper = ADD | SUB | MUL | DIV | EQ | NEQ | LT | LE | GT | GE | AND | OR

  datatype 'exp var
   = SIMPLE of sym * pos
   | FIELD of 'exp var * sym * pos
   | INDEX of 'exp var * 'exp * pos

  datatype ('body,'exp) dec
   = FUN_DEC of 'body fundec list
   | TYPE_DEC of typedec list
   | VAR_DEC of 'exp vardec

  withtype typedec = {name: sym, ty: ty, pos: pos}
  and 'exp vardec
   = {name: sym, esc: bool ref, typ: (sym*pos) option, init: 'exp, pos: pos}
  and 'body fundec
   = { name: sym, args: field list, result: (sym*pos) option, body: 'body
     , pos: pos }
 end

 structure AST = struct
  open Common
  datatype exp
   = VAR of var'
   | NIL
   | INT of int
   | STR of string * pos
   | CALL of {func: sym, args: exp list, pos: pos}
   | OP of {left: exp, oper: oper, right: exp, pos: pos}
   | REC of { fields: (sym * exp * pos) list
           , typ: sym, pos: pos}
   | SEQ of (exp * pos) list
   | ASSIGN of {var: var', exp: exp, pos: pos}
   | IF of {test: exp, then': exp, else': exp option, pos: pos}
   | WHILE of {test: exp, body: exp, pos: pos}
   | FOR of { var: sym, esc: bool ref
            , lo: exp, hi: exp, body: exp, pos: pos
            }
   | BREAK of pos
   | LET of {decs: dec' list, body: exp, pos: pos}
   | ARRAY of {typ: sym, size: exp, init: exp, pos: pos}
  withtype var' = exp var
  and dec' = (exp,exp) dec

  type dec = dec' and var = var'
 end

 structure NoLets = struct
  open Common
  datatype exp
   = VAR of var'
   | NIL
   | INT of int
   | STR of string * pos
   | CALL of {func: sym, args: exp list}
   | OP of {left: exp, oper: oper, right: exp}
   | REC of {fields: (sym * exp) list, typ: sym}
   | SEQ of exp list
   | ASSIGN of {var: var', exp: exp}
   | IF of {test: exp, then': exp, else': exp option}
   | WHILE of {test: exp, body: exp}
   | FOR of {var: sym, esc: bool ref, lo: exp, hi: exp, body: exp}
   | BREAK
   | ARRAY of {typ: sym, size: exp, init: exp}

  and block
   = BLOCK of
    { types: typedec list
    , vars: exp vardec list
    , funs: block fundec list
    , body: exp }

  withtype var' = exp var
  type var = var'
 end

 structure AR = struct
  open Common
  datatype exp
   = VAR of var'
   | NIL
   | INT of int
   | STR of string * pos
   | CALL of {func: sym, args: exp list}
   | OP of {left: exp, oper: oper, right: exp}
   | REC of {fields: (sym * exp) list, typ: sym}
   | SEQ of exp list
   | ASSIGN of {var: var', exp: exp}
   | IF of {test: exp, then': exp, else': exp option}
   | WHILE of {test: exp, body: exp}
   | FOR of {var: sym, esc: bool ref, lo: exp, hi: exp, body: exp}
   | BREAK
   | ARRAY of {typ: sym, size: exp, init: exp}

  and ar = AR of {parent: ar option, slots: field list}
  and block = BLOCK of
   {ar: ar, types: typedec list, funs: block fundec list, body: exp}
  withtype var' = exp var

  type var = var'
 end

 structure Globals = struct
  open Common
  datatype exp
   = VAR of var'
   | NIL
   | INT of int
   | STR of string * pos
   | CALL of {func: sym, args: exp list}
   | OP of {left: exp, oper: oper, right: exp}
   | REC of {fields: (sym * exp) list, typ: sym}
   | SEQ of exp list
   | ASSIGN of {var: var', exp: exp}
   | IF of {test: exp, then': exp, else': exp option}
   | WHILE of {test: exp, body: exp}
   | FOR of {var: sym, esc: bool ref, lo: exp, hi: exp, body: exp}
   | BREAK
   | ARRAY of {typ: sym, size: exp, init: exp}

  and ar = AR of {parent: ar option, slots: field list}
  and block = BLOCK of
   { ar: ar, types: typedec list, funs: block fundec list, body: exp }
  withtype var' = exp var
  type var = var'
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

  fun printSeq d [] = ()
    | printSeq d (x::[]) = print' d x
    | printSeq d (x::xs) = (print' d x; w " "; printSeq d xs)
  and print' d (SEQ l) = (w "\n"; indent (1+d); w "("; printSeq (1+d) l; w ")")
    | print' d (BOOL true) = w "#t"
    | print' d (BOOL false) = w "#f"
    | print' d (SYM s) = w s
    | print' d (STR s) = (w "\""; w s; w "\"")
    | print' d (INT i) = w (Int.toString i)
 in
  fun printSexp s = (print' 0 s; w "\n"; TextIO.flushOut TextIO.stdOut)
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
    | exp (FOR{var=v,esc=b,lo,hi,body,pos}) =
       sexp "for" [fix v, S.BOOL(!b), exp lo, exp hi, exp body]
    | exp (BREAK p) = S.SEQ [S.SYM "break"]
    | exp (LET{decs,body,pos}) =
       sexp "let" [S.SEQ(map dec decs), exp body]
    | exp (ARRAY{typ,size,init,pos}) =
       sexp "array" [fix typ, exp size, exp init]

   and dec (FUN_DEC l) =
        let fun field{name,esc,typ,pos} =
             S.SEQ [fix name, S.BOOL(!esc), fix typ]
            fun f{name,args,result,body,pos} =
             case result
              of NONE => S.SEQ [fix name, S.SEQ(map field args), exp body]
               | SOME(s,_) =>
                  S.SEQ [fix name, fix s, S.SEQ(map field args), exp body]
        in sexp "fun" (map f l) end
     | dec (VAR_DEC{name,esc,typ,init,pos}) =
        (case typ
          of NONE => sexp "var" [fix name, S.BOOL(!esc), exp init]
           | (SOME(s,_)) =>
              sexp "var" [fix name, S.BOOL(!esc), fix s, exp init])
     | dec (TYPE_DEC l) =
        let fun tdec{name,ty=t,pos} = S.SEQ [fix name, ty t]
        in sexp "type" (map tdec l) end

   and ty (NAME_TY(s,p)) = sexp "name-type" [fix s]
     | ty (REC_TY l) =
        let fun f {name,esc,typ,pos} =
             S.SEQ[fix name, S.BOOL(!esc), fix typ]
        in sexp "record-type" (map f l) end
     | ty(ARRAY_TY(s,p)) = sexp "array-type" [fix s]

 in
  val toSexp = exp
 end
end
