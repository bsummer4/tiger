(*
	This defines the representation of symbol tables, the AST
	representation for tiger code, and a function to output an AST
	(AST.print).

	This is mostly derived from the code here:

		http://www.cs.princeton.edu/~appel/modern/ml/project.html
*)

signature TABLE = sig
 type key
 type 'a t
 val empty: 'a t
 val enter: 'a t * key * 'a -> 'a t
 val look: 'a t * key -> 'a option
end

signature SYMBOL = sig
 structure Table: TABLE
 eqtype t
 sharing type t = Table.key
 val mk: string -> t
 val name: t -> string
end

functor IntMapTable (type key val getInt: key -> int): TABLE = struct
 type key = key
 type 'a t = 'a IntBinaryMap.map
 val empty = IntBinaryMap.empty
 fun enter(t,k,a) = IntBinaryMap.insert(t,getInt k,a)
 fun look(t,k) = IntBinaryMap.find(t,getInt k)
end

structure Symbol:> SYMBOL = struct
 structure H = HashTable
 type t = string * int
 structure Table = IntMapTable(type key = t fun getInt(s,n) = n)
 exception Symbol
 val (nextsym, sizeHint) = (ref 0, 128)
 val hashtable: (string,int) H.hash_table =
  H.mkTable(HashString.hashString, op =) (sizeHint,Symbol)

 fun name(s,n) = s
 fun mk name =
  case H.find hashtable name
   of SOME i => (name,i)
    | NONE => let val i = !nextsym
              in nextsym := i+1
               ; H.insert hashtable (name,i)
               ; (name,i)
              end
end

structure AST = struct
 type pos = int and sym = Symbol.t
 datatype var = SIMPLE of sym * pos
              | FIELD of var * sym * pos
              | INDEX of var * exp * pos

 and exp = VAR of var
         | NIL
         | INT of int
         | STR of string * pos
         | CALL of {func: sym, args: exp list, pos: pos}
         | OP of {left: exp, oper: oper, right: exp, pos: pos}
         | REC of { fields: (sym * exp * pos) list
                  , typ: sym, pos: pos}
         | SEQ of (exp * pos) list
         | ASSIGN of {var: var, exp: exp, pos: pos}
         | IF of {test: exp, then': exp, else': exp option, pos: pos}
         | WHILE of {test: exp, body: exp, pos: pos}
         | FOR of { var: sym, esc: bool ref
                  , lo: exp, hi: exp, body: exp, pos: pos }
         | BREAK of pos
         | LET of {decs: dec list, body: exp, pos: pos}
         | ARRAY of {typ: sym, size: exp, init: exp, pos: pos}

 and dec = FUN_DEC of fundec list
         | TYPE_DEC of {name: sym, ty: ty, pos: pos} list
         | VAR_DEC of { name: sym
                     , esc: bool ref
                     , typ: (sym * pos) option
                     , init: exp
                     , pos: pos }

 and ty = NAME_TY of sym * pos | REC_TY of field list | ARRAY_TY of sym * pos
 and oper = ADD | SUB | MUL | DIV | EQ | NEQ | LT | LE | GT | GE
 withtype field = {name: sym, esc: bool ref, typ: sym, pos: pos}
 and fundec = { name: sym
              , args: field list
              , result: (sym * pos) option
              , body: exp
              , pos: pos }
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
  fun printSeq [] = ()
    | printSeq (x::[]) = print' x
    | printSeq (x::xs) = (print' x; w " "; printSeq xs)
  and print' (SEQ l) = (w "("; printSeq l; w ")")
    | print' (BOOL true) = w "#t"
    | print' (BOOL false) = w "#f"
    | print' (SYM s) = w s
    | print' (STR s) = (w "\""; w s; w "\"")
    | print' (INT i) = w (Int.toString i)
 in
  fun printSexp s = (print' s; w "\n"; TextIO.flushOut TextIO.stdOut)
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
     of ADD => "+" | SUB => "-" | MUL => "*" | DIV => "/" | EQ => "=" 
      | NEQ => "<>" | LT => "<" | LE => "<=" | GT => ">" | GE => ">="

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

  fun unexp (e: Sexp.sexp) = NIL
 in val toSexp = exp
    val fromSexp = unexp
 end
end
