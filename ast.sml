(*
	This defines the representation of symbol tables, the AST
	representation for tiger code, and a function to output an AST
	(AST.print).

	This is mostly derived from the code here:

		http://www.cs.princeton.edu/~appel/modern/ml/project.html
*)

signature TABLE = sig
 type key
 type 'a table
 val empty: 'a table
 val enter: 'a table * key * 'a -> 'a table
 val look: 'a table * key -> 'a option
end

signature SYMBOL = sig
 type 'a table
 eqtype symbol
 val symbol: string -> symbol
 val name: symbol -> string
 val empty: 'a table
 val enter: 'a table * symbol * 'a -> 'a table
 val look: 'a table * symbol -> 'a option
end

functor IntMapTable (type key val getInt: key -> int): TABLE = struct
 type key=key
 type 'a table = 'a IntBinaryMap.map
 val empty = IntBinaryMap.empty
 fun enter(t,k,a) = IntBinaryMap.insert(t,getInt k,a)
 fun look(t,k) = IntBinaryMap.find(t,getInt k)
end

structure Symbol:> SYMBOL = struct
 structure H = HashTable
 type symbol = string * int
 exception Symbol
 val (nextsym, sizeHint) = (ref 0, 128)
 val hashtable: (string,int) H.hash_table =
  H.mkTable(HashString.hashString, op =) (sizeHint,Symbol)

 fun name(s,n) = s
 fun symbol name =
  case H.find hashtable name
   of SOME i => (name,i)
    | NONE => let val i = !nextsym
              in nextsym := i+1;
                 H.insert hashtable (name,i);
                 (name,i)
              end

 structure Table = IntMapTable(type key = symbol fun getInt(s,n) = n)
 type 'a table = 'a Table.table
 val (empty,enter,look) = (Table.empty,Table.enter,Table.look)
end

structure AST = struct
 type pos = int and symbol = Symbol.symbol
 datatype var = SimpleVar of symbol * pos
              | FieldVar of var * symbol * pos
              | SubscriptVar of var * exp * pos

 and exp = VarExp of var
         | NilExp
         | IntExp of int
         | StringExp of string * pos
         | CallExp of {func: symbol, args: exp list, pos: pos}
         | OpExp of {left: exp, oper: oper, right: exp, pos: pos}
         | RecordExp of { fields: (symbol * exp * pos) list
                        , typ: symbol, pos: pos}
         | SeqExp of (exp * pos) list
         | AssignExp of {var: var, exp: exp, pos: pos}
         | IfExp of {test: exp, then': exp, else': exp option, pos: pos}
         | WhileExp of {test: exp, body: exp, pos: pos}
         | ForExp of { var: symbol, escape: bool ref
                     , lo: exp, hi: exp, body: exp, pos: pos }
         | BreakExp of pos
         | LetExp of {decs: dec list, body: exp, pos: pos}
         | ArrayExp of {typ: symbol, size: exp, init: exp, pos: pos}

 and dec = FunctionDec of fundec list
         | VarDec of { name: symbol
                     , escape: bool ref
                     , typ: (symbol * pos) option
                     , init: exp
                     , pos: pos }
         | TypeDec of {name: symbol, ty: ty, pos: pos} list

 and ty = NameTy of symbol * pos
        | RecordTy of field list
        | ArrayTy of symbol * pos

 and oper = PlusOp | MinusOp | TimesOp | DivideOp
          | EqOp | NeqOp | LtOp | LeOp | GtOp | GeOp

 withtype field = { name: symbol, escape: bool ref
                  , typ: symbol, pos: pos }

 and fundec = { name: symbol
              , params: field list
              , result: (symbol * pos) option
              , body: exp
              , pos: pos }

(*
	:TODO: Less code
		This is a lot of code;  It can probably be shortened.
*)
 fun print (out,e0) =
  let
   fun say s = TextIO.output(out,s)
   fun sayln s = (say s; say "\n")
   fun indent 0 = ()
     | indent i = (say " "; indent(i-1))

   fun opname PlusOp = "PlusOp" | opname MinusOp = "MinusOp"
     | opname TimesOp = "TimesOp" | opname DivideOp = "DivideOp"
     | opname EqOp = "EqOp" | opname NeqOp = "NeqOp"
     | opname LtOp = "LtOp" | opname LeOp = "LeOp"
     | opname GtOp = "GtOp" | opname GeOp = "GeOp"

  fun dolist d f [a] = (sayln ""; f(a,d+1))
    | dolist d f (a::r) = (sayln ""; f(a,d+1); say ","; dolist d f r)
    | dolist d f nil = ()

  fun var(SimpleVar(s,p),d) =
       (indent d; say "SimpleVar("; say(Symbol.name s); say ")")
    | var(FieldVar(v,s,p),d) =
       ( indent d; sayln "FieldVar("; var(v,d+1); sayln ","
       ; indent(d+1); say(Symbol.name s); say ")"
       )
    | var(SubscriptVar(v,e,p),d) =
       ( indent d; sayln "SubscriptVar("; var(v,d+1); sayln ","
       ; exp(e,d+1); say ")"
       )

  and exp(VarExp v, d) = (indent d; sayln "VarExp("; var(v,d+1); say ")")
    | exp(NilExp, d) = (indent d; say "NilExp")
    | exp(IntExp i, d) =
       (indent d; say "IntExp("; say(Int.toString i); say ")")
    | exp(StringExp(s,p),d) =
       (indent d; say "StringExp(\""; say s; say "\")")
    | exp(CallExp{func,args,pos},d) =
       (indent d; say "CallExp("; say(Symbol.name func);
        say ",["; dolist d exp args; say "])")
    | exp(OpExp{left,oper,right,pos},d) =
       (indent d; say "OpExp("; say(opname oper); sayln ",";
         exp(left,d+1); sayln ","; exp(right,d+1); say ")")

    | exp(RecordExp{fields,typ,pos},d) =
       let fun f((name,e,pos),d) =
            ( indent d; say "("; say(Symbol.name name)
            ; sayln ","; exp(e,d+1)
            ; say ")")
       in indent d; say "RecordExp("; say(Symbol.name typ);
          sayln ",["; dolist d f fields; say "])"
      end
    | exp(SeqExp l, d) = ( indent d; say "SeqExp["
                           ; dolist d exp (map #1 l); say "]" )
    | exp(AssignExp{var=v,exp=e,pos},d) =
       (indent d; sayln "AssignExp("; var(v,d+1); sayln ",";
        exp(e,d+1); say ")")
    | exp(IfExp{test,then',else',pos},d) =
       ( indent d; sayln "IfExp("; exp(test,d+1); sayln ","
       ; exp(then',d+1)
       ; case else' of NONE => ()
                     | SOME e => (sayln ","; exp(e,d+1))
       ; say ")" )

    | exp(WhileExp{test,body,pos},d) =
       (indent d; sayln "WhileExp("; exp(test,d+1); sayln ",";
        exp(body,d+1); say ")")
    | exp(ForExp{var=v,escape=b,lo,hi,body,pos},d) =
       (indent d; sayln "ForExp(";
        say(Symbol.name v); say ","; say(Bool.toString (!b)); sayln ",";
        exp(lo,d+1); sayln ","; exp(hi,d+1); sayln ",";
        exp(body,d+1); say ")")
    | exp(BreakExp p, d) = (indent d; say "BreakExp")
    | exp(LetExp{decs,body,pos},d) =
       (indent d; say "LetExp([";
        dolist d dec decs; sayln "],"; exp(body,d+1); say")")
    | exp(ArrayExp{typ,size,init,pos},d) =
       (indent d; say "ArrayExp("; say(Symbol.name typ); sayln ",";
        exp(size,d+1); sayln ","; exp(init,d+1); say ")")

  and dec(FunctionDec l, d) =
       let fun field({name,escape,typ,pos},d) =
            ( indent d; say "("; say(Symbol.name name)
            ; say ","; say(Bool.toString(!escape))
            ; say ","; say(Symbol.name typ); say ")"
            )
           fun f({name,params,result,body,pos},d) =
            ( indent d; say "("; say (Symbol.name name); say ",["
            ; dolist d field params; sayln "],"
            ; case result of NONE => say "NONE"
                   | SOME(s,_) => (say "SOME("; say(Symbol.name s); say ")")
            ; sayln ","; exp(body,d+1); say ")"
            )
       in indent d; say "FunctionDec["; dolist d f l; say "]"
       end

    | dec(VarDec{name,escape,typ,init,pos},d) =
       ( indent d; say "VarDec("; say(Symbol.name name); say ","
       ; say(Bool.toString (!escape)); say ","
       ; case typ of NONE => say "NONE"
                   | SOME(s,p) => (say "SOME("; say(Symbol.name s); say ")")
       ; sayln ","; exp(init,d+1); say ")"
       )

    | dec(TypeDec l, d) =
       let fun tdec({name,ty=t,pos},d) = ( indent d; say"("
                                         ; say(Symbol.name name); sayln ","
                                         ; ty(t,d+1); say ")"
                                         )
       in indent d; say "TypeDec["; dolist d tdec l; say "]"
       end

  and ty(NameTy(s,p), d) =
       (indent d; say "NameTy("; say(Symbol.name s); say ")")
    | ty(RecordTy l, d) =
       let fun f({name,escape,typ,pos},d) =
            ( indent d; say "("; say (Symbol.name name)
            ; say ","; say (Bool.toString (!escape)); say ","
            ; say (Symbol.name typ); say ")"
            )
       in indent d; say "RecordTy["; dolist d f l; say "]"
       end
    | ty(ArrayTy(s,p),d) =
       (indent d; say "ArrayTy("; say(Symbol.name s); say ")")

 in exp(e0,0); sayln ""; TextIO.flushOut out
 end
end
