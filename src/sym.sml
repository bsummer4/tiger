(*
	This defines the representation of symbols and symbol tables.
	Symbols are really just strings with very fast comparisons. A
	symbol table is a persistent data structure that maps symbols
	to some other type

	`mk' returns the symbol associated with a string. If mk is passed
	the same string twice, it will return the same symbol both times.
	`gensym' is the same except it always creates a globally unique
	symbol with each call. Note that `gensym' and `mk' will never
	return the same symbol.

	`name' returns the string used to create a symbol. Note that
	this string is not guaranteed to be unique to that symbol since
	symbols created with `gensym' may share the same name. `unique'
	returns a string that is unique to a given symbol.
*)

signature SYMBOL = sig
 eqtype symbol
 val mk: string -> symbol
 val gensym: symbol -> symbol
 val name: symbol -> string
 val unique: symbol -> string
 val num: symbol -> int
 val compare: symbol * symbol -> order
 val empty: symbol
end

signature SYM_TABLE = sig
 structure Symbol: SYMBOL
 include ORD_MAP
 sharing type Key.ord_key = Symbol.symbol
end

structure Symbol = struct
 open Util
 structure H = HashTable
 val (nextsym, sizeHint) = (ref 0, 128)
 val forward : (string,int) H.hash_table =
  H.mkTable(HashString.hashString, op =) (sizeHint,FAIL)
 val backward : (int,string) H.hash_table =
  H.mkTable(Word.fromInt, op =) (sizeHint,FAIL)
 type symbol = int

 val compare = Int.compare
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

 val empty = mk ""

 fun gensym s =
  let val i = !nextsym
  in nextsym := i+1
   ; H.insert backward (i,name s)
   ; i
  end

 fun unique s = String.concat [name s, "_", Int.toString s]
end

structure SymTable:> SYM_TABLE = struct
 open Util
 open IntBinaryMap
 structure Symbol = Symbol
 fun lookup' (t,k) =
  ( if debug then List.app print ["(lookup ", Symbol.unique k, ")"]
             else ()
  ; lookup(t,k)
  )
 val lookup = lookup'
end

structure Symbol = SymTable.Symbol
