signature SYMBOL = sig
 eqtype symbol
 val symbol: string -> symbol
 val name: symbol -> string
 type 'a table
 val empty: 'a table
 val enter: 'a table * symbol * 'a -> 'a table
 val look: 'a table * symbol -> 'a option
end

structure Symbol :> SYMBOL = struct
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
