structure Types = struct
 type unique = unit ref
 datatype ty = NIL | INT | STRING | UNIT
             | RECORD of (Symbol.symbol * ty) list * unique
             | ARRAY of ty * unique
             | NAME of Symbol.symbol * ty option ref
end
