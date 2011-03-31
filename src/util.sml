structure Util = struct
 val FAIL = Fail "This shouldn't ever happen"

 fun range n =
  let fun r sofar i = if i<0 then sofar else r (i::sofar) (i-1)
  in r [] (n-1) end

 (* Is 'e' a member of 'l'? *)
 fun mem e l = case List.find (fn x=>x=e) l of NONE=>false | _=>true

 (*
	 This is like valOf except the caller chooses what exception is thrown.
 *)
 fun protect e NONE = raise e
   | protect _ (SOME x) = x

 (* This lets us compare objects by identity instead of by value. *)
 type unique = unit ref

 fun last [] = raise Match
   | last (x::[]) = x
   | last (x::xs) = last xs

 fun TODO() = raise Fail "Not Implemented"

 fun inc (num : int ref) = num := !num + 1
 fun dec (num : int ref) = num := !num - 1
end
