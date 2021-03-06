structure Util = struct
 datatype swearWord = SHIT | FUCK | OH_WELL | WTF of string
 exception SwearWordException of swearWord
 fun fuck() = raise SwearWordException FUCK
 fun shit() = raise SwearWordException SHIT
 fun ohwell() = raise SwearWordException OH_WELL
 fun wtf s = raise SwearWordException (WTF s)
 val FAIL = Fail "This shouldn't ever happen"

 val debug = false

 fun range n =
  let fun r sofar i = if i<0 then sofar else r (i::sofar) (i-1)
  in r [] (n-1) end

 exception NotFound
 fun lookup k l =
  case List.find (fn(a,b) => a=k) l
   of NONE => raise NotFound
    | SOME (k,v) => v

 (* Is 'e' a member of 'l'? *)
 fun mem e l = case List.find (fn x=>x=e) l of NONE=>false | _=>true

 (* TODO slow *)
 fun ins _ (n, []) = [n]
   | ins l (n, ns as h::t) = if l(n,h) then n::ns else h::(ins l (n, t))
 fun insertionSort cmp l =
  List.foldr (ins (fn a => case cmp a of LESS => true | _ => false))
   [] l

 (*
	 This is like valOf except the caller chooses what exception is thrown.
 *)
 fun protect e NONE = raise e
   | protect _ (SOME x) = x

 (* This lets us compare objects by identity instead of by value. *)
 type unique = unit ref

 exception YourMom
 fun last [] = raise YourMom
   | last (x::[]) = x
   | last (x::xs) = last xs

 fun TODO() = raise Fail "Not Implemented"

 fun trace s f a =
  let val () = app print ["(",s,"{"]
      val r =  f a
      val () = print "})"
  in r end

 fun inc (num : int ref) = num := !num + 1
 fun dec (num : int ref) = num := !num - 1

 fun id x = x
end

