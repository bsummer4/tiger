open IR
val vars = [Type.INT, Type.INT, Type.INT];
val mainType = (Type.VOID,[]) : Type.proc
val mainCode = ([],[IR.RETURN NONE]) : procData
val withVars =
 #1 (foldr (fn (ty,(prog,vl)) => case decVar prog ty of (a,b) => (a,b::vl))
     (empty,[]) vars)

val prog = withVars
val (prog',main) = decProc prog mainType
val prog'' = defProc prog' (main,mainCode)

;
CG.generate prog'' main;
