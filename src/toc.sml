structure ToC = struct
 open Util
 open IR
 structure T=Type
 structure S=Symbol


 structure Preprocess = struct

  val tmp = Symbol.mk "tmp"

  fun unit e = {ty=T.UNIT,e=e}
  fun seq el = unit(SEQ(el))

  fun splitForLast l =
   let fun r _ [] = fuck()
         | r acc (x::[]) = (rev acc,x)
         | r acc (x::xs) = r (x::acc) xs
   in r [] l
   end

  datatype expClass = EXP | STMT | BAD
  fun okStmt e = BAD<>(expClass e)
  and okExp e = (EXP=(expClass e))
  and expClass (texp as {ty,e}) = case e
   of STR _ => EXP
    | VAR _ => EXP
    | INT _ => EXP
    | NIL => EXP
    | BREAK => STMT
    | ARR {size,init=NONE} => if okExp size then EXP else BAD
    | ARR _ => BAD
    | REC NONE => EXP
    | REC (SOME l) => BAD
    | ASSIGN {var,exp} => if okExp exp then STMT else BAD
    | CALL {func,args=ref args} => if List.all okExp args then EXP else BAD
    | IF {test,then'} =>
       if okExp test andalso okStmt then' then STMT else BAD
    | IFELSE {test,then',else'} =>
       if okExp test andalso List.all okStmt [then',else']
       then STMT else BAD
    | OP {left,oper,right} =>
       if List.all okExp [left,right] then EXP else BAD
    | SEQ l =>
       if List.all okStmt l then STMT else BAD
    | WHILE {test,body} =>
       if okExp test andalso okStmt body then STMT else BAD

  fun push vl e = vl:=(e::(!vl))

  (* fix :: (sym*ty) list ref -> (program * texp) -> (program * texp) *)
  fun fix vl p (te as {e=exp,ty=typ}) =
   let val fix = fix vl p
       fun tmpVar ty =
        let val sym = Symbol.gensym tmp
            val () = push vl (sym,ty)
        in SIMPLE sym
        end
   in case exp

    of WHILE {test=test,body=body} =>
        if okExp test then unit(WHILE{test=test,body=(fix body)})
        else let val t = tmpVar T.INT
                 val updateTest = fix(unit(ASSIGN{var=t,exp=test}))
             in seq[ updateTest
                   , unit(WHILE{ test={ty=T.INT,e=VAR t}
                               , body=seq[fix body, updateTest]
                               })]
             end

     | SEQ l => {ty=typ,e=SEQ (map fix l)}

     | ASSIGN {var,exp as {ty,e}} =>
        (case e
         of (SEQ el) =>
             (case splitForLast el of (prefix,last) =>
               fix({ty=ty,e=SEQ(List.concat
                                 [prefix,
                                  [{ ty=ty
                                   , e=ASSIGN{var=var,exp=last}
                                   }]])}))
          | (IFELSE{test,then',else'}) =>
             fix(unit(IFELSE{ test=test
                            , then'=unit(ASSIGN{var=var, exp=then'})
                            , else'=unit(ASSIGN{var=var, exp=else'})
                            }))
          | _ => if okExp exp then te else fix(unit((ASSIGN{var=var, exp=(fix exp)}))))

     | CALL {func, args=(ref args)} =>
        let val tmps = map (fn{ty,e}=>(ty,e,tmpVar ty)) args
            val args = map (fn(ty,_,v)=>{ty=ty,e=VAR v}) tmps
            val setup = map (fn(ty,e,v)=>unit(ASSIGN{var=v,exp={e=e,ty=ty}}))
                         tmps
        in {ty=typ,e=SEQ
            [ seq setup
            , {ty=typ,e=CALL{func=func,args=ref args}}
            ]}
        end

     | IF {test, then'} =>
        fix(unit(IFELSE{test=test, then'=then', else'=(unit (SEQ []))}))

     | IFELSE {test, then', else'} =>
        let val t = tmpVar T.INT
        in {ty=typ, e=SEQ[ fix(unit(ASSIGN{var=t, exp=test}))
                         , {ty=typ, e=IFELSE{ test={ty=T.INT, e=VAR t}
                                            , then'=fix(then')
                                            , else'=fix(else')}}]}
        end

     | OP {left, oper, right} =>
        (case left of {ty, e} =>
          let val t1 = tmpVar ty
              val t2 = tmpVar ty
          in {ty=typ, e=SEQ
              [ fix(unit(ASSIGN{var=t1, exp=left}))
              , fix(unit(ASSIGN{var=t2, exp=right}))
              , { ty=typ, e=OP{ left={ty=ty, e=VAR t1}
                              , oper=oper
                              , right={ty=ty, e=VAR t2}}}]}
          end)

     | ARR {size, init=SOME init} =>
        let val t1 = tmpVar T.INT
            val t2 = tmpVar typ
            val t3 = tmpVar T.INT
        in {ty=typ, e=SEQ
            [ fix(unit(ASSIGN{var=t1, exp=size}))
            , unit(ASSIGN{ var=t2
                         , exp={ty=typ
                             , e=ARR{ size={ty=T.INT, e=VAR t1}
                                    , init=NONE}}})
            , unit(WHILE{ test={ ty=T.INT
                               , e=OP{ left={ty=T.INT,e=VAR t3}
                                     , oper=LT
                                     , right={ty=T.INT,e=VAR t1}}}
                        , body=fix(unit(ASSIGN{ var=INDEX(t2, { ty=T.INT
                                                              , e=VAR t3})
                                              , exp=init}))})
             , {ty=typ, e=VAR t2}]}
        end

     | REC (SOME l) =>
        let val t = tmpVar typ
            fun foo (sym,{ty,e}) =
                 fix(unit(ASSIGN{var=(FIELD(t,sym)),exp={ty=ty,e=e}}))
            val inits = ST.listItems (ST.mapi foo l)
        in { ty=typ
           , e=SEQ(List.concat[ [unit(ASSIGN{var=t, exp={ty=typ, e=REC NONE}})]
                              , inits
                              , [{ty=typ, e=VAR t}]])
           }
        end

     | _ => te
   end

  (* transform :: (program * blockname) -> program *)
  fun fromAlist l = foldl (fn((k,v),t)=>ST.insert(t,k,v)) ST.empty l
  fun transform (program:program, blockname:S.symbol) =
   let val vl = ref ([]:(S.symbol*T.ty)list)
       val {main,blocks,procs,arrays,records,vars=pvars} = program
       val {body,vars,args} = ST.lookup(blocks, blockname)
       val body' = fix vl program body
       val block' = {body=body',vars=List.concat[map #1 (!vl),vars],args=args}
       val newvars =
        fromAlist (map (fn(n,ty)=>(n,{typ=ty,block=blockname,ref'=false}))
                   (!vl))
       val vars' = ST.unionWith (fn _=>fuck()) (newvars,pvars)
       val blocks' = ST.insert(blocks,blockname,block')
   in
    {main=main,blocks=blocks',procs=procs,arrays=arrays,records=records,vars=vars'}
   end

  fun processIR (program:program as {blocks,...}) =
   ST.foldli (fn (k,v,a)=> transform(a,k)) program blocks

 end 
 

 structure IRtoCIR = struct
  open IR
  structure CT = CIR.Type
  val label = Symbol.mk "label"
  val goto  = Symbol.mk "goto"

  fun pop [] = fuck()
    | pop (x::xs) = x

  fun irTypeCIR ty = case ty
   of Type.NIL => CT.VOID_PTR
    | Type.INT => CT.INT
    | Type.STR => CT.STR
    | Type.UNIT => CT.VOID
    | Type.REC r => CT.REC r
    | Type.ARR a => CT.ARR a

  fun irOpCIR oper = case oper
   of ADD => CIR.ADD | SUB => CIR.SUB | MUL => CIR.MUL | DIV => CIR.DIV
    | EQ  => CIR.EQ  | NEQ => CIR.NEQ | LT  => CIR.LT  | LE  => CIR.LE
    | GT  => CIR.GT  | GE  => CIR.GE  | AND => CIR.AND | OR  => CIR.OR

(* flatten :: (IR.texp,IR.texp list) -> IR.texp list *)
  fun flatten ((te as {ty=typ,e=exp}),sofar) = case exp
   of SEQ l => foldr flatten l sofar
    | x => te::sofar

  and convertVar v = case v
   of SIMPLE s => CIR.SIMPLE s
    | FIELD (v,s) => CIR.FIELD (convertVar v, s)
    | INDEX (v,te) => CIR.INDEX (convertVar v, convertExp te)

  and convertStmt lbls (te as {ty=typ,e=exp}) = case exp
   of ARR {size,init=NONE} => [CIR.EXP (convertExp te)]
    | ARR {size,init=SOME init} => fuck()
    | ASSIGN {var,exp=exp'} =>
       [CIR.ASSIGN {var=(convertVar var),exp=(convertExp exp')}]
    | BREAK => [CIR.GOTO (pop lbls)]
    | CALL {func,args} => [CIR.EXP (convertExp te)]
    | IF _ => fuck()
    | IFELSE {test,then',else'} =>
       [CIR.IF { test=(convertExp test)
               , then'=(List.concat (map (convertStmt lbls) (flatten (then',[]))))
               , else'=(List.concat (map (convertStmt lbls) (flatten (else',[]))))}]
    | INT i => [CIR.EXP (convertExp te)]
    | NIL => [CIR.EXP (convertExp te)]
    | OP {left,oper,right} => [CIR.EXP(convertExp te)]
    | REC (SOME l) => fuck()
    | REC (NONE) => [CIR.EXP(convertExp te)]
    | SEQ l => fuck()
    | STR s => [CIR.EXP(convertExp te)]
    | VAR v => [CIR.EXP(convertExp te)]
    | WHILE {test,body} =>
       let val start = label
           val end' = label
       in List.concat
          [ [CIR.LABEL start]
          , [CIR.IF { test= {ty=CT.INT ,e=CIR.CALL { func= (S.mk "not")
                                                   , args= [convertExp test]} }
                    , then'=[CIR.GOTO end']
                    , else'=[]
                    }]
          , List.concat (map (convertStmt (end'::lbls)) (flatten (body,[])))
          , [CIR.GOTO start]
          ]
       end

  and convertExp (te as {ty=typ,e=exp}) = case exp
   of ARR {size,init=NONE} => 
       {ty=(irTypeCIR typ), e=CIR.ARR(convertExp size)}
    | ARR {size,init=SOME init} => fuck()
    | ASSIGN _ => fuck()
    | BREAK => fuck()
    | CALL {func,args} =>
       {ty=irTypeCIR typ, e=CIR.CALL{func=func,args= (map convertExp (!args))}}
    | IF _ => fuck()
    | IFELSE _ => fuck()
    | INT i => {ty=CT.INT, e=CIR.INT i}
    | NIL => {ty=CT.VOID_PTR, e=CIR.NULL}
    | OP {left,oper,right} =>
       { ty=(irTypeCIR typ)
       , e=CIR.OP{ left=(convertExp left)
                 , oper=(irOpCIR oper)
                 , right=(convertExp right)}}
    | REC (SOME l) => fuck()
    | REC (NONE) => {ty=irTypeCIR typ, e=CIR.REC}
    | SEQ l => fuck()
    | STR s => {ty=CT.STR, e=CIR.STR s}
    | VAR v => {ty=irTypeCIR typ, e=CIR.VAR (convertVar v)}
    | WHILE _ => fuck()

  fun convertBlock (blockname, (program:program as {blocks,...})) : CIR.block =
   let val {body,vars,args} = ST.lookup(blocks, blockname)
       val flat_body = flatten (body,[])
       val cbody = List.concat (map (convertStmt []) flat_body)
   in {args=args,vars=vars,body=cbody}:CIR.block
   end

  fun convertProc (procname, (program:program as {procs,...})) =
   let val {res,args} = ST.lookup(procs, procname)
   in {res=irTypeCIR res, args=map irTypeCIR args}
   end

  fun convertRecord (recordname, (program:program as {records,...})) = TODO()
   let val l = ST.lookup(records, recordname)
   in ST.map irTypeCIR l
   end


  fun convertVar' (varname, (program:program as {vars,...})) =
   let val {typ,block,ref'} = ST.lookup(vars, varname)
   in {ty=irTypeCIR typ, isRef=ref'}
   end

  fun convertIR (program:program) : CIR.program =
   let val {main,blocks,procs,arrays,records,vars} = program
       fun hack f (k,v) = f(k,program)
   in { main=(main:Symbol.symbol)
      , blocks=ST.mapi (hack convertBlock) blocks
      , procs=ST.mapi (hack convertProc) procs
      , arrays=ST.map irTypeCIR arrays
      , records=ST.mapi (hack convertRecord) records
      , vars=ST.mapi (hack convertVar') vars
      }
   end
 end
end
