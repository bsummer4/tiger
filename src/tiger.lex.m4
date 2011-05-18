structure Tokens = Tokens
open Util

type pos = int
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue,pos) token
val (linenum, comment) = (ref 1, ref 1)

fun eof () = Tokens.Eof(0,0)
fun error (e,l:int,_) =
 app (fn x=>TextIO.output(TextIO.stdErr,x))
  ["char ",Int.toString l,": ",e,"\n"]

fun parseInt p s = Tokens.Integer(valOf(Int.fromString s),p,p+size s)
fun fixStr s =
 ( app (fn c => case c of #"\n" => inc linenum | _ => ())
    (explode s)
 ; if size s<2 then fuck() else substring (s,1,size s-2)
 )

define(`KW',`
 "$1" => Tokens.$2 (stp,endp)')
fun checkpunc word stp endp = case word
  of KW(`,',Comma)  | KW(`:',Colon) | KW(`;',Semi)    | KW(`(',Lparen)
   | KW(`)',Rparen) | KW(`[',Lbrak) | KW(`]',Rbrak)   | KW(`{',Lbrace)
   | KW(`}',Rbrace) | KW(`.',Dot)   | KW(`+',Add)     | KW(`-',Sub)
   | KW(`*',Mul)    | KW(`/',Div)   | KW(`=',Eq)      | KW(`<>',Neq)
   | KW(`<',Lt)     | KW(`<=',Le)   | KW(`>',Gt)      | KW(`>=',Ge)
   | KW(`&',And)    | KW(`|',Or)    | KW(`:=',Assign)
   | _ => fuck()

fun checkword word stp endp = case word
  of KW(array,Array) | KW(if,If)       | KW(then,Then)
   | KW(else,Else)   | KW(while,While) | KW(for,For)
   | KW(to,To)       | KW(do,Do)       | KW(let,Let)
   | KW(in,In)       | KW(end,End)     | KW(of,Of)
   | KW(break,Break) | KW(nil,Nil)     | KW(function,Fun)
   | KW(var,Var)     | KW(type,Type)
   | _ => Tokens.Id(word,stp,endp)

%%
%header (functor TigerLexFun(structure Tokens: Tiger_TOKENS));
%s COMMENT;

ws   = [\ \t]+;
num  = [0-9]*;
id   = [A-Za-z][0-9A-Za-z_]*;
punc = [,:;(){}.*/=><&|+-] | "["|"]"|"<>"|"<="|">="|":=";
q    = "\"";
str  = {q}[^\n"]*{q};

%%
\n               => (inc linenum; lex());
<INITIAL>{ws}    => (lex());
<INITIAL>{id}    => (checkword yytext yypos (yypos+size yytext));
<INITIAL>{punc}  => (checkpunc yytext yypos (yypos+size yytext));
<INITIAL>{num}   => (parseInt yypos yytext);
<INITIAL>{str}   => (Tokens.String(fixStr yytext,yypos,yypos+size yytext));
<INITIAL> "/*"   => (YYBEGIN COMMENT; comment:=1; lex());
<COMMENT> "/*"   => (inc comment; lex());
<COMMENT> [^*/]* => (lex());
<COMMENT> "*"    => (lex());
<COMMENT> "*/"   => ( dec comment
                    ; if 0=(!comment) then YYBEGIN INITIAL else ()
                    ; lex()
                    );
