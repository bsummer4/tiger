structure Tokens = Tokens

type pos = int
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue,pos) token

val linenum = ref 1

fun eof () = Tokens.EOF(0,0)
fun error (e,l : int,_) = TextIO.output (TextIO.stdOut,
           String.concat["line ", (Int.toString l), ": ", e, "\n"])

%%

%header (functor TigerLexFun(structure Tokens: Tiger_TOKENS));

num    = [0-9]+;
id     = [A-Za-z][0-9A-Za-z_]*;
ws     = [\ \t]+;

%%

\n         => (linenum := !linenum + 1; lex());
{ws}       => (lex());
{id}       => (Tokens.STR ((yytext,yypos), yypos, yypos + size yytext) );
{num}      => (Tokens.INT ((valOf (Int.fromString yytext)), 
                yypos, yypos + size yytext) );

.          => (error ("ignoring bad character "^yytext,yypos,yypos + size yytext);
                lex());
