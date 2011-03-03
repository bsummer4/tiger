structure Tokens = Tokens

type pos = int
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue,pos) token

val linenum = ref 1
val comment = ref 1
val empty   = ref false
val strv    = ref ""
val strp    = ref 0

fun eof () = Tokens.Eof(0,0)
fun error (e,l : int,_) = 
    TextIO.output (TextIO.stdOut,
      String.concat["char ", (Int.toString l), ": ", e, "\n"])

fun checkpunc word stp endp = case word
  of ","  => Tokens.Comma (stp, endp)
  |  ":"  => Tokens.Colon (stp,endp)
  |  ";"  => Tokens.Semi (stp,endp)
  |  "("  => Tokens.Lparen (stp,endp)
  |  ")"  => Tokens.Rparen (stp,endp)
  |  "["  => Tokens.Lbrak (stp,endp)
  |  "]"  => Tokens.Rbrak (stp,endp)
  |  "{"  => Tokens.Lbrace (stp,endp)
  |  "}"  => Tokens.Rbrace (stp,endp)
  |  "."  => Tokens.Dot (stp,endp)
  |  "+"  => Tokens.Plus (stp,endp)
  |  "-"  => Tokens.Minus (stp,endp)
  |  "*"  => Tokens.Mult (stp,endp)
  |  "/"  => Tokens.Div (stp,endp)
  |  "="  => Tokens.Eq (stp,endp)
  |  "<>" => Tokens.Neq (stp,endp)
  |  "<"  => Tokens.Lt (stp,endp)
  |  "<=" => Tokens.Leq (stp,endp)
  |  ">"  => Tokens.Gt (stp,endp)
  |  ">=" => Tokens.Geq (stp,endp)
  |  "&"  => Tokens.And (stp,endp)
  |  "|"  => Tokens.Or (stp,endp)
  |  ":=" => Tokens.Assign (stp,endp)
  |  _    => raise Match

fun checkword word stp endp =
  case word
  of "array"    => Tokens.Array (stp,endp)
  |  "if"       => Tokens.If (stp,endp)
  |  "then"     => Tokens.Then (stp,endp)
  |  "else"     => Tokens.Else (stp,endp)
  |  "while"    => Tokens.While (stp,endp)
  |  "for"      => Tokens.For (stp,endp)
  |  "to"       => Tokens.To (stp,endp)
  |  "do"       => Tokens.Do (stp,endp)
  |  "let"      => Tokens.Let (stp,endp)
  |  "in"       => Tokens.In (stp,endp)
  |  "end"      => Tokens.End (stp,endp)
  |  "of"       => Tokens.Of (stp,endp)
  |  "break"    => Tokens.Break (stp,endp)
  |  "nil"      => Tokens.Nil (stp,endp)
  |  "function" => Tokens.Fun (stp,endp)
  |  "var"      => Tokens.Var (stp,endp)
  |  "type"     => Tokens.Type (stp,endp)
  |  _          => Tokens.ID (word,stp,endp)
  
val print = TextIO.print
fun inc (num : int ref) = num := !num + 1
fun dec (num : int ref) = num := !num - 1

%%

%header (functor TigerLexFun(structure Tokens: Tiger_TOKENS));
%s STRING COMMENT;

ws     = [\ \t]+;
num    = [1-9][0-9]*;
id     = [A-Za-z][0-9A-Za-z_]*;
p1     = "," | ":" |";" |"(" |")" |"[";
p2     = "]" | "{" |"}" |"." |"+" |"-";
p3     = "*" | "/" |"=" |"<>"|"<" |"<=";
p4     = ">" | ">="|"&" |"|" |":=";
punc   = {p1}|{p2}|{p3}|{p4};
q      = "\"";
str    = [^\n"]*;

%%

\n               => (inc linenum; lex());

<INITIAL>{ws}    => (lex());
<INITIAL>{id}    => (checkword yytext yypos (yypos + size yytext) );
<INITIAL>{punc}  => (checkpunc yytext yypos (yypos + size yytext) );
<INITIAL>{num}   => (Tokens.Integer ((valOf (Int.fromString yytext)), 
                       yypos, yypos + size yytext) );

<INITIAL>{q}     => (YYBEGIN STRING; empty := true; strp := yypos; lex());
<STRING>{str}    => (strv := yytext; empty := false; lex());
<STRING>{q}      => (if !empty then strv := "" else (); YYBEGIN INITIAL;
                       Tokens.String (!strv,!strp,!strp + size (!strv)) );

<INITIAL> "/*"   => (YYBEGIN COMMENT; comment := 1; lex());
<COMMENT> "/*"   => (inc comment; lex());
<COMMENT> [^*/]* => (lex());
<COMMENT> "*"    => (lex());
<COMMENT> "*/"   => (dec comment; if !comment = 0 then (YYBEGIN INITIAL; lex())
                       else lex());

<INITIAL> "$"    => (Tokens.Eof (yypos,yypos) );

.                => (error ("ignoring bad character "^yytext,
                       yypos,yypos + size yytext); lex());
