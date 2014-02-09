type pos = int
type lexresult = Tokens.token

val cdepth = ref 0
val sval = ref ""
val spos = ref 0

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
fun err(p1,p2) = ErrorMsg.error p1

fun eof() = let 
				val pos = hd(!linePos) 
			in 
				(if !spos <> 0 
				then ErrorMsg.error pos "unfinished string"
                else if !cdepth <> 0 
                	 then ErrorMsg.error pos "unclosed comment"
                     else ();
                cdepth := 0; spos := 0;
				Tokens.EOF(pos,pos))
			end

%%
%s INITIAL COMMENTS STRING STRINGCONT;
%%
\n                => (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
<INITIAL>"/*"     => (YYBEGIN COMMENTS; cdepth := !cdepth + 1; continue());
<INITIAL>\"       => (YYBEGIN STRING; spos := yypos; sval := ""; continue());
<INITIAL>to       => (Tokens.TO(yypos, yypos+2));
<INITIAL>for      => (Tokens.FOR(yypos, yypos+3));
<INITIAL>while    => (Tokens.WHILE(yypos, yypos+5));
<INITIAL>break    => (Tokens.BREAK(yypos, yypos+5));
<INITIAL>let      => (Tokens.LET(yypos, yypos+3));
<INITIAL>end      => (Tokens.END(yypos, yypos+3));
<INITIAL>in       => (Tokens.IN(yypos, yypos+2));
<INITIAL>function => (Tokens.FUNCTION(yypos, yypos+8));
<INITIAL>var  	  => (Tokens.VAR(yypos,yypos+3));
<INITIAL>type     => (Tokens.TYPE(yypos,yypos+4));
<INITIAL>array    => (Tokens.ARRAY(yypos, yypos+5));
<INITIAL>if       => (Tokens.IF(yypos, yypos+2));
<INITIAL>then     => (Tokens.THEN(yypos, yypos+4));
<INITIAL>do       => (Tokens.DO(yypos, yypos+2));
<INITIAL>else     => (Tokens.ELSE(yypos, yypos+4));
<INITIAL>of       => (Tokens.OF(yypos, yypos+2));
<INITIAL>nil      => (Tokens.NIL(yypos, yypos+3));
<INITIAL>">="     => (Tokens.GE(yypos, yypos+2));
<INITIAL>">"      => (Tokens.GT(yypos, yypos+1));
<INITIAL>"<="     => (Tokens.LE(yypos, yypos+2));
<INITIAL>"<"      => (Tokens.LT(yypos, yypos+1));
<INITIAL>":="     => (Tokens.ASSIGN(yypos, yypos+2));
<INITIAL>"|"      => (Tokens.OR(yypos, yypos+1));
<INITIAL>"&"      => (Tokens.AND(yypos, yypos+1));
<INITIAL>"<>"     => (Tokens.NEQ(yypos, yypos+2));
<INITIAL>"="     => (Tokens.EQ(yypos, yypos+1));
<INITIAL>","     => (Tokens.COMMA(yypos, yypos+1));
<INITIAL>":"     => (Tokens.COLON(yypos, yypos+1));
<INITIAL>";"     => (Tokens.SEMICOLON(yypos, yypos+1));
<INITIAL>"("     => (Tokens.LPAREN(yypos, yypos+1));
<INITIAL>")"     => (Tokens.RPAREN(yypos, yypos+1));
<INITIAL>"["     => (Tokens.LBRACK(yypos, yypos+1));
<INITIAL>"]"     => (Tokens.RBRACK(yypos, yypos+1));
<INITIAL>"{"     => (Tokens.LBRACE(yypos, yypos+1));
<INITIAL>"}"     => (Tokens.RBRACE(yypos, yypos+1));
<INITIAL>"."     => (Tokens.DOT(yypos, yypos+1));
<INITIAL>"+"     => (Tokens.PLUS(yypos, yypos+1));
<INITIAL>"-"     => (Tokens.MINUS(yypos, yypos+1));
<INITIAL>"*"     => (Tokens.TIMES(yypos, yypos+1));
<INITIAL>"/"     => (Tokens.DIVIDE(yypos, yypos+1));
<INITIAL>[A-Za-z][A-Za-z0-9_]* => (Tokens.ID(yytext,yypos, yypos + size(yytext)));
<INITIAL>[0-9]+  => (Tokens.INT(Option.valOf(Int.fromString(yytext)), yypos, yypos + size(yytext)));
<INITIAL>[ \t]+  => (continue());

<COMMENTS>"*/"   => (cdepth := !cdepth - 1; (if !cdepth = 0 then (YYBEGIN INITIAL) else (YYBEGIN COMMENTS)); continue());
<COMMENTS>"/*"   => (YYBEGIN COMMENTS; cdepth := !cdepth + 1; continue());
<COMMENTS>.|\n  => (continue());

<STRING>\\n      => (sval := !sval ^ "\n"; continue());
<STRING>\\t      => (sval := !sval ^ "\t"; continue());
<STRING>\\[01][0-9][0-9]|2[0-4][0-9]|25[0-5] => 
	((case Char.fromCString(yytext) of
	  SOME s => sval := !sval ^ Char.toString(s)
	| None => (ErrorMsg.error yypos ("illegal character " ^ yytext))); continue());
<STRING>\\\"     => (sval := !sval ^ "\""; continue());
<STRING>\\       => (YYBEGIN STRINGCONT; continue());
<STRING>\"       => (YYBEGIN INITIAL; spos := 0; Tokens.STRING(!sval, !spos, yypos-1));
<STRING>.        => (sval := !sval ^ yytext; continue());

<STRINGCONT>\\   => (YYBEGIN STRING; continue());
<STRINGCONT>[\t\r\n ] => (continue());
<STRINGCONT>.    => (ErrorMsg.error yypos ("illegal character in wrapped string " ^ yytext); continue());
.                => (ErrorMsg.error yypos ("illegal character " ^ yytext); continue());
