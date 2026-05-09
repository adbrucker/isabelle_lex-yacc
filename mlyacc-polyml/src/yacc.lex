(* Modified by Vesa Karvonen on 2007-12-18.
 * Create line directives in output.
 *)
(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi

   yacc.lex: Lexer specification
 *)
open Isabelle_lex_yacc
structure Tokens = Tokens
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue,pos) token

type lexarg = Hdr.inputSource
type arg = lexarg

open Tokens
val error = Hdr.error
val text = Hdr.text

val pcount = ref 0
val commentLevel = ref 0
val actionstart = ref Position.none

fun linePos () = Position.none
fun pos yypos = Isabelle_lex_yacc.get_pos yypos

val eof = fn i => (if (!pcount)>0 then
                        error i (!actionstart)
                              " eof encountered in action beginning here !"
                   else (); EOF(linePos (), linePos ()))

val Add = fn s => (text := s::(!text))


local val dict = [("%prec",PREC_TAG),("%term",TERM),
               ("%nonterm",NONTERM), ("%eop",PERCENT_EOP),("%start",START),
               ("%prefer",PREFER),("%subst",SUBST),("%change",CHANGE),
               ("%keyword",KEYWORD),("%name",NAME),
               ("%verbose",VERBOSE), ("%nodefault",NODEFAULT),
               ("%value",VALUE), ("%noshift",NOSHIFT),
               ("%header",PERCENT_HEADER),("%pure",PERCENT_PURE),
               ("%token_sig_info",PERCENT_TOKEN_SIG_INFO),
               ("%arg",PERCENT_ARG),
               ("%pos",PERCENT_POS)]
in
fun lookup (s,left,right) = let
       fun f ((a,d)::b) = if a=s then d(left,right) else f b
         | f nil = UNKNOWN(s,left,right)
       in
          f dict
       end
end

fun inc (ri as ref i) = (ri := i+1)
fun dec (ri as ref i) = (ri := i-1)


%%
%header (
functor LexMLYACC(structure Tokens : Mlyacc_TOKENS
                  structure Hdr : HEADER (* = Header *)
                    where type prec = Header.prec
                      and type inputSource = Header.inputSource) : ARG_LEXER
);
%arg (inputSource);
%s A CODE F COMMENT STRING EMPTYCOMMENT;
ws = [\t\ ]+;
eol=("\n"|"\013\n"|"\013");
idchars = [A-Za-z_'0-9];
id=[A-Za-z]{idchars}*;
tyvar="'"{idchars}*;
qualid ={id}".";
%%
<INITIAL>"(*"   => (
                    (Isabelle_lex_yacc.report_token) (yypos, 2, Markup.comment, "comment");
                    Add yytext; YYBEGIN COMMENT; commentLevel := 1;
                    continue(); YYBEGIN INITIAL; continue());
<A>"(*"         => (
                    (Isabelle_lex_yacc.report_token) (yypos, 2, Markup.comment, "comment");
                    YYBEGIN EMPTYCOMMENT; commentLevel := 1; continue());
<CODE>"(*"      => (
                    (Isabelle_lex_yacc.report_token) (yypos, 2, Markup.comment, "comment");
                    Add yytext; YYBEGIN COMMENT; commentLevel := 1;
                    continue(); YYBEGIN CODE; continue());
<INITIAL>[^(%\013\n]+ => (
                    (Isabelle_lex_yacc.report_token) (yypos, size yytext, ("ML_source", []), "ML_source");
                    Add yytext; continue());
<INITIAL>"%%"    => (
                    (Isabelle_lex_yacc.report_token) (yypos, 2, Markup.keyword2, "delimiter");
                    YYBEGIN A; HEADER (concat (rev (!text)),pos yypos,pos yypos));
<INITIAL,CODE,COMMENT,F,EMPTYCOMMENT>{eol}  => (Add yytext; continue());
<INITIAL>.       => (
                    (Isabelle_lex_yacc.report_token) (yypos, 1, ("ML_source", []), "ML_source");
                    Add yytext; continue());

<A>{eol}        => (continue ());
<A>{ws}+        => (continue());
<A>of           => (Isabelle_lex_yacc.tok (yypos, yytext, Markup.keyword1, "keyword", OF));
<A>for          => (Isabelle_lex_yacc.tok (yypos, yytext, Markup.keyword1, "keyword", FOR));
<A>"{"          => (Isabelle_lex_yacc.tok (yypos, yytext, Markup.keyword2, "delimiter", LBRACE));
<A>"}"          => (Isabelle_lex_yacc.tok (yypos, yytext, Markup.keyword2, "delimiter", RBRACE));
<A>","          => (Isabelle_lex_yacc.tok (yypos, yytext, Markup.keyword2, "delimiter", COMMA));
<A>"*"          => (Isabelle_lex_yacc.tok (yypos, yytext, Markup.keyword2, "delimiter", ASTERISK));
<A>"->"         => (Isabelle_lex_yacc.tok (yypos, yytext, Markup.keyword2, "delimiter", ARROW));
<A>"%left"      => (Isabelle_lex_yacc.tok_val (yypos, yytext, Markup.keyword2, "directive", PREC, Hdr.LEFT));
<A>"%right"     => (Isabelle_lex_yacc.tok_val (yypos, yytext, Markup.keyword2, "directive", PREC, Hdr.RIGHT));
<A>"%nonassoc"  => (Isabelle_lex_yacc.tok_val (yypos, yytext, Markup.keyword2, "directive", PREC, Hdr.NONASSOC));
<A>"%"[a-z_]+   => (
                    (Isabelle_lex_yacc.report_token) (yypos, size yytext, Markup.keyword2, "directive");
                    lookup(yytext,pos yypos,pos yypos));
<A>{tyvar}      => (Isabelle_lex_yacc.tok_val (yypos, yytext, Markup.entity "ML_Yacc_type" yytext, "type", TYVAR, yytext));
<A>{qualid}     => (Isabelle_lex_yacc.tok_val (yypos, yytext, Markup.entity "ML_Yacc_id" yytext, "id", IDDOT, yytext));
<A>[0-9]+       => (Isabelle_lex_yacc.tok_val (yypos, yytext, Markup.numeral, "numeral", INT, yytext));
<A>"%%"         => (Isabelle_lex_yacc.tok (yypos, yytext, Markup.keyword2, "delimiter", DELIMITER));
<A>":"          => (Isabelle_lex_yacc.tok (yypos, yytext, Markup.keyword2, "delimiter", COLON));
<A>"|"          => (Isabelle_lex_yacc.tok (yypos, yytext, Markup.keyword2, "delimiter", BAR));
<A>{id}         => (Isabelle_lex_yacc.tok_val (yypos, yytext, Markup.entity "ML_Yacc_id" yytext, "id", ID, (yytext, pos yypos)));
<A>"("          => (pcount := 1; actionstart := pos yypos;
                    text := nil; YYBEGIN CODE; continue() before YYBEGIN A);
<A>.            => (UNKNOWN(yytext,pos yypos,pos yypos));
<CODE>"("       => (
                    (Isabelle_lex_yacc.report_token) (yypos, 1, ("ML_source", []), "ML_source");
                    inc pcount; Add yytext; continue());
<CODE>")"       => (
                    (Isabelle_lex_yacc.report_token) (yypos, 1, ("ML_source", []), "ML_source");
                    dec pcount;
                    if !pcount = 0 then
                         PROG (concat (rev (!text)),!actionstart,pos yypos)
                    else (Add yytext; continue()));
<CODE>"\""      => (
                    (Isabelle_lex_yacc.report_token) (yypos, 1, Markup.string, "string");
                    Add yytext; YYBEGIN STRING; continue());
<CODE>[^()"\n\013]+ => (
                    (Isabelle_lex_yacc.report_token) (yypos, size yytext, ("ML_source", []), "ML_source");
                    Add yytext; continue());

<COMMENT>[(*)]  => (
                    (Isabelle_lex_yacc.report_token) (yypos, size yytext, Markup.comment, "comment");
                    Add yytext; continue());
<COMMENT>"*)"   => (
                    (Isabelle_lex_yacc.report_token) (yypos, 2, Markup.comment, "comment");
                    Add yytext; dec commentLevel;
                    if !commentLevel=0
                         then BOGUS_VALUE(pos yypos,pos yypos)
                         else continue()
                   );
<COMMENT>"(*"   => (
                    (Isabelle_lex_yacc.report_token) (yypos, 2, Markup.comment, "comment");
                    Add yytext; inc commentLevel; continue());
<COMMENT>[^*()\n\013]+ => (
                    (Isabelle_lex_yacc.report_token) (yypos, size yytext, Markup.comment, "comment");
                    Add yytext; continue());

<EMPTYCOMMENT>[(*)]  => (
                    (Isabelle_lex_yacc.report_token) (yypos, size yytext, Markup.comment, "comment");
                    continue());
<EMPTYCOMMENT>"*)"   => (
                    (Isabelle_lex_yacc.report_token) (yypos, 2, Markup.comment, "comment");
                    dec commentLevel;
                          if !commentLevel=0 then YYBEGIN A else ();
                          continue ());
<EMPTYCOMMENT>"(*"   => (
                    (Isabelle_lex_yacc.report_token) (yypos, 2, Markup.comment, "comment");
                    inc commentLevel; continue());
<EMPTYCOMMENT>[^*()\n\013]+ => (
                    (Isabelle_lex_yacc.report_token) (yypos, size yytext, Markup.comment, "comment");
                    continue());

<STRING>"\""    => (
                    (Isabelle_lex_yacc.report_token) (yypos, 1, Markup.string, "string");
                    Add yytext; YYBEGIN CODE; continue());
<STRING>\\      => (
                    (Isabelle_lex_yacc.report_token) (yypos, 1, Markup.string, "string");
                    Add yytext; continue());
<STRING>{eol}   => (
                    (Isabelle_lex_yacc.report_token) (yypos, size yytext, Markup.string, "string");
                    Add yytext; error inputSource (pos yypos) "unclosed string";
                    YYBEGIN CODE; continue());
<STRING>[^"\\\n\013]+ => (
                    (Isabelle_lex_yacc.report_token) (yypos, size yytext, Markup.string, "string");
                    Add yytext; continue());
<STRING>\\\"    => (
                    (Isabelle_lex_yacc.report_token) (yypos, 2, Markup.string, "string");
                    Add yytext; continue());
<STRING>\\{eol} => (
                    (Isabelle_lex_yacc.report_token) (yypos, size yytext, Markup.string, "string");
                    Add yytext; YYBEGIN F; continue());
<STRING>\\[\ \t] => (
                    (Isabelle_lex_yacc.report_token) (yypos, size yytext, Markup.string, "string");
                    Add yytext; YYBEGIN F; continue());

<F>{ws}         => (
                    (Isabelle_lex_yacc.report_token) (yypos, size yytext, Markup.string, "string");
                    Add yytext; continue());
<F>\\           => (
                    (Isabelle_lex_yacc.report_token) (yypos, 1, Markup.string, "string");
                    Add yytext; YYBEGIN STRING; continue());
<F>.            => (
                    (Isabelle_lex_yacc.report_token) (yypos, 1, Markup.string, "string");
                    Add yytext; error inputSource (pos yypos) "unclosed string";
                    YYBEGIN CODE; continue());
