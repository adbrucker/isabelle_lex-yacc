theory 
  Calc 
imports
  LexYacc
keywords
  "calc" :: diag
begin



ml_lex_yacc[verbose] "calc"
  with_lex\<open>
%header (functor CalcLexFun(structure Tokens: Calc_TOKENS));
alpha=[A-Za-z];
digit=[0-9];
ws = [\ \t\r];
%%
\n       => (lex());
{ws}+    => (lex());

{digit}+ => (tok_val (yypos, yytext, Markup.numeral, "NUM", Tokens.NUM, valOf (Int.fromString yytext)));

"+"      => (tok (yypos, yytext, Markup.keyword2, "PLUS", Tokens.PLUS));
"*"      => (tok (yypos, yytext, Markup.keyword2, "TIMES", Tokens.TIMES));
";"      => (tok (yypos, yytext, Markup.delimiter, "SEMI", Tokens.SEMI));

{alpha}+ => (if yytext="print"
                 then tok (yypos, yytext, Markup.keyword1, "PRINT", Tokens.PRINT)
                 else tok_val (yypos, yytext, Markup.free, "ID", Tokens.ID, yytext)
            );

"-"      => (tok (yypos, yytext, Markup.keyword2, "SUB", Tokens.SUB));
"^"      => (tok (yypos, yytext, Markup.keyword2, "CARAT", Tokens.CARAT));
"/"      => (tok (yypos, yytext, Markup.keyword2, "DIV", Tokens.DIV));
.        => (lex());
\<close>
and_yacc\<open>
fun lookup "bogus" = 10000
  | lookup s = 0

%%

%eop EOF SEMI
%pos Position.T

%left SUB PLUS
%left TIMES DIV
%right CARAT

%term ID of string | NUM of int | PLUS | TIMES | PRINT |
      SEMI | EOF | CARAT | DIV | SUB
%nonterm EXP of int | START of int option

%name Calc

%subst PRINT for ID
%prefer PLUS TIMES DIV SUB
%keyword PRINT SEMI

%noshift EOF
%value ID ("bogus")
%verbose
%%

  START : PRINT EXP (print (Int.toString EXP);
                     print "\n";
                     SOME EXP)
        | EXP (SOME EXP)
        | (NONE)
  EXP : NUM             (NUM)
      | ID              (lookup ID)
      | EXP PLUS EXP    (EXP1+EXP2)
      | EXP TIMES EXP   (EXP1*EXP2)
      | EXP DIV EXP     (EXP1 div EXP2)
      | EXP SUB EXP     (EXP1-EXP2)
      | EXP CARAT EXP   (let fun e (m,0) = 1
                                | e (m,l) = m*e(m,l-1)
                         in e (EXP1,EXP2)
                         end)
\<close>
 
text\<open>Linking lexer and parser and establishing PIDE position lookups\<close>
ML\<open>
structure Calc: sig
  val parse_source : Proof.context -> Input.source -> int
end =
struct

  structure CalcLrVals =
    CalcLrValsFun(structure Token = LrParser.Token)

  structure CalcLex =
    CalcLexFun(structure Tokens = CalcLrVals.Tokens)

  structure CalcParser =
    Join(
      structure LrParser = LrParser
      structure ParserData = CalcLrVals.ParserData
      structure Lex = CalcLex
    )

  fun parse_source ctxt source =
    let 
      val _ = CalcLex.UserDeclarations.set source ctxt 
    in
      Isabelle_lex_yacc.parse_source
        CalcParser.parse
        CalcParser.makeLexer
        CalcParser.Stream.get
        CalcParser.sameToken
        CalcLrVals.Tokens.EOF
        source      
    end

end
\<close>

text\<open>Defining a simple Isar-toplevel command\<close>
ML\<open>
fun calc source thy = 
    let 
      val ctxt = Proof_Context.init_global thy
      val _ = writeln(Int.toString (Calc.parse_source ctxt source)) 
    in thy end

val _ = Outer_Syntax.command @{command_keyword "calc"}
        "A simple inline calculator" 
        (Parse.input Parse.cartouche >> (fn source => Toplevel.theory (calc source)))
\<close>

calc\<open>
1
  +
    3
   * (201 - 7)
\<close>

end
