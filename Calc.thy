theory 
  Calc 
imports
  LexYacc
keywords
  "calc" :: diag
begin

text\<open>The calculator example from the ml-lex distribution.\<close>
ml_lex_yacc
  with_lex\<open>
structure Tokens = Tokens

type pos = int
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult= (svalue,pos) token

val pos = ref 0
fun eof () = Tokens.EOF(!pos,!pos)
fun error (e,l : int,_) = TextIO.output (TextIO.stdOut, String.concat[
        "line ", (Int.toString l), ": ", e, "\n"
      ])

%%
%header (functor CalcLexFun(structure Tokens: Calc_TOKENS));
alpha=[A-Za-z];
digit=[0-9];
ws = [\ \t];
%%
\n       => (pos := (!pos) + 1; lex());
{ws}+    => (lex());
{digit}+ => (Tokens.NUM (valOf (Int.fromString yytext), !pos, !pos));

"+"      => (Tokens.PLUS(!pos,!pos));
"*"      => (Tokens.TIMES(!pos,!pos));
";"      => (Tokens.SEMI(!pos,!pos));
{alpha}+ => (if yytext="print"
                 then Tokens.PRINT(!pos,!pos)
                 else Tokens.ID(yytext,!pos,!pos)
            );
"-"      => (Tokens.SUB(!pos,!pos));
"^"      => (Tokens.CARAT(!pos,!pos));
"/"      => (Tokens.DIV(!pos,!pos));
"."      => (error ("ignoring bad character "^yytext,!pos,!pos);
             lex());
\<close>
and_yacc\<open>
(* Sample interactive calculator for ML-Yacc *)

fun lookup "bogus" = 10000
  | lookup s = 0

%%

%eop EOF SEMI

(* %pos declares the type of positions for terminals.
   Each symbol has an associated left and right position. *)

%pos int

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

(* the parser returns the value associated with the expression *)

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

SML_export \<open>structure LrParser = struct open LrParser end\<close>
text\<open>
  Loading the Join function into ML, which is a slight duplication of code 
  avoiding exporting a functor (which seems to be fiddly).\<close> 
ML_file\<open>mlyacc-polyml/mlyacc-lib/base.sig\<close> 
ML_file\<open>mlyacc-polyml/mlyacc-lib/join.sml\<close> 

text\<open>Linking lexer and parser\<close>
ML\<open>
structure Calc : sig
	           val parse_string : string -> int
                 end   = 
struct

  structure CalcLrVals =
    CalcLrValsFun(structure Token = LrParser.Token)

  structure CalcLex =
    CalcLexFun(structure Tokens = CalcLrVals.Tokens)

  structure CalcParser =
    Join(structure LrParser = LrParser
	 structure ParserData = CalcLrVals.ParserData
	 structure Lex = CalcLex)

   fun invoke lexstream =
      let fun print_error (s,i:int,_) =
              error ("Error, line " ^ (Int.toString i) ^ ", " ^ s)
       in CalcParser.parse(0,lexstream,print_error,())
      end

 fun parse_fp lexer =  let
    val dummyEOF = CalcLrVals.Tokens.EOF(0,0)
    fun loop lexer =
      let
        val _ = (CalcLex.UserDeclarations.pos := (0);())
        val (res,lexer) = invoke lexer
        val (nextToken,lexer) = CalcParser.Stream.get lexer
      in if CalcParser.sameToken(nextToken,dummyEOF) then ((),res) else loop lexer end
  in #2(loop lexer)
  end

 fun parse_string input = let
       val parsed = Unsynchronized.ref false
       fun input_string _  = if !parsed then "" else (parsed := true ;input)
             val lexer = CalcParser.makeLexer input_string
     in
       the (parse_fp lexer)
     end

end
\<close>

text\<open>A first test on the ML-level\<close>

ML\<open>Calc.parse_string "3 + 4"\<close>


text\<open>Defining a simple Isar-toplevel command\<close>
ML\<open>
fun calc expression thy = 
    let val _ = writeln(Int.toString (Calc.parse_string expression)) in  thy end

val _ = Outer_Syntax.command @{command_keyword "calc"}
        "A simple inline calculator" 
        (Parse.cartouche  >> (fn expression => Toplevel.theory (calc expression)))
\<close>

calc\<open>1+3\<close>


end

