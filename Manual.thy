theory Manual
  imports LexYacc
begin
section \<open>Manual\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>license "Kevin Kappelmann"\<close>

text \<open>
  The @{command "ml_lex_yacc"} command provides an integrated, Isar-level interface for defining 
  and generating Standard ML parsers using ML-Lex and ML-Yacc directly within Isabelle theories. 
  It processes lexical and grammatical specifications, compiles them into SML structures, 
  and loads them into the current Isabelle theory context.

  Description
  \<^item> \<open>name\<close>: Specifies the name of the parser. By default, it is also used as prefix for the 
    generated SML structures. For example, providing the name "MyLang" will generate underlying 
    ML structures like \<open>MyLangLex\<close>, \<open>MyLangLrVals\<close>, and a unified \<open>MyLangParser\<close>. In expert mode 
    (see below), the SML structures will be named based on the lex and yacc directives that are 
    part of the lex and yacc specifications (e.g., \<open>%name\<close>). 

  \<^item> The lex specification is broken into three parts. In the original lex specification, these 
    parts are separated by \<open>%%\<close> (which should be omitted here). Furthermore, by default no directives
    specifying functors or names should be included, as they break the automated linking): 

    \<^item> \<open>lex_user_declarations\<close> (optional): An embedded ML source block containing user-level
      SML code (e.g., token type aliases, state variables, or helper functions). 

    \<^item> \<open>lex_definitions\<close>: The ml-lex definitions, such as regular expression macros (e.g., 
      \<open>alpha=[A-Za-z];\<close>) and lexer state declarations (e.g., \<open>%s COMMENT;\<close>).

    \<^item> \<open>lex_rules\<close>: The ml-lex scanning rules and their corresponding SML semantic actions.

  \<^item> The yacc specification is broken into three parts. In the original lex specification, these 
    parts are separated by \<open>%%\<close> (which should be omitted here). Furthermore, by default no directives
    specifying functors or names should be included, as they break the automated linking): 

    \<^item> \<open>yacc_user_declarations\<close> (optional): An embedded ML source block containing user-level 
      SML code to be injected at the top of the generated parser. Useful for defining custom 
      datatypes or helper functions used in semantic actions.

    \<^item> \<open>yacc_definitions\<close>: A cartouche containing ML-Yacc definitions, including \<open>%term\<close> and 
      \<open>%nonterm\<close> declarations, associativity, and start symbols.

    \<^item> \<open>yacc_rules\<close>: A cartouche containing the ML-Yacc grammar productions (BNF format) and 
      their corresponding SML semantic actions.

  \<^item> The command accepts two configuration options that can be provided as a comma-separated list 
    enclosed in square brackets \<open>[ ... ]\<close> immediately following the command name:

    \<^item> \<open>verbose\<close>: Instructs the underlying ML-Yacc/ML-Lex generator to output verbose
      information. Generated artifacts  (such as SML code or the automaton descrcripton) are stored
      for inspection in Isabelle's virtual file system. 

    \<^item> \<open>expert\<close>: Enables advanced/expert mode where the specified lex and yacc specifications are 
      passed unmodified to lex yacc (except adding the \<open>%%\<close> separators between the three block 
      of each specification. Furthermore, automated linking is disabled in expert mode. 

    \<^item> \<open>no_linking\<close>: Skips the automatic generation of the boilerplate "linking" structure 
      (the code that normally joins the Lexer, ParserData, and LrVals together). This is useful 
      if you intend to manually wire the generated ML functor blocks together later.
\<close>


text \<open>
  The @{command ml_lex_yacc} command provides a seamless, Isar-level interface for defining 
  and generating Standard ML parsers using ML-Lex and ML-Yacc directly within Isabelle/HOL. 
  It processes lexical and grammatical specifications, compiles them into SML structures, 
  and automatically loads them into the current Isabelle theory context, complete with 
  Prover IDE (PIDE) support for syntax highlighting and tooltips.

  This manual outlines how to define grammars in both **Standard Mode** (the automated, 
  highly integrated approach) and **Expert Mode** (the bare-metal approach).
\<close>


section \<open>Command Syntax Overview\<close>

text \<open>
  The general syntax for the command is as follows:

  @{rail \<open>
    @@{command ml_lex_yacc} ('[' options ']')? name \<newline> 'where'
      lex_spec 'and' yacc_spec
    ;
    options: ('verbose' | 'expert' | 'no_linking') + ','
    ;
    lex_spec: ('lex_user_declarations' text)?
              'lex_definitions'  \<newline> text
              'lex_rules' text
    ;
    yacc_spec: ('yacc_user_declarations' text)?
               'yacc_definitions'  \<newline> text
               'yacc_rules' text
  \<close>}

  \<^item> \<^emph>\<open>name\<close>: The identifier used as the prefix for the generated ML structures.
  \<^item> \<^emph>\<open>options\<close>: 
    \<^item> \<open>verbose\<close>: Instructs the ML-Yacc/ML-Lex generators to output verbose info and saves generated artifacts in the Isabelle virtual file system.
    \<^item> \<open>expert\<close>: Disables automated boilerplate injection and linking.
    \<^item> \<open>no_linking\<close>: Keeps boilerplate generation but skips the automatic generation of the linking structure (the Join functor).
\<close>


section \<open>Standard Mode\<close>

text \<open>
  By default, @{command ml_lex_yacc} operates in Standard Mode. This mode is designed to minimize 
  boilerplate and handle the tricky wiring of the lexer, parser, and Isabelle PIDE infrastructure 
  automatically.

  In Standard Mode, the framework automatically:
  \<^enum> Injects standard aliases and PIDE-reporting functions (like \<^ML>\<open>Isabelle_lex_yacc.tok\<close> and \<^ML>\<open>Isabelle_lex_yacc.tok_val\<close>) via the \<^ML_structure>\<open>Isabelle_lex_yacc\<close> environment.
  \<^enum> Provides the standard eof token definition.
  \<^enum> Generates the ML-Lex \<open>%header\<close> and ML-Yacc \<open>%name\<close> and \<open>%pos\<close> directives.
  \<^enum> Automatically applies the Join functor to fuse the Lexer and Parser components.
  \<^enum> Exposes a unified structure (e.g., MyLang) containing a \<^ML>\<open>Isabelle_lex_yacc.parse_source\<close> function.
\<close>

subsection\<open>Example: A Simple Calculator (Standard Mode)\<close>
text\<open>
  Here is how you define a grammar in Standard Mode without writing any linking ML code:
\<close>

ml_lex_yacc "CalcStandard" where
lex_definitions\<open>
alpha=[A-Za-z];
digit=[0-9];
ws = [\ \t\r];
\<close>
lex_rules\<open>
\n       => (lex());
{ws}+    => (lex());

{digit}+ => (tok_val (yypos, yytext, Markup.numeral, "NUM", "", Tokens.NUM, valOf (Int.fromString yytext)));

"+"      => (tok (yypos, yytext, Markup.keyword2, "PLUS", "", Tokens.PLUS));
";"      => (tok (yypos, yytext, Markup.delimiter, "SEMI", "", Tokens.SEMI));

.        => (lex());
\<close>
and yacc_definitions\<open>
%eop EOF SEMI

%left PLUS

%term NUM of int | PLUS | SEMI | EOF
%nonterm EXP of int | START of int option

%noshift EOF
\<close>
yacc_rules\<open>
  START : EXP (SOME EXP)
        | (NONE)
  EXP : NUM             (NUM)
      | EXP PLUS EXP    (EXP1+EXP2)
\<close>

subsubsection\<open>The Generated ML API\<close>
text \<open>
  When Standard Mode executes, it produces a unified ML structure named after your parser 
  (e.g., \<^ML_structure>\<open>CalcStandard\<close>). The most important automatically generated function is:

  \<^ML_type>\<open>Proof.context -> Input.source -> int option\<close> (where the return type matches the \<open>START\<close> nonterminal).

  You can use it directly in a custom Isar command:
\<close>

ML \<open>
  fun run_calc source thy = 
    let 
      val ctxt = Proof_Context.init_global thy
      val res = CalcStandard.parse_source ctxt source
      val _ = writeln (case res of SOME v => Int.toString v | NONE => "No result")
    in thy end
\<close>
subsubsection\<open>PIDE Integration API\<close>
text \<open>
  Inside your \<open>lex_rules\<close>, you should use the globally provided \<^ML>\<open>Isabelle_lex_yacc.tok\<close> and \<^ML>\<open>Isabelle_lex_yacc.tok_val\<close> 
  functions to emit tokens. These functions automatically register Isabelle markups for syntax highlighting.

  \<^item> tok (yypos, yytext, markup, typ, sort, cons)
    Used for valueless tokens (like keywords and symbols). 
    Example: \<open>tok (yypos, yytext, Markup.keyword2, "PLUS", "", Tokens.PLUS)\<close>
  
  \<^item> tok\_val (yypos, yytext, markup, typ, sort, cons, value)
    Used for tokens that carry semantic values (like integers or identifiers).
    Example: \<open>tok\_val (yypos, yytext, Markup.numeral, "NUM", "", Tokens.NUM, valOf (Int.fromString yytext))\<close>
\<close>


section \<open>Expert Mode\<close>

text \<open>
  When you invoke @{command ml_lex_yacc} with the \<open>[expert]\<close> option, the integration backs off 
  and expects you to write a fully compliant, standalone ML-Lex/ML-Yacc specification.

  What is disabled in Expert Mode?
  \<^enum> **No Hidden Inclusions:** You must declare \<open>Tokens\<close>, \<open>lexresult\<close>, \<open>pos\<close>, and \<open>svalue\<close> manually in \<open>lex_user_declarations\<close>.
  \<^enum> **No Auto-Directives:** You must manually provide the \<open>%header\<close> directive for Lex and the \<open>%name\<close> and \<open>%pos\<close> directives for Yacc.
  \<^enum> **No Auto-Linking:** The framework will compile the \<open>.lex.sml\<close> and \<open>.grm.sml\<close> files into the ML environment, but it will **not** generate the final parser structure or the \<open>parse_source\<close> function. You must write the Join functor application yourself.
  \<^enum> **No Default PIDE hooks:** The \<^ML>\<open>Isabelle_lex_yacc.tok\<close> and \<^ML>\<open>Isabelle_lex_yacc.tok_val\<close> helpers from \<^ML_structure>\<open>Isabelle_lex_yacc\<close> are not automatically imported. If you want syntax highlighting, you must implement the position lookup and report logic yourself.
\<close>

subsection\<open>Example: Calculator (Expert Mode)\<close>
text\<open>
  Below is the skeleton required when using Expert Mode. Notice the explicit declarations.
\<close>

ml_lex_yacc [expert] "CalcExpert" where
lex_user_declarations\<open>
structure Tokens = Tokens
type pos = Position.T
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue, pos) token

fun eof () = Tokens.EOF(Position.none, Position.none)
fun error' (e, p: Position.T, _) = () 

(* You must implement your own `tok` and `tok\_val` if you want PIDE support here *)
\<close>
lex_definitions\<open>
%header (functor CalcExpertLexFun(structure Tokens: CalcExpert_TOKENS));
digit=[0-9];
\<close>
lex_rules\<open>
{digit}+ => (Tokens.NUM(valOf (Int.fromString yytext), Position.none, Position.none));
"+"      => (Tokens.PLUS(Position.none, Position.none));
";"      => (Tokens.SEMI(Position.none, Position.none));
.        => (lex());
\<close>
and yacc_definitions\<open>
%name CalcExpert
%pos Position.T
%eop EOF SEMI

%left PLUS
%term NUM of int | PLUS | SEMI | EOF
%nonterm EXP of int | START of int option
%noshift EOF
\<close>
yacc_rules\<open>
  START : EXP (SOME EXP)
        | (NONE)
  EXP : NUM             (NUM)
      | EXP PLUS EXP    (EXP1+EXP2)
\<close>

subsubsection\<open>Linking Expert Mode Output\<close>
text \<open>
  Because Expert Mode disables auto-linking, you must manually assemble the parser in an ML block. 
  This requires using the ML-Yacc Join  functor:
\<close>

ML \<open>
structure CalcExpertParser =
struct
  structure CalcExpertLrVals =
    CalcExpertLrValsFun(structure Token = LrParser.Token)

  structure CalcExpertLex =
    CalcExpertLexFun(structure Tokens = CalcExpertLrVals.Tokens)

  structure Parser =
    Join(structure LrParser = LrParser
         structure ParserData = CalcExpertLrVals.ParserData
         structure Lex = CalcExpertLex)

  (* In a real implementation, you would write your own `parse_source` here, 
     handling the Lexer initialization and the `Stream.get` loop. *)
end
\<close>

subsubsection\<open>When to use Expert Mode?\<close>
text \<open>
  Expert Mode is recommended only when you have highly customized lexer states, require bespoke 
  error-correction strategies directly within the Lexer, or are porting legacy SML codebases where 
  the automatic Isabelle-specific wrappers conflict with existing user declarations.
\<close>

end
