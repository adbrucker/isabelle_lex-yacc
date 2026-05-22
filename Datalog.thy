theory Datalog
  imports LexYacc
  keywords "datalog" :: diag
begin

ml_lex_yacc [verbose] "Datalog" where
lex_user_declarations\<open>

(* Language-specific keyword hash table *)
structure KeyWord : sig
    val find : string -> (Position.T * Position.T -> (svalue, Position.T) token) option
end = struct
    val TableSize = 211
    val HashFactor = 5

    fun hash s = foldl (fn (c,v) => (v * HashFactor + (ord c)) mod TableSize) 0 (explode s)

    val HashTable = Array.array(TableSize, nil) : 
        (string * (Position.T * Position.T -> (svalue, Position.T) token)) list Array.array

    fun add (s, v) =
        let val i = hash s
        in Array.update(HashTable, i, (s, v) :: (Array.sub(HashTable, i))) end

    fun find s =
        let val i = hash s
            fun f ((key, v)::r) = if s = key then SOME v else f r
              | f nil = NONE
        in f (Array.sub(HashTable, i)) end

    val _ = List.app add [
         ("not",Tokens.YNOT), ("count",Tokens.YCOUNT), ("avg",Tokens.YAVG),
         ("sum",Tokens.YSUM), ("min",Tokens.YMIN), ("max",Tokens.YMAX),
         ("true",Tokens.YTRUE), ("false",Tokens.YFALSE)
    ]
end
open KeyWord
\<close>
lex_definitions\<open>
%s C L;
alpha=[A-Za-z];
digit=[0-9];
hexdigit=[0-9a-fA-F];
octdigit=[0-7];
bindigit=[01];
idletterordigit=[a-zA-Z0-9_];

optsign=("+"|"-")?;
integer={digit}+;
frac="."{digit}+;
exp=(e|E){optsign}{digit}+;
ws = [\ \t\r\n\f];

\<close>
lex_rules\<open>
<INITIAL>{ws}+  => (lex());
<INITIAL>{alpha}{idletterordigit}* => (
    case find (String.map Char.toLower yytext) of 
        SOME v => 
            let val p = get_pos yypos
                val _ = report_token (yypos, String.size yytext, Markup.keyword1, yytext, "")
            in v(p, p) end
      | _ => tok (yypos, yytext, Markup.free, "YPREDICATE", "", Tokens.YPREDICATE));

<INITIAL>"?"{alpha}{idletterordigit}* => (tok (yypos, yytext, Markup.free, "YVARIABLE", "", Tokens.YVARIABLE));

<INITIAL>{optsign}{integer}({frac}{exp}?|{frac}?{exp}) => (tok (yypos, yytext, Markup.numeral, "YFLOAT", "", Tokens.YFLOAT));
<INITIAL>{optsign}{integer} => (tok (yypos, yytext, Markup.numeral, "YINT", "", Tokens.YINT));
<INITIAL>0[xX]{hexdigit}+   => (tok (yypos, yytext, Markup.numeral, "YINT", "", Tokens.YINT));
<INITIAL>0[bB]{bindigit}+   => (tok (yypos, yytext, Markup.numeral, "YINT", "", Tokens.YINT));
<INITIAL>0{octdigit}+       => (tok (yypos, yytext, Markup.numeral, "YINT", "", Tokens.YINT));

<INITIAL>"'"([^'\\]|\\.)"'" => (tok (yypos, yytext, Markup.string, "YCHAR", "", Tokens.YCHAR));
<INITIAL>"\""([^\"\\]|\\.)*"\"" => (tok (yypos, yytext, Markup.string, "YSTRING", "", Tokens.YSTRING));

<INITIAL>"/*"   => (YYBEGIN C; lex());
<INITIAL>"%"    => (YYBEGIN L; lex());

<INITIAL>":-"   => (tok (yypos, yytext, Markup.operator, "YCOLONDASH", "", Tokens.YCOLONDASH));
<INITIAL>"?-"   => (tok (yypos, yytext, Markup.operator, "YQUESTIONDASH", "", Tokens.YQUESTIONDASH));
<INITIAL>"."    => (tok (yypos, yytext, Markup.delimiter, "YDOT", "", Tokens.YDOT));
<INITIAL>","    => (tok (yypos, yytext, Markup.delimiter, "YCOMMA", "", Tokens.YCOMMA));
<INITIAL>"("    => (tok (yypos, yytext, Markup.delimiter, "YLPAR", "", Tokens.YLPAR));
<INITIAL>")"    => (tok (yypos, yytext, Markup.delimiter, "YRPAR", "", Tokens.YRPAR));
<INITIAL>"<"    => (tok (yypos, yytext, Markup.operator, "YLT", "", Tokens.YLT));
<INITIAL>">"    => (tok (yypos, yytext, Markup.operator, "YGT", "", Tokens.YGT));
<INITIAL>.      => (tok (yypos, yytext, Markup.error, "YILLCH", "", Tokens.YILLCH));

<C>"*/"         => (YYBEGIN INITIAL; lex());
<C>[^*]+        => (lex());
<C>"*"          => (lex());

<L>\n           => (YYBEGIN INITIAL; lex());
<L>[^\n]+       => (lex());
\<close>
and yacc_user_declarations\<open>
\<close>
yacc_definitions\<open>
%eop EOF
%pos Position.T
%pure
%noshift EOF

%term
        YNOT    |   YCOUNT  |   YAVG    |   YSUM    |   YMIN |
        YMAX    |   YTRUE   |   YFALSE  |   YILLCH  |
        YVARIABLE | YPREDICATE | YINT   |   YFLOAT  |   YCHAR | YSTRING |
        YDOT    |   YLPAR   |   YRPAR   |   YCOMMA  |
        YCOLONDASH | YQUESTIONDASH | YLT |  YGT     |
        EOF

%nonterm start_rule of unit option | program | clauses | clause |
         query | atom | atoms | 
         variableOrLiteral | variableOrLiterals | aggregateVariable | 
         aggregateOp | variable | predicate | literal

%keyword
        YNOT        YCOUNT      YAVG        YSUM        YMIN
        YMAX        YTRUE       YFALSE

%prefer YPREDICATE YDOT YCOMMA YLPAR
\<close>
yacc_rules\<open>
start_rule: program (SOME ())

program: clauses query                     ()
       | clauses                           ()
       | query                             ()

clauses: clause                            ()
       | clauses clause                    ()

(* A clause resolves the conflict. It acts as either a fact or a rule depending on what follows the atom. *)
clause: atom YDOT                          ()
      | atom YCOLONDASH atoms YDOT         ()

query: YQUESTIONDASH atom                  ()

atom: predicate YLPAR variableOrLiterals YRPAR ()
    | YNOT atom                            ()

atoms: atom                                ()
     | atoms YCOMMA atom                   ()

variableOrLiteral: variable                ()
                 | literal                 ()
                 | aggregateVariable       ()

variableOrLiterals: variableOrLiteral                      ()
                  | variableOrLiterals YCOMMA variableOrLiteral ()

aggregateVariable: aggregateOp YLT variable YGT            ()

aggregateOp: YCOUNT                        ()
           | YAVG                          ()
           | YSUM                          ()
           | YMIN                          ()
           | YMAX                          ()

variable: YVARIABLE                        ()
predicate: YPREDICATE                      ()

literal: YINT                              ()
       | YFLOAT                            ()
       | YTRUE                             ()
       | YFALSE                            ()
       | YCHAR                             ()
       | YSTRING                           ()
\<close>

text\<open>Defining a simple Isar-toplevel command to test the Parser\<close>
ML\<open>
fun run_datalog source thy = 
    let 
      val ctxt = Proof_Context.init_global thy
      val _ = Datalog.parse_source ctxt source 
    in thy end

val _ = Outer_Syntax.command @{command_keyword "datalog"}
        "Syntax check a Datalog block" 
        (Parse.input Parse.cartouche >> (fn source => Toplevel.theory (run_datalog source)))
\<close>

text\<open>Testing the generated Datalog parser with syntax highlighting\<close>
datalog\<open>
% Ground facts
parent("john", "mary").
parent("john", "david").
age("john", 45).

/* 
 * Rules with explicit typed variable querying
 */
ancestor(?x, ?y) :- parent(?x, ?y).
ancestor(?x, ?z) :- parent(?x, ?y), ancestor(?y, ?z).

% Aggregation example
child_count(?p, count<?c>) :- parent(?p, ?c).

% Query
?- ancestor("john", ?descendant)
\<close>

end