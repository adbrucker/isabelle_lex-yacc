(***********************************************************************************
 * Copyright (c) University of Exeter, UK
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 ***********************************************************************************)

theory
  CalcState
imports
  LexYacc
keywords
  "calc_state" "calc_count" :: diag
begin

section\<open>The Calculator with a Per-Parse State Object\<close>

text\<open>
  The calculator of \<^verbatim>\<open>Calc.thy\<close> again, generated with the \<open>[state]\<close> option of
  @{command ml_lex_yacc}. Instead of the process-wide state of \<^ML_structure>\<open>Isabelle_lex_yacc\<close>,
  every call of \<open>parse_source\<close> creates its own state object
  (\<^ML>\<open>Lex_yacc_state.init\<close>), which is handed to the lexer - there it is the variable
  \<open>st\<close>, bound by ML-Lex's \<open>%arg\<close> - and to the parser, where the same variable \<open>st\<close>
  is bound by ML-Yacc's \<open>%arg\<close>. Two parses running at the same time therefore cannot
  disturb each other.

  Differences to the global-state version, in \<open>lex_rules\<close> only: the helpers take the state
  first (\<open>tok st (\<dots>)\<close>), and a rule that skips input says \<open>continue ()\<close> where it said
  \<open>lex ()\<close> (in ML-Lex's \<open>%arg\<close> mode \<open>lex\<close> itself needs the argument).
\<close>

ml_lex_yacc [state] "CalcState" where
lex_definitions\<open>
digit=[0-9];
ws = [\ \t\r];
\<close>
lex_rules\<open>
\n       => (continue ());
{ws}+    => (continue ());

{digit}+ => (tok_val st (yypos, yytext, Markup.numeral, "NUM", "", Tokens.NUM, valOf (Int.fromString yytext)));

"+"      => (tok st (yypos, yytext, Markup.keyword2, "PLUS", "", Tokens.PLUS));
"*"      => (tok st (yypos, yytext, Markup.keyword2, "TIMES", "", Tokens.TIMES));
"-"      => (tok st (yypos, yytext, Markup.keyword2, "SUB", "", Tokens.SUB));
"/"      => (tok st (yypos, yytext, Markup.keyword2, "DIV", "", Tokens.DIV));
"^"      => (tok st (yypos, yytext, Markup.keyword2, "CARAT", "", Tokens.CARAT));
.        => (continue ());
\<close>
and yacc_definitions\<open>
%eop EOF
%left SUB PLUS
%left TIMES DIV
%right CARAT
%term NUM of int | PLUS | TIMES | EOF | CARAT | DIV | SUB
%nonterm EXP of int | START of int option
%noshift EOF
\<close>
yacc_rules\<open>
  START : EXP (SOME EXP)
        | (NONE)
  EXP : NUM             (NUM)
      | EXP PLUS EXP    (EXP1+EXP2)
      | EXP TIMES EXP   (EXP1*EXP2)
      | EXP DIV EXP     (EXP1 div EXP2)
      | EXP SUB EXP     (EXP1-EXP2)
      | EXP CARAT EXP   (let fun e (m,0) = 1
                                | e (m,l) = m*e(m,l-1)
                         in e (EXP1,EXP2)
                         end)
\<close>

ML\<open>
fun calc_state source thy =
  let
    val ctxt = Proof_Context.init_global thy
    val _ = writeln (Int.toString (the (CalcState.parse_source ctxt source)))
  in thy end

val _ = Outer_Syntax.command @{command_keyword "calc_state"}
        "A simple inline calculator, with a per-parse state"
        (Parse.input Parse.cartouche >> (fn source => Toplevel.theory (calc_state source)))
\<close>

calc_state\<open>
1
  +
    3
   * (201 - 7)
\<close>

section\<open>Extending the State: a Token Counter\<close>

text\<open>
  A language usually needs state of its own - the comment accumulator of the C11 front-end, the
  indentation recorder of occam 2. It is added by \<^emph>\<open>redefining\<close> three things in
  \<open>lex_user_declarations\<close>: the type \<open>arg\<close> (by default the bare state), the function
  \<open>init\<close> that creates one for a parse, and \<open>base\<close>, which projects it back to the bare state the
  library functions (\<open>tok\<close>, \<open>get_pos\<close>, \<open>print_error\<close>, \<open>\<dots>\<close>) work on. The parser needs the same
  type for its \<open>%arg\<close>; as the generator cannot know a language's own type, it is stated in
  \<open>yacc_definitions\<close>, which replaces the default \<open>%arg\<close> it would otherwise add.

  Here the extension is a counter of the tokens the lexer has produced; the parser reads it
  when the start symbol is reduced, and the result is the pair of the value and the count.
\<close>

ml_lex_yacc [state] "CalcCount" where
lex_user_declarations\<open>
type arg = {base : Lex_yacc_state.T, tokens : int ref}
fun init ctxt source : arg = {base = Lex_yacc_state.init ctxt source, tokens = ref 0}
fun base (st : arg) = #base st
fun count (st : arg) = (#tokens st) := !(#tokens st) + 1
\<close>
lex_definitions\<open>
digit=[0-9];
ws = [\ \t\r\n];
\<close>
lex_rules\<open>
{ws}+    => (continue ());
{digit}+ => (count st; tok_val (base st) (yypos, yytext, Markup.numeral, "NUM", "", Tokens.NUM, valOf (Int.fromString yytext)));
"+"      => (count st; tok (base st) (yypos, yytext, Markup.keyword2, "PLUS", "", Tokens.PLUS));
.        => (continue ());
\<close>
and yacc_definitions\<open>
%eop EOF
%arg (st) : {base : Lex_yacc_state.T, tokens : int ref}
%left PLUS
%term NUM of int | PLUS | EOF
%nonterm EXP of int | START of (int * int) option
%noshift EOF
\<close>
yacc_rules\<open>
  START : EXP (SOME (EXP, !(#tokens st)))
        | (NONE)
  EXP : NUM             (NUM)
      | EXP PLUS EXP    (EXP1+EXP2)
\<close>

ML\<open>
fun calc_count source thy =
  let
    val ctxt = Proof_Context.init_global thy
    val (v, n) = the (CalcCount.parse_source ctxt source)
    val _ = writeln (Int.toString v ^ " (" ^ Int.toString n ^ " tokens)")
  in thy end

val _ = Outer_Syntax.command @{command_keyword "calc_count"}
        "Adds numbers and counts the tokens lexed"
        (Parse.input Parse.cartouche >> (fn source => Toplevel.theory (calc_count source)))
\<close>

calc_count\<open>1 + 2 + 3 + 4\<close>

section\<open>Parallel Parses\<close>

text\<open>
  What the state object is for: many parses at once, on one process. Every result must be the
  one a sequential run gives. (Done with the global-state version this fails: the parses read
  one another's source and positions.)
\<close>

ML\<open>
local
  fun expr n = String.concatWith " + " (replicate n "1")
  val sizes = List.tabulate (24, fn i => 20 * (i + 1))
  val ctxt = @{context}
in
  fun round () =
    Par_List.map (fn n =>
      let val (v, c) = the (CalcCount.parse_source ctxt (Input.string (expr n)))
      in (n, v, c, the (CalcState.parse_source ctxt (Input.string (expr n)))) end) sizes
  val _ =
    List.app (fn _ =>
      List.app (fn (n, v, c, w) =>
        if v = n andalso w = n andalso c = n + (n - 1) then ()
        else error ("parallel parse gave a wrong result for " ^ Int.toString n))
        (round ())) (List.tabulate (10, I))
end
\<close>

end
