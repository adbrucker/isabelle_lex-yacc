(***********************************************************************************
 * Copyright (c) University of Paris-Saclay
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

(*<*)
theory Occam2_Manual
  imports "Occam2.Occam2_Example"
begin

(* The example theory leaves its own declarations and a unit counter behind; start from the
   environment holding exactly the standard handlers, so the numbering of the store keys below
   is this theory's own. *)
reset_oenv
(*>*)

section\<open>What is Isabelle/occam\<close>

text\<open>
  Isabelle/occam is a front-end that lets occam 2 source text live inside an Isabelle
  theory as a first-class citizen: parsed by a real grammar that follows the INMOS
  \<^emph>\<open>occam 2 Reference Manual\<close> \<^cite>\<open>"inmos:occam2:1988"\<close>, checked incrementally under
  Isabelle/PIDE (so a syntax error, an undeclared name or a malformed annotation is reported
  like any other Isabelle error, with the usual jEdit markup, hyperlinking and hovering),
  and open to attaching arbitrary Isabelle-level content - proof obligations, HOL terms,
  arbitrary Isar commands - to specific points of the occam source via a comment-based
  antiquotation mechanism. It is not an occam compiler, nor a verification tool in its
  own right: it is the \<^emph>\<open>front-end layer\<close> on which one would build a verification
  tool (a semantic backend, for instance in the style of CSP), a documentation
  generator, or a static analysis.
\<close>

subsection\<open>Context\<close>

text\<open>
  occam 2 is the programming language of the INMOS transputer: a small, statically
  checked language whose programs are built from a handful of \<^emph>\<open>primitive processes\<close>
  (assignment, input and output on a channel, \<open>SKIP\<close>, \<open>STOP\<close>) and \<^emph>\<open>constructions\<close>
  (\<open>SEQ\<close>, \<open>PAR\<close>, \<open>IF\<close>, \<open>CASE\<close>, \<open>WHILE\<close>, \<open>ALT\<close>), communicating over synchronous
  point-to-point channels. Its semantics is close to Hoare's CSP, which makes it an
  attractive target for formal tools, and its syntax has one unusual property that sets it
  apart from every other language of this repository: \<^emph>\<open>there are no brackets\<close>. The body
  of a construction is written on the following lines, indented by two spaces, and that
  indentation is the \<^emph>\<open>only\<close> grouping mechanism the language has (the \<^emph>\<open>offside rule\<close>,
  shared with languages like Haskell or Python).

  Isabelle/occam is the second language front-end built on the design of
  \<^bold>\<open>Isabelle/C, Version 2.0\<close>, which this repository's \<^verbatim>\<open>C11/\<close> folder contains
  \<^cite>\<open>"tuong.ea:isabellec:2019" and "tuong.ea:deeply:2019"\<close>. It is deliberately
  built from the same parts and carries the same concepts over one for one:
  the \<^verbatim>\<open>ml_lex_yacc\<close> command of this repository (an off-the-shelf ML-Lex/ML-Yacc
  integration \<^cite>\<open>"appel.ea:lexical:1994" and "tarditi.ea:ml-yacc:2000"\<close>) generates lexer
  and parser; every node of the abstract syntax tree carries a source position plus the
  comments and antiquotations attached to it; a per-theory environment tracks the
  declared names for declaration/use hyperlinking; programmable handlers, a navigation
  language and an evaluation order give meaning to the antiquotations; and a family of
  Isar commands (\<open>occam2\<close>, \<open>occam2_file\<close>, \<open>occam2_expr\<close>, \<open>\<dots>\<close>) drive all of it. Someone who
  knows the C11 manual will therefore find the same structure in this one, and the same
  names with \<open>c11\<close> replaced by \<open>occam2\<close>, \<open>cenv\<close> by \<open>oenv\<close>, and \<open>CEnv\<close> by \<open>OEnv\<close>.

  What differs is dictated by the language, and takes up most of the remainder:
  the treatment of \<^emph>\<open>layout\<close> (\<open>\<section>2.1\<close>), the (much simpler) name space and the occam
  scoping rules (\<open>\<section>2.2\<close>), and the shape of the abstract syntax, which has
  processes where C has statements and has specifications where C has declarations
  (\<open>\<section>4\<close>). The thread of the INMOS reference manual is followed throughout: its
  appendix on the syntax summary is the specification of the grammar in
  \<^verbatim>\<open>Occam2_Parser.thy\<close>, and every deviation from it is listed in \<open>\<section>5\<close>.
\<close>

section\<open>Main Features of Isabelle/occam\<close>

text\<open>
  Four pieces fit together to give the \<open>occam2\<close>-family commands (\<open>\<section>3\<close>) their
  behaviour: a lexer and parser that handle the offside rule and produce a real AST with
  genuine source positions at every node (\<open>\<section>2.1\<close>); a per-theory environment tracking every
  declared name, used to hyperlink each name \<^emph>\<open>use\<close> back to its declaration (\<open>\<section>2.2\<close>); a
  mechanism for attaching programmable content to a specific AST node via a comment
  (\<open>\<section>2.3\<close>); and a well-defined order and navigation language governing exactly
  \<^emph>\<open>which\<close> node an antiquotation resolves to and \<^emph>\<open>when\<close> it runs (\<open>\<section>2.4\<close>).
\<close>

subsection\<open>Parsing and Layout\<close>

text\<open>
  The grammar (\<^verbatim>\<open>Occam2_Parser.thy\<close>) covers the language of the reference manual:
  all primitive data types, arrays, channels, timers and ports, protocols (simple,
  sequential, tagged), abbreviations and retyping, procedures and functions (with value
  processes), all processes and constructions including replicators, \<open>PRI PAR\<close>,
  \<open>PRI ALT\<close> and \<open>PLACED PAR\<close>, and the full expression language including tables,
  conversions and slices. The annex (\<open>\<section>7\<close>) shows the lexical structure and the grammar as
  railroad diagrams.

  \<^bold>\<open>The offside rule.\<close> An ml-yacc parser is driven by a lexer that returns one token
  per call and knows nothing about indentation, and a context-free grammar cannot count
  columns. Isabelle/occam therefore splits the problem in two. The \<^emph>\<open>lexer\<close> records, for every
  token it produces, the indentation of the line the token starts on (and whether a
  newline preceded it). A small \<^emph>\<open>stream transformer\<close> between lexer and parser
  (\<open>Occam2_Parse.layout_stream\<close>) then keeps the classical stack of indentation levels and
  injects three synthetic tokens:

  \<^item> \<open>NEWLINE\<close>, at the end of every logical line;
  \<^item> \<open>INDENT\<close>, when a line is indented deeper than the previous one; and
  \<^item> \<open>OUTDENT\<close>, once for every level that a line returns past (a dedent to a column that
    is on none of the stack's levels is a syntax error).

  The grammar proper is thus an ordinary context-free ml-yacc grammar over tokens that
  include \<open>NEWLINE\<close>, \<open>INDENT\<close> and \<open>OUTDENT\<close>; a \<open>SEQ\<close> is simply
  \<open>SEQ NEWLINE INDENT process\<^sup>+ OUTDENT\<close>. Three details make this robust:

  \<^item> \<^emph>\<open>Blank lines and comment-only lines are harmless\<close>, because layout is produced lazily:
    only the indentation of the line the \<^emph>\<open>next token\<close> actually sits on is ever consulted.
  \<^item> \<^emph>\<open>Continuation lines.\<close> An expression or a list may be continued on the next line
    after a token that cannot end a statement: a dyadic or monadic operator, a comma, a
    semicolon, \<open>:=\<close>, \<open>!\<close>, \<open>?\<close>, \<open>&\<close>, \<open>::\<close>, or one of the keywords \<open>IS\<close>, \<open>FROM\<close>, \<open>FOR\<close>,
    \<open>AFTER\<close>, \<open>AND\<close>, \<open>OR\<close>, \<open>NOT\<close>, \<open>SIZE\<close>, \<open>ROUND\<close>, \<open>TRUNC\<close> (the lexer flags exactly these
    tokens). Such a continuation line produces no layout tokens whatever its indentation.
  \<^item> \<^emph>\<open>The first token fixes the base level.\<close> A fragment inside a cartouche may be indented as a
    whole; only the \<^emph>\<open>relative\<close> indentation counts.

  \<^bold>\<open>No operator precedence.\<close> occam has none. The manual's grammar for expressions is
  \<open>operand dyadic.operator operand\<close>, every larger expression being bracketed explicitly,
  with just one exception: a run of \<open>AND\<close>s or a run of \<open>OR\<close>s may be written without brackets.
  The yacc grammar mirrors this directly, and needs no \<open>%left\<close> declarations at all. The
  AST represents such a run as one node (\<open>EChain\<close>). A consequence the programmer meets
  immediately is that \<open>a + b * c\<close> is a \<^emph>\<open>syntax error\<close>, not a surprise:
\<close>

occam2_expr\<open>(a + b) * c\<close>

occam2_expr_reject\<open>a + b * c\<close>

text\<open>
  \<^bold>\<open>Entry points.\<close> A program unit is a run of specifications followed by a process,
  but a bare expression or a bare name are also useful things to check, and \<open>f(x)\<close> is at
  the same time a valid procedure instance \<^emph>\<open>and\<close> a valid function call. Rather than let
  ml-yacc settle such overlaps by accident, the stream transformer prepends one of
  three synthetic tokens (\<open>ENTRY_UNIT\<close>, \<open>ENTRY_EXPR\<close>, \<open>ENTRY_ID\<close>) chosen by the calling
  command, so that each entry point has a grammar of its own. The commands of \<open>\<section>3\<close> are
  thin wrappers around exactly these three entry points.

  \<^bold>\<open>Positions.\<close> Every AST node's annotation field (\<open>'a nodeInfo\<close>, \<^verbatim>\<open>occam2_ast.ML\<close>) carries
  a genuine \<^verbatim>\<open>Position.T\<close> - for a name, its exact source range - together with any comments
  and antiquotations attached to the node, so PIDE markup (hovering, hyperlinking, error
  underlining) is available at every level of the tree.
\<close>

subsection\<open>The occam Environment, and Declaration/Use Navigation\<close>

text\<open>
  \<^verbatim>\<open>Occam2_Env.thy\<close> defines \<open>oenv\<close>, the counterpart of C11's \<open>cenv\<close>: a record stored as
  ordinary \<^verbatim>\<open>Generic_Data\<close>, so that it persists across commands within a theory and merges
  correctly under Isabelle's parallel, incremental checking. It holds

  \<^enum> \<open>idents\<close>, every declared name together with what it was declared as (a variable, a
    channel - which includes timers and ports -, an abbreviation, a formal parameter, a
    replicator index, a procedure, a function, a protocol or a protocol tag);
  \<^enum> \<open>occam_antiq\<close>, the registry of antiquotation handlers (\<open>\<section>2.3\<close>); and
  \<^enum> a per-theory unit counter, used to name the sections processed by an \<open>occam2\<close> command.

  occam has \<^emph>\<open>one\<close> name space: variables, channels, procedures, protocols and tags are all
  just "names" in the sense of the reference manual. So, unlike C11, there is no separate
  tag table, and since the language has no \<open>#include\<close> mechanism there is no counterpart of
  \<open>c11_predef\<close> either (see \<open>\<section>5\<close>).

  \<^verbatim>\<open>Occam2_AnaEval.thy\<close>'s \<open>analyse_and_eval\<close> is a single, purely functional, scoped walk over
  a parsed root that fills \<open>oenv\<close> as it goes. Every name \<^emph>\<open>use\<close> is hyperlinked to its
  declaration via \<^ML>\<open>Position.entity_markup\<close>, reported once at the declaration site and once
  at every use; a name that resolves nowhere is underlined (\<^ML>\<open>Markup.bad ()\<close>) instead of
  rejected, since "undeclared here" routinely just means "declared in a unit this parse
  never saw". The \<^emph>\<open>scoping rules\<close> are those of the reference manual, implemented as
  shadow-and-restore on the \<open>idents\<close> table:

  \<^item> A specification is in scope exactly in the process (or value process, or choice, option,
    variant, alternative) it prefixes - the scope ends where that construct ends.
  \<^item> A specification sees only the names \<^emph>\<open>above\<close> it: in \<open>x IS x:\<close>, the right-hand \<open>x\<close> is an
    outer one.
  \<^item> A replicator \<open>SEQ i = 0 FOR n\<close> scopes its index over the body only; \<open>0\<close> and \<open>n\<close> are
    resolved \<^emph>\<open>outside\<close> it.
  \<^item> \<^emph>\<open>occam 2 forbids recursion.\<close> The body of a \<open>PROC\<close> or \<open>FUNCTION\<close> is walked before the
    procedure's own name is registered, so a procedure calling itself is - correctly - a
    call of an undeclared name.
  \<^item> The formal parameters are registered one by one, each type walked \<^emph>\<open>before\<close> its names, so
    a later formal's array size may use an earlier formal (\<open>PROC p (VAL INT n, []BYTE s)\<close>).
  \<^item> A unit consisting only of specifications - a \<^emph>\<open>library\<close> in the loose sense of the manual
    - is the one construct that does \<^emph>\<open>not\<close> restore: its names stay in \<open>oenv\<close>, and later
    fragments of the same theory can use them.

  Being persistent per-theory data - the same idiom a simp set uses, not something private to
  the \<open>occam2\<close> commands - is what lets occam fragments be freely \<^emph>\<open>interleaved\<close> with arbitrary Isar
  content and still resolve a name used in one fragment back to its declaration in an
  earlier one. The flip side is that \<open>oenv\<close> only ever grows across a theory; the commands
  \<open>set_oenv_default\<close> and \<open>reset_oenv\<close> (\<open>\<section>3\<close>) give a theory explicit control. A small example
  of both the library mechanism and the scoping rules (hover over the names in jEdit):
\<close>

occam2\<open>
VAL INT limit IS 100:
INT FUNCTION double (VAL INT n)
  INT r:
  VALOF
    r := n * 2
  RESULT r
:
\<close>

occam2\<open>
INT x:
SEQ
  x := double (limit)
  SEQ i = 0 FOR limit
    x := x + i
\<close>

text\<open>Occam forbids recursion, so the call inside the body of \<open>again\<close> below is marked as
  undeclared (underlined), although the fragment is syntactically fine, and so is the
  call of \<open>nowhere\<close>:\<close>

occam2\<open>
PROC again (VAL INT n)
  IF
    n > 0
      again (n - 1)
    TRUE
      nowhere ()
:
SKIP
\<close>

subsection\<open>Programmable occam-Antiquotations, and Handlers\<close>

text\<open>
  occam has only line comments, introduced by \<open>--\<close>. A comment of the shape
  \<open>@tag[navi](level) \<open>body\<close>\<close> - an \<open>@\<close>-prefixed tag, an optional bracketed navigation string
  (\<open>\<section>2.4\<close>), an optional parenthesised integer \<open>level\<close> (\<open>0\<close> when omitted), and a body written as
  a nested Isabelle cartouche or, equivalently, a double-quoted string - is recognised
  lexically inside a \<open>--\<close> comment, and attached to whichever AST node it resolves against
  (\<open>\<section>2.4\<close>). The cartouche may span several lines, which an ordinary \<open>--\<close> comment cannot.
  Any other comment is kept as plain text (\<open>Raw_txt\<close>). A comment is attached to the AST node
  that begins at the \<^emph>\<open>next real token\<close>, so an annotation is written on the line(s) \<^emph>\<open>above\<close>
  what it annotates, at any indentation:

  \<^verbatim>\<open>--@ highlight\<close>

  (a tag alone is a complete antiquotation with an empty body).

  The \<open>tag\<close> selects a \<^emph>\<open>handler\<close>: an ordinary ML function of type

  \<^verbatim>\<open>type type_antiq_fun = oenv * pos Occam2_Ast.root * int -> (string * pos) -> Context.generic -> Context.generic\<close>

  registered once, ahead of time, via \<open>OEnv.store_antiq (tag, handler)\<close>. When
  \<open>analyse_and_eval\<close> reaches a node carrying an \<open>@tag ...\<close> antiquotation, it resolves the
  navigation string against the closest-surrounding-context stack (\<open>\<section>2.4\<close>) into a single
  concrete \<open>root\<close> value, then instantiates the handler with \<open>(oenv, resolved_root, level)\<close> and
  the body text together with its own source position; a handler is never itself
  responsible for interpreting \<open>u\<close>/\<open>U\<close>/\<open>r\<close>/\<open>d\<close>.

  \<open>Context.generic\<close> rather than \<open>theory\<close>, deliberately: a handler may do anything a genuine
  Isar toplevel command can, including running real ML code at the ML environment level
  (the \<open>ML\<close> antiquotation, below), which no function on theory \<^emph>\<open>data\<close> can express. All
  collected actions are folded into one \<open>Context.generic -> Context.generic\<close> function by
  ordinary composition and lifted to the toplevel exactly once, at the end (\<open>full_eval_and_store\<close>
  in \<^verbatim>\<open>Occam2.thy\<close>) - lifting them one by one would silently run only the first, because
  \<open>Toplevel.theory\<close> appends an \<^emph>\<open>alternative\<close> to a transition rather than composing.

  Most handlers never need this generality: an ordinary \<open>theory -> theory\<close> function is
  \<^emph>\<open>recaptured\<close> by \<open>OEnv.lift_theory_antiq\<close> when it is registered, without changing its body.
  A first handler, which turns a plain comment into a checked diagnostic reported against
  the exact node the comment resolves to:
\<close>

ML\<open>
val todo_antiq =
  let
    fun handler (_ : OEnv.oenv, ast, level) (body, _ : Position.T) thy =
      (warning ("TODO (level " ^ Int.toString level ^ ") at " ^
                Position.here (AnaEval.pos_of_root ast) ^ ": " ^ body);
       thy)
  in OEnv.store_antiq ("todo", OEnv.lift_theory_antiq handler) end
\<close>
setup\<open>todo_antiq\<close>

occam2\<open>
PROC clear (INT x)
  --@ todo \<open>check the range of x first\<close>
  x := 0
:
SKIP
\<close>

text\<open>
  A tag with no registered handler is a hard error: every tag that can appear in a theory's
  source must be registered before that theory's \<open>occam2\<close>-family commands run.
\<close>

subsection\<open>Execution (Order, Navigation, etc.)\<close>

text\<open>
  \<^bold>\<open>Order.\<close> A unit can carry several antiquotations whose handlers have side effects
  that depend on one another (a \<open>definition\<close> must precede the \<open>lemma\<close> that mentions it).
  \<open>level\<close> is the author's explicit ordering knob: \<open>full_eval_and_store\<close> collects every
  \<open>(level, action)\<close> pair the walk produces, sorts by \<open>level\<close> - a stable sort, so equal levels
  keep their textual order - and chains them, each against the context the previous one
  produced. A physical antiquotation is dispatched \<^emph>\<open>exactly once\<close>, no matter how many AST
  nodes share its leftmost source position (the classic case in occam: an assignment, its
  left-hand variable and the variable's name all begin at the same token).

  \<^bold>\<open>Context.\<close> Every antiquotation resolves, by default, to its \<^emph>\<open>closest surrounding
  context\<close>: the walk threads a stack of enclosing nodes. Three kinds of node always push
  themselves on that stack, at every level of nesting: \<^emph>\<open>expressions\<close>, \<^emph>\<open>processes\<close> and
  \<^emph>\<open>specifications\<close> (the root type has the variants \<open>Expr\<close>, \<open>Proc\<close>, \<open>Spec\<close>, in addition to
  \<open>Id\<close> for a bare name and \<open>Specs\<close> for a library unit). Everything else - types, protocols,
  formal parameters, replicators, choices, options, variants, alternatives, guards - never
  pushes, and resolves to whatever is on top, which is what makes every node kind a valid
  place for a comment. A variable used as an expression (an assignment target, a channel
  operand) is pushed as an \<open>Expr\<close>, so that a comment above \<open>x := 1\<close> resolves to the whole
  assignment, and navigation can reach the variable \<open>x\<close> and the literal \<open>1\<close> from it.

  \<^bold>\<open>Navigation.\<close> The bracketed \<open>[navi]\<close> string points an antiquotation \<^emph>\<open>away\<close> from its
  closest context. Its syntax and its rules are exactly those of C11: written
  \<open>(u|U)*(r|d)*\<close>, zero or more ascend steps followed by zero or more descend steps.
  \<open>u\<close> ascends one level (a lone, final \<open>u\<close> is a no-op); \<open>U\<close> ascends past a whole run of
  consecutive ancestors of the same category; \<open>r\<close> advances a 1-based cursor among the current
  node's children in source order and \<open>d\<close> descends into the child at the cursor (cursor 1
  if no \<open>r\<close> preceded it). There is no wrapping: a cursor beyond the children, or \<open>d\<close> on a
  leaf, is a hard error reported at the antiquotation's own tag position. The children
  of a node, in source order, are its sub-expressions, sub-processes and sub-specifications;
  nodes without a \<open>root\<close> counterpart are flattened into their parent's list (the guard
  and body of every branch of an \<open>IF\<close>, the replicator's base and count, ...) or dropped (types
  and protocols), exactly as C11 drops type-names. A few examples (the node a handler
  receives, on the assignment \<open>x := 1\<close> inside a \<open>SEQ\<close>):

  \<^item> no navigation: the assignment \<open>x := 1\<close> itself;
  \<^item> \<open>[uu]\<close>: the enclosing \<open>SEQ\<close>; (the first \<open>u\<close> ascends, the second, being final, stays);
  \<^item> \<open>[d]\<close> or \<open>[rd]\<close>: its first child, the variable \<open>x\<close>; \<open>[rrd]\<close>: its second child, the
    literal \<open>1\<close>.

  A \<open>PSpecP\<close> node, a specification together with the process it prefixes, has exactly two
  children, the specification and the process; a chain of specifications is therefore a
  right-nested chain of such nodes.
\<close>

subsection\<open>Standard Antiquotations\<close>

text\<open>
  \<^verbatim>\<open>Occam2_AnaEval.thy\<close> registers the same eight demonstration antiquotations as C11. All of
  them are written in a \<open>--\<close> comment and see the node their navigation string selects:

  \<^descr> \<open>probe_oenv\<close> stores the current \<open>oenv\<close> into an ML reference (\<open>OENV\<close>) for inspection.
  \<^descr> \<open>probe_ast\<close> prints the resolved node, pretty-printed back to occam, with its level, and
    stores it into \<open>OCCAM_AST\<close>.
  \<^descr> \<open>highlight\<close> marks the resolved node's source range in the editor - the quickest way to
    \<^emph>\<open>see\<close> what a navigation string selects.
  \<^descr> \<open>term \<open>t\<close>\<close> reads \<open>t\<close> as a HOL term in the theory's current context; a malformed or
    ill-typed term is a real Isabelle error positioned inside the occam comment.
  \<^descr> \<open>ML \<open>code\<close>\<close> runs \<open>code\<close> as ML source, so a definition written in an occam comment becomes a
    later-visible ML binding.
  \<^descr> \<open>text \<open>t\<close>\<close> runs \<open>t\<close> through the document machinery of Isabelle's \<open>text\<close> command, so that
    inner antiquotations are checked and hyperlinked (the result is stashed, not typeset; see \<open>\<section>5\<close>).
  \<^descr> \<open>definition \<open>d\<close>\<close> is Isabelle's \<open>definition\<close> command: the new constant is a genuine,
    later-visible theory constant.
  \<^descr> \<open>lemma \<open>l\<close>\<close> states \<open>l\<close> and proves it with one terminal \<open>by\<close> proof - proof-carrying code:
    a formal property of the program's constants, \<^emph>\<open>actually proved\<close>, right where the occam
    text that motivates it lives. A failed proof is an Isabelle error positioned in the comment.
\<close>

section\<open>The occam2 Main Commands\<close>

text\<open>
  \<^descr> \<open>occam2 \<open>...\<close>\<close> parses its argument as a program unit - a process, optionally preceded by
    specifications, or a library unit consisting of specifications only - runs
    \<open>analyse_and_eval\<close>, chains the collected antiquotation actions in level order, and stores
    the AST under a fresh key, reported as \<open>[stored as Theory#N]\<close>.
  \<^descr> \<open>occam2_file \<open>path\<close>\<close> is the same, reading the unit from an external file (resolved relative
    to the theory's master directory via \<^ML>\<open>Resources.parse_file\<close>, so file positions and
    build-dependency tracking come for free).
  \<^descr> \<open>occam2_expr \<open>...\<close>\<close> and \<open>occam2_ident \<open>...\<close>\<close> parse a bare expression, respectively a bare
    name. The analysis still runs, for its hyperlinks, but its antiquotation actions are
    discarded: a standalone fragment is a syntax check, not a program.
  \<^descr> \<open>occam2_reject \<open>...\<close>\<close>, \<open>occam2_expr_reject \<open>...\<close>\<close> and \<open>occam2_ident_reject \<open>...\<close>\<close> document a
    fragment as correctly \<^emph>\<open>not\<close> accepted by the corresponding entry point. They are silent
    (no error markup is left on the expected failure) and are the means of writing negative
    tests.
  \<^descr> \<open>set_oenv_default\<close> and \<open>reset_oenv\<close> control the ever-growing \<open>oenv\<close>. \<open>set_oenv_default\<close>
    nominates what \<open>oenv\<close> holds \<^emph>\<open>right now\<close> as the snapshot a later \<open>reset_oenv\<close> restores;
    with no earlier \<open>set_oenv_default\<close> in scope \<open>reset_oenv\<close> falls back to the empty \<open>oenv\<close>.
    \<^verbatim>\<open>Occam2.thy\<close> itself nominates, as its last step, the environment holding exactly the
    standard antiquotation handlers.
  \<^descr> \<open>occam2_export \<open>path\<close> exports \<open>key\<^sub>1\<close> \<open>\<dots>\<close> \<open>key\<^sub>n\<close>\<close> renders previously stored sections - given by the
    store keys the accepting commands report - back to occam text with
    \<^ML>\<open>Occam2_Ast.pp_root\<close> and writes them to \<open>path.occ\<close>. With \<open>[verbatim]\<close> after the command
    name the original source text is written instead of the (deliberately simple,
    canonical two-space layout) pretty-printer's.

  The accepting commands are \<open>thy_decl\<close> commands, not \<open>diag\<close>, because they change theory data;
  \<open>occam2_file\<close> is \<open>thy_load\<close> so that Isabelle tracks the file dependency; only the \<open>_reject\<close>
  commands, which store nothing, are \<open>diag\<close>.
\<close>

subsection\<open>A Worked Example\<close>

text\<open>
  A producer, a consumer and a multiplexer. First the protocol shared by producer and
  consumer: a tagged protocol with a \<open>data\<close> message carrying an integer and a \<open>stop\<close> message
  without any payload. The first annotation introduces a HOL constant for the number of
  items (an \<open>@definition\<close>, evaluated at level 0), the second proves a fact about it
  (level 1, so after the definition), the third checks a HOL term mentioning it
  (level 2).
\<close>

occam2\<open>
PROTOCOL msg
  CASE
    data; INT
    stop
:

--@ definition \<open>n_items :: nat where "n_items = 10"\<close>
--@ lemma(1) \<open>n_items_sum: "n_items * (n_items - 1) div 2 = 45" by (simp add: n_items_def)\<close>
--@ term(2) \<open>n_items * n_items\<close>
VAL INT n IS 10:

PROC producer (CHAN OF msg out)
  SEQ
    SEQ i = 0 FOR n
      out ! data; i
    out ! stop
:

PROC consumer (CHAN OF msg in, CHAN OF INT result)
  INT sum, x:
  BOOL running:
  SEQ
    sum := 0
    running := TRUE
    --@ highlight
    WHILE running
      in ? CASE
        data; x
          sum := sum + x
        stop
          running := FALSE
    result ! sum
:
\<close>

text\<open>
  The highlighted \<open>WHILE\<close> is the node the comment above it resolves to. Each name below is
  hyperlinked back to the specification above: \<open>producer\<close>, \<open>consumer\<close>, the channels \<open>c\<close> and
  \<open>r\<close>, and the variable \<open>total\<close>. The three branches of the \<open>PAR\<close> run concurrently; the
  last one is an input on \<open>r\<close> that completes when \<open>consumer\<close> outputs its result:
\<close>

occam2\<open>
CHAN OF msg c:
CHAN OF INT r:
INT total:
SEQ
  PAR
    producer (c)
    consumer (c, r)
    r ? total
  SKIP
\<close>

text\<open>
  An \<open>ALT\<close> waits for whichever of several inputs becomes ready first. The multiplexer
  below forwards values arriving on either of two channels; guards and bodies are
  indented one level each, and a replicated \<open>ALT\<close> or \<open>PAR\<close> takes the same form with a
  replicator after the keyword:
\<close>

occam2\<open>
PROC mux (CHAN OF INT a, b, CHAN OF INT out)
  INT v:
  WHILE TRUE
    ALT
      a ? v
        out ! v
      b ? v
        out ! v
:
\<close>

text\<open>
  Navigation is easiest to understand by looking at it. In the next unit, the comment
  \<open>--@ highlight[rrd]\<close> sits above the assignment, but selects the \<^emph>\<open>second child\<close> of the
  assignment, the literal \<open>42\<close>, and the one on the \<open>SEQ\<close> next to it, \<open>[uu]\<close>, selects the whole
  enclosing \<open>SEQ\<close>. Select a command's output in jEdit to see the highlighted ranges.
\<close>

occam2\<open>
INT x:
SEQ
  --@ highlight[rrd]
  x := 42
  --@ highlight[uu]
  x := x + 1
\<close>

text\<open>
  And the export: the multiplexer's section, written back as occam text into \<^verbatim>\<open>mux.occ\<close>
  next to this theory (the key is the one the corresponding \<open>occam2\<close> command printed).
  The canonical layout regenerated by the pretty-printer shows that the AST has retained
  everything but the comments and the original layout.
\<close>

occam2_export "mux" exports "Occam2_Manual#7"

ML\<open>
val exported = File.read (Path.append (Resources.master_directory @{theory}) (Path.explode "mux.occ"))
val _ = writeln exported
\<close>

subsection\<open>Contracts and Concurrency: The Example Theory\<close>

text\<open>
  The session's own worked example, \<^verbatim>\<open>Occam2_Example.thy\<close>, is the occam analogue of the C11
  project's \<^verbatim>\<open>SelectionSort.thy\<close>: two small programs whose annotations are \<^emph>\<open>mockups\<close>, in
  the sense that they check their HOL content and keep it for a later semantic backend, but
  assign no meaning to it. It is condensed here; the theory itself also exports both
  programs back to occam text (\<^verbatim>\<open>euclid.occ\<close>, \<^verbatim>\<open>buffer.occ\<close>). The four mockups
  \<open>requires\<close>, \<open>ensures\<close>, \<open>inv\<close> and \<open>measure\<close> are the contract-style annotations of the C11
  examples (which took them from the why3 suite); they are produced by one ML function of the
  example theory, \<open>mockup_annotation_antiq\<close>, and registered with \<open>setup\<close>:
\<close>

setup\<open>mockup_annotation_antiq "requires"\<close>
setup\<open>mockup_annotation_antiq "ensures"\<close>
setup\<open>mockup_annotation_antiq "inv"\<close>
setup\<open>mockup_annotation_antiq "measure"\<close>

text\<open>
  \<^bold>\<open>A sequential program.\<close> Euclid's algorithm as an occam \<open>FUNCTION\<close>, a value process whose
  \<open>VALOF\<close> contains the loop. The contract sits in front of the function, the invariant and
  the termination measure in front of the \<open>WHILE\<close>. The annotation of level \<open>1\<close> is not a
  mockup but the standard \<open>lemma\<close> antiquotation: it proves, once, the HOL fact that makes the
  invariant preserved by the loop body (\<open>\<section>2.5\<close>), so it runs after the level-\<open>0\<close> mockups.
  An annotation's cartouche may span several lines. \<open>REM\<close> is occam's remainder, equal to
  HOL's \<open>mod\<close> on non-negative operands; \<open>INT\<close> is read as \<^typ>\<open>int\<close>, a small gap that a
  semantic backend would have to close.
\<close>

occam2\<open>
--@ requires \<open>(0::int) \<le> a \<and> 0 \<le> b\<close>
--@ ensures \<open>(x::int) = gcd a b\<close>
--@ lemma(1) \<open>gcd_loop_step: "(y::int) \<noteq> 0 \<Longrightarrow> gcd y (x mod y) = gcd x y"
             by (metis gcd_red_int)\<close>
INT FUNCTION gcd (VAL INT a, b)
  INT x, y:
  VALOF
    SEQ
      x := a
      y := b
      --@ inv \<open>(gcd (x::int) y) = gcd a b\<close>
      --@ measure \<open>nat (y::int)\<close>
      WHILE y <> 0
        INT t:
        SEQ
          t := x REM y
          x := y
          y := t
  RESULT x
:
\<close>

thm gcd_loop_step

text\<open>
  \<^bold>\<open>A concurrent program.\<close> A one-place buffer between a source and a sink. The two channels
  are synchronous and unbuffered: \<open>c ! v\<close> does not complete before the partner's \<open>c ? x\<close>
  does, so it is the buffer process that lets the source run ahead of the sink by one value. The
  sink's contract is what a semantic backend would have to prove, whatever the interleaving of
  the three processes: it ends with the Gauss sum. (The accumulator is \<open>acc\<close>, not
  \<open>total\<close>: a mockup reads an occam name as a free HOL variable, and \<open>total\<close> is a HOL constant
  - the same trap as \<open>min\<close> in the C11 \<^verbatim>\<open>SelectionSort.thy\<close>. The processes are called
  \<open>source\<close>, \<open>cell\<close> and \<open>sink\<close> here only because \<open>producer\<close> and \<open>consumer\<close> are taken by the
  previous section's example; the theory itself uses those two names.)
\<close>

occam2\<open>
PROC source (VAL INT n, CHAN OF INT out)
  SEQ i = 1 FOR n
    out ! i
:

PROC cell (CHAN OF INT in, out)
  INT x:
  WHILE TRUE
    SEQ
      in ? x
      out ! x
:

--@ requires \<open>(0::nat) \<le> n\<close>
--@ ensures \<open>(acc::nat) = n * (n + 1) div 2\<close>
PROC sink (VAL INT n, CHAN OF INT in, INT acc)
  INT x:
  SEQ
    acc := 0
    SEQ i = 1 FOR n
      SEQ
        in ? x
        acc := acc + x
:
\<close>

text\<open>
  The system itself. The comment above the \<open>PAR\<close> uses navigation: attached to the \<open>PAR\<close> as a
  whole, \<open>[rrrd]\<close> makes it point at the third of its three branches, the sink (the children
  are the three processes, and the first \<open>r\<close> only starts the cursor).
\<close>

occam2\<open>
CHAN OF INT a, b:
INT sum:
SEQ
  --@ highlight[rrrd]
  PAR
    source (10, a)
    cell (a, b)
    sink (10, b, sum)
  SKIP
\<close>

section\<open>The Abstract Syntax\<close>

text\<open>
  There is no pre-existing reference AST for occam 2 to port, unlike C11, whose AST is a
  pruned port of the Haskell \<^verbatim>\<open>language-c\<close> tree. The AST in \<^verbatim>\<open>occam2_ast.ML\<close> is therefore an
  educated design of this project: one datatype per syntactic category of the reference
  manual's grammar, one constructor per alternative, close enough to the concrete syntax
  that \<^ML>\<open>Occam2_Ast.pp_root\<close> can print any parsed program back as legal occam. Layout is
  \<^emph>\<open>not\<close> part of it: the parser turns indentation into explicit tokens, and the printer
  regenerates a canonical two-space layout. All datatypes are parametrised by the position
  type \<open>'a\<close> (instantiated with \<^verbatim>\<open>Position.T\<close>), and every constructor but the pure
  wrappers carries a \<open>'a nodeInfo\<close> as its last field.

  \<^bold>\<open>Annotations\<close>, shared with C11 and so with everything built on it: \<open>nodeInfo\<close> is a bare
  position or a position with the comments attached; a \<open>comment\<close> is raw text or an
  antiquotation (tag, navigation steps, level, cartouche with its position);
  \<open>ident\<close> is a name with its \<open>nodeInfo\<close>.

  \<^bold>\<open>Syntactic categories\<close> (the constructors are those of \<^verbatim>\<open>occam2_ast.ML\<close>):

  \<^item> \<open>oType\<close>: \<open>TPrim\<close> (\<open>BOOL\<close>, \<open>BYTE\<close>, \<open>INT\<close>, \<open>INT16\<close>, \<open>INT32\<close>, \<open>INT64\<close>, \<open>REAL32\<close>, \<open>REAL64\<close>),
    \<open>TChan\<close>, \<open>TTimer\<close>, \<open>TPort\<close>, \<open>TArray\<close>, \<open>TOpenArray\<close>; with \<open>oProtocol\<close> (\<open>PrName\<close>, \<open>PrSeq\<close>,
    \<open>PrAny\<close>) and \<open>oSimpleProt\<close> (a type, or a counted array \<open>INT::[]BYTE\<close>).
  \<^item> \<open>oExpr\<close>: \<open>EElem\<close> (an \<open>oElement\<close>: \<open>ENamed\<close>, \<open>ESub\<close>, \<open>ESlice\<close>), \<open>ELit\<close> (\<open>oLit\<close>), \<open>ETable\<close>
    (\<open>oTable\<close>), \<open>EParen\<close>, \<open>EMon\<close>, \<open>EBin\<close>, \<open>EChain\<close> (an \<open>AND\<close> or \<open>OR\<close> run), \<open>EConv\<close>
    (\<open>INT x\<close>, \<open>REAL32 ROUND x\<close>, \<open>INT TRUNC x\<close>), \<open>EMost\<close> (\<open>MOSTPOS\<close>/\<open>MOSTNEG\<close>), \<open>ECall\<close> (a
    function instance), \<open>EValof\<close> (a value process in brackets).
  \<^item> \<open>oSpec\<close>: \<open>SDecl\<close>, \<open>SAbbrev\<close>/\<open>SValAbbrev\<close>, \<open>SRetypes\<close>/\<open>SValRetypes\<close>, \<open>SProtocol\<close>,
    \<open>SProtocolCase\<close> (with \<open>oTagged\<close>), \<open>SProc\<close> and \<open>SFunction\<close>/\<open>SFunctionIs\<close> (with \<open>oFormal\<close>
    and \<open>oValueProcess\<close>).
  \<^item> \<open>oProcess\<close>: \<open>PSkip\<close>, \<open>PStop\<close>, \<open>PAssign\<close>, \<open>PInput\<close> (\<open>oInput\<close>, \<open>oInputItem\<close>), \<open>POutput\<close>
    (\<open>oOutItem\<close>), \<open>PCaseInput\<close> (\<open>oVariant\<close>), \<open>PSeq\<close>, \<open>PIf\<close> (\<open>oChoice\<close>), \<open>PCase\<close> (\<open>oOption\<close>),
    \<open>PWhile\<close>, \<open>PPar\<close> (with \<open>PRI\<close> flag), \<open>PAlt\<close> (\<open>oAlt\<close>, \<open>oGuard\<close>, with \<open>PRI\<close> flag), \<open>PPlacedPar\<close>
    (\<open>oPlaced\<close>), \<open>PInstance\<close>, \<open>PSpecP\<close> (a specification and the process it scopes over), \<open>PPlace\<close>.
    The three constructions that can be replicated (\<open>SEQ\<close>, \<open>PAR\<close>, \<open>ALT\<close>, \<open>IF\<close>, \<open>PLACED PAR\<close>)
    carry an optional \<open>oReplicator\<close>.
  \<^item> \<open>root\<close>: the result of a parse by entry point - \<open>Id\<close>, \<open>Expr\<close>, \<open>Proc\<close> or \<open>Specs\<close> - plus
    \<open>Spec\<close>, never produced by a parse but used by the analysis as the closest context of
    an annotation on a single specification.

  Where the reference manual's grammar is ambiguous without semantic information, the AST
  follows the grammar's syntactic reading and leaves resolution to the analysis. The
  examples: \<open>c ! t\<close> is output of an expression whether \<open>t\<close> is a variable or a protocol tag
  (both are a bare \<open>ENamed\<close>; only the environment knows), and an \<open>actual\<close> parameter, which
  the manual defines as an element or an expression, is always an \<open>oExpr\<close>.
\<close>

section\<open>Limitations\<close>

text\<open>
  Isabelle/occam is a deliberately modest slice of the language, and the navigation language
  is the narrowed one of Isabelle/C 2.0. Concretely:

  \<^item> \<^bold>\<open>Lenient indentation.\<close> Indentation is checked for consistency, not for exact width:
    a body indented by more than two columns is accepted (the manual prescribes two), a dedent
    that lands on none of the open levels is an error, and a tab counts as one column.
  \<^item> \<^bold>\<open>Four benign grammar conflicts.\<close> ml-yacc reports one reduce/reduce and three
    shift/reduce conflicts, each resolved in the intended way (and visible in the exported
    \<^verbatim>\<open>Occam2.grm.desc\<close> when \<open>ml_lex_yacc\<close> is run with \<open>[verbose]\<close>). (1) In \<open>INT x, y:\<close> the
    comma may continue the name list of a declaration or follow a type conversion \<open>INT x\<close> in an
    expression list; the declaration wins (the earlier rule). (2) \<open>[e]\<close> may begin an array
    type or be a one-element table; the array type wins (shift). (3) \<open>INT\<close> may be a complete simple
    protocol or the head of a counted array protocol \<open>INT::[]BYTE\<close>; the longer reading wins
    (shift). (4) A \<open>;\<close> after the protocol of a \<open>CHAN OF\<close> type inside a protocol continues that
    protocol rather than ending it (shift).
  \<^item> \<^bold>\<open>No compiler directives.\<close> \<open>#USE\<close>, \<open>#INCLUDE\<close>, \<open>#OPTION\<close>, \<open>#IMPORT\<close> and the like are
    outside the language proper in the reference manual and are not recognised. Consequently
    there is no counterpart of \<open>c11_predef\<close>; the way to make names of one unit visible to
    another is a library unit of specifications (\<open>\<section>2.2\<close>).
  \<^item> \<^bold>\<open>No semantics.\<close> There is no type checker, no usage checker (the parallel-usage rules that
    make \<open>PAR\<close> safe), no constant folding of array sizes and no arity check of procedure
    instances. An undeclared name is underlined, but a call with the wrong number of arguments
    is not detected; this is the task of a semantic backend built on top.
  \<^item> \<^bold>\<open>Comment placement.\<close> A comment is attached to the node starting at the next real token. A
    comment placed directly before a \<^emph>\<open>name\<close> that does not begin its line is attached to that
    name, not to the construct around it; an annotation meant for a whole process or
    specification belongs on its own line above it.
  \<^item> \<^bold>\<open>The \<open>text\<close> antiquotation never reaches the generated document.\<close> It runs the body
    through the real \<^ML>\<open>Document_Output.output_document\<close> (so inner antiquotations are checked
    and hyperlinked), but the result only reaches a probe reference. This is a limitation of
    Isabelle itself, not of this front-end: the presentation of a command is only consulted
    for document-class commands, which a \<open>thy_decl\<close> command can never be, and the
    \<open>occam2\<close> commands must be \<open>thy_decl\<close> to change \<open>oenv\<close>.
  \<^item> \<^bold>\<open>A single, shared, non-reentrant lexer state.\<close> The comment accumulator and the layout
    recorder are process-wide, so the parser cannot safely be invoked re-entrantly. For the
    same reason the theories of this session that run parser commands are chained by imports
    rather than left to Isabelle's scheduler to run in parallel.
  \<^item> \<^bold>\<open>Navigation is not total.\<close> An \<open>Id\<close> root is a leaf and is never navigable by \<open>r\<close>/\<open>d\<close>;
    there is no wrapping; and the counted-array and protocol syntax, types and replicator
    names, having no \<open>root\<close> variant, cannot be navigation targets.
\<close>

section\<open>Conclusion\<close>

text\<open>
  Isabelle/occam shows that the design of Isabelle/C Version 2.0 carries over to a language
  that looks very different: no brackets, no declarations-versus-statements split, no
  operator precedence, and concurrency as a first-class construct. The one genuinely new
  problem, indentation-sensitive syntax, is isolated in a small stream transformer between an
  ordinary ml-lex lexer and an ordinary ml-yacc grammar; everything on top of the parser -
  positions, environment, hyperlinks, antiquotations, navigation, commands - is the C11 design
  instantiated for a new AST. What is documented in \<open>\<section>5\<close> as missing is, in every case, a
  scoping decision rather than an accident: the natural next steps are a semantic backend
  (a CSP-style denotation of the processes of \<open>\<section>4\<close>, with the usage rules as proof
  obligations discharged by the antiquotations of \<open>\<section>2.5\<close>), and the arity and type checks that
  such a backend needs.

  \pagebreak
\<close>

section\<open>Annex: The occam 2 Grammar as Railroad Diagrams\<close>

subsection\<open>Lexical Structure\<close>

text\<open>
  The lexer is a small ml-lex specification in \<^verbatim>\<open>Occam2_Parser.thy\<close>. Keywords are written in
  upper case and are reserved (\<open>AFTER\<close>, \<open>ALT\<close>, \<open>AND\<close>, \<open>ANY\<close>, \<open>AT\<close>, \<open>BITAND\<close>, \<open>BITNOT\<close>,
  \<open>BITOR\<close>, \<open>BOOL\<close>, \<open>BYTE\<close>, \<open>CASE\<close>, \<open>CHAN\<close>, \<open>ELSE\<close>, \<open>FALSE\<close>, \<open>FOR\<close>, \<open>FROM\<close>, \<open>FUNCTION\<close>,
  \<open>IF\<close>, \<open>INT\<close>, \<open>INT16\<close>, \<open>INT32\<close>, \<open>INT64\<close>, \<open>IS\<close>, \<open>MINUS\<close>, \<open>MOSTNEG\<close>, \<open>MOSTPOS\<close>, \<open>NOT\<close>,
  \<open>OF\<close>, \<open>OR\<close>, \<open>PAR\<close>, \<open>PLACE\<close>, \<open>PLACED\<close>, \<open>PLUS\<close>, \<open>PORT\<close>, \<open>PRI\<close>, \<open>PROC\<close>, \<open>PROCESSOR\<close>,
  \<open>PROTOCOL\<close>, \<open>REAL32\<close>, \<open>REAL64\<close>, \<open>REM\<close>, \<open>RESULT\<close>, \<open>RETYPES\<close>, \<open>ROUND\<close>, \<open>SEQ\<close>, \<open>SIZE\<close>,
  \<open>SKIP\<close>, \<open>STOP\<close>, \<open>TIMER\<close>, \<open>TIMES\<close>, \<open>TRUE\<close>, \<open>TRUNC\<close>, \<open>VAL\<close>, \<open>VALOF\<close>, \<open>WHILE\<close>). A
  \<^emph>\<open>name\<close> is a letter followed by letters, digits and dots (\<open>producer\<close>, \<open>a.b\<close>). Literals are
  decimal integers, hexadecimal integers (\<open>#FF\<close>), reals with a mandatory fractional part and an
  optional exponent (\<open>3.14\<close>, \<open>1.0E+3\<close>), byte literals in single quotes and strings in double
  quotes, with \<open>*\<close> as the escape character as in the reference manual (\<open>*n\<close>, \<open>*'\<close>, \<open>*#41\<close>).

  Both the layout recorder and the comment machinery live in the lexer. Whitespace and the
  line structure update the layout state (\<open>\<section>2.1\<close>); \<open>--\<close> enters a comment state that runs to the
  end of the line, in which an antiquotation is recognised by a regular expression for its
  head, followed by a nesting-depth counter for a cartouche body, exactly as in C11. The
  syntax of the head:

  \<^rail>\<open>
    antiquotation : '@' tag navi? level? body
    ;
    navi : '[' (step *) ']'
    ;
    step : 'u' | 'U' | 'r' | 'd'
    ;
    level : '(' integer ')'
    ;
    body : cartouche | '"' text '"'
  \<close>

  The bracket around the navigation steps is a delimiter on purpose: \<open>u\<close>, \<open>U\<close>, \<open>r\<close>, \<open>d\<close> are
  ordinary identifier characters, so a tag ending in one of them (\<open>@answer\<close>) would otherwise be
  ambiguous between a tag and a tag plus a step.
\<close>

subsection\<open>Grammar\<close>

text\<open>
  The grammar follows the syntax summary of the reference manual. It is reproduced here
  slightly simplified: \<open>NEWLINE\<close>, \<open>INDENT\<close> and \<open>OUTDENT\<close> are shown as the indentation they stand
  for (a construct's body is written \<^emph>\<open>indented\<close>), and the dozen productions that merely
  enumerate the operators are abbreviated.

  \<^rail>\<open>
    program__unit : (specification *) process | (specification +)
    ;
    specification : declaration | abbreviation | retyping | protocol__definition
                  | procedure__definition | function__definition
    ;
    declaration : type name ((',' name) *) ':'
    ;
    abbreviation : ('VAL')? type? name 'IS' (element | expression) ':'
    ;
    retyping : ('VAL')? type name 'RETYPES' (element | expression) ':'
    ;
    protocol__definition : 'PROTOCOL' name 'IS' protocol ':'
                         | 'PROTOCOL' name 'CASE' ((tag ((';' simple__protocol) *)) +) ':'
    ;
    procedure__definition : 'PROC' name '(' formals? ')' process ':'
    ;
    function__definition : type ((',' type) *) 'FUNCTION' name '(' formals? ')'
                           (value__process ':' | 'IS' expression ((',' expression) *) ':')
    ;
    formals : ('VAL')? type name ((',' ('VAL')? type? name) *)
    ;
    type : primitive__type | 'CHAN' 'OF' protocol | 'TIMER' | 'PORT' 'OF' type
         | '[' expression? ']' type
    ;
    protocol : 'ANY' | name | simple__protocol ((';' simple__protocol) *)
    ;
    simple__protocol : type | primitive__type '::' '[' ']' type
  \<close>

  \<^rail>\<open>
    process : 'SKIP' | 'STOP' | assignment | input | output | case__input
            | 'SEQ' replicator? (process *) | conditional | case
            | 'WHILE' expression process
            | parallel | alternation | placed__par | instance | specification process
    ;
    assignment : variable ((',' variable) *) ':=' expression ((',' expression) *)
    ;
    input : channel '?' input__item ((';' input__item) *) | timer '?' 'AFTER' expression
    ;
    output : channel '!' output__item ((';' output__item) *)
    ;
    case__input : channel '?' 'CASE' (variant +)
    ;
    variant : (specification *) tag ((';' input__item) *) process
    ;
    conditional : 'IF' replicator? (choice *)
    ;
    choice : (specification *) (expression process | conditional)
    ;
    case : 'CASE' expression (option *)
    ;
    option : (specification *) (expression ((',' expression) *) | 'ELSE') process
    ;
    parallel : ('PRI')? 'PAR' replicator? (process *)
    ;
    alternation : ('PRI')? 'ALT' replicator? (alternative *)
    ;
    alternative : (specification *)
                  (guard process | (expression '&')? channel '?' 'CASE' (variant +))
    ;
    guard : (expression '&')? (input | 'SKIP')
    ;
    placed__par : 'PLACED' 'PAR' replicator? ((('PROCESSOR' expression process)) *)
    ;
    replicator : name '=' expression 'FOR' expression
  \<close>

  \<^rail>\<open>
    value__process : (specification *) 'VALOF' process 'RESULT' expression ((',' expression) *)
    ;
    expression : operand | monadic__operator operand | operand dyadic__operator operand
               | operand (('AND' operand) +) | operand (('OR' operand) +)
               | primitive__type ('ROUND' | 'TRUNC')? operand
               | ('MOSTPOS' | 'MOSTNEG') type
    ;
    operand : element | literal | table | '(' expression ')'
            | '(' value__process ')' | name '(' (expression ((',' expression) *))? ')'
    ;
    element : name | element '[' expression ']'
            | '[' element 'FROM' expression 'FOR' expression ']'
    ;
    table : string | '[' expression ((',' expression) *) ']' | table '[' expression ']'
          | '[' table 'FROM' expression 'FOR' expression ']'
    ;
    literal : integer | real | byte | string | 'TRUE' | 'FALSE' | literal '(' type ')'
  \<close>

  Antiquotation-carrying comments may occur, lexically, in front of any token. They are not
  part of this grammar (no production mentions them): they are attached to whichever AST
  node's \<open>nodeInfo\<close> claims them, by position, after the fact (\<open>\<section>2.3\<close>).
\<close>
(*<*)
end
(*>*)
