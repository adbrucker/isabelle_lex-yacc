(***********************************************************************************
 * Copyright (c) University of Paris-Saclay, 2026
 *
 * Author : Burkhart Wolff
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
theory C11_Manual
  imports "C11"
begin
(*>*)
section\<open>What is Isabelle/C\<close>

text\<open>
  Isabelle/C is a front-end that lets C11 source text live inside an Isabelle theory
  as a first-class citizen: parsed by a real grammar, checked incrementally under
  Isabelle/PIDE (so a syntax error, an undeclared identifier, or a malformed
  annotation is reported exactly like any other Isabelle error, with the usual
  jEdit markup, hyperlinking, and hovering), and open to attaching arbitrary
  Isabelle-level content - proof obligations, HOL terms, arbitrary Isar commands -
  to specific points in the C source via a comment-based antiquotation mechanism.
  It is not a C compiler, nor a verification tool in its own right: it is the
  \<^emph>\<open>front-end layer\<close> of a verification tool, a documentation generator, or a static
  analysis that would be built on top of it.
\<close>

subsection\<open>Context\<close>

text\<open>
  Isabelle/C already exists, as the \<^verbatim>\<open>Isabelle_C\<close> AFP entry
  \<^cite>\<open>"tuong.ea:isabellec:2019"\<close>, described in \<^cite>\<open>"tuong.ea:deeply:2019"\<close>
  (Tuong and Wolff, \<^emph>\<open>Deeply Integrating C11 Code Support into Isabelle/PIDE\<close>,
  F-IDE 2019). That entry provides a full C11/C18 front-end built around its
  \<^emph>\<open>own\<close>, hand-written, PIDE-integrated incremental lexer and parser
  (\<^verbatim>\<open>C_Lex\<close>, \<^verbatim>\<open>C_Parser\<close>, \<^verbatim>\<open>C_Grammar_Rule\<close>, \<open>\<dots>\<close>) together with a rich
  antiquotation-navigation language for pointing an annotation at a specific
  sub-term of the surrounding AST.

  This project - \<^bold>\<open>Isabelle/C, Version 2.0\<close> - is a from-scratch redesign of that
  same idea of a generic fontend/IDE for C, which can be hooked up with semantic
  backends, i.e specific analyser or verification environments implemented in Isabelle/HOL.
  Isabelle/C Version 2 is built on \<^verbatim>\<open>ml_lex_yacc\<close>, Isabelle/AFP's own
  generic, off-the-shelf ML-Lex/ML-Yacc integration for Isabelle/HOL ('Main')
  rather than the hand-crafted mix of generated lexer and parser sources of Version 1.    
  It is not a port of the AFP entry's code, and does not depend on it; 
  it exists to answer a narrower question: how much of the  \<^emph>\<open>essence\<close> of the 
  Isabelle/C approach - inline and file-based parsing commands, antiquotation-carrying
  comments, an environment tracking declarations across a translation unit,
  programmable handlers - can be reproduced on top of a generic parser-generator
  toolkit, while \<^emph>\<open>simplifying\<close> the original design that experience
  showed to be disproportionately complex. Since the lexer-part of version 1.0
  was effectively based on a version-split from Isabelle2019, the maintenance of
  Isabelle/C version 1.0 turned out to be problematic at various occasions in the
  Isabelle AFP development \<^footnote>\<open>An dieser Stelle ein grosses Dankeschoen an 
  Makarius Wenzel, der wiederholt ``ìssues'' des AFP Eintrags loeste und
  diesen Prototypen damit bis jetzt am Leben hielt.\<close>
 
  The antiquotation-navigation language
  (\<^verbatim>\<open>select_ast\<close>, \<open>\<section>2.4\<close>) is the clearest example: Isabelle/C 1.0's own
  navigation concept is, by design, considerably more general (and considerably
  more complex) than what most annotations actually need; this project restarts
  that design from a small, explicit set of primitives (\<open>u\<close>/\<open>U\<close>/\<open>r\<close>/\<open>d\<close>) chosen to
  cover the common cases plainly, at the cost of not (yet) covering everything
  the original does.
\<close>


section\<open>Main Features of Isabelle/C\<close>

text\<open>
  Four pieces fit together to give the \<open>c11\<close>-family commands (\<open>\<section>3\<close>) their
  behaviour: a parser that produces a real AST with genuine source positions
  attached to every node (\<open>\<section>2.1\<close>); a per-theory environment tracking every
  declared name, used to hyperlink each identifier \<^emph>\<open>use\<close> back to its
  declaration (\<open>\<section>2.2\<close>); a mechanism for attaching arbitrary, programmable
  content to a specific AST node via a comment (\<open>\<section>2.3\<close>); and a well-defined
  order and a navigation language governing exactly \<^emph>\<open>which\<close> node an
  antiquotation resolves to and \<^emph>\<open>when\<close> it runs (\<open>\<section>2.4\<close>).
\<close>

subsection\<open>Parsing\<close>

text\<open>
  The grammar (\<^verbatim>\<open>C11_Parser.thy\<close>, generated via this repository's own
  \<^verbatim>\<open>ml_lex_yacc\<close> command from an ml-lex lexer specification and an ml-yacc LALR(1)
  grammar) covers ISO C11's expression, statement, and declaration syntax -
  see the annex (\<open>\<section>6\<close>) for the lexical structure and a representative subset
  of the grammar as railroad diagrams. Every AST node's own annotation field
  (\<open>'a nodeInfo\<close>, \<^verbatim>\<open>c_ast.ML\<close>) carries a genuine \<^verbatim>\<open>Position.T\<close> together with
  any comments/antiquotations attached to that node, so PIDE markup - hovering,
  hyperlinking, error underlining - is available at every level of the tree, not
  only at the top. Four entry points parse a fragment of a given shape and store
  its AST (\<open>\<section>3\<close>); the \<open>_reject\<close> counterpart of each documents, rather than
  silently skips, an input this fragment is known not to accept.

  This is deliberately a \<^emph>\<open>simplified\<close> fragment of full C11, not a conforming
  implementation: translation phases 1 and 2 (trigraphs, backslash-newline line
  splicing) are not implemented, since a conforming implementation would need to
  preprocess the source text - with its own position-mapping machinery - before
  the lexer ever sees it, and \<open>\<section>4\<close> lists further, similarly deliberate gaps.
\<close>

subsection\<open>The C-Environment, and Declaration/Use Navigation\<close>

text\<open>
  \<^verbatim>\<open>CEnv.thy\<close> defines \<open>cenv\<close>, a small record - a symbol table (\<open>idents\<close>,
  currently variables/functions/parameters/preprocessor constants/macros/enum
  constants; \<open>types\<close>, the separate struct/union/enum \<^emph>\<open>tag\<close> namespace,
  \<open>\<section>2.6\<close> is not the only reader of it - \<open>\<section>4\<close>'s member-linking item also
  depends on it directly; a registry of antiquotation handlers, \<open>c_antiq\<close>,
  \<open>\<section>2.3\<close>; \<open>predefined_envs\<close>, \<open>\<section>2.6\<close>'s reusable per-header effects; and a
  per-theory AST unit counter) - stored as ordinary \<^verbatim>\<open>Generic_Data\<close>, so it
  persists across commands within one theory and merges correctly under
  Isabelle's parallel, incremental checking.

  \<^verbatim>\<open>AnaEval.thy\<close>'s \<open>analyse_and_eval\<close> is a single, purely functional, scoped
  walk over a parsed root that populates \<open>cenv\<close> as it goes: entering a function
  body, a compound-statement block, or a \<open>for\<close>-loop's own declaration clause
  remembers the incoming symbol table and restores exactly that once that
  scope's walk returns, giving ordinary sequential C scoping. Every identifier
  \<^emph>\<open>use\<close> (a variable/function name, or a preprocessor constant/macro reference -
  this fragment does not expand macros, so a later reference to one is simply
  another use of that name in the same flat namespace) is hyperlinked to its
  declaration via \<^ML>\<open>Position.entity_markup\<close>, reported once at the
  declaration site and once at every use; a name that resolves nowhere in
  \<open>cenv\<close> is underlined (\<^ML>\<open>Markup.bad ()\<close>) rather than rejected outright,
  since this fragment has no symbol table spanning multiple files - "undeclared
  here" routinely just means "declared somewhere this parse never saw".

  Being ordinary, persistent, per-theory \<^verbatim>\<open>Generic_Data\<close> - the same idiom a
  simp-set or a \<open>Named_Theorems\<close> collection uses, not something private to
  the \<open>c11\<close>-family commands - is what lets \<open>c11\<close>/\<open>c11_file\<close>/\<open>\<dots>\<close> be freely
  \<^emph>\<open>interleaved\<close> with arbitrary Isar content (definitions, proofs, plain
  text) and still resolve a name used in one C fragment back to its
  declaration in an earlier one, however much unrelated material sits in
  between - navigation \<^emph>\<open>across\<close> fragments, scattered through an otherwise
  ordinary Isabelle theory, is the actual point of threading \<open>cenv\<close> this
  way rather than starting each fragment from scratch. The flip side is
  that \<open>cenv\<close> then only ever \<^emph>\<open>grows\<close> across a theory, with no built-in
  notion of "start this section fresh": two commands, \<open>set_cenv_default\<close>
  and \<open>reset_cenv\<close> (\<open>\<section>3\<close>), give a theory explicit control over that,
  letting it nominate a snapshot - typically right after the standard
  antiquotation handlers below are registered, or later still, once a
  theory has predefined the headers (\<open>\<section>2.6\<close>) it wants known by default -
  that a later point in the same theory can return to.
\<close>

subsection\<open>Programmable C-Antiquotations, and Handlers\<close>

text\<open>
  A comment of the shape \<open>@tag[navi](level) \<open>body\<close>\<close> - an \<open>@\<close>-prefixed tag, an
  optional bracketed navigation string (\<open>\<section>2.4\<close>), an optional parenthesized
  integer \<open>level\<close> (\<open>0\<close> when omitted), and a body written either as a nested
  Isabelle cartouche or, equivalently, a double-quoted string - is recognized
  lexically wherever an ordinary \<open>/* ... */\<close> or \<open>// ...\<close> comment would be, and
  attached to whichever AST node it resolves against (\<open>\<section>2.4\<close>). \<open>tag\<close> selects a
  \<^emph>\<open>handler\<close>: an ordinary ML function of type

  \<^verbatim>\<open>type type_antiq_fun = cenv * pos C_Ast.root * int -> (string * pos) -> Context.generic -> Context.generic\<close>

  registered once, ahead of time, via \<open>CEnv.store_antiq (tag, handler)\<close>. When
  \<open>analyse_and_eval\<close> reaches a node carrying an \<open>@tag ...\<close> antiquotation, it
  resolves the navigation string against the closest-surrounding-context stack
  (\<open>\<section>2.4\<close>) into a single concrete \<open>root\<close> value, then instantiates the handler
  with \<open>(cenv, resolved_root, level)\<close> and the body text together with its own
  source position - a handler is never itself responsible for interpreting
  \<open>u\<close>/\<open>U\<close>/\<open>r\<close>/\<open>d\<close>; by the time it runs, \<open>navi\<close> has already been resolved to a
  single AST node.

  \<open>Context.generic\<close>, not plain \<open>theory\<close>, deliberately: a handler is free to do
  anything a genuine Isar toplevel command can, including running real ML code
  at the actual ML environment level (\<open>ML\<close>, below) - something no
  \<open>theory -> theory\<close> function could ever express, since that mutates \<open>theory\<close>
  \<^emph>\<open>data\<close>, not the ML environment itself. Every antiquotation action collected
  during a walk is folded together as plain \<open>Context.generic -> Context.generic\<close>
  functions (ordinary composition) and lifted to
  \<open>Toplevel.transition -> Toplevel.transition\<close> \<^emph>\<open>exactly once\<close>, at the very
  end (\<open>full_eval_and_store\<close>, \<^verbatim>\<open>C11.thy\<close>) - not per handler: confirmed directly
  against \<^verbatim>\<open>Pure/Isar/toplevel.ML\<close> that \<open>Toplevel.theory\<close>/
  \<open>Toplevel.generic_theory\<close> each \<^emph>\<open>append one alternative\<close> action to a
  transition's own action list rather than composing sequentially, so chaining
  several already-lifted handlers with \<open>#>\<close> would silently run only the first
  of them.

  Most handlers never need this extra generality - they are ordinary
  \<open>theory -> theory\<close> functions, exactly as before, only now \<^emph>\<open>recaptured\<close> via
  \<open>CEnv.lift_theory_antiq\<close> at the point they are registered, rather than
  changing a single line of the handler's own body:
\<close>

ML\<open>
val todo_antiq =
  let
    fun handler (_ : CEnv.cenv, ast, level) (body, _ : Position.T) thy =
      (warning ("TODO (level " ^ Int.toString level ^ ") at " ^
                Position.here (AnaEval.pos_of_root ast) ^ ": " ^ body);
       thy)
  in CEnv.store_antiq ("todo", CEnv.lift_theory_antiq handler) end
\<close>
setup\<open>todo_antiq\<close>

text\<open>
  which, once registered, turns a plain comment into a genuine, checked
  diagnostic - reported against the exact AST node the comment resolves to,
  not merely "somewhere in this function":
\<close>

c11\<open>
int f(int x) {
  /*@ todo \<open>refine the overflow check below\<close> */
  return x + 1;
}
\<close>

text\<open>
  A tag with no registered handler is a hard error (\<open>analyse_and_eval\<close> has no
  notion of an "unknown, ignore it" antiquotation) - every tag that can appear
  in a theory's source must be registered before that theory's \<open>c11\<close>-family
  commands run.
\<close>

subsection\<open>Execution (Order, Navigation, etc.)\<close>

text\<open>
  \<^bold>\<open>Order.\<close> A parsed root can carry several antiquotations, possibly with
  side-effecting handlers whose relative order matters (a \<open>setup\<close> that must
  run before a later \<open>requires\<close> depends on what it set up, say). \<open>level\<close> is
  the author's own explicit ordering knob: \<open>full_eval_and_store\<close> (\<^verbatim>\<open>C11.thy\<close>)
  collects every \<open>(level, Context.generic -> Context.generic)\<close> pair the walk
  produces, sorts by \<open>level\<close> - a stable sort, so antiquotations sharing a
  level keep their relative, i.e.\ textual, order - and chains them, each
  against the context the previous one produced. A physical antiquotation is
  dispatched \<^emph>\<open>exactly
  once\<close> regardless of how many AST nodes reachable from the walk happen to
  share its leftmost source position (the classic case: an expression-statement
  and its own wrapped expression share one leftmost token) - tracked by
  physical comment \<^emph>\<open>value\<close>, not by position alone, and reset once per
  \<open>analyse_and_eval\<close> call.

  \<^bold>\<open>Context.\<close> Every antiquotation resolves, by default, to its \<^emph>\<open>closest
  surrounding context\<close>: the walk threads a stack (\<open>ctx\<close>) of every enclosing
  expression/statement/unit, pushing a fresh frame at \<^emph>\<open>every\<close> level of
  expression/statement nesting (so a comment three levels deep inside a cast
  resolves to that inner sub-expression, not the enclosing statement), while a
  declaration, declarator, initializer, or parameter list never pushes its own
  frame and so resolves to whatever is currently on top - which is what makes
  every node kind a valid antiquotation target, including ones (a block-local
  declaration, a \<open>for\<close>-loop's own clause, a cast's abstract type-name) that
  have no sensible "own" context otherwise.

  \<^bold>\<open>Navigation.\<close> The bracketed \<open>[navi]\<close> string lets an antiquotation point
  \<^emph>\<open>away\<close> from its own closest context instead of accepting it as-is - written
  \<open>(u|U)*(r|d)*\<close> (possibly empty), i.e.\ zero or more ascend-steps followed by
  zero or more descend-steps, never interleaved. \<open>u\<close> ascends one level (a
  lone, final \<open>u\<close> is a no-op: "stay here"); \<open>U\<close> ascends past an entire run of
  consecutive same-category ancestors in one step (three nested expressions in
  a row collapse to whichever expression the run's outermost member is, in the
  same single step "uuu" would need three of); \<open>r\<close> advances a 1-based cursor
  rightward among the current node's own children (its own sub-expressions/
  sub-statements, in declaration order - a declaration, an identifier, or any
  other field with no \<open>root\<close> counterpart is silently not a candidate); \<open>d\<close>
  descends into the child the cursor currently points at (cursor \<open>1\<close>, i.e.\
  a bare \<open>d\<close>, if no \<open>r\<close> preceded it) and continues resolving the rest of the
  string against \<^emph>\<open>that\<close> child. There is no wrapping: a cursor beyond the
  current node's own children, or a \<open>d\<close> on a node with none at all (an
  ordinary leaf, or a node whose only field is a declaration/type-name), is a
  hard error, reported at the antiquotation's own tag position. For example,
  on an \<open>if (c) s1; else s2;\<close> statement, \<open>[rd]\<close> selects \<open>c\<close>, \<open>[rrd]\<close> selects
  \<open>s1\<close>, and \<open>[rrrd]\<close> selects \<open>s2\<close> - a fourth \<open>r\<close> would be out of range.
\<close>

subsection\<open>Standard Antiquotations\<close>

text\<open>
  \<^verbatim>\<open>AnaEval.thy\<close> registers five demonstration handlers, available to every
  theory that imports \<^verbatim>\<open>C11\<close> (they are not meant as production
  verification-condition generators - each is a small, self-contained example
  of one facility a real handler might use):

  \<^descr> \<open>probe_cenv\<close> stashes the \<open>cenv\<close> it was called with into a global
    \<^ML>\<open>Unsynchronized.ref\<close> (\<^ML>\<open>CENV\<close>), letting a test or an interactive
    session inspect the symbol table as it stood at that point in the walk.
  \<^descr> \<open>probe_ast\<close> likewise stashes its resolved AST node (\<^ML>\<open>AST\<close>), the
    facility used throughout this manual's own test suite to confirm exactly
    which node a given \<open>[navi]\<close> string resolves to.
  \<^descr> \<open>highlight\<close> calls \<^ML>\<open>Position.report\<close> with \<^ML>\<open>Markup.intensify\<close> on
    the resolved node's own position - the simplest possible example of a
    handler that only ever produces PIDE markup, no side effect on \<open>thy\<close> at
    all.
  \<^descr> \<open>term\<close> parses its body as a genuine HOL term against the theory's
    \<^emph>\<open>current\<close> context via \<^ML>\<open>Syntax.read_term\<close>, reading it through a real,
    position-carrying \<^ML>\<open>Input.source\<close> (mirroring how Isabelle's own
    \<open>@{term \<open>...\<close>}\<close> antiquotation reads a term from the outer token stream) so
    that hovering over a symbol \<^emph>\<open>inside\<close> the parsed term links back to that
    symbol's own place in the term, not to some unrelated fallback position. A
    malformed or ill-typed term is a genuine, checked Isabelle error - e.g.\ an
    ACSL-style \<open>//@ requires \<open>x \<ge> 0\<close>\<close> is a real, checked HOL proposition, not
    merely stored text.
  \<^descr> \<open>ML\<close> runs its body as real ML source at the actual ML toplevel
    (\<^ML>\<open>ML_Context.exec\<close>/\<^ML>\<open>ML_Context.eval_source\<close>, the same machinery the
    real top-level \<open>ML\<open>...\<close>\<close> command itself uses) - a definition written
    inside a C comment genuinely becomes a later-visible ML binding, not
    \<open>theory\<close>-level data. Unlike the four above, it is written directly against
    \<open>Context.generic -> Context.generic\<close> rather than through
    \<open>CEnv.lift_theory_antiq\<close>, since that is precisely the capability a plain
    \<open>theory -> theory\<close> function cannot express - the reason a handler's own
    type was generalized past \<open>theory -> theory\<close> in the first place.
\<close>

subsection\<open>Predefined Header Declarations\<close>

text\<open>
  Real C code routinely uses names this fragment never itself declares -
  \<open>printf\<close>, \<open>malloc\<close>, \<open>errno\<close>, \<open>assert\<close> - because they come from a system
  header. Left with no way to tell this fragment about them, every such
  use would be reported exactly like a genuinely undeclared name
  (\<open>Markup.bad ()\<close>, \<open>\<section>2.2\<close>) - technically correct (this fragment really
  never saw a declaration for it), but noisy and unhelpful for anything
  beyond a self-contained toy example.

  \<open>c11_predef [header] \<open>decl_list\<close>\<close> (\<open>\<section>3\<close>) closes this gap by genuinely
  connecting to \<open>#include\<close>, the one preprocessor form (\<open>\<section>2.1\<close>) that is no
  longer purely syntactic: walking \<open>decl_list\<close> does \<^emph>\<open>not\<close> itself register
  any name into \<open>cenv\<close> - it only captures the walk's own effect as a
  reusable \<open>cenv -> cenv\<close> function and stores \<^emph>\<open>that\<close> under \<open>header\<close>
  (\<^verbatim>\<open>CEnv.predefined_envs\<close>). A later \<open>#include <header>\<close>, anywhere this
  \<open>cenv\<close> is in scope, is what actually applies it
  (\<open>AnaEval.walk_pp_directive\<close>'s \<open>CPPInclude\<close> case) - matching real C, where
  a header's declarations are only in scope once it is genuinely included,
  not merely known about somewhere in the theory. \<open>#include <stdio.h>\<close>
  applies exactly the effect registered under the label \<open>stdio.h\<close>, storing
  the header-name token's own declaration position alongside that effect
  (\<^verbatim>\<open>CEnv.predefined_envs\<close>) so \<open>stdio.h\<close> \<^emph>\<open>itself\<close>, in the \<open>#include\<close>
  line, is now navigable - hyperlinking back to where it was predefined,
  exactly like an ordinary declaration/use pair; a header never declared
  via \<open>c11_predef\<close> anywhere in scope is instead underlined as unresolved
  (\<^ML>\<open>Markup.bad ()\<close>), leaving \<open>#include\<close> the no-op it always was, but
  now visibly so. Once applied, a predefined name is indistinguishable in
  \<open>cenv\<close> from one the theory declared itself: it hyperlinks, participates
  in scoping, and can be the target of a struct/union/enum tag or member
  lookup (\<open>\<section>2.2\<close>) exactly the same way. \<open>stdio.h\<close>, \<open>stdlib.h\<close>,
  \<open>errno.h\<close>, and \<open>assert.h\<close> are, in fact, predefined once, in
  \<^verbatim>\<open>C11.thy\<close> itself (immediately followed by \<open>set_cenv_default\<close>, \<open>\<section>3\<close>),
  so any theory built on it gets them for free.

  One thing is deliberately \<^emph>\<open>not\<close> provided, matching the "basic
  functionality" this command is scoped to: \<open>decl_list\<close> may only declare
  an \<^emph>\<open>interface\<close>, never an implementation - a function \<^emph>\<open>definition\<close>
  (a real \<open>{ ... }\<close> body) is rejected outright, since the point is only to
  let the environment know a name exists and roughly what it looks like,
  not to give it real, executable semantics. A genuine limitation of what
  can be declared this way at all - not a scoping choice - is discussed in
  \<open>\<section>4\<close>.
\<close>

section\<open>The C11 Main Commands\<close>

text\<open>
  \<^descr> \<open>c11 \<open>...\<close>\<close> parses its argument as a whole translation unit, runs
    \<open>analyse_and_eval\<close> under \<open>full_eval = true\<close> semantics (\<open>\<section>2.4\<close>), and
    stores the resulting AST under a fresh key.
  \<^descr> \<open>c11_file \<open>path\<close>\<close> is the same, reading the translation unit from an
    external \<open>.c\<close> file (resolved relative to the theory's master directory,
    via \<^ML>\<open>Resources.parse_file\<close> - the same Isabelle/Pure machinery the
    built-in \<open>ML_file\<close> command uses, so file positions and build-dependency
    tracking come for free).
  \<^descr> \<open>c11_ident \<open>...\<close>\<close>, \<open>c11_expr \<open>...\<close>\<close>, \<open>c11_statement \<open>...\<close>\<close> parse a bare
    identifier, expression, or statement respectively - \<open>analyse_and_eval\<close>
    still runs (so declaration/use hyperlinking is reported), but the
    antiquotation actions it collects are discarded rather than chained,
    since a standalone fragment is a syntax check, not a genuine compilation
    unit.
  \<^descr> \<open>c11_reject \<open>...\<close>\<close>, and the \<open>_reject\<close> counterpart of each of the three
    above, document a fragment as correctly \<^emph>\<open>not\<close> that shape - rejected
    either by a genuine parse failure, or by parsing successfully as the
    \<^emph>\<open>wrong\<close> shape (an expression handed to \<open>c11_statement_reject\<close>, say).
  \<^descr> \<open>c11_predef [header] \<open>decl_list\<close>\<close> (\<open>\<section>2.6\<close>) captures a fragment of
    predefined global variables/macro-definitions/function prototypes -
    the usual contents of a standard header such as \<open>stdio.h\<close> - as a
    reusable effect on \<open>cenv\<close>, applied only once a later \<open>#include
    <header>\<close> actually triggers it, so that names like \<open>printf\<close> are no
    longer "genuinely undeclared" once (and only once) their header is
    genuinely included. \<open>header\<close> (e.g.\ \<open>stdio.h\<close>, parsed directly as a
    dotted \<open>name\<close> token) doubles as the key \<open>#include\<close> looks up. A
    function \<^emph>\<open>definition\<close> (a real \<open>{ ... }\<close> body) is rejected outright:
    this command is for declaring an interface, never an implementation.
  \<^descr> \<open>set_cenv_default\<close> and \<open>reset_cenv\<close> (\<open>\<section>2.2\<close>) give explicit control
    over \<open>cenv\<close>'s otherwise ever-growing scope across a theory.
    \<open>set_cenv_default\<close> takes no argument: it nominates whatever \<open>cenv\<close>
    holds \<^emph>\<open>right now\<close> as the snapshot a later \<open>reset_cenv\<close> restores -
    callable more than once, each call moving the baseline forward.
    \<open>reset_cenv\<close>, likewise argument-free, restores exactly that snapshot;
    with no \<open>set_cenv_default\<close> anywhere earlier in scope, it falls back to
    the empty \<open>cenv\<close> rather than erroring. Neither touches the separate,
    per-\<open>typedef\<close>-name lexer table (\<open>\<section>4\<close>'s \<open>typedef\<close> item) - only the
    symbolic environment used for hyperlinking and member-/type-chasing is
    reset.
\<close>

text\<open>A whole translation unit, with declaration/use hyperlinking and a
  checked antiquotation:\<close>
c11\<open>
int max(int a, int b) {
  if (a > b) return a; else return b;
}

int main(void) {
  /*@ highlight */
  int x = max(3, 42);
  return x;
}
\<close>

text\<open>A bare expression, syntax-checked on its own:\<close>
c11_expr\<open>max(1, 2) + 3\<close>

text\<open>Documenting, rather than silently accepting, an out-of-scope construct
  (this fragment's simplified \<open>#define\<close> takes a single expression, not the
  real preprocessor's replacement-token list):\<close>
c11_reject\<open>
#define SQUARE(x) x * x
\<close>

text\<open>A predefined-header fragment of our own, and its effect on a later use
  of one of its names - once \<open>#include <mymath.h>\<close> actually applies it (a
  bare \<open>#include\<close> is only meaningful as part of a translation unit, so
  this needs a whole \<open>c11\<close> block, not a standalone \<open>c11_expr\<close>).
  \<open>stdio.h\<close>/\<open>stdlib.h\<close>/\<open>errno.h\<close>/\<open>assert.h\<close> need no such declaration here
  at all any more - \<^verbatim>\<open>C11.thy\<close> itself already predefines all four, right
  after \<open>c11_predef\<close> is defined, as part of the \<^emph>\<open>default\<close> \<open>cenv\<close> baseline
  (\<open>\<section>2.2\<close>) - so \<open>printf\<close> below just works, out of the box.\<close>
c11_predef [mymath.h] \<open>
double square_root(double x);
\<close>

c11\<open>
#include <stdio.h>
#include <mymath.h>

int greet(void) {
  printf("%f\n", square_root(2.0));
  return printf("hello, %d\n", 42);
}
\<close>

text\<open>The header name itself, in a \<open>#include\<close>, is navigable - hovering over
  \<open>stdio.h\<close> above hyperlinks back to the \<open>c11_predef [stdio.h] ...\<close> token
  in \<^verbatim>\<open>C11.thy\<close> that declared it, exactly like an ordinary declaration/use
  pair (\<open>AnaEval.walk_pp_directive\<close>'s \<open>CPPInclude\<close> case); a header
  \<open>#include\<close>d with no matching \<open>c11_predef\<close> anywhere in scope is
  underlined as unresolved, exactly like a genuinely undeclared name,
  rather than silently ignored.\<close>

text\<open>\<open>set_cenv_default\<close>/\<open>reset_cenv\<close>: the snapshot below already includes
  everything declared above (\<open>max\<close>, \<open>printf\<close>, \<open>greet\<close>, \<open>\<dots>\<close>), so only
  \<open>scratch_only\<close> - declared \<^emph>\<open>after\<close> \<open>set_cenv_default\<close> - is at risk of
  being forgotten once \<open>reset_cenv\<close> runs.\<close>
set_cenv_default
c11\<open>int scratch_only;\<close>
reset_cenv

subsection\<open>An Example Session\<close>

text\<open>
  The following are jEdit/PIDE screenshots from an interactive session against
  this test suite, using the \<open>highlight\<close> antiquotation (\<open>\<section>2.5\<close>) to make
  \<open>select_ast\<close>'s resolved node visible directly in the editor - the same
  effect \<open>probe_ast\<close> makes visible programmatically (\<open>\<section>2.5\<close>) is shown here
  as PIDE markup instead.

  \<^bold>\<open>Order.\<close> \<open>level\<close> reorders execution independently of textual order
  (\<open>\<section>2.4\<close>): despite \<open>setup(1) \<open>alfa\<close>\<close> appearing \<^emph>\<open>after\<close>
  \<open>setup(2) \<open>beta\<close>\<close> in the source, the Output panel confirms it ran first.

  \begin{figure}[!htb]
  \begin{center}
  \includegraphics[width=0.8\textwidth]{figures/ExecutionOrderLevels}
  \end{center}
  \caption{\<open>setup(1)\<close> executes before \<open>setup(2)\<close>, despite being written
    textually after it - the Output panel (bottom) reports \<open>"alfa"\<close> before
    \<open>"beta"\<close>.}
  \label{fig:execution-order-levels}
  \end{figure}

  \<^bold>\<open>Ascending with \<open>u\<close>.\<close> Two screenshots against the same nested cast
  expression \<open>a + (int)(b * c)\<close> (\<open>\<section>2.4\<close>): \<open>[uu]\<close> ascends one level from
  \<open>b * c\<close> to the enclosing cast, \<open>[uuu]\<close> ascends one level further, to the
  outer addition.

  \begin{figure}[!htb]
  \begin{center}
  \includegraphics[width=0.8\textwidth]{figures/NaviInExpr1}
  \end{center}
  \caption{\<open>highlight[uu]\<close>: two ascend-steps from \<open>b * c\<close> land on the
    enclosing cast \<open>(int)(b * c)\<close>.}
  \label{fig:navi-in-expr-1}
  \end{figure}

  \begin{figure}[!htb]
  \begin{center}
  \includegraphics[width=0.8\textwidth]{figures/NaviInExpr2}
  \end{center}
  \caption{\<open>highlight[uuu]\<close>: one more ascend-step reaches the outer
    addition \<open>a + (int)(b * c)\<close>.}
  \label{fig:navi-in-expr-2}
  \end{figure}

  \<^bold>\<open>Descending with \<open>r\<close>/\<open>d\<close>.\<close> One screenshot shows all three navigable
  children of a single \<open>if\<close>/\<open>else\<close> statement at once: \<open>[rd]\<close>, \<open>[rrd]\<close>, and
  \<open>[rrrd]\<close> select the condition, the then-branch, and the else-branch
  respectively.

  \begin{figure}[!htb]
  \begin{center}
  \includegraphics[width=0.9\textwidth]{figures/NaviInStmt1}
  \end{center}
  \caption{\<open>highlight[rd]\<close>/\<open>highlight[rrd]\<close>/\<open>highlight[rrrd]\<close> on three
    copies of the same \<open>if (a) return 1; else return 0;\<close>, selecting the
    condition, the then-branch, and the else-branch respectively.}
  \label{fig:navi-in-stmt-1}
  \end{figure}

  A second pair contrasts \<open>[dd]\<close> against no navigation string at all on the
  same expression-statement \<open>a + b;\<close>: \<open>[dd]\<close> descends to the left operand
  \<open>a\<close>, while a bare \<open>highlight\<close> (empty navigation string) highlights the
  \<^emph>\<open>whole\<close> closest-context expression instead - the default \<open>select_ast\<close>
  falls back to when no navigation is requested.

  \begin{figure}[!htb]
  \begin{center}
  \includegraphics[width=0.8\textwidth]{figures/NaviInExpr3}
  \end{center}
  \caption{\<open>highlight[dd]\<close> (top) selects the left operand \<open>a\<close>; a bare
    \<open>highlight\<close> with no navigation string (bottom) highlights the whole
    expression \<open>a + b\<close> instead.}
  \label{fig:navi-in-expr-3}
  \end{figure}

  Finally, \<open>[d]\<close> on a compound statement demonstrates that a block-local
  declaration is silently not a navigable child (\<open>\<section>2.4\<close>): the highlighted
  target is the first real \<^emph>\<open>statement\<close>, not the \<open>int x = 0;\<close> declaration
  that precedes it in the source.

  \begin{figure}[!htb]
  \begin{center}
  \includegraphics[width=0.6\textwidth]{figures/NaviInStmt2}
  \end{center}
  \caption{\<open>highlight[d]\<close> on a compound statement skips its block-local
    declaration \<open>int x = 0;\<close> and lands on \<open>x = 1;\<close>.}
  \label{fig:navi-in-stmt-2}
  \end{figure}

  \<^bold>\<open>Beyond navigation.\<close> Two further screenshots show the surrounding
  machinery the navigation examples above build on: an ACSL-style
  \<open>requires\<close>/\<open>ensures\<close>/\<open>highlight\<close> block attached to a function definition
  (\<open>\<section>2.3\<close>), and declaration/use hyperlinking (\<open>\<section>2.2\<close>) - hovering a use of
  \<open>sum\<close> inside a \<open>while\<close> loop shows its declaration kind and offers to jump
  to it.

  \begin{figure}[!htb]
  \begin{center}
  \includegraphics[width=0.7\textwidth]{figures/AcslRequiresEnsuresHighlight}
  \end{center}
  \caption{An ACSL-style \<open>requires\<close>/\<open>ensures\<close>/\<open>highlight\<close> comment attached
    to \<open>int abs(int n)\<close>.}
  \label{fig:acsl-requires-ensures-highlight}
  \end{figure}

  \begin{figure}[!htb]
  \begin{center}
  \includegraphics[width=0.6\textwidth]{figures/DeclUseHoverLoop2}
  \end{center}
  \caption{Hovering a use of \<open>sum\<close> inside a \<open>while\<close> loop: the popup reports
    \<open>C11 local variable "sum"\<close>, hyperlinked back to its declaration.}
  \label{fig:decl-use-hover-loop}
  \end{figure}
\<close>

section\<open>Limitations\<close>

text\<open>
  This fragment is a deliberately simplified slice of C11, not a conforming
  implementation, and the antiquotation-navigation language (\<open>\<section>2.4\<close>) is
  itself a deliberately narrowed restart of Isabelle/C 1.0's own, more general
  one (\<open>\<section>1.1\<close>). Concretely:

  \<^item> \<^bold>\<open>No translation phases 1 and 2.\<close> Trigraphs and backslash-newline line
    splicing are not implemented - both are, per ISO C11 \<open>\<section>5.1.1.2\<close>, purely
    textual transformations that happen \<^emph>\<open>before\<close> tokenization, so a
    genuinely conforming lexer would need its own preprocessing pass (with its
    own position-mapping machinery) ahead of the one this fragment has. In
    particular, a backslash-newline may legitimately split even a single
    keyword in standard C11 (translation phase 2 does not know about tokens at
    all); this fragment's lexer, having no such pass, simply sees two
    unrelated identifiers instead and rejects the input - a real gap, not a
    standards-correct rejection, and documented as such where it is tested.
  \<^item> \<^bold>\<open>A simplified preprocessor fragment.\<close> Only \<open>#define name = expr\<close>,
    \<open>#define name(a, \<dots>) = expr\<close> (a single expression, not a general
    replacement-token sequence), \<open>#include\<close>, and \<open>#ifdef\<close>/\<open>#ifndef\<close> (with an
    optional \<open>#else\<close>) are recognized as real AST nodes; the general \<open>#if\<close>/
    \<open>#elif\<close> constant-expression language, token pasting/stringizing, and
    \<open>_Pragma\<close> are out of scope.
  \<^item> \<^bold>\<open>Member linking, and its real remaining bound.\<close> A struct/union/enum
    \<^emph>\<open>tag\<close> is tracked (\<open>type_ident\<close>, \<^verbatim>\<open>CEnv.thy\<close>) and hyperlinked like any
    other declared name, and an enum's own constants are registered into the
    ordinary namespace right alongside variables and functions. Resolving a
    member access \<open>e.field\<close>/\<open>e->field\<close> back to \<open>field\<close>'s own declaration
    (\<open>AnaEval.report_member_use\<close>) goes through \<open>AnaEval.base_specs_of_expr\<close>
    - a small, deliberately shallow form of type inference finding the
    declaration-specifiers describing \<open>e\<close>'s own type - which now covers a
    bare variable, a function call's return type (\<open>f().field\<close>), an array
    index or pointer dereference or address-of (\<open>arr[0].field\<close>,
    \<open>p->field\<close> via an explicit \<open>*p\<close>, \<open>(&x)->field\<close>), a cast's own target
    type, and a chained member access itself (\<open>a.b.c\<close>, \<open>p->next->field\<close>) -
    and, on whatever specifiers it finds, \<open>AnaEval.member_decls_of_specs\<close>
    chases through any number of \<open>typedef\<close>s (via \<open>idents\<close>, recursively) to
    the real struct/union member list, including an inline, fully anonymous
    struct/union body (\<open>typedef struct { \<dots> } point_t;\<close>) - so
    \<open>report_member_use\<close> genuinely handles the same shapes
    \<open>c11_predef [setjmp.h]\<close>/\<open>c11_predef [stdarg.h]\<close> (\<open>\<section>2.6\<close>) already need
    \<open>typedef\<close> support for. What remains genuinely unresolved: a base
    expression shape neither function covers (a binary/ternary/assignment
    expression, a literal, a generic selection, \<open>\<dots>\<close> - there is no real type
    system behind any of this, only specifiers-chasing), and a
    function-pointer-typed call (\<open>(*fp)(...).field\<close> would need chasing
    through a \<open>CFunDeclr\<close> derived declarator, which
    \<open>member_decls_of_specs\<close> does not do) - both still fall back to
    unresolved markup rather than a hyperlink, exactly like a genuinely
    undeclared name.
  \<^item> \<^bold>\<open>\<open>typedef\<close> names, with two narrow gaps.\<close> \<open>C11_Typedefs\<close>
    (\<^verbatim>\<open>C11_Parser.thy\<close>) gives the lexer real "lexer hack" feedback: once a
    \<open>typedef\<close> declaration has been reduced, its name is recognized as
    \<open>TYPEDEF_NAME\<close> (not a plain identifier) in every later use, in the same
    or a later command - \<open>typedef int my_int; my_int x;\<close> now parses (given
    at least one further token between the \<open>typedef\<close>'s own \<open>";"\<close> and
    \<open>my_int\<close>'s reuse, see below), and \<open>c11_predef [setjmp.h]\<close>/
    \<open>c11_predef [stdarg.h]\<close> (\<open>\<section>2.6\<close>, \<open>\<section>3\<close>) can now be written faithfully,
    including the genuine glibc shape of \<open>jmp_buf\<close> itself (an array of a
    tagged struct, not the struct itself). Two narrow limitations remain: a
    typedef'd name used as the \<^emph>\<open>literal next\<close> token right after its own
    \<open>";"\<close> is not recognized (the underlying LALR(1) parser has already
    fetched that token as a plain identifier, its own required one-token
    lookahead, before the reduce that registers the name can run); and once
    registered, a name stays a typedef name for the rest of the session
    (the "single, shared, non-reentrant lexer state" item below applies
    here too), so it cannot later be redeclared as an unrelated, fresh
    typedef - matching, not violating, real C's own restriction against
    redeclaring a typedef name.
  \<^item> \<^bold>\<open>A single, shared, non-reentrant lexer state.\<close> The generated lexer
    keeps its antiquotation-comment accumulator in one shared, mutable
    structure (\<^verbatim>\<open>C11_Comments\<close>) rather than a value threaded functionally
    through parsing, a known constraint on how safely this fragment's parser
    can be invoked re-entrantly (e.g.\ from within another parse already in
    progress).
  \<^item> \<^bold>\<open>Navigation is not total.\<close> \<open>select_ast\<close>'s \<open>r\<close>/\<open>d\<close> phase (\<open>\<section>2.4\<close>) is
    defined for every \<open>cStatement\<close>/\<open>cExpression\<close> constructor, but an \<open>Id\<close> or
    \<open>Units\<close> root is never \<open>r\<close>/\<open>d\<close>-navigable at all (an identifier is always a
    leaf; a translation unit's own top-level declaration list has no
    per-element indexing defined for it), and there is no wrapping - an
    out-of-range cursor is always a hard error rather than a saturating or
    silently-clamped one.
\<close>

section\<open>Conclusion\<close>

text\<open>
  Isabelle/C, Version 2.0 reproduces the essential shape of a PIDE-integrated
  C11 front-end - inline and file-based parsing, an environment with
  declaration/use hyperlinking, and a programmable, position-aware
  antiquotation mechanism - on top of a generic, reusable ml-lex/ml-yacc
  integration, while deliberately narrowing the most complex corner of the
  original design (antiquotation navigation) down to a small, explicit set of
  primitives. What is here is a genuine, working front-end for a real subset
  of C11, suitable as the basis for a verification tool, a documentation
  generator, or a static analysis; what is documented in \<open>\<section>4\<close> as missing is,
  in every case, a scoping decision rather than an accident - room for a later
  round to broaden the preprocessor fragment, or grow \<open>select_ast\<close>'s own
  \<open>children_of\<close> table (\<open>\<section>2.4\<close>) as concrete uses demand it.

  \pagebreak
\<close>

section\<open>Annex: The C11 Grammar as Railroad Diagrams\<close>

subsection\<open>Lexical Structure\<close>

text\<open>
  The lexer (generated via \<^verbatim>\<open>ml_lex_yacc\<close> from the \<open>lex_definitions\<close>/
  \<open>lex_user_declarations\<close> blocks in \<^verbatim>\<open>C11_Parser.thy\<close>) tokenizes ordinary
  C11 lexemes - keywords, identifiers, integer/floating/character/string
  constants, punctuators - in its \<open>INITIAL\<close> state exactly as an ordinary
  hand-written C lexer would; no \<open>[expert]\<close> ml-lex mode is needed anywhere in
  it. Two auxiliary start-states, entered from \<open>INITIAL\<close> on \<open>/*\<close> and \<open>//\<close>
  respectively, handle comments:

  \<^item> \<open>COMMENT\<close> (a block comment) scans until the matching \<open>*/\<close> - a \<open>/* */\<close>
    comment does \<^emph>\<open>not\<close> nest, matching ISO C11 exactly: the first \<open>*/\<close>
    closes it, regardless of any \<open>/*\<close> that may appear inside.
  \<^item> \<open>LCOMMENT\<close> (a line comment) scans until the next newline.

  Both states share one further piece of machinery: recognizing an
  antiquotation \<open>@tag[navi](level) \<open>body\<close>\<close> (or \<open>@tag[navi](level) "body"\<close>)
  requires more than a single regular expression, since a cartouche body can
  nest arbitrarily and a plain regular expression cannot count. A small
  amount of \<open>lex_user_declarations\<close> state (a nesting-depth counter,
  \<open>antiq_tag\<close> holding the tag/navigation-list/level/position parsed so far)
  turns this into a well-defined sequence of ordinary ml-lex rules: the tag,
  an optional \<open>[navi]\<close> bracket, and an optional \<open>(level)\<close> are matched by one
  extended regular expression (below); what follows is then either a
  \<^emph>\<open>double-quoted string\<close> - matched as a single further token, since it
  cannot nest - or the start of a cartouche, entering a dedicated nested-nest-
  counting sub-state until the matching close is found. Every plain,
  non-antiquotation comment character is simply accumulated as ordinary
  \<open>Raw_txt\<close>.

  The tag/navigation/level syntax itself:

  \<^rail>\<open>
    antiquotation : '@' tag navi? level? body
    ;
    navi : '[' step* ']'
    ;
    step : 'u' | 'U' | 'r' | 'd'
    ;
    level : '(' integer ')'
    ;
    body : cartouche | '"' text '"'
  \<close>

  The \<open>[navi]\<close> bracket is its own delimiter, deliberately, rather than being
  bare-adjacent to the tag: \<open>u\<close>/\<open>U\<close>/\<open>r\<close>/\<open>d\<close> are ordinary identifier
  characters with no special lexical status of their own, and the tag itself
  is matched by a greedy identifier regular expression - without a delimiter,
  a tag that happens to \<^emph>\<open>end\<close> in one of those four letters (\<open>@answer\<close>, say)
  would be genuinely ambiguous between "the whole tag \<open>answer\<close>, no navigation"
  and "the tag \<open>answe\<close> plus a navigation step \<open>r\<close>". An absent bracket and an
  empty \<open>[]\<close> both mean an empty navigation string.
\<close>

subsection\<open>Grammar (Representative Subset)\<close>

text\<open>
  The full grammar covers every ISO C11 declaration, statement, and
  expression form; reproduced here is a representative subset - enough to
  show the overall shape - simplified in two respects relative to the actual
  ml-yacc grammar in \<^verbatim>\<open>C11_Parser.thy\<close>: operator precedence is collapsed
  into one \<open>expression\<close> rule rather than the dozen or so precedence-climbing
  non-terminals LALR(1) actually needs, and declaration-specifier / declarator
  syntax (itself close to a third of the real grammar, needed to express C's
  notoriously declarator-centred type syntax, e.g.\ function pointers and
  multi-dimensional arrays) is abbreviated to a single \<open>type\<close> place-holder.

  \<^rail>\<open>
    translation__unit : external__declaration +
    ;
    external__declaration : function__definition | declaration | pp__directive
    ;
    function__definition : type declarator compound__statement
    ;
    declaration : type (declarator ('=' initializer)? (',' declarator ('=' initializer)?)*)? ';'
    ;
    compound__statement : '{' block__item * '}'
    ;
    block__item : statement | declaration
    ;
    statement : compound__statement
              | 'if' '(' expression ')' statement ('else' statement)?
              | 'switch' '(' expression ')' statement
              | 'while' '(' expression ')' statement
              | 'do' statement 'while' '(' expression ')' ';'
              | 'for' '(' for__init expression? ';' expression? ')' statement
              | 'return' expression? ';'
              | 'break' ';' | 'continue' ';'
              | 'goto' identifier ';'
              | identifier ':' statement
              | expression? ';'
    ;
    for__init : expression? ';' | declaration
    ;
    expression : assignment__expression (',' assignment__expression)*
    ;
    assignment__expression : conditional__expression (assign__op assignment__expression)?
    ;
    conditional__expression : binary__expression ('?' expression ':' conditional__expression)?
    ;
    binary__expression : unary__expression (binary__op binary__expression)*
    ;
    unary__expression : ('&' | '*' | '+' | '-' | '~' | '!' | '++' | '--') unary__expression
                       | '(' type ')' unary__expression
                       | 'sizeof' ('(' type ')' | unary__expression)
                       | postfix__expression
    ;
    postfix__expression : primary__expression
        ( '[' expression ']'
        | '(' (assignment__expression (',' assignment__expression)*)? ')'
        | '.' identifier | '->' identifier | '++' | '--' ) *
    ;
    primary__expression : identifier | constant | string__literal | '(' expression ')'
  \<close>

  Antiquotation-carrying comments (\<open>\<section>6.1\<close>) may occur, lexically, in front of
  any token at all - they are not part of this grammar in the ordinary sense
  (no non-terminal above mentions them), since they are attached to whichever
  AST node's own \<open>nodeInfo\<close> claims them (\<open>\<section>2.3\<close>) after the fact, by
  position, rather than being parsed as part of any one production.
\<close>
(*>*)
end
(*<*)
