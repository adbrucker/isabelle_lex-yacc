(******************************************************************************
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
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 ******************************************************************************)

(*<*)
theory Scala3_Manual
  imports "Scala3.Scala3"
begin
(*>*)

section\<open>What is Isabelle/Scala 3\<close>

text\<open>
  Isabelle/Scala 3 is a front-end that lets Scala 3 source text live inside an
  Isabelle theory as a first-class citizen: parsed by a real grammar that
  follows the \<^emph>\<open>Scala 3 Syntax Summary\<close> \<^cite>\<open>"odersky.ea:scala3:2026"\<close>, checked
  incrementally under Isabelle/PIDE (so a syntax error or a malformed annotation
  is reported like any other Isabelle error, with the usual jEdit markup,
  hyperlinking and hovering), and open to attaching arbitrary Isabelle-level
  content - proof obligations, HOL terms, arbitrary Isar commands - to specific
  points of the Scala source via a comment-based antiquotation mechanism. It is
  not a Scala compiler, nor a verification tool in its own right: it is the
  \<^emph>\<open>front-end layer\<close> on which one builds a verification tool (a semantic
  backend), a documentation generator, a static analysis, or the management of
  Scala sources in the document model of Isabelle itself.
\<close>

subsection\<open>Context\<close>

text\<open>
  Scala is, next to Standard ML, the implementation language of Isabelle:
  the PIDE protocol, the build system, the jEdit plugin and the command line
  tools are written in Scala (380 source files with 93\,000 lines in the
  distribution of Isabelle2026). Isabelle treats its ML sources as part of
  its document model - they are edited, checked and navigated within theories
  - but its Scala sources are plain files outside of it. A front-end for Scala
  that provides an abstract syntax tree with source positions, a notion of
  declaration and use, and a hook for annotations is the first step towards
  closing that gap.

  Unlike Rust, Scala 3 does have a specification of its syntax: the \<^emph>\<open>Syntax
  Summary\<close> of the language reference, an EBNF grammar. What makes it hard to
  turn into an LALR grammar is not missing information but three features of the
  language that a context-free grammar over a stream of tokens cannot express:

  \<^item> \<^bold>\<open>Newlines are statement separators\<close> - when the token before can end a
    statement, the token after can begin one, and the newline is not inside
    parentheses. This is the same problem as the offside rule of occam 2,
    solved in the same way, by a stream between lexer and parser
    (\<open>\<section>2.1\<close>).
  \<^item> \<^bold>\<open>Soft keywords\<close>: \<open>given\<close>, \<open>using\<close>, \<open>extension\<close>, \<open>inline\<close>, \<open>opaque\<close>, \<open>open\<close>,
    \<open>infix\<close>, \<open>transparent\<close>, \<open>as\<close> are keywords only in certain positions and
    ordinary identifiers elsewhere (\<open>end\<close> and \<open>derives\<close> as well, in the full
    language).
  \<^item> \<^bold>\<open>Significant indentation\<close>: a block may be written without braces. This is
    \<^emph>\<open>not\<close> covered by Isabelle/Scala 3 (\<open>\<section>6\<close>). The decision is informed by a
    survey of the 380 Scala sources of Isabelle: they are written in the brace
    style, use \<open>enum\<close> (27 times), \<open>extension\<close> (4), \<open>given\<close> (2) and \<open>using\<close> (1),
    and none of \<open>opaque\<close>, \<open>transparent\<close>, \<open>infix\<close> modifiers, \<open>derives\<close>, context
    functions, type lambdas, match types, macros, end markers or optional
    braces. The soft keywords \<open>extension\<close> and \<open>using\<close> matter; \<open>end\<close>, on the
    other hand, is an ordinary identifier all over the place (\<open>end: Int\<close>,
    \<open>end.shortcut\<close>).

  Isabelle/Scala 3 is the third language front-end built on the design of
  \<^bold>\<open>Isabelle/C, Version 2.0\<close>, which this repository's \<^verbatim>\<open>C11/\<close> folder contains
  \<^cite>\<open>"tuong.ea:isabellec:2019" and "tuong.ea:deeply:2019"\<close>, after C11 itself and
  occam 2. It is built from the same parts and carries the same concepts over
  one for one: the \<^verbatim>\<open>ml_lex_yacc\<close> command of this repository (an ML-Lex/ML-Yacc
  integration \<^cite>\<open>"appel.ea:lexical:1994" and "tarditi.ea:ml-yacc:2000"\<close>) generates
  lexer and parser; every node of the abstract syntax tree carries a source
  position plus the comments and antiquotations attached to it; a per-theory
  environment tracks the declared names for declaration/use hyperlinking;
  programmable handlers, a navigation language and an evaluation order give
  meaning to the antiquotations; and a family of Isar commands (\<open>scala3\<close>,
  \<open>scala3_file\<close>, \<open>scala3_expr\<close>, \<open>\<dots>\<close>) drive all of it. Someone who knows the C11
  manual will find the same structure in this one, and the same names with \<open>c11\<close>
  replaced by \<open>scala3\<close>, \<open>cenv\<close> by \<open>senv\<close>, and \<open>CEnv\<close> by \<open>SEnv\<close>. Like the other
  members it is \<^emph>\<open>re-entrant\<close>: it is built with \<open>ml_lex_yacc [state]\<close>, every
  parse has a state object of its own, and any number of parses may run at the
  same time.

  What differs is dictated by the language and takes up most of the
  remainder: the layout and the operators (\<open>\<section>2.1\<close>), the two name spaces and the
  scoping rules of Scala (\<open>\<section>2.2\<close>), and the shape of the abstract syntax, in
  which almost everything is an expression (\<open>\<section>4\<close>).
\<close>

section\<open>Main Features of Isabelle/Scala 3\<close>

text\<open>
  Four pieces fit together to give the \<open>scala3\<close>-family commands (\<open>\<section>3\<close>) their
  behaviour: a lexer and parser that produce a real AST with genuine source
  positions at every node (\<open>\<section>2.1\<close>); a per-theory environment tracking every
  declared name, used to hyperlink each name \<^emph>\<open>use\<close> back to its declaration
  (\<open>\<section>2.2\<close>); a mechanism for attaching programmable content to a specific AST
  node via a comment (\<open>\<section>2.3\<close>); and a well-defined order and navigation language
  governing exactly \<^emph>\<open>which\<close> node an antiquotation resolves to and \<^emph>\<open>when\<close> it runs
  (\<open>\<section>2.4\<close>).
\<close>

subsection\<open>Parsing, Layout and Operators\<close>

text\<open>
  The grammar (\<^verbatim>\<open>Scala3_Parser.thy\<close>) is an ordinary LALR(1) ml-yacc grammar that
  covers the brace-delimited language of the Syntax Summary:

  \<^item> \<^bold>\<open>definitions\<close>: \<open>val\<close>, \<open>var\<close>, \<open>def\<close> (with type, term and using/implicit
    parameter clauses), \<open>type\<close> (aliases, abstract types, bounds, higher-kinded
    parameters), \<open>class\<close>, \<open>trait\<close>, \<open>object\<close>, \<open>case class\<close>, \<open>case object\<close>, \<open>enum\<close>
    with its cases, \<open>given\<close> (named, anonymous, with a body), \<open>extension\<close> (with
    its methods), \<open>package\<close> clauses and package objects; with annotations and
    all the modifiers (\<open>private[x]\<close>, \<open>protected\<close>, \<open>sealed\<close>, \<open>abstract\<close>, \<open>final\<close>,
    \<open>override\<close>, \<open>implicit\<close>, \<open>lazy\<close>, \<open>inline\<close>, \<open>opaque\<close>, \<open>open\<close>, \<open>transparent\<close>,
    \<open>infix\<close>);
  \<^item> \<^bold>\<open>imports and exports\<close> with selectors (\<open>{a, b => c, given, _}\<close>, \<open>*\<close>);
  \<^item> \<^bold>\<open>expressions\<close>: literals, paths, \<open>this\<close>/\<open>super\<close>, application (also with named
    and \<open>using\<close> arguments), type application, infix, prefix and postfix
    operators, assignment, ascription, annotated and splat expressions, lambdas
    (also context lambdas), blocks, \<open>if\<close>/\<open>while\<close>/\<open>try\<close>/\<open>throw\<close>/\<open>return\<close>, \<open>for\<close>
    with \<open>yield\<close> (generators, guards, value definitions), \<open>match\<close> and pattern
    matching anonymous functions, \<open>new\<close> with a template body, tuples,
    placeholders;
  \<^item> \<^bold>\<open>patterns\<close>: wildcard, variables, literals, stable identifiers, extractor
    patterns, infix patterns, alternatives, binders \<open>x @ p\<close>, typed patterns,
    given patterns;
  \<^item> \<^bold>\<open>types\<close>: paths and selections, singleton types, projections, applications,
    tuples, function and context-function types, by-name and repeated
    parameter types, infix types and \<open>with\<close>, refinements, annotated types,
    wildcard types with bounds, type lambdas and polymorphic function types,
    match types.

  \<^bold>\<open>Statement separators.\<close> Scala has no statement terminator token in its lexical
  grammar. A newline \<^emph>\<open>is\<close> a separator when the token before it can end a
  statement (an identifier, a literal, \<open>this\<close>, \<open>null\<close>, \<open>true\<close>, \<open>false\<close>,
  \<open>return\<close>, \<open>type\<close>, \<open>_\<close>, a closing bracket, the wildcard \<open>*\<close> of an import), the
  token after it can begin one (everything but \<open>catch else extends finally match
  with yield\<close>, the separators and the closing brackets, and the arrows), and the
  newline is not inside parentheses or brackets. Newlines are enabled inside
  braces, and disabled again between \<open>case\<close> and its \<open>=>\<close>. The lexer cannot
  decide this alone, as it depends on the nesting, so it only \<^emph>\<open>records\<close> facts
  per token (\<open>Scala3_Layout\<close>: the number of newlines before it, its kind, its
  extent) and a stream between lexer and parser (\<open>Scala3_Parse.layout_stream\<close>)
  keeps a stack of the open brackets and inserts a \<open>NEWLINE\<close> token where the
  rules say so. Two refinements of Scala are implemented: a line that starts
  with an infix operator followed by an operand on the same line continues the
  previous line (a \<^emph>\<open>leading infix operator\<close>), and a single newline before \<open>{\<close> is
  ignored (the rule that lets \<open>f\<close> and \<open>{ \<dots> }\<close> on separate lines form an
  application).

  \<^bold>\<open>Disambiguating \<open>case\<close>.\<close> The keyword \<open>case\<close> begins a match clause, a generator
  (\<open>for (case p <- e)\<close>) or an enum case, depending on what follows. The stream
  looks ahead (outside nested brackets, up to the end of the logical line)
  for a \<open>=>\<close> or a \<open><-\<close> and delivers a distinct token, \<open>CASE\<close> or \<open>ENUMCASE\<close> (and
  \<open>CASEMOD\<close> for \<open>case class\<close> and \<open>case object\<close>).

  \<^bold>\<open>Operators.\<close> Scala has no operator declarations: the precedence of an infix
  operator is given by its first character, its associativity by its last (a
  colon makes it right-associative). The lexer classifies each operator token
  accordingly (nine classes, from \<open>|\<close> through \<open>^ & = ! < > :\<close>, \<open>+ -\<close> and \<open>* / %\<close>
  to all other symbols) and the yacc grammar declares the nine precedence
  levels; the alphanumeric operators are identifiers. One simplification: every
  operator that ends in a colon (\<open>::\<close>, \<open>+:\<close>, \<open>/:\<close>) is right-associative \<^emph>\<open>at the
  level of \<open>::\<close>\<close>, not at the level of its own first character.

  \<^bold>\<open>Soft keywords.\<close> The lexer emits distinct tokens for \<open>as\<close>, \<open>extension\<close>,
  \<open>infix\<close>, \<open>inline\<close>, \<open>opaque\<close>, \<open>open\<close>, \<open>transparent\<close> and \<open>using\<close>; the grammar's
  \<open>name\<close> accepts all of them in the place of an identifier, and the LALR(1)
  look-ahead decides what a given occurrence is. \<open>end\<close> and \<open>derives\<close> are plain
  identifiers.

  \<^bold>\<open>Strings.\<close> Plain, multi-line (\<open>"""\<close>) and interpolated strings (\<open>s"\<dots>"\<close>,
  \<open>f"""\<dots>"""\<close>) are single tokens. The embedded expressions \<open>${\<dots>}\<close> of an
  interpolated string are skipped over (balanced, with nested strings and
  characters) but not parsed; the token carries the raw text.

  \<^bold>\<open>Positions and comments.\<close> Every node carries the exact source range of its
  text; a name carries the range of the name. Comments nest in Scala. They, and
  the antiquotations among them (\<open>\<section>2.3\<close>), are not part of the grammar: the lexer
  collects them and attaches them to the node of the next real token.

  A first example: an \<open>enum\<close>, an \<open>extension\<close> with a method, a \<open>given\<close> and a
  method with a \<open>using\<close> clause, in the brace style, with newlines as separators:
\<close>

scala3\<open>
enum Color {
  case Red, Green
  case Rgb(r: Int, g: Int, b: Int)
}

extension (c: Color) {
  def isRed: Boolean = c match {
    case Color.Red => true
    case _ => false
  }
}

given Ordering[Color] = Ordering.by(_.ordinal)

def sorted(cs: List[Color])(using ord: Ordering[Color]): List[Color] =
  cs.sorted(using ord)
\<close>

text\<open>
  Soft keywords are identifiers where Scala wants them to be: \<open>end\<close>, \<open>open\<close>,
  \<open>inline\<close> and \<open>using\<close> are used as names below, and a line that starts with an
  operator continues the previous one:
\<close>

scala3\<open>
class Range(val start: Int, val end: Int) {
  def open = start
  def inline(using: Int) = using + end
  def total = start
    + end
    + inline(open)
}
\<close>

subsection\<open>The Scala 3 Environment, and Declaration/Use Navigation\<close>

text\<open>
  \<^verbatim>\<open>Scala3_Env.thy\<close> defines \<open>senv\<close>, the counterpart of C11's \<open>cenv\<close>: a record
  stored as ordinary \<^verbatim>\<open>Generic_Data\<close>, so that it persists across commands
  within a theory and merges correctly under Isabelle's parallel, incremental
  checking. It holds

  \<^enum> \<open>terms\<close> and \<open>types\<close>, the declared names of Scala's two name spaces, each with
    what it was declared as (a value, a variable, a method, a parameter, a
    pattern variable, an object, a class or type, an enum case, a given, an
    imported name);
  \<^enum> \<open>scala_antiq\<close>, the registry of antiquotation handlers (\<open>\<section>2.3\<close>); and
  \<^enum> a per-theory unit counter, used to name the sections processed by a \<open>scala3\<close>
    command.

  Scala has \<^emph>\<open>two\<close> name spaces. A class, trait, enum, type alias or type
  parameter lives in \<open>types\<close>; a value, variable, method, parameter, pattern
  variable, object or enum case in \<open>terms\<close>; a \<open>case class\<close>, an \<open>enum\<close> and an
  \<open>object\<close> (the companion) declare a name in both.

  \<^verbatim>\<open>Scala3_AnaEval.thy\<close>'s \<open>analyse_and_eval\<close> is a single, purely functional,
  scoped walk over a parsed root that fills \<open>senv\<close> as it goes. Every name \<^emph>\<open>use\<close>
  is hyperlinked to its declaration via \<^ML>\<open>Position.entity_markup\<close>, reported
  once at the declaration site and once at every use. \<^bold>\<open>A name that resolves
  nowhere is not marked\<close> - unlike C11 and occam 2, where it is underlined. In
  Scala a name routinely comes from the standard library, a wildcard import or
  a member inherited from a parent class, none of which this pass sees;
  underlining them would drown the useful markup. A member selection \<open>e.f\<close> is
  not resolved either (that needs types); only \<open>e\<close> is. The \<^emph>\<open>scoping rules\<close> are
  those of Scala, implemented as shadow-and-restore (the environment is a
  value; a scope simply does not hand its extension back):

  \<^item> A block is a scope. A local \<open>val\<close> is visible only \<^emph>\<open>after\<close> its definition;
    local methods, classes, objects and types are visible throughout the block
    (local functions may be mutually recursive).
  \<^item> The members of a template (a class, trait, object or enum body), and the top
    level of a compilation unit, are visible throughout it: a method may call
    one defined further down, a \<open>val\<close> may be used by an earlier method.
  \<^item> A method: its type parameters, then each parameter clause in turn (a later
    clause may mention an earlier parameter), then the body. A class: type
    parameters, constructor parameters, the template.
  \<^item> A lambda, and a \<open>case\<close> clause (its pattern variables are visible in the guard
    and the body). A \<open>for\<close> comprehension: a generator's variables are visible in
    the following enumerators and in the body.
  \<^item> A lone name in a pattern is a \<^emph>\<open>variable\<close> if it starts with a lower-case
    letter (or \<open>_\<close>), and otherwise a stable identifier - a \<^emph>\<open>use\<close> -, exactly as
    in the language definition; the same applies to \<open>val\<close> patterns, except that
    \<open>val A = 1\<close> defines \<open>A\<close>.
  \<^item> An import registers the imported names, in both name spaces, at their
    selector (the renamed name for \<open>b => c\<close>); a use is hyperlinked to it. A
    wildcard import registers nothing.
  \<^item> A compilation unit is the one root whose names \<^emph>\<open>persist\<close>: after \<open>scala3\<close> has
    analysed it, its top-level names stay in \<open>senv\<close> for the following units, as
    the members of a package do.

  Being persistent per-theory data - the same idiom a simp set uses - is what
  lets Scala fragments be freely \<^emph>\<open>interleaved\<close> with arbitrary Isar content and
  still resolve a name used in one fragment back to its declaration in an
  earlier one. The flip side is that \<open>senv\<close> only ever grows across a theory; the
  commands \<open>set_senv_default\<close> and \<open>reset_senv\<close> (\<open>\<section>3\<close>) give a theory explicit
  control. A small example of the persistence and the scoping rules (hover over
  the names in jEdit):
\<close>

scala3\<open>
object Lib {
  def twice(n: Int): Int = n * 2
}

val LIMIT = 100
\<close>

scala3\<open>
val total = Lib.twice(LIMIT)
\<close>

text\<open>
  A template's members are visible throughout it, a block's \<open>val\<close> only after
  its definition, and a pattern variable only in its clause. The names \<open>Some\<close>
  and \<open>unknown\<close> resolve nowhere and are not marked:
\<close>

scala3\<open>
class Shape {
  def area: Int = width * height
  val width = 2
  val height = 3
}

def classify(o: Option[Int]): Int = {
  val y = helper(1)
  o match {
    case Some(v) => v + y
    case _ => unknown
  }
}

def helper(n: Int): Int = n
\<close>

subsection\<open>Programmable Scala-Antiquotations, and Handlers\<close>

text\<open>
  A comment of the shape \<open>@tag[navi](level) \<open>body\<close>\<close> - an \<open>@\<close>-prefixed tag, an
  optional bracketed navigation string (\<open>\<section>2.4\<close>), an optional parenthesised
  integer \<open>level\<close> (\<open>0\<close> when omitted), and a body written as a nested Isabelle
  cartouche or, equivalently, a double-quoted string - is recognised lexically
  inside a \<open>//\<close> or \<open>/* \<dots> */\<close> comment, and attached to whichever AST node it
  resolves against (\<open>\<section>2.4\<close>). The cartouche may span several lines, which a \<open>//\<close>
  comment cannot. Any other comment is kept as plain text (\<open>Raw_txt\<close>). A comment
  is attached to the AST node that begins at the \<^emph>\<open>next real token\<close>, so an
  annotation is written on the line(s) \<^emph>\<open>above\<close> what it annotates:

  \<^verbatim>\<open>//@ highlight\<close>

  (a tag alone is a complete antiquotation with an empty body). As the Scaladoc
  tags (\<open>@param\<close>, \<open>@return\<close>, \<open>\<dots>\<close>) look exactly like bodyless antiquotation tags,
  a \<^emph>\<open>bodyless\<close> tag is recognised only directly after the comment opener (\<open>//@\<close>,
  \<open>/*@\<close>); a tag \<^emph>\<open>followed by a body\<close> is one anywhere in a comment. Documentation
  comments are therefore plain comments.

  The \<open>tag\<close> selects a \<^emph>\<open>handler\<close>: an ordinary ML function of type

  \<^verbatim>\<open>type type_antiq_fun =
    senv * pos Scala3_Ast.root * int -> (string * pos) ->
    Context.generic -> Context.generic\<close>

  registered once, ahead of time, via \<open>SEnv.store_antiq (tag, handler)\<close>. When
  \<open>analyse_and_eval\<close> reaches a node carrying an \<open>@tag \<dots>\<close> antiquotation, it
  resolves the navigation string against the closest-surrounding-context stack
  (\<open>\<section>2.4\<close>) into a single concrete \<open>root\<close> value, then instantiates the handler
  with \<open>(senv, resolved_root, level)\<close> and the body text together with its own
  source position; a handler is never itself responsible for interpreting
  \<open>u\<close>/\<open>U\<close>/\<open>r\<close>/\<open>d\<close>.

  \<open>Context.generic\<close> rather than \<open>theory\<close>, deliberately: a handler may do
  anything a genuine Isar toplevel command can, including running real ML code
  at the ML environment level (the \<open>ML\<close> antiquotation, below). All collected
  actions are folded into one \<open>Context.generic -> Context.generic\<close> function by
  ordinary composition and lifted to the toplevel exactly once, at the end
  (\<open>full_eval_and_store\<close> in \<^verbatim>\<open>Scala3.thy\<close>). Most handlers never need this
  generality: an ordinary \<open>theory -> theory\<close> function is \<^emph>\<open>recaptured\<close> by
  \<open>SEnv.lift_theory_antiq\<close> when it is registered. A first handler, which turns a
  plain comment into a checked diagnostic reported against the exact node the
  comment resolves to:
\<close>

ML\<open>
val todo_antiq =
  let
    fun handler (_ : SEnv.senv, ast, level) (body, _ : Position.T) thy =
      (warning ("TODO (level " ^ Int.toString level ^ ") at " ^
                Position.here (AnaEval.pos_of_root ast) ^ ": " ^ body);
       thy)
  in SEnv.store_antiq ("todo", SEnv.lift_theory_antiq handler) end
\<close>
setup\<open>todo_antiq\<close>

scala3\<open>
object Counter {
  var n = 0
  //@ todo \<open>check the overflow of n\<close>
  def inc(): Unit = { n += 1 }
}
\<close>

text\<open>
  A tag with no registered handler is a hard error: every tag that can appear
  in a theory's source must be registered before that theory's
  \<open>scala3\<close>-family commands run.
\<close>

subsection\<open>Execution (Order, Navigation, etc.)\<close>

text\<open>
  \<^bold>\<open>Order.\<close> A unit can carry several antiquotations whose handlers have side
  effects that depend on one another (a \<open>definition\<close> must precede the \<open>lemma\<close>
  that mentions it). \<open>level\<close> is the author's explicit ordering knob:
  \<open>full_eval_and_store\<close> collects every \<open>(level, action)\<close> pair the walk produces,
  sorts by \<open>level\<close> - a stable sort, so equal levels keep their textual order -
  and chains them, each against the context the previous one produced. A
  physical antiquotation is dispatched \<^emph>\<open>exactly once\<close>, no matter how many AST
  nodes share its leftmost source position (the classic case in Scala: an infix
  expression, its left operand and the operand's name all begin at the same
  token).

  \<^bold>\<open>Context.\<close> Every antiquotation resolves, by default, to its \<^emph>\<open>closest
  surrounding context\<close>: the walk threads a stack of enclosing nodes.
  Expressions, types, patterns and definitions and imports (a statement other
  than an expression statement) push themselves on that stack, at every level
  of nesting; the root type has the variants \<open>Expr\<close>, \<open>Type\<close>, \<open>Pat\<close>, \<open>Stat\<close> in
  addition to \<open>Id\<close> for a bare name and \<open>Unit\<close> for a compilation unit. Everything
  else - case clauses, enumerators, parameters, parents, selectors, template
  bodies - never pushes and resolves to what is on top, which is what makes
  every node kind a valid place for a comment.

  \<^bold>\<open>Navigation.\<close> The bracketed \<open>[navi]\<close> string points an antiquotation \<^emph>\<open>away\<close>
  from its closest context. Its syntax and its rules are exactly those of C11:
  written \<open>(u|U)*(r|d)*\<close>, zero or more ascend steps followed by zero or more
  descend steps. \<open>u\<close> ascends one level (a lone, final \<open>u\<close> is a no-op); \<open>U\<close>
  ascends past a whole run of consecutive ancestors of the same category; \<open>r\<close>
  advances a 1-based cursor among the current node's children in source order
  and \<open>d\<close> descends into the child at the cursor (cursor 1 if no \<open>r\<close> preceded
  it). There is no wrapping: a cursor beyond the children, or \<open>d\<close> on a leaf, is
  a hard error reported at the antiquotation's own tag position. The children of
  a node, in source order, are its sub-expressions, sub-types, sub-patterns and
  sub-definitions; nodes without a \<open>root\<close> counterpart (parameters, clauses,
  parents, selectors) are flattened into their parent's list or dropped, and an
  expression statement is its expression. A few examples (the node a handler
  receives, on the expression \<open>x + y\<close> in a block):

  \<^item> no navigation: the expression \<open>x + y\<close> itself;
  \<^item> \<open>[d]\<close> or \<open>[rd]\<close>: its first child, \<open>x\<close>; \<open>[rrd]\<close>: its second child, \<open>y\<close>;
  \<^item> \<open>[uu]\<close>: the enclosing definition.

\<close>

scala3\<open>
def sum(x: Int, y: Int): Int = {
  //@ probe_ast[rrd]
  //@ highlight[rrd]
  x + y
}
\<close>

ML\<open>
val _ = if Scala3_Pp.pp_root (!SCALA_AST) = "y"
        then writeln "[rrd] reaches the second operand"
        else error "navigation"
\<close>

subsection\<open>Standard Antiquotations\<close>

text\<open>
  \<^verbatim>\<open>Scala3_AnaEval.thy\<close> registers the same eight demonstration antiquotations
  as C11. All of them are written in a comment and see the node their
  navigation string selects:

  \<^descr> \<open>probe_senv\<close> stores the current \<open>senv\<close> into an ML reference (\<open>OENV\<close>) for
    inspection.
  \<^descr> \<open>probe_ast\<close> prints the resolved node, pretty-printed back to Scala, with
    its level, and stores it into \<open>SCALA_AST\<close>.
  \<^descr> \<open>highlight\<close> marks the resolved node's source range in the editor - the
    quickest way to \<^emph>\<open>see\<close> what a navigation string selects.
  \<^descr> \<open>term \<open>t\<close>\<close> reads \<open>t\<close> as a HOL term in the theory's current context; a
    malformed or ill-typed term is a real Isabelle error positioned inside the
    Scala comment.
  \<^descr> \<open>ML \<open>code\<close>\<close> runs \<open>code\<close> as ML source, so a definition written in a Scala
    comment becomes a later-visible ML binding.
  \<^descr> \<open>text \<open>t\<close>\<close> runs \<open>t\<close> through the document machinery of Isabelle's \<open>text\<close>
    command, so that inner antiquotations are checked and hyperlinked (the
    result is stashed, not typeset; see \<open>\<section>6\<close>).
  \<^descr> \<open>definition \<open>d\<close>\<close> is Isabelle's \<open>definition\<close> command: the new constant is a
    genuine, later-visible theory constant.
  \<^descr> \<open>lemma \<open>l\<close>\<close> states \<open>l\<close> and proves it with one terminal \<open>by\<close> proof -
    proof-carrying code: a formal property of the program's constants,
    \<^emph>\<open>actually proved\<close>, right where the Scala text that motivates it lives. A
    failed proof is an Isabelle error positioned in the comment.

\<close>

section\<open>The Scala 3 Main Commands\<close>

text\<open>

  \<^descr> \<open>scala3 \<open>\<dots>\<close>\<close> parses its argument as a compilation unit - a sequence of
    statements: packages, imports, definitions, expressions - runs
    \<open>analyse_and_eval\<close>, chains the collected antiquotation actions in level
    order, and stores the AST under a fresh key, reported as
    \<open>[stored as Theory#N]\<close>.
  \<^descr> \<open>scala3_file \<open>path\<close>\<close> is the same, reading the unit from an external file
    (resolved relative to the theory's master directory via
    \<^ML>\<open>Resources.parse_file\<close>, so file positions and build-dependency tracking
    come for free).
  \<^descr> \<open>scala3_expr \<open>\<dots>\<close>\<close>, \<open>scala3_type \<open>\<dots>\<close>\<close> and \<open>scala3_ident \<open>\<dots>\<close>\<close> parse a bare
    expression, type, respectively name. The analysis still runs, for its
    hyperlinks, but its antiquotation actions are discarded: a standalone
    fragment is a syntax check, not a program.
  \<^descr> \<open>scala3_reject\<close>, \<open>scala3_expr_reject\<close>, \<open>scala3_type_reject\<close> and
    \<open>scala3_ident_reject\<close> document a fragment as correctly \<^emph>\<open>not\<close> accepted by the
    corresponding entry point. They are silent (no error markup is left on the
    expected failure) and are the means of writing negative tests.
  \<^descr> \<open>set_senv_default\<close> and \<open>reset_senv\<close> control the ever-growing \<open>senv\<close>.
    \<open>set_senv_default\<close> nominates what \<open>senv\<close> holds \<^emph>\<open>right now\<close> as the snapshot a
    later \<open>reset_senv\<close> restores; with no earlier \<open>set_senv_default\<close> in scope
    \<open>reset_senv\<close> falls back to the empty \<open>senv\<close>. \<^verbatim>\<open>Scala3.thy\<close> itself nominates,
    as its last step, the environment holding exactly the standard antiquotation
    handlers.
  \<^descr> \<open>setup_backend \<open>f\<close>\<close> installs the \<^emph>\<open>semantic backend\<close>: \<open>f\<close> is an ML expression
    of type \<open>Position.T Scala3_Ast.root -> theory -> theory\<close>, evaluated like the
    argument of Isabelle's own \<open>setup\<close> command. At the very end of every
    \<open>scala3\<close> and \<open>scala3_file\<close> - after the antiquotation actions have run and
    the AST is stored - the installed function is applied to the parsed root and
    the theory the command has produced, and its result is the theory the
    command returns; the fragment commands never trigger it. The default is \<open>K
    I\<close>, which \<open>setup_backend \<open>K I\<close>\<close> restores. The function is kept in the
    theory's context (separately from \<open>senv\<close>, so \<open>reset_senv\<close> does not uninstall
    it) and is inherited by later theories.
  \<^descr> \<open>scala3_export \<open>path\<close> exports \<open>key\<^sub>1\<close> \<open>\<dots>\<close> \<open>key\<^sub>n\<close>\<close> renders previously stored
    sections - given by the store keys the accepting commands report - back to
    Scala text with \<^ML>\<open>Scala3_Pp.pp_root\<close> and writes them to \<open>path.scala\<close>. With
    \<open>[verbatim]\<close> after the command name the original source text is written
    instead of the (deliberately simple, canonical, brace-style)
    pretty-printer's.

  The accepting commands are \<open>thy_decl\<close> commands, because they change theory
  data (\<open>scala3_file\<close> is \<open>thy_load\<close>, so that Isabelle tracks the file
  dependency); the \<open>_reject\<close> commands, which store nothing, are \<open>diag\<close>. Isabelle
  evaluates a \<open>diag\<close> command asynchronously, in parallel with the commands that
  follow; that is harmless here, because every parse has its own state (\<open>\<section>2.1\<close>).
\<close>

subsection\<open>A Worked Example\<close>

text\<open>
  A constant of the Scala program mirrored in HOL, and a fact about it proved
  where the program is. The first annotation introduces a HOL constant (a
  \<open>definition\<close>, evaluated at level 0), the second proves a fact about it (level
  1, so after the definition), the third checks a HOL term mentioning it
  (level 2).
\<close>

scala3\<open>
// A constant of the Scala program, mirrored in HOL:
//@ definition \<open>bound :: nat where "bound = 100"\<close>
//@ lemma(1) \<open>bound_double: "bound * 2 = 200" by (simp add: bound_def)\<close>
//@ term(2) \<open>bound + 1\<close>
val bound = 100

def countUp(): Int = {
  var i = 0
  while (i < bound) { i += 1 }
  i
}
\<close>

thm bound_def bound_double

subsection\<open>Source Files, Backends, Export\<close>

text\<open>
  \<open>scala3_file\<close> reads an external file (here two units of this repository's
  examples: an \<open>enum\<close>, an \<open>extension\<close>, a \<open>given\<close>, pattern matching and a \<open>for\<close>
  comprehension; then a class using what the first declared) and stores its
  AST; the names of a unit are visible to the following ones.
\<close>

scala3_file \<open>../examples/Lists.scala\<close>

scala3_file \<open>../examples/Pipeline.scala\<close>

text\<open>
  A semantic backend is an ML function installed with \<open>setup_backend\<close>. The
  following one only counts the top-level statements of every unit it is
  applied to; a real backend would translate them. It is applied to the
  \<^emph>\<open>parsed root\<close> and the theory, after the annotations have run:
\<close>

ML\<open>
val stat_counts = Unsynchronized.ref ([] : int list)
\<close>

setup_backend\<open>fn root => fn thy =>
  (case root of
     Scala3_Ast.Unit stats => (stat_counts := length stats :: !stat_counts; thy)
   | _ => thy)\<close>

scala3\<open>
val a = 1
def f(x: Int) = x + a
class C
\<close>

setup_backend\<open>K I\<close>

ML\<open>
val _ = writeln ("top-level statements per unit seen by the backend: " ^
                 commas (map Int.toString (rev (!stat_counts))))
\<close>

text\<open>
  An accepted unit can be written back as Scala, in the canonical brace layout
  of the pretty-printer (or, with \<open>[verbatim]\<close>, as it was written). The key of a
  unit is the one the command reported when it was stored:
\<close>

scala3\<open>
def id(x: Int): Int = x
\<close>

ML\<open>
val key_of_last =
  let val SEnv.mk {units, ...} = SEnv.get (Context.Theory @{theory})
  in SEnv.ast_store_key @{theory} (units - 1) end
val _ = writeln ("the last unit is stored as " ^ key_of_last)
\<close>

section\<open>The Abstract Syntax\<close>

text\<open>
  There is no pre-existing reference AST for Scala to port, unlike C11, whose
  AST is a pruned port of the Haskell \<^verbatim>\<open>language-c\<close> tree. The AST in
  \<^verbatim>\<open>scala3_ast.ML\<close> is therefore an educated design of this project: one datatype
  per syntactic category of the Syntax Summary, one constructor per
  alternative, close enough to the concrete syntax that \<^ML>\<open>Scala3_Pp.pp_root\<close>
  can print any parsed program back as Scala. Layout is \<^emph>\<open>not\<close> part of it: the
  stream turns newlines into explicit tokens, and the printer regenerates a
  canonical brace layout (two spaces, one statement per line, braces always).
  Parentheses \<^emph>\<open>are\<close> part of it (\<open>EParen\<close>), so the printer needs no precedence
  reasoning. All datatypes are parametrised by the position type \<open>'a\<close>
  (instantiated with \<^verbatim>\<open>Position.T\<close>), and every constructor but the pure wrappers
  carries a \<open>'a nodeInfo\<close> as its last field.

  \<^bold>\<open>Annotations\<close>, shared with C11 and so with everything built on it: \<open>nodeInfo\<close>
  is a bare position or a position with the comments attached; a \<open>comment\<close> is
  raw text or an antiquotation (tag, navigation steps, level, cartouche with
  its position); \<open>ident\<close> is a name with its \<open>nodeInfo\<close>.

  \<^bold>\<open>Syntactic categories\<close> (the constructors are those of \<^verbatim>\<open>scala3_ast.ML\<close>; the
  prefix \<open>s\<close> stands for ``Scala''):

  \<^item> \<open>sExpr\<close>: \<open>EIdent\<close>, \<open>ESelect\<close>, \<open>EThis\<close>, \<open>ESuper\<close>, \<open>ELit\<close> (\<open>sLit\<close>: \<open>LInt\<close>,
    \<open>LFloat\<close>, \<open>LChar\<close>, \<open>LString\<close>, \<open>LInterp\<close>, \<open>LBool\<close>, \<open>LNull\<close>), the applications
    \<open>EApply\<close> (with \<open>sArg\<close>: plain or named arguments, and a flag for \<open>using\<close>) and
    \<open>ETypeApply\<close>, the operators \<open>EInfix\<close>, \<open>EPrefix\<close>, \<open>EPostfix\<close>, \<open>EAssign\<close>, the
    annotations \<open>ETyped\<close>, \<open>EAnnotated\<close>, \<open>ESplat\<close>, \<open>ELambda\<close>, \<open>EBlock\<close>, \<open>ECases\<close>
    (a pattern matching anonymous function), the control constructs \<open>EIf\<close>,
    \<open>EWhile\<close>, \<open>ETry\<close>, \<open>EThrow\<close>, \<open>EReturn\<close>, \<open>EFor\<close> (with \<open>sEnum\<close>: \<open>EnGen\<close>,
    \<open>EnGuard\<close>, \<open>EnVal\<close>), \<open>EMatch\<close> (with \<open>sCase\<close>), \<open>ENew\<close>, \<open>ETuple\<close>, \<open>EParen\<close>,
    \<open>EPlaceholder\<close>.
  \<^item> \<open>sType\<close>: \<open>TName\<close>, \<open>TSelect\<close>, \<open>TSingleton\<close>, \<open>TProject\<close>, \<open>TApply\<close>, \<open>TTuple\<close>,
    \<open>TFun\<close>, \<open>TByName\<close>, \<open>TRepeated\<close>, \<open>TInfix\<close>, \<open>TWith\<close>, \<open>TRefine\<close>, \<open>TAnnot\<close>,
    \<open>TWild\<close> (with \<open>sTypeBounds\<close>), \<open>TLit\<close>, \<open>TLambda\<close>, \<open>TPolyFun\<close>, \<open>TMatch\<close> (with
    \<open>sTypeCase\<close>).
  \<^item> \<open>sPat\<close>: \<open>PVar\<close> (a lower-case binder), \<open>PWild\<close>, \<open>PLit\<close>, \<open>PRef\<close> (a stable
    identifier), \<open>PApply\<close>, \<open>PTuple\<close>, \<open>PInfix\<close>, \<open>PAlt\<close>, \<open>PBind\<close>, \<open>PTyped\<close>,
    \<open>PSplat\<close>, \<open>PGiven\<close>.
  \<^item> \<open>sDef\<close>: \<open>DVal\<close>, \<open>DDef\<close>, \<open>DType\<close>, \<open>DClass\<close> (with a \<open>classKind\<close>: class, trait,
    object, enum, case class, case object, package object), \<open>DGiven\<close>,
    \<open>DExtension\<close>, \<open>DEnumCase\<close>, \<open>DPackage\<close>; with the pieces \<open>sTypeParam\<close>,
    \<open>sParam\<close>, \<open>sClause\<close> (parameter clauses: plain, \<open>using\<close>, \<open>implicit\<close>; type
    clauses), \<open>sAnnot\<close>, \<open>modifier\<close>, \<open>sParent\<close>, \<open>sSelf\<close>, \<open>sTemplateBody\<close>.
  \<^item> \<open>sStat\<close>: \<open>SExpr\<close>, \<open>SImport\<close> (with \<open>sImport\<close> and \<open>sSelector\<close>) and \<open>SDef\<close>.
  \<^item> \<open>root\<close>: the result of a parse by entry point - \<open>Id\<close>, \<open>Expr\<close>, \<open>Type\<close> or \<open>Unit\<close>
    - plus \<open>Stat\<close> and \<open>Pat\<close>, never produced by a parse but used by the
    analysis as the closest context of an annotation on a definition or a
    pattern.

  Where the grammar is ambiguous without semantic information, the AST follows
  the syntactic reading and leaves the decision to the analysis: \<open>f(x)\<close> is an
  \<open>EApply\<close> whether \<open>f\<close> is a method, a function value or a constructor, and a
  name in a pattern is a \<open>PVar\<close> or a \<open>PRef\<close> by the case of its first letter
  (\<open>\<section>2.2\<close>), as the language definition prescribes.
\<close>

section\<open>The Test Corpus: the Scala Sources of Isabelle\<close>

text\<open>
  The real test of a front-end for a language is the code that is written in it,
  and here that code is at hand: \<^verbatim>\<open>Scala3_Tests.thy\<close> reads \<^emph>\<open>every\<close> \<open>.scala\<close> file
  below \<^verbatim>\<open>~~/src\<close> of the Isabelle installation the theory is built with - 380
  files with 93\,000 lines in Isabelle2026 - as a compilation unit, prints the
  AST back and reads the printed text again; the two prints must be equal
  (\<^emph>\<open>idempotence\<close>). The files are read in parallel (\<open>Par_List.map\<close>), which also
  tests the re-entrancy of the parser. All 380 pass. If the directory is absent,
  the test does nothing.

  The corpus is what decided the scope of the grammar (\<open>\<section>1.1\<close>), and what found
  facts that no description of the language gives: that \<open>end\<close> must not be a
  keyword, that a leading infix operator and a leading \<open>+\<close> or \<open>-\<close> have to be
  told apart by the blank after them, and that \<open>case\<close> needs a look-ahead to be
  told from an enum case.

  Besides the corpus, the test theories contain round-trip tests for every
  construct (a program in the printer's canonical layout comes back unchanged),
  layout tests (the same program written with newlines, semicolons, operators at
  the end or the beginning of lines, method chains with leading dots, and
  newlines inside parentheses, must give one tree), operator tests, rejection
  tests, and, in \<^verbatim>\<open>Scala3_Cmd_Tests.thy\<close>, tests of the commands: the number of
  entity markups for each scoping rule, navigation, the evaluation order,
  \<open>scala3_file\<close>, export and the backend hook.
\<close>

section\<open>Limitations\<close>

text\<open>
  Isabelle/Scala 3 is a deliberately modest slice of the language, and the
  navigation language is the narrowed one of Isabelle/C 2.0. Concretely:

  \<^item> \<^bold>\<open>No significant indentation.\<close> A block is delimited by braces; the
    indentation-delimited syntax of Scala 3 (optional braces, \<open>then\<close>/\<open>do\<close>, end
    markers, \<open>:\<close> at the end of a line to start a block) is not read. Isabelle's
    own sources do not use it; adding it would need a second layout stage like
    the one of Isabelle/occam.
  \<^item> \<^bold>\<open>No metaprogramming.\<close> Quotes and splices (\<open>'{ \<dots> }\<close>, \<open>${ \<dots> }\<close>) and inline
    matches are outside the grammar; so is the \<open>derives\<close> clause.
  \<^item> \<^bold>\<open>Interpolated strings are not parsed.\<close> The expressions inside \<open>${\<dots>}\<close> are
    skipped over, balanced, and kept as text; names used inside them are not
    hyperlinked.
  \<^item> \<^bold>\<open>Conflicts.\<close> ml-yacc reports no shift/reduce conflict and 12
    reduce/reduce conflicts (visible in the exported \<^verbatim>\<open>Scala3.grm.desc\<close> when
    \<open>ml_lex_yacc\<close> is run with \<open>[verbose]\<close>). The shift/reduce conflicts of the
    grammar - a type continuing with an operator, a refinement or \<open>with\<close>,
    \<open>(implicit\<close> and \<open>(using\<close>, a statement list absorbing a separator, and so
    on - were all cases in which shifting is the reading Scala intends; they are
    resolved by precedence declarations (the reducing rules have the
    pseudo-precedence \<open>TYLOW\<close>, the continuing tokens a higher one) and not
    left to the default of the tool. The reduce/reduce conflicts that remain
    are the soft modifiers \<open>open\<close>, \<open>infix\<close>, \<open>inline\<close>, \<open>opaque\<close> and
    \<open>transparent\<close> before an identifier or an annotation inside \<open>(using \<dots>)\<close>,
    where a type and a parameter cannot be told apart by one token, and
    \<open>()\<close> followed by \<open>[\<close>; yacc takes the rule that comes first, the modifier.
  \<^item> \<^bold>\<open>One operator simplification.\<close> Every operator ending in a colon is
    right-associative at the level of \<open>::\<close>, not at the level of its first
    character (\<open>\<section>2.1\<close>).
  \<^item> \<^bold>\<open>No semantics.\<close> There is no type checker, no implicit resolution, no
    overload resolution, no inheritance. A name that resolves nowhere is
    silently left unmarked, a member selection \<open>e.f\<close> is never resolved, and a
    name brought in by a wildcard import or by a parent class is simply not
    known.
  \<^item> \<^bold>\<open>Comment placement.\<close> A comment is attached to the node starting at the next
    real token. A comment before a name that does not begin its line is
    attached to that name, not to the construct around it; an annotation meant
    for a definition belongs on its own line above it.
  \<^item> \<^bold>\<open>The \<open>text\<close> antiquotation never reaches the generated document.\<close> It runs the
    body through the real \<^ML>\<open>Document_Output.output_document\<close>, but the result
    only reaches a probe reference. This is a limitation of Isabelle itself, not
    of this front-end: the presentation of a command is only consulted for
    document-class commands, which a \<open>thy_decl\<close> command can never be.
  \<^item> \<^bold>\<open>Navigation is not total.\<close> An \<open>Id\<close> root is a leaf and is never navigable by
    \<open>r\<close>/\<open>d\<close>; there is no wrapping; and nodes without a \<open>root\<close> variant
    (parameters, clauses, parents, selectors) cannot be navigation targets.

\<close>

section\<open>Conclusion\<close>

text\<open>
  Isabelle/Scala 3 shows that the design of Isabelle/C Version 2.0 carries over
  to a language of a very different kind: an expression-oriented language with
  user-defined operators, soft keywords, two name spaces and a newline that is
  sometimes a separator and sometimes not. The language-specific difficulties
  are isolated in a small stream between an ordinary ml-lex lexer and an
  ordinary ml-yacc grammar, and the grammar is tested against the largest body
  of Scala code at hand, the sources of Isabelle itself; everything on top of
  the parser - positions, environment, hyperlinks, antiquotations,
  navigation, commands - is the C11 design instantiated for a new AST. What is
  documented in \<open>\<section>6\<close> as missing is, in every case, a scoping decision rather
  than an accident: the natural next steps are the indentation-based syntax,
  needed for sources other than Isabelle's, and a semantic backend - for
  example one that lets the Scala sources of Isabelle be browsed, checked and
  annotated in the document model next to the ML sources they interoperate
  with.

  \pagebreak
\<close>

section\<open>Annex: The Scala 3 Grammar as Railroad Diagrams\<close>

subsection\<open>Lexical Structure\<close>

text\<open>
  The lexer is a small ml-lex specification in \<^verbatim>\<open>Scala3_Parser.thy\<close>. The hard
  keywords of Scala 3 are reserved (\<open>abstract\<close>, \<open>case\<close>, \<open>catch\<close>, \<open>class\<close>, \<open>def\<close>,
  \<open>do\<close>, \<open>else\<close>, \<open>enum\<close>, \<open>export\<close>, \<open>extends\<close>, \<open>false\<close>, \<open>final\<close>, \<open>finally\<close>, \<open>for\<close>,
  \<open>given\<close>, \<open>if\<close>, \<open>implicit\<close>, \<open>import\<close>, \<open>lazy\<close>, \<open>match\<close>, \<open>new\<close>, \<open>null\<close>, \<open>object\<close>,
  \<open>override\<close>, \<open>package\<close>, \<open>private\<close>, \<open>protected\<close>, \<open>return\<close>, \<open>sealed\<close>, \<open>super\<close>,
  \<open>then\<close>, \<open>this\<close>, \<open>throw\<close>, \<open>trait\<close>, \<open>true\<close>, \<open>try\<close>, \<open>type\<close>, \<open>val\<close>, \<open>var\<close>,
  \<open>while\<close>, \<open>with\<close>, \<open>yield\<close>); the soft keywords \<open>as\<close>, \<open>extension\<close>, \<open>infix\<close>,
  \<open>inline\<close>, \<open>opaque\<close>, \<open>open\<close>, \<open>transparent\<close> and \<open>using\<close> have tokens of their own
  that the grammar also accepts as identifiers. An \<^emph>\<open>identifier\<close> is a letter, \<open>$\<close>
  or \<open>_\<close> followed by letters, digits, \<open>$\<close> and \<open>_\<close> (and, after an underscore,
  operator characters: \<open>unary_!\<close>), an operator (a run of the operator
  characters), or any text in backquotes. Integer literals are decimal,
  hexadecimal or binary, with underscores and an \<open>L\<close> suffix; floats have a
  fractional part, an exponent or a suffix. A character literal is \<open>'x'\<close>;
  strings are \<open>"\<dots>"\<close>, \<open>"""\<dots>"""\<close>, and interpolated with a prefix. The comment
  machinery lives in the lexer, as in the other front-ends: \<open>//\<close> enters a
  comment state that runs to the end of the line, \<open>/*\<close> a nesting one, and an
  antiquotation is recognised by a regular expression for its head, followed by
  a nesting-depth counter for a cartouche body. The syntax of the head:

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

  The bracket around the navigation steps is a delimiter on purpose: \<open>u\<close>, \<open>U\<close>,
  \<open>r\<close>, \<open>d\<close> are ordinary identifier characters, so a tag ending in one of them
  (\<open>@answer\<close>) would otherwise be ambiguous between a tag and a tag plus a step.
\<close>

subsection\<open>Grammar\<close>

text\<open>
  The grammar follows the Syntax Summary. It is reproduced here slightly
  simplified: \<open>NEWLINE\<close> is shown as the line break it stands for (a separator
  \<open>sep\<close> is a semicolon or a newline), and the productions that enumerate
  modifiers and operators are abbreviated.

  \<^rail>\<open>
    compilation__unit : ((statement sep) *) 
    ;
    statement : import | export | (annotation *) (modifier *) definition
              | expression
    ;
    import : 'import' (import__expr ((',' import__expr) *))
    ;
    import__expr : path '.'
                   ('*' | 'given' | '_' | name | '{'
                       (selector ((',' selector) *)) '}')
    ;
    selector : name (('=>' | 'as') (name | '_'))? | 'given' type?
  \<close>

  \<^rail>\<open>
    definition : pattern__definition | method__definition | type__definition
               | class__definition | given__definition | extension__definition
               | package__clause
    ;
    pattern__definition : ('val' | 'var') pattern ((',' pattern) *) (':' type)?
                          ('=' expression)?
    ;
    method__definition : 'def' name (clause *) (':' type)? ('=' expression)?
    ;
    clause : '[' (type__parameter ((',' type__parameter) *)) ']'
           | '(' ('using' | 'implicit')? (parameter ((',' parameter) *)) ')'
    ;
    type__definition : 'type' name (clause *)
                       (('>:' type)? ('<:' type)? | '=' type)
    ;
    class__definition : ('case')? ('class' | 'trait' | 'object' | 'enum')
                        name (clause *) ('extends' parents)? template__body?
    ;
    given__definition : 'given' (name)? (clause *) (':' | 'as')? type
                        ('=' expression | 'with' template__body)?
    ;
    extension__definition : 'extension' clause (clause *)
                            ('{' ((statement sep) *) '}' | statement)
    ;
    package__clause : 'package' path ('{' ((statement sep) *) '}')?
  \<close>

  \<^rail>\<open>
    expression : lambda
               | 'if' '(' expression ')' expression ('else' expression)?
               | 'while' '(' expression ')' expression
               | 'try' expression ('catch' expression)? ('finally' expression)?
               | 'throw' expression | 'return' expression?
               | 'for' ('(' | '{') ((enumerator sep) +) (')' | '}') 'yield'?
                 expression
               | postfix__expression
                 (':' type | 'match' '{' (case__clause +) '}')?
               | assignment
    ;
    postfix__expression : prefix__expression ((operator prefix__expression) *)
                          operator?
    ;
    prefix__expression : ('-' | '+' | '~' | '!')? simple__expression
    ;
    simple__expression : literal | path | 'this' | 'super' | '_'
                       | '(' (expression ((',' expression) *))? ')'
                       | '{' ((statement sep) *) '}'
                       | 'new' parents template__body?
                       | simple__expression '.' name
                       | simple__expression '[' (type ((',' type) *)) ']'
                       | simple__expression '(' ('using')?
                         (argument ((',' argument) *))? ')'
    ;
    lambda : (name | '_' | '(' (binding ((',' binding) *))? ')') ('=>' | '?=>')
             expression
    ;
    case__clause : 'case' pattern ('if' expression)? '=>' ((statement sep) *)
    ;
    enumerator : 'case'? pattern '<-' expression | 'if' expression
               | pattern '=' expression
  \<close>

  \<^rail>\<open>
    pattern : pattern__1 (('|' pattern__1) *)
    ;
    pattern__1 : pattern__2 (':' type)? | name '@' pattern__2
    ;
    pattern__2 : literal | '_' | name | path | 'given' type
               | path ('[' (type ((',' type) *)) ']')? '(' ((pattern ',') *) ')'
               | '(' ((pattern ',') *) ')' | pattern__2 operator pattern__2
    ;
    type : infix__type | clause__type '=>' type | clause__type '?=>' type
         | '=>' type
         | type 'match' '{' (type__case +) '}'
    ;
    infix__type : refined__type ((operator refined__type) *)
    ;
    refined__type : annotated__type (('with' annotated__type) *)
                    ('{' ((statement sep) *) '}')?
    ;
    annotated__type : simple__type (annotation *) '*'?
    ;
    simple__type : path | path '.' 'type' | simple__type '#' name
                 | simple__type '[' (type ((',' type) *)) ']'
                 | '(' ((type ',') *) ')' | '_' (('>:' type)? ('<:' type)?)
                 | literal
    ;
    path : ('this' | 'super' ('[' name ']')? | name) (('.' name) *)
    ;
    parents : parent (('with' parent) *)
    ;
    parent : type (('(' (argument ((',' argument) *))? ')') *)
    ;
    template__body : '{' (name ':' type '=>')? ((statement sep) *) '}'
  \<close>
\<close>

end
