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
theory MicroRust_Manual
  imports "MicroRust.MicroRust"
begin
(*>*)

section\<open>What is Isabelle/MicroRust\<close>

text\<open>
  Isabelle/MicroRust is a front-end that lets Rust source text live inside an
  Isabelle theory as a first-class citizen: parsed by a real grammar, checked
  incrementally under Isabelle/PIDE (so a syntax error or a malformed annotation
  is reported like any other Isabelle error, with the usual jEdit markup,
  hyperlinking and hovering), and open to attaching arbitrary Isabelle-level
  content - proof obligations, HOL terms, arbitrary Isar commands - to specific
  points of the Rust source via a comment-based antiquotation mechanism. It is
  not a Rust compiler, nor a verification tool in its own right: it is the
  \<^emph>\<open>front-end layer\<close> on which one builds a verification tool (a semantic backend,
  for instance a translation into the shallow embedding of AutoCorrode
  \<^cite>\<open>"awslabs:autocorrode:2025"\<close>), a documentation generator, or a static
  analysis.
\<close>

subsection\<open>Context\<close>

text\<open>
  \<^bold>\<open>There is no official grammar of Rust.\<close> The reference implementation, \<^verbatim>\<open>rustc\<close>,
  is the specification; its macro system, which transcribes and re-parses token
  trees, is part of the language. The Rust Reference \<^cite>\<open>"rust:reference:2026"\<close>
  describes the syntax in a PEG-style notation (ordered choice, with a ``hard
  cut'' operator to forbid backtracking) that cannot be turned into an LALR
  grammar mechanically, and the grammar file of \<^verbatim>\<open>rust-analyzer\<close>
  \<^cite>\<open>"rustanalyzer:ungrammar:2026"\<close> - the engine behind the VS Code plugin, whose
  parser is hand-written and error-resilient - states about itself that it
  ``does not specify parsing rules (ambiguities, precedence, etc)'': it
  describes the \<^emph>\<open>shape\<close> of the syntax trees, not how to obtain them. A front-end
  whose grammar is an explicit, reviewable specification, as the other members
  of this repository's family have it, cannot be derived from any of these.

  Isabelle/MicroRust therefore does what verification frameworks for Rust do
  anyway: it fixes a \<^emph>\<open>subset with an explicit syntax table\<close>. The subset is
  \<^emph>\<open>uRust\<close>, the Rust-like language of AutoCorrode, a framework for reasoning
  about imperative programs in Isabelle/HOL with separation logic. In
  AutoCorrode uRust is an Isabelle syntax category with about 130 mixfix rules
  and priorities (\<^verbatim>\<open>Micro_Rust_Syntax.thy\<close>) that is mapped into HOL by a shallow
  embedding; programs are written between \<^verbatim>\<open>FunctionBody \<lbrakk>\<close> and \<^verbatim>\<open>\<rbrakk>\<close>, with HOL
  terms embedded by \<open>\<llangle>\<dots>\<rrangle>\<close>. Isabelle/MicroRust takes that syntax table as the
  specification of the \<^emph>\<open>constructs\<close>, the Rust Reference as the specification of
  the \<^emph>\<open>operator precedences\<close>, and adds a thin layer of \<^emph>\<open>items\<close> (\<open>fn\<close>, \<open>struct\<close>,
  \<open>enum\<close>, \<open>impl\<close>, \<open>trait\<close>, \<open>const\<close>, \<open>static\<close>, \<open>type\<close>, \<open>use\<close>, \<open>mod\<close>) so that a
  whole source file can be read and not only the body of a function. The result
  is \<^emph>\<open>checked against the real thing\<close>: every uRust body in the sources of
  AutoCorrode itself is read by the test-suite (\<open>\<section>5\<close>).

  Isabelle/MicroRust is the fourth language front-end built on the design of
  \<^bold>\<open>Isabelle/C, Version 2.0\<close>, which this repository's \<^verbatim>\<open>C11/\<close> folder contains
  \<^cite>\<open>"tuong.ea:isabellec:2019" and "tuong.ea:deeply:2019"\<close>, after occam 2 and
  Scala 3. It is built from the same parts and carries the same concepts over
  one for one: the \<^verbatim>\<open>ml_lex_yacc\<close> command of this repository (an ML-Lex/ML-Yacc
  integration \<^cite>\<open>"appel.ea:lexical:1994" and "tarditi.ea:ml-yacc:2000"\<close>) generates
  lexer and parser; every node of the abstract syntax tree carries a source
  position plus the comments and antiquotations attached to it; a per-theory
  environment tracks the declared names for declaration/use hyperlinking;
  programmable handlers, a navigation language and an evaluation order give
  meaning to the antiquotations; and a family of Isar commands (\<open>microrust\<close>,
  \<open>microrust_body\<close>, \<open>microrust_file\<close>, \<open>\<dots>\<close>) drive all of it. Someone who knows
  the C11 manual will find the same structure in this one, and the same names
  with \<open>c11\<close> replaced by \<open>microrust\<close>, \<open>cenv\<close> by \<open>renv\<close>, and \<open>CEnv\<close> by \<open>REnv\<close>.
  Like the other members it is \<^emph>\<open>re-entrant\<close>: it is built with \<open>ml_lex_yacc
  [state]\<close>, every parse has a state object of its own, and any number of parses
  may run at the same time.

  What differs is dictated by the language and takes up most of the remainder:
  the three places where an LALR grammar needs help to read Rust (\<open>\<section>2.1\<close>), the
  name spaces and scoping rules of Rust (\<open>\<section>2.2\<close>), and the shape of the abstract
  syntax, in which almost everything is an expression (\<open>\<section>4\<close>).
\<close>

section\<open>Main Features of Isabelle/MicroRust\<close>

text\<open>
  Four pieces fit together to give the \<open>microrust\<close>-family commands (\<open>\<section>3\<close>) their
  behaviour: a lexer and parser that produce a real AST with genuine source
  positions at every node (\<open>\<section>2.1\<close>); a per-theory environment tracking every
  declared name, used to hyperlink each name \<^emph>\<open>use\<close> back to its declaration
  (\<open>\<section>2.2\<close>); a mechanism for attaching programmable content to a specific AST
  node via a comment (\<open>\<section>2.3\<close>); and a well-defined order and navigation language
  governing exactly \<^emph>\<open>which\<close> node an antiquotation resolves to and \<^emph>\<open>when\<close> it runs
  (\<open>\<section>2.4\<close>).
\<close>

subsection\<open>Parsing\<close>

text\<open>
  The grammar (\<^verbatim>\<open>MicroRust_Parser.thy\<close>) is an ordinary LALR(1) ml-yacc grammar.
  It covers

  \<^item> \<^bold>\<open>statements\<close>: \<open>let\<close> (with a type, with \<open>else\<close>), uRust's \<open>const x = e;\<close>
    binding, expression statements, items; attributes (\<open>#[fuel(n)] while \<dots>\<close>) on
    statements and expressions;
  \<^item> \<^bold>\<open>expressions\<close>: literals (with Rust's integer suffixes, \<open>0xFF_u8\<close>, raw
    strings), paths with turbofish and qualified paths (\<open>Vec::<u8>::new\<close>, \<open><T as
    Trait>::f\<close>), the unary and binary operators with the precedences of the Rust
    Reference, ranges, assignment and compound assignment, \<open>as\<close> casts, \<open>?\<close>,
    calls, method calls, fields, tuple indices (\<open>x.0.1\<close>), indexing, tuples,
    arrays and repeats, struct expressions (with \<open>..base\<close>), closures, \<open>if\<close>, \<open>if
    let\<close>, \<open>else if\<close>, \<open>while\<close>, \<open>while let\<close>, \<open>loop\<close> and \<open>for\<close> with labels, \<open>match\<close>
    with guards, \<open>return\<close>, \<open>break\<close>, \<open>continue\<close>, and the macro calls
    \<open>name!(args)\<close>, \<open>name![args]\<close>, \<open>vec![e; n]\<close> and \<open>matches!(e, p)\<close>;
  \<^item> \<^bold>\<open>patterns\<close>: wildcard, identifiers (\<open>mut\<close>, \<open>x @ p\<close>), literals, ranges, paths,
    tuple structs, structs, tuples, slices with \<open>..\<close>, references, or-patterns;
  \<^item> \<^bold>\<open>types\<close>: paths with generic arguments, references, raw pointers, tuples,
    slices, arrays, \<open>fn\<close> types, \<open>impl\<close>/\<open>dyn\<close> bounds, \<open>_\<close>, \<open>!\<close>;
  \<^item> \<^bold>\<open>items\<close>: functions with generics, bounds and \<open>where\<close> clauses, structs (named,
    tuple, unit), enums, \<open>impl\<close> blocks (inherent and trait impls), traits,
    \<open>const\<close>, \<open>static\<close>, type aliases, \<open>use\<close> trees and modules, with visibility
    and attributes.

  \<^bold>\<open>uRust specifics.\<close> Besides the Rust it is, uRust has HOL in it, and so does
  the lexer: a HOL term or type is embedded as \<open>\<llangle>\<dots>\<rrangle>\<close> (optionally followed by a
  sub-script, \<open>\<llangle>f\<rrangle>\<^sub>1(x)\<close>, which selects the arity of an embedded function), as
  \<open>\<epsilon>\<open>\<dots>\<close>\<close>, or, as the argument of a logging macro, as \<open>l\<llangle>"text"\<rrangle>\<close>. All of these
  are kept as \<^emph>\<open>opaque text\<close> in the AST: reading them as HOL is the job of the
  semantic backend (or of the \<open>term\<close> antiquotation, \<open>\<section>2.5\<close>). The keywords
  \<open>yield\<close> and \<open>log\<close> of uRust (also written in Isabelle's bold-letter symbols),
  the match keywords \<open>match_switch\<close> and \<open>match_case\<close>, a parenthesized statement
  sequence \<open>(a; b; c)\<close>, and Isabelle's comment cartouches (the symbol for a
  comment, followed by a cartouche) are part of the language as well; \<open>ref\<close> is
  an ordinary identifier, as in AutoCorrode. A uRust \<^emph>\<open>function body\<close> has no
  braces: it is a statement sequence with a final expression, as written between
  \<^verbatim>\<open>FunctionBody \<lbrakk>\<close> and \<^verbatim>\<open>\<rbrakk>\<close>. It is a grammar entry point of its own and the
  argument of the command \<open>microrust_body\<close>.

  \<^bold>\<open>Three places where an LALR grammar needs help.\<close> Rust is context-sensitive in
  a few places where a one-token look-ahead cannot decide. They are resolved in
  a small \<^emph>\<open>stream\<close> between lexer and parser (\<open>MicroRust_Parse.struct_stream\<close>),
  so that the grammar itself stays an ordinary context-free one:

  \<^enum> \<^emph>\<open>Struct expression or block?\<close> In \<open>Foo { a: 1 }\<close> the brace opens a struct
    expression; in \<open>if x { \<dots> }\<close> it opens the body, although \<open>x\<close> looks the same.
    The stream keeps a stack of regions (the head of an \<open>if\<close>, \<open>while\<close>, \<open>match\<close>,
    \<open>for \<dots> in\<close> or of an item is a region in which a struct expression is not
    allowed, exactly as in \<^verbatim>\<open>rustc\<close>; parentheses allow it again) and delivers an
    opening brace as \<open>STRUCTLB\<close> (after a path, where allowed), \<open>BLOCKLB\<close> (the
    body of a construct whose head is being read) or \<open>LBRACE\<close>. The same
    distinction keeps \<open>for i in 0.. { \<dots> }\<close> from reading the body as the end of
    the range.
  \<^enum> \<^emph>\<open>One \<open>>\<close> or two?\<close> In \<open>Vec<Vec<u8>>\<close> the \<open>>>\<close> closes two generics, in \<open>a >> b\<close>
    it is a shift, and \<open>>=\<close> and \<open>>>=\<close> are operators too. The lexer produces
    single \<open>>\<close> tokens; the stream marks a \<open>>\<close> that is immediately followed by
    \<open>>\<close> or \<open>=\<close> as \<^emph>\<open>joint\<close> (\<open>GTJ\<close>), the grammar reads the operators from joint
    tokens and accepts a joint \<open>>\<close> as well as a plain one to close a list of
    generic arguments. A blank in \<open>a > > b\<close> is thus an error in the type of the
    construct, not in the lexer.
  \<^enum> \<^emph>\<open>Does a block-like expression end the statement?\<close> In \<open>if c { f(); } *x\<close> the
    \<open>*x\<close> is a new statement and not a multiplication, whereas in \<open>let y = if c {
    1 } else { 2 } * 3;\<close> it is a multiplication; and \<open>match e { \<dots> }.f()\<close>
    continues the expression. As in \<^verbatim>\<open>rustc\<close> a block-like expression at the start
    of a statement ends it, unless a \<open>.\<close> or \<open>?\<close> follows. The grammar has a
    reduce/reduce conflict there, resolved by the order of its rules (a
    statement before an expression); the same rule applies to a match arm whose
    body is block-like (it needs no comma).

  \<^bold>\<open>Positions and comments.\<close> Every node carries the exact source range of its
  text, from its first to its last token; a name carries the range of the name.
  Comments, and the antiquotations among them (\<open>\<section>2.3\<close>), are not part of the
  grammar: the lexer collects them and attaches them to the node of the next
  real token. Rust comments are \<open>//\<close> to the end of the line (also \<open>///\<close> and
  \<open>//!\<close>) and \<open>/* \<dots> */\<close>, which \<^emph>\<open>nest\<close>.

  A first example, a function body in the style of AutoCorrode (the HOL type
  annotation is an opaque escape; the second statement is a block-like \<open>if\<close>
  without a semicolon, followed by an expression that begins with \<open>*\<close>):
\<close>

microrust_body\<open>
let mut x = \<llangle>0 :: nat\<rrangle>;
if *x < 10 {
    x += 1;
}
*x
\<close>

text\<open>
  Rust's integer suffixes and underscores, nested comments and raw strings are
  lexical matters of the grammar too:
\<close>

microrust_expr\<open>0xFF_u8 as u32 + 1_000u32 /* a /* nested */ comment */
  + r#"a "raw" string"#.len() as u32\<close>

subsection\<open>The MicroRust Environment, and Declaration/Use Navigation\<close>

text\<open>
  \<^verbatim>\<open>MicroRust_Env.thy\<close> defines \<open>renv\<close>, the counterpart of C11's \<open>cenv\<close>: a record
  stored as ordinary \<^verbatim>\<open>Generic_Data\<close>, so that it persists across commands within
  a theory and merges correctly under Isabelle's parallel, incremental checking.
  It holds

  \<^enum> \<open>terms\<close> and \<open>types\<close>, the declared names of Rust's two name spaces, each with
    what it was declared as (a variable, a parameter, a function, a constant, a
    static, a struct, an enum, a variant, a trait, a type alias, a generic
    parameter, a module, an imported name);
  \<^enum> \<open>rust_antiq\<close>, the registry of antiquotation handlers (\<open>\<section>2.3\<close>); and
  \<^enum> a per-theory unit counter, used to name the sections processed by a
    \<open>microrust\<close> command.

  Rust has \<^emph>\<open>two\<close> name spaces. A struct, enum, trait, type alias, module or
  generic parameter lives in \<open>types\<close>, a function, constant, static, variable or
  parameter in \<open>terms\<close>, and a tuple or unit struct (which is both a type and a
  value) in both. In an expression a lone name is looked up among the values
  first; the first segment of a longer path (\<open>Vec::new\<close>, \<open>m::f\<close>, \<open>E::A\<close>) among
  the types first, and the other segments are \<^emph>\<open>not\<close> resolved: that would require
  types and modules.

  \<^verbatim>\<open>MicroRust_AnaEval.thy\<close>'s \<open>analyse_and_eval\<close> is a single, purely functional,
  scoped walk over a parsed root that fills \<open>renv\<close> as it goes. Every name \<^emph>\<open>use\<close>
  is hyperlinked to its declaration via \<^ML>\<open>Position.entity_markup\<close>, reported once
  at the declaration site and once at every use. \<^bold>\<open>A name that resolves nowhere
  is not marked\<close> - unlike C11 and occam 2, where it is underlined. In Rust a
  name routinely comes from the prelude, a glob import or the standard library,
  none of which this pass sees; underlining them would drown the useful markup.
  The \<^emph>\<open>scoping rules\<close> are those of Rust, implemented as shadow-and-restore (the
  environment is a value; a scope simply does not hand its extension back):

  \<^item> A function: its generic parameters first, then its parameters, then its body;
    a parameter is visible in the body and nowhere else.
  \<^item> A block: its \<^emph>\<open>items\<close> are visible throughout it (local functions may be
    mutually recursive), a \<open>let\<close> only after its statement; the initializer does
    not see the variables the \<open>let\<close> binds, and a \<open>let \<dots> else\<close> block sees none of
    them.
  \<^item> The items of a module, of a source file: visible throughout (forward
    references).
  \<^item> A closure: its parameters over its body. A \<open>match\<close> arm: its pattern variables
    over the guard and the body. \<open>for\<close>: the pattern over the body. \<open>if let\<close> and
    \<open>while let\<close>: the pattern over the body, \<^emph>\<open>not\<close> over the \<open>else\<close> branch.
  \<^item> A lone name in a pattern is a \<^emph>\<open>binder\<close> if it starts with a lower-case letter
    or \<open>_\<close> (or is marked \<open>mut\<close>, or has a sub-pattern \<open>x @ p\<close>), and otherwise a
    \<^emph>\<open>use\<close> of a constant, a unit struct or a variant: Rust's naming convention,
    which a lint enforces, decides what the grammar cannot.
  \<^item> A \<open>use\<close> declares the imported name (the alias for a renamed one) at its path
    segment, in both name spaces; a glob import declares nothing.
  \<^item> The members of an \<open>impl\<close> or a \<open>trait\<close> are not entered into the environment
    (they are reached through a type or a value), but their declaration sites
    are reported.
  \<^item> A source file is the one root whose names \<^emph>\<open>persist\<close>: after \<open>microrust\<close> has
    analysed it, its top-level names stay in \<open>renv\<close> for the following units, as
    the members of a crate do for its modules.

  Being persistent per-theory data - the same idiom a simp set uses - is what
  lets Rust fragments be freely \<^emph>\<open>interleaved\<close> with arbitrary Isar content and
  still resolve a name used in one fragment back to its declaration in an
  earlier one. The flip side is that \<open>renv\<close> only ever grows across a theory; the
  commands \<open>set_renv_default\<close> and \<open>reset_renv\<close> (\<open>\<section>3\<close>) give a theory explicit
  control. A small example of the library mechanism and the scoping rules (hover
  over the names in jEdit):
\<close>

microrust\<open>
mod arith {
    pub fn twice(n: u32) -> u32 {
        n * 2
    }
}

const LIMIT: u32 = 100;
\<close>

microrust\<open>
fn total() -> u32 {
    let mut sum = arith::twice(LIMIT);
    for i in 0..LIMIT {
        sum += i;
    }
    sum
}
\<close>

text\<open>
  The pattern variables of an arm are visible in its body, a \<open>let\<close> only after
  its statement, and the function \<open>helper\<close> is visible before its definition. The
  names \<open>Some\<close> and \<open>unknown\<close> resolve nowhere and are not marked:
\<close>

microrust\<open>
fn classify(o: Option<u32>) -> u32 {
    let y = helper(1);
    match o {
        Some(v) => v + y,
        _ => unknown,
    }
}

fn helper(n: u32) -> u32 {
    n
}
\<close>

subsection\<open>Programmable MicroRust-Antiquotations, and Handlers\<close>

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

  (a tag alone is a complete antiquotation with an empty body). A \<^emph>\<open>bodyless\<close> tag
  is recognised only directly after the comment opener (\<open>//@\<close>, \<open>/*@\<close>), so that
  an \<open>@\<close> in running text - an e-mail address, a documentation tag - is not
  mistaken for an antiquotation; a tag followed by a body is one anywhere in a
  comment.

  The \<open>tag\<close> selects a \<^emph>\<open>handler\<close>: an ordinary ML function of type

  \<^verbatim>\<open>type type_antiq_fun =
    renv * pos MicroRust_Ast.root * int -> (string * pos) ->
    Context.generic -> Context.generic\<close>

  registered once, ahead of time, via \<open>REnv.store_antiq (tag, handler)\<close>. When
  \<open>analyse_and_eval\<close> reaches a node carrying an \<open>@tag \<dots>\<close> antiquotation, it
  resolves the navigation string against the closest-surrounding-context stack
  (\<open>\<section>2.4\<close>) into a single concrete \<open>root\<close> value, then instantiates the handler
  with \<open>(renv, resolved_root, level)\<close> and the body text together with its own
  source position; a handler is never itself responsible for interpreting
  \<open>u\<close>/\<open>U\<close>/\<open>r\<close>/\<open>d\<close>.

  \<open>Context.generic\<close> rather than \<open>theory\<close>, deliberately: a handler may do
  anything a genuine Isar toplevel command can, including running real ML code
  at the ML environment level (the \<open>ML\<close> antiquotation, below). All collected
  actions are folded into one \<open>Context.generic -> Context.generic\<close> function by
  ordinary composition and lifted to the toplevel exactly once, at the end
  (\<open>full_eval_and_store\<close> in \<^verbatim>\<open>MicroRust.thy\<close>). Most handlers never need this
  generality: an ordinary \<open>theory -> theory\<close> function is \<^emph>\<open>recaptured\<close> by
  \<open>REnv.lift_theory_antiq\<close> when it is registered. A first handler, which turns a
  plain comment into a checked diagnostic reported against the exact node the
  comment resolves to:
\<close>

ML\<open>
val todo_antiq =
  let
    fun handler (_ : REnv.renv, ast, level) (body, _ : Position.T) thy =
      (warning ("TODO (level " ^ Int.toString level ^ ") at " ^
                Position.here (AnaEval.pos_of_root ast) ^ ": " ^ body);
       thy)
  in REnv.store_antiq ("todo", REnv.lift_theory_antiq handler) end
\<close>
setup\<open>todo_antiq\<close>

microrust\<open>
fn clear(x: &mut u32) {
    //@ todo \<open>check the range of x first\<close>
    *x = 0;
}
\<close>

text\<open>
  A tag with no registered handler is a hard error: every tag that can appear in
  a theory's source must be registered before that theory's \<open>microrust\<close>-family
  commands run.
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
  nodes share its leftmost source position (the classic case in Rust: a binary
  expression, its left operand and the operand's name all begin at the same
  token).

  \<^bold>\<open>Context.\<close> Every antiquotation resolves, by default, to its \<^emph>\<open>closest
  surrounding context\<close>: the walk threads a stack of enclosing nodes. Five kinds
  of node push themselves on that stack at every level of nesting:
  \<^emph>\<open>expressions\<close>, \<^emph>\<open>types\<close>, \<^emph>\<open>patterns\<close>, \<^emph>\<open>items\<close> and \<^emph>\<open>statements\<close> other than
  expression statements (which are their expression) - the root type has the
  variants \<open>Expr\<close>, \<open>Type\<close>, \<open>Pat\<close>, \<open>Item\<close>, \<open>Stmt\<close> in addition to \<open>Id\<close> for a bare
  name, \<open>Body\<close> for a function body and \<open>Crate\<close> for a source file. Everything
  else - blocks, match arms, parameters, fields, generic parameters, \<open>where\<close>
  predicates - never pushes and resolves to what is on top, which is what makes
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
  a node, in source order, are its sub-expressions, sub-types, sub-patterns,
  statements and items; \<^emph>\<open>blocks are flattened into their parent\<close>, so the
  children of an \<open>if\<close> are its condition followed by the statements of its
  blocks. A few examples (the node a handler receives, on the expression \<open>x + y\<close>
  that ends a function):

  \<^item> no navigation: the expression \<open>x + y\<close> itself;
  \<^item> \<open>[d]\<close> or \<open>[rd]\<close>: its first child, \<open>x\<close>; \<open>[rrd]\<close>: its second child, \<open>y\<close>;
  \<^item> \<open>[uu]\<close>: the enclosing function.

\<close>

microrust\<open>
fn sum(x: u32, y: u32) -> u32 {
    //@ probe_ast[rrd]
    //@ highlight[rrd]
    x + y
}
\<close>

ML\<open>
val _ = if MicroRust_Pp.pp_root (!RUST_AST) = "y"
  then writeln "[rrd] reaches the second operand"
        else error "navigation"
\<close>

subsection\<open>Standard Antiquotations\<close>

text\<open>
  \<^verbatim>\<open>MicroRust_AnaEval.thy\<close> registers the same eight demonstration antiquotations
  as C11. All of them are written in a comment and see the node their navigation
  string selects:

  \<^descr> \<open>probe_renv\<close> stores the current \<open>renv\<close> into an ML reference (\<open>RENV\<close>) for
    inspection.
  \<^descr> \<open>probe_ast\<close> prints the resolved node, pretty-printed back to Rust, with its
    level, and stores it into \<open>RUST_AST\<close>.
  \<^descr> \<open>highlight\<close> marks the resolved node's source range in the editor - the
    quickest way to \<^emph>\<open>see\<close> what a navigation string selects.
  \<^descr> \<open>term \<open>t\<close>\<close> reads \<open>t\<close> as a HOL term in the theory's current context; a
    malformed or ill-typed term is a real Isabelle error positioned inside the
    Rust comment.
  \<^descr> \<open>ML \<open>code\<close>\<close> runs \<open>code\<close> as ML source, so a definition written in a Rust
    comment becomes a later-visible ML binding.
  \<^descr> \<open>text \<open>t\<close>\<close> runs \<open>t\<close> through the document machinery of Isabelle's \<open>text\<close>
    command, so that inner antiquotations are checked and hyperlinked (the
    result is stashed, not typeset; see \<open>\<section>6\<close>).
  \<^descr> \<open>definition \<open>d\<close>\<close> is Isabelle's \<open>definition\<close> command: the new constant is a
    genuine, later-visible theory constant.
  \<^descr> \<open>lemma \<open>l\<close>\<close> states \<open>l\<close> and proves it with one terminal \<open>by\<close> proof -
    proof-carrying code: a formal property of the program's constants, \<^emph>\<open>actually
    proved\<close>, right where the Rust text that motivates it lives. A failed proof
    is an Isabelle error positioned in the comment.

\<close>

section\<open>The MicroRust Main Commands\<close>

text\<open>

  \<^descr> \<open>microrust \<open>\<dots>\<close>\<close> parses its argument as a source file - a sequence of items -
    runs \<open>analyse_and_eval\<close>, chains the collected antiquotation actions in level
    order, and stores the AST under a fresh key, reported as \<open>[stored as
    Theory#N]\<close>.
  \<^descr> \<open>microrust_body \<open>\<dots>\<close>\<close> is the same for a uRust function body: statements and a
    final expression, without braces, as written between \<^verbatim>\<open>FunctionBody \<lbrakk>\<close> and
    \<^verbatim>\<open>\<rbrakk>\<close>.
  \<^descr> \<open>microrust_file \<open>path\<close>\<close> is the same as \<open>microrust\<close>, reading the source file
    from an external \<open>.rs\<close> file (resolved relative to the theory's master
    directory via \<^ML>\<open>Resources.parse_file\<close>, so file positions and build-dependency
    tracking come for free).
  \<^descr> \<open>microrust_expr \<open>\<dots>\<close>\<close>, \<open>microrust_type \<open>\<dots>\<close>\<close> and \<open>microrust_ident \<open>\<dots>\<close>\<close> parse a
    bare expression, type, respectively name. The analysis still runs, for its
    hyperlinks, but its antiquotation actions are discarded: a standalone
    fragment is a syntax check, not a program.
  \<^descr> \<open>microrust_reject\<close>, \<open>microrust_body_reject\<close>, \<open>microrust_expr_reject\<close>,
    \<open>microrust_type_reject\<close> and \<open>microrust_ident_reject\<close> document a fragment as
    correctly \<^emph>\<open>not\<close> accepted by the corresponding entry point. They are silent
    (no error markup is left on the expected failure) and are the means of
    writing negative tests.
  \<^descr> \<open>set_renv_default\<close> and \<open>reset_renv\<close> control the ever-growing \<open>renv\<close>.
    \<open>set_renv_default\<close> nominates what \<open>renv\<close> holds \<^emph>\<open>right now\<close> as the snapshot a
    later \<open>reset_renv\<close> restores; with no earlier \<open>set_renv_default\<close> in scope
    \<open>reset_renv\<close> falls back to the empty \<open>renv\<close>. \<^verbatim>\<open>MicroRust.thy\<close> itself
    nominates, as its last step, the environment holding exactly the standard
    antiquotation handlers.
  \<^descr> \<open>setup_backend \<open>f\<close>\<close> installs the \<^emph>\<open>semantic backend\<close>: \<open>f\<close> is an ML expression
    of type \<open>Position.T MicroRust_Ast.root -> theory -> theory\<close>, evaluated like
    the argument of Isabelle's own \<open>setup\<close> command. At the very end of every
    \<open>microrust\<close>, \<open>microrust_body\<close> and \<open>microrust_file\<close> - after the antiquotation
    actions have run and the AST is stored - the installed function is applied
    to the parsed root and the theory the command has produced, and its result
    is the theory the command returns; the fragment commands never trigger it.
    The default is \<open>K I\<close>, which \<open>setup_backend \<open>K I\<close>\<close> restores. The function is
    kept in the theory's context (separately from \<open>renv\<close>, so \<open>reset_renv\<close> does
    not uninstall it) and is inherited by later theories. This is where a
    translation of the uRust bodies of \<open>\<section>4\<close> into the shallow embedding of
    AutoCorrode would plug in.
  \<^descr> \<open>microrust_export \<open>path\<close> exports \<open>key\<^sub>1\<close> \<open>\<dots>\<close> \<open>key\<^sub>n\<close>\<close> renders previously stored
    sections - given by the store keys the accepting commands report - back to
    Rust text with \<^ML>\<open>MicroRust_Pp.pp_root\<close> and writes them to \<open>path.rs\<close>. With
    \<open>[verbatim]\<close> after the command name the original source text is written
    instead of the (deliberately simple, canonical four-space layout)
    pretty-printer's.

  The accepting commands are \<open>thy_decl\<close> commands, because they change theory
  data (\<open>microrust_file\<close> is \<open>thy_load\<close>, so that Isabelle tracks the file
  dependency); the \<open>_reject\<close> commands, which store nothing, are \<open>diag\<close>. Isabelle
  evaluates a \<open>diag\<close> command asynchronously, in parallel with the commands that
  follow; that is harmless here, because every parse has its own state (\<open>\<section>2.1\<close>).
\<close>

subsection\<open>A Worked Example\<close>

text\<open>
  A function in the style of AutoCorrode: a constant mirrored in HOL, a loop
  with a fuel annotation, and a contract stated as HOL. The first annotation
  introduces a HOL constant for the bound (an \<open>@definition\<close>, evaluated at level
  0), the second proves a fact about it (level 1, so after the definition), the
  third checks a HOL term mentioning it (level 2).
\<close>

microrust\<open>
//@ definition \<open>bound :: nat where "bound = 10"\<close>
//@ lemma(1) \<open>bound_double: "bound * 2 = 20" by (simp add: bound_def)\<close>
//@ term(2) \<open>bound + 1\<close>
const BOUND: u32 = 10;

fn count_up() -> u32 {
    let mut i = 0;
    //@ highlight
    #[fuel(10)]
    while i < BOUND {
        i += 1;
    }
    i
}
\<close>

thm bound_def bound_double

text\<open>
  The same in the style in which AutoCorrode itself uses uRust: the body alone,
  with the HOL escapes of the verification framework (\<open>\<llangle>\<dots>\<rrangle>\<close> lifts a HOL term,
  the sub-scripted form lifts a HOL function applied to arguments, \<open>\<epsilon>\<open>\<dots>\<close>\<close> embeds
  a HOL term):
\<close>

microrust_body\<open>
let mut left = \<llangle>42 :: nat\<rrangle>;
let mut right = 72;
swap_ref(left, right);
\<llangle>show\<rrangle>\<^sub>1(*left) + \<epsilon>\<open>n :: nat\<close>
\<close>

subsection\<open>Source Files, Backends, Export\<close>

text\<open>
  \<open>microrust_file\<close> reads an external file (here one of the examples of this
  repository: enum, trait, impl, a \<open>match\<close>, a \<open>for\<close> loop) and stores its AST;
  the names of its items are visible to the following units.
\<close>

microrust_file \<open>../examples/shapes.rs\<close>

microrust_file \<open>../examples/counter.rs\<close>

text\<open>
  A semantic backend is an ML function installed with \<open>setup_backend\<close>. The
  following one only counts the functions of every source file it is applied to;
  a real backend would translate them. It is applied to the \<^emph>\<open>parsed root\<close> and
  the theory, after the annotations have run:
\<close>

ML\<open>
val fn_counts = Unsynchronized.ref ([] : int list)
\<close>

setup_backend\<open>fn root => fn thy =>
  (case root of
     MicroRust_Ast.Crate items =>
       let
         fun is_fn (MicroRust_Ast.MkItem (_, _, MicroRust_Ast.IFn _, _)) = true
           | is_fn _ = false
       in (fn_counts := length (filter is_fn items) :: !fn_counts; thy) end
   | _ => thy)\<close>

microrust\<open>
fn one() -> u32 { 1 }
fn two() -> u32 { 2 }
struct S;
\<close>

setup_backend\<open>K I\<close>

ML\<open>
val _ = writeln ("functions per unit seen by the backend: " ^
                 commas (map Int.toString (rev (!fn_counts))))
\<close>

text\<open>
  An accepted unit can be written back as Rust, in the canonical layout of the
  pretty-printer (or, with \<open>[verbatim]\<close>, as it was written). The key of the unit
  is the one the command reported when it was stored. This is the way a
  generated or normalised file is produced from a theory:
\<close>

microrust\<open>
fn id(x: u32) -> u32 { x }
\<close>

ML\<open>
val key_of_last =
  let val REnv.mk {units, ...} = REnv.get (Context.Theory @{theory})
  in REnv.ast_store_key @{theory} (units - 1) end
val _ = writeln ("the last unit is stored as " ^ key_of_last)
\<close>

section\<open>The Abstract Syntax\<close>

text\<open>
  There is no pre-existing reference AST for Rust to port, unlike C11, whose AST
  is a pruned port of the Haskell \<^verbatim>\<open>language-c\<close> tree (the AST of \<^verbatim>\<open>rust-analyzer\<close>
  is untyped, a generic tree of tokens). The AST in \<^verbatim>\<open>microrust_ast.ML\<close> is
  therefore an educated design of this project: one datatype per syntactic
  category, one constructor per alternative, close enough to the concrete syntax
  that \<^ML>\<open>MicroRust_Pp.pp_root\<close> can print any parsed program back as Rust. Layout
  is \<^emph>\<open>not\<close> part of it: the printer regenerates a canonical layout (four spaces,
  braces always, one statement per line). Parentheses \<^emph>\<open>are\<close> part of it
  (\<open>EParen\<close>, \<open>PParen\<close>), so the printer needs no precedence reasoning. All
  datatypes are parametrised by the position type \<open>'a\<close> (instantiated with
  \<^verbatim>\<open>Position.T\<close>), and every constructor but the pure wrappers carries a \<open>'a
  nodeInfo\<close> as its last field.

  \<^bold>\<open>Annotations\<close>, shared with C11 and so with everything built on it: \<open>nodeInfo\<close>
  is a bare position or a position with the comments attached; a \<open>comment\<close> is
  raw text or an antiquotation (tag, navigation steps, level, cartouche with its
  position); \<open>ident\<close> is a name with its \<open>nodeInfo\<close>.

  \<^bold>\<open>Syntactic categories\<close> (the constructors are those of \<^verbatim>\<open>microrust_ast.ML\<close>; the
  prefix \<open>r\<close> stands for ``Rust''):

  \<^item> \<open>rExpr\<close>: \<open>ELit\<close> (\<open>rLit\<close>: \<open>LInt\<close>, \<open>LFloat\<close>, \<open>LChar\<close>, \<open>LStr\<close>, \<open>LBool\<close>, all as
    written), \<open>EPath\<close>, the HOL escapes \<open>EHol\<close>, \<open>EEps\<close>, \<open>ELogLit\<close>, the operators
    \<open>EUnary\<close>, \<open>EBinary\<close>, \<open>EAssign\<close> (plain or compound), \<open>ECast\<close>, \<open>ETry\<close>,
    \<open>ERange\<close>, the postfix forms \<open>ECall\<close>, \<open>EMethod\<close>, \<open>EField\<close>, \<open>ETupIdx\<close>,
    \<open>EIndex\<close>, the aggregates \<open>ETuple\<close>, \<open>EParen\<close>, \<open>EArray\<close>, \<open>ERepeat\<close>, \<open>EStruct\<close>,
    the control constructs \<open>EBlock\<close>, \<open>EUnsafe\<close>, \<open>EIf\<close> (with an \<open>rCond\<close>: an
    expression or \<open>if let\<close>), \<open>EWhile\<close>, \<open>ELoop\<close>, \<open>EFor\<close>, \<open>EMatch\<close> (with \<open>rArm\<close>s),
    \<open>EClosure\<close>, \<open>EReturn\<close>, \<open>EBreak\<close>, \<open>EContinue\<close>, the macro calls \<open>EMacro\<close>,
    \<open>EMacroRepeat\<close>, \<open>EMatches\<close>, \<open>EAttr\<close> (an expression with attributes), and the
    uRust forms \<open>EYield\<close>, \<open>ELog\<close>, \<open>ESeq\<close>.
  \<^item> \<open>rPath\<close> (with an optional qualified self type, a leading \<open>::\<close>, and
    \<open>rSeg\<close>ments carrying \<open>rGArgs\<close>), \<open>rType\<close> (\<open>TPath\<close>, \<open>TRef\<close>, \<open>TPtr\<close>, \<open>TTuple\<close>,
    \<open>TSlice\<close>, \<open>TArray\<close>, \<open>TInfer\<close>, \<open>TNever\<close>, \<open>TFn\<close>, \<open>TImpl\<close>, \<open>TDyn\<close>, \<open>THol\<close>) and
    \<open>rBound\<close>.
  \<^item> \<open>rPat\<close>: \<open>PWild\<close>, \<open>PRest\<close>, \<open>PIdent\<close> (binder or constant: \<open>ref\<close>/\<open>mut\<close> flags,
    sub-pattern), \<open>PLit\<close>, \<open>PRange\<close>, \<open>PPath\<close>, \<open>PTupleStruct\<close>, \<open>PStruct\<close>,
    \<open>PTuple\<close>, \<open>PSlice\<close>, \<open>PRef\<close>, \<open>PAlt\<close>, \<open>PParen\<close>, \<open>PMut\<close>, \<open>PHol\<close>.
  \<^item> \<open>rStmt\<close>: \<open>SLet\<close> (also uRust's \<open>const\<close> binding, and \<open>let \<dots> else\<close>), \<open>SExpr\<close>
    (with a flag for the semicolon), \<open>SItem\<close>, \<open>SEmpty\<close>; and \<open>rBlock\<close>, a list of
    statements with an optional final expression.
  \<^item> \<open>rItem\<close>: a \<open>MkItem\<close> of attributes, a visibility and an \<open>rItemKind\<close>: \<open>IFn\<close>
    (qualifiers, generics, \<open>rFnParam\<close>s - \<open>PSelf\<close> or \<open>PParam\<close> -, result type,
    \<open>where\<close> predicates, optional body), \<open>IStruct\<close> (\<open>rFields\<close>: named, tuple or
    unit), \<open>IEnum\<close> (\<open>rVariant\<close>s), \<open>IImpl\<close>, \<open>ITrait\<close>, \<open>IConst\<close>, \<open>IStatic\<close>,
    \<open>ITypeAlias\<close>, \<open>IUse\<close> (an \<open>rUse\<close> tree) and \<open>IMod\<close>.
  \<^item> \<open>root\<close>: the result of a parse by entry point - \<open>Id\<close>, \<open>Expr\<close>, \<open>Type\<close>, \<open>Pat\<close>,
    \<open>Body\<close> or \<open>Crate\<close> - plus \<open>Stmt\<close> and \<open>Item\<close>, never produced by a parse but
    used by the analysis as the closest context of an annotation on a statement
    or an item.

  Where the grammar is ambiguous without name resolution, the AST follows the
  syntactic reading and leaves the decision to the analysis: a lone identifier
  in a pattern is a \<open>PIdent\<close> whether it will turn out to be a binder or the name
  of a constant (\<open>\<section>2.2\<close>), \<open>f(x)\<close> is an \<open>ECall\<close> whether \<open>f\<close> is a function or a
  tuple struct, and a path is a path whether its first segment is a module, a
  type or an enum.
\<close>

section\<open>The Test Corpus: the Sources of AutoCorrode\<close>

text\<open>
  A grammar for a language without a specification must be tested against what
  the community writes. The test theory \<^verbatim>\<open>MicroRust_Tests.thy\<close> therefore ends
  with a corpus test: if the environment variable \<^verbatim>\<open>AUTOCORRODE_HOME\<close> names a
  checkout of AutoCorrode \<^cite>\<open>"awslabs:autocorrode:2025"\<close>, every \<open>\<lbrakk> \<dots> \<rbrakk>\<close> in its
  \<open>.thy\<close> files is read as a function body, printed back, and read again; the two
  prints must be equal. Of the 962 bracketed texts of the version used when this
  was written, 936 pass. The other 26 are not uRust at all and are listed one by
  one in the test: Isabelle's own statement assumptions \<open>\<lbrakk> A; B \<rbrakk>\<close>, the mixfix
  templates in which AutoCorrode defines the notation (\<open>\<lbrakk>_\<rbrakk>\<close>), and Isabelle text
  such as \<open>\<dots>\<close>. The test found a number of facts about uRust that no written
  description gives: its match arrow is the symbol \<open>\<Rightarrow>\<close>; \<open>ref\<close> is an ordinary
  identifier; the logging macros take a string written \<open>l\<llangle>"\<dots>"\<rrangle>\<close>; a parenthesised
  sequence \<open>(a; b)\<close> is an expression; \<open>assert!\<close> may contain \<open>let\<close>; \<open>let mut (x,
  y) = \<dots>\<close> is accepted.

  Besides the corpus, the test theories contain round-trip tests for every
  construct (a program in the printer's canonical layout comes back unchanged,
  and every accepted program is a fixed point of parse-then-print), rejection
  tests, and, in \<^verbatim>\<open>MicroRust_Cmd_Tests.thy\<close>, tests of the commands: the number of
  entity markups for each scoping rule, navigation, the evaluation order,
  \<open>microrust_file\<close>, export and the backend hook.
\<close>

section\<open>Limitations\<close>

text\<open>
  Isabelle/MicroRust is a deliberately modest slice of the language, and the
  navigation language is the narrowed one of Isabelle/C 2.0. Concretely:

  \<^item> \<^bold>\<open>A subset, chosen for verification.\<close> There is no macro definition
    (\<open>macro_rules!\<close>) and no general token-tree macro: a macro call must have
    expressions as its arguments, which covers \<open>panic!\<close>, \<open>assert!\<close>, \<open>vec!\<close>, the
    formatting macros and \<open>matches!\<close>. There is no \<open>async\<close>, \<open>union\<close>, \<open>extern\<close>, no
    higher-ranked bound (\<open>for<'a>\<close>), no \<open>Fn(A) -> B\<close> sugar, no let chains, no
    lifetimes in \<open>dyn\<close>, no attribute on a pattern or a field of a struct
    expression, and a macro argument that is a statement sequence must be
    parenthesised.
  \<^item> \<^bold>\<open>Fifteen shift/reduce and 48 reduce/reduce conflicts\<close> are reported by ml-yacc
    (visible in the exported \<^verbatim>\<open>MicroRust.grm.desc\<close> when \<open>ml_lex_yacc\<close> is run with
    \<open>[verbose]\<close>); the 48 are two states, once per look-ahead token. All are
    resolved in the intended way and all are of these kinds: a block-like
    expression starting a statement or being the body of a match arm ends it
    (rustc's rule, \<open>\<section>2.1\<close>); \<open>impl<\<close> opens generics rather than a qualified type
    (so \<open>impl <T as Tr>::X {}\<close> is not read); \<open>a as u32 < b\<close> reads \<open><\<close> as the
    start of generic arguments (as \<^verbatim>\<open>rustc\<close> does); \<open>pub (\<close> starts a visibility;
    \<open>..\<close>, \<open>return\<close> and \<open>break\<close> take an operand if one follows.
  \<^item> \<^bold>\<open>No semantics.\<close> There is no type checker, no borrow checker, no trait
    resolution, no macro expansion. A name that resolves nowhere is silently
    left unmarked, a field or method name is never resolved, and a path is
    resolved at its first segment only. Whether a lone capitalised pattern name
    is a constant or a variant, or the name of a variable the author
    capitalised, is decided by the convention alone.
  \<^item> \<^bold>\<open>A deliberate leniency.\<close> The joint-\<open>>\<close> mechanism requires that \<open>>>\<close> and \<open>>=\<close>
    be written without a blank; that is checked. What is not checked is anything
    the grammar of \<^verbatim>\<open>rustc\<close> rejects after parsing: a \<open>let\<close> without a place that
    can be assigned, a non-associative comparison chain that happens to be
    ambiguous in the front end, a \<open>self\<close> parameter outside an \<open>impl\<close>.
  \<^item> \<^bold>\<open>HOL is opaque.\<close> The HOL escapes are kept as text. Reading them as HOL terms
    and types in the right context - the variables of the surrounding function
    are HOL variables there - is the job of a semantic backend.
  \<^item> \<^bold>\<open>Comment placement.\<close> A comment is attached to the node starting at the next
    real token. A comment before a name that does not begin its line is attached
    to that name, not to the construct around it; an annotation meant for a
    statement belongs on its own line above it. A comment before an attribute
    \<open>#[\<dots>]\<close> belongs to the construct the attribute precedes.
  \<^item> \<^bold>\<open>The \<open>text\<close> antiquotation never reaches the generated document.\<close> It runs the
    body through the real \<^ML>\<open>Document_Output.output_document\<close>, but the result only
    reaches a probe reference. This is a limitation of Isabelle itself, not of
    this front-end: the presentation of a command is only consulted for
    document-class commands, which a \<open>thy_decl\<close> command can never be.
  \<^item> \<^bold>\<open>Navigation is not total.\<close> An \<open>Id\<close> root is a leaf and is never navigable by
    \<open>r\<close>/\<open>d\<close>; there is no wrapping; and nodes without a \<open>root\<close> variant (arms,
    parameters, fields, generic parameters) cannot be navigation targets.

\<close>

section\<open>Conclusion\<close>

text\<open>
  Isabelle/MicroRust shows that the design of Isabelle/C Version 2.0 carries
  over to a language that has no specification but a de-facto syntax that the
  community writes down in tools: not a grammar, but a \<^emph>\<open>subset with a syntax
  table\<close>, tested against the code of the framework it was made for. The
  language-specific difficulties of Rust - struct literals against blocks, \<open>>>\<close>
  against generics, statements that end without a semicolon - are isolated in a
  small stream between an ordinary ml-lex lexer and an ordinary ml-yacc grammar;
  everything on top of the parser - positions, environment, hyperlinks,
  antiquotations, navigation, commands - is the C11 design instantiated for a
  new AST. What is documented in \<open>\<section>6\<close> as missing is, in every case, a scoping
  decision rather than an accident: the natural next steps are a semantic
  backend that translates the bodies of \<open>\<section>4\<close> into the shallow embedding of
  AutoCorrode - the antiquotations of \<open>\<section>2.5\<close> then discharge the contracts that
  AutoCorrode otherwise states in HOL next to the program - and the macro
  expansion that a larger subset of Rust needs.

  \pagebreak
\<close>

section\<open>Annex: The MicroRust Grammar as Railroad Diagrams\<close>

subsection\<open>Lexical Structure\<close>

text\<open>
  The lexer is a small ml-lex specification in \<^verbatim>\<open>MicroRust_Parser.thy\<close>. The
  keywords of Rust are reserved (\<open>as\<close>, \<open>break\<close>, \<open>const\<close>, \<open>continue\<close>, \<open>crate\<close>,
  \<open>dyn\<close>, \<open>else\<close>, \<open>enum\<close>, \<open>extern\<close>, \<open>false\<close>, \<open>fn\<close>, \<open>for\<close>, \<open>if\<close>, \<open>impl\<close>, \<open>in\<close>,
  \<open>let\<close>, \<open>loop\<close>, \<open>match\<close>, \<open>mod\<close>, \<open>move\<close>, \<open>mut\<close>, \<open>pub\<close>, \<open>return\<close>, \<open>self\<close>, \<open>Self\<close>,
  \<open>static\<close>, \<open>struct\<close>, \<open>super\<close>, \<open>trait\<close>, \<open>true\<close>, \<open>type\<close>, \<open>unsafe\<close>, \<open>use\<close>,
  \<open>where\<close>, \<open>while\<close>, and, of uRust, \<open>yield\<close>), with the exception of \<open>ref\<close>. An
  \<^emph>\<open>identifier\<close> is a letter or \<open>_\<close> followed by letters, digits and underscores.
  Integer literals are decimal, hexadecimal (\<open>0x\<close>), octal (\<open>0o\<close>) or binary
  (\<open>0b\<close>), with underscores and an optional suffix (\<open>u8\<close> \<open>\<dots>\<close> \<open>u128\<close>, \<open>usize\<close>,
  \<open>i8\<close> \<open>\<dots>\<close> \<open>i128\<close>, \<open>isize\<close>); floats have a fractional part or an exponent. A
  character literal is \<open>'x'\<close> (or \<open>b'x'\<close>), a string \<open>"\<dots>"\<close> (or \<open>b"\<dots>"\<close>) with the
  usual escapes, a raw string \<open>r"\<dots>"\<close>, \<open>r#"\<dots>"#\<close> or \<open>r##"\<dots>"##\<close>. A lifetime or
  label is \<open>'a\<close>. The comment machinery lives in the lexer, as in the other
  front-ends: \<open>//\<close> enters a comment state that runs to the end of the line, \<open>/*\<close>
  a nesting one, and an antiquotation is recognised by a regular expression for
  its head, followed by a nesting-depth counter for a cartouche body. The syntax
  of the head:

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
  The uRust escapes of the lexer:

  \<^rail>\<open>
    hol__escape : '\<llangle>' text '\<rrangle>' subscript? | 'l' '\<llangle>' text '\<rrangle>' subscript?
                | '\<epsilon>' cartouche
    ;
    subscript : (digit__subscript +)
    ;
    isabelle__comment : 'comment__symbol' cartouche
    ;
    attribute : '#[' text ']' | '#![' text ']'
  \<close>
\<close>

subsection\<open>Grammar\<close>

text\<open>
  The grammar is reproduced here slightly simplified: the three kinds of opening
  brace (\<open>LBRACE\<close>, \<open>BLOCKLB\<close>, \<open>STRUCTLB\<close>) are shown as \<open>{\<close>, the joint \<open>>\<close> as the
  operators it stands for, and the operator productions are abbreviated by their
  precedence table: from the loosest to the tightest binding, \<open>=\<close> and the
  compound assignments (right-associative); \<open>..\<close> and \<open>..=\<close>; \<open>||\<close>; \<open>&&\<close>; the
  comparisons \<open>==\<close>, \<open>!=\<close>, \<open><\<close>, \<open>>\<close>, \<open><=\<close>, \<open>>=\<close>; \<open>|\<close>; \<open>^\<close>; \<open>&\<close>; \<open><<\<close> and \<open>>>\<close>;
  \<open>+\<close> and \<open>-\<close>; \<open>*\<close>, \<open>/\<close>, \<open>%\<close>; \<open>as\<close>; the prefix operators \<open>-\<close>, \<open>!\<close>, \<open>*\<close>, \<open>&\<close>,
  \<open>&mut\<close>; and the postfix forms \<open>.\<close>, \<open>?\<close>, calls and indexing.

  \<^rail>\<open>
    source__file : (item *)
    ;
    body : (statement *) expression?
    ;
    statement : ';'
              | (attribute *)
                (let__statement | item | expression ';' | block__like)
    ;
    let__statement : 'let' pattern (':' type)? ('=' expression ('else' block)?)?
                     ';'
                   | 'const' pattern '=' expression ';'
    ;
    block : '{' body '}'
  \<close>

  \<^rail>\<open>
    expression : primary | block__like | expression binary__operator expression
               | prefix__operator expression | postfix__form | range__expression
               | closure | jump
    ;
    primary : literal | path | hol__escape | struct__expression | macro__call
            | '(' ')' | '(' expression ')'
            | '(' expression ',' (expression ',') * ')'
            | '(' statement body ')' | '[' ((expression ',') *) ']'
            | '[' expression ';' expression ']'
    ;
    struct__expression : path '{' ((field__init ',') *) '}'
    ;
    macro__call : path '!' '(' ((expression ',') *) ')'
                | path '!' '[' (expression ((',' expression) *))? ']'
                | path '!' '[' expression ';' expression ']'
                | 'matches!' '(' expression ',' pattern ')'
    ;
    postfix__form : expression 'as' type | expression '?' | expression '.' name
                  | expression '.' name ('::' '<' (generic__argument +) '>')?
                    '(' ((expression ',') *) ')'
                  | expression '(' ((expression ',') *) ')'
                  | expression '[' expression ']'
    ;
    range__expression : expression ('..' | '..=') expression?
                      | ('..' | '..=') expression?
    ;
    jump : 'return' expression? | 'break' label? expression? | 'continue' label?
         | 'yield'
         | 'log' hol__escape hol__escape
    ;
  \<close>

  \<^rail>\<open>
    block__like : (label ':')? ('{' | 'unsafe' '{') body '}' | if__expression
                | 'match' expression '{' (arm *) '}'
                | (label ':')?
                  ('while' condition block | 'loop' block | 'for' pattern 'in'
                      expression block)
    ;
    if__expression : 'if' condition block ('else' (block | if__expression))?
    ;
    condition : expression | 'let' pattern '=' expression
    ;
    arm : (attribute *) pattern ('if' expression)? '=>' expression ','?
    ;
    closure : 'move'? ('|' ((pattern (':' type)? ',') *) '|' | '||')
              (expression | '->' type block)
    ;
    field__init : name (':' expression)? | '..' expression
  \<close>

  \<^rail>\<open>
    pattern : pattern__no__alt ('|' pattern__no__alt) *
    ;
    pattern__no__alt : '_' | '..' | name ('@' pattern__no__alt)?
                     | 'mut' name ('@' pattern__no__alt)?
                     | literal | '-' literal
                     | range__bound ('..' | '..=') range__bound?
                     | path '(' ((pattern ',') *) ')'
                     | path '{' ((field__pattern ',') *) '..'? '}'
                     | '(' ((pattern ',') *) ')' | '[' ((pattern ',') *) ']'
                     | '&' 'mut'? pattern__no__alt | hol__escape
    ;
    field__pattern : name (':' pattern)?
  \<close>

  \<^rail>\<open>
    path : '::'? segment ('::' segment) *
         | '<' type ('as' path)? '>' '::' segment ('::' segment) *
    ;
    segment : name
              ('::'? '<' (generic__argument ((',' generic__argument) *)) '>')?
    ;
    generic__argument : type | lifetime | name '=' type | literal
                      | '{' expression '}'
    ;
    type : path | '&' lifetime? 'mut'? type | '*' ('const' | 'mut') type
         | '(' ((type ',') *) ')'
         | '[' type ']' | '[' type ';' expression ']' | '_' | '!'
         | 'fn' '(' ((type ',') *) ')' ('->' type)?
         | 'impl' bounds | 'dyn' bounds | hol__escape
    ;
    bounds : bound ('+' bound) *
    ;
    bound : '?'? path | lifetime
  \<close>

  \<^rail>\<open>
    item : (attribute *) visibility? item__kind
    ;
    visibility : 'pub' ('(' ('crate' | 'super' | 'self') ')')?
    ;
    item__kind : function | structure
               | 'enum' name generics where? '{' ((variant ',') *) '}'
               | 'unsafe'? 'impl' generics? (path 'for')? type where? '{'
                 (item *) '}'
               | 'unsafe'? 'trait' name generics? (':' bounds)? where? '{'
                 (item *) '}'
               | 'const' name ':' type ('=' expression)? ';'
               | 'static' 'mut'? name ':' type ('=' expression)? ';'
               | 'type' name generics? (':' bounds)? ('=' type)? ';'
               | 'use' use__tree ';'
               | 'mod' name (';' | '{' (item *) '}')
    ;
    function : (('const' | 'unsafe') *) 'fn' name generics? '('
               ((parameter ',') *) ')' ('->' type)? where? (block | ';')
    ;
    parameter : (attribute *)
                ('&' lifetime? 'mut'? 'self' | 'mut'? 'self' (':' type)? |
                    pattern__no__alt ':' type)
    ;
    structure : 'struct' name generics?
                (where? '{' ((field ',') *) '}' | '(' ((type ',') *) ')' where?
                    ';' | where? ';')
    ;
    variant : (attribute *) name
              ('(' ((type ',') *) ')' | '{' ((field ',') *) '}' | '='
                  expression)?
    ;
    generics : '<' ((generic__parameter ',') *) '>'
    ;
    generic__parameter : lifetime (':' lifetime ('+' lifetime) *)?
                       | name (':' bounds)? ('=' type)?
                       | 'const' name ':' type
    ;
    where : 'where' (((type ':' bounds) | (lifetime ':' lifetime)) ',') *
    ;
    use__tree : path ('as' name)? | path '::' '*'
              | path '::' '{' ((use__tree ',') *) '}' | '*'
  \<close>
\<close>

end
