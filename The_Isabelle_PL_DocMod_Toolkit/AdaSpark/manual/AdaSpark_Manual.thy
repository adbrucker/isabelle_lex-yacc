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
theory AdaSpark_Manual
  imports "AdaSpark.AdaSpark"
begin
(*>*)

section\<open>What is Isabelle/AdaSpark\<close>

text\<open>
  Isabelle/AdaSpark is a front-end that lets Ada source text, in the subset that
  SPARK 2014 uses, live inside an Isabelle theory as a first-class citizen:
  parsed by a real grammar, checked incrementally under Isabelle/PIDE (so a
  syntax error or a malformed annotation is reported like any other Isabelle
  error, with the usual jEdit markup, hyperlinking and hovering), and open to
  attaching arbitrary Isabelle-level content - proof obligations, HOL terms,
  arbitrary Isar commands - to specific points of the Ada source via a
  comment-based antiquotation mechanism. It is not an Ada compiler, nor a
  verification tool in its own right: it is the \<^emph>\<open>front-end layer\<close> on which one
  builds a verification tool (a semantic backend, for instance a generator of
  proof obligations from SPARK contracts), a documentation generator, or a
  static analysis.
\<close>

subsection\<open>Context\<close>

text\<open>
  \<^bold>\<open>Ada has an official grammar.\<close> Annex P of the Ada Reference Manual
  \<^cite>\<open>"ada:rm:2012"\<close> is an EBNF syntax summary of the whole language, and it is
  one of the better specifications of a programming language syntax: the
  language was designed to be read, and to be parsed without help from the
  lexer. This is the first member of the family of front-ends whose grammar is
  not a reconstruction.

  \<^bold>\<open>SPARK 2014 is a subset of Ada 2012\<close> \<^cite>\<open>"spark:rm:2014"\<close>, designed so that
  programs can be proved formally correct. It leaves out what makes a program
  hard to reason about (access types are restricted, tasking is restricted,
  exceptions are not handled in proved code) and adds, as \<^emph>\<open>aspects\<close> - the Ada
  2012 syntax for properties attached to a declaration - the language of
  contracts: \<open>Pre\<close> and \<open>Post\<close> conditions, \<open>Contract_Cases\<close>, data-flow
  specifications (\<open>Global\<close>, \<open>Depends\<close>), abstract state (\<open>Abstract_State\<close>,
  \<open>Refined_State\<close>), ghost code, and loop invariants (pragmas). Because contracts
  are syntactically ordinary Ada 2012, the grammar of this front-end needs no
  separate contract language: an aspect is a name with an optional expression,
  and its expressions are Ada expressions, including the conditional and
  quantified expressions that Ada 2012 introduced for exactly this purpose.

  Isabelle/AdaSpark follows Annex P for the subset: packages and their bodies,
  subprograms (procedures, functions, expression functions, null procedures),
  the scalar, array, record, tagged, derived, private and access types,
  statements and exception handlers, the full expression language, aspects and
  pragmas. It leaves out generics, tasking and protected objects, \<open>goto\<close>,
  interfaces, renamings and \<open>separate\<close> units (\<open>\<section>6\<close>). It is \<^emph>\<open>checked against the
  real thing\<close>: the twenty Ada sources of Isabelle's own SPARK verification
  environment \<^cite>\<open>"berghofer:holspark:2011"\<close> are read by the test suite
  (\<open>\<section>5\<close>).

  Isabelle/AdaSpark is the fifth language front-end built on the design of
  \<^bold>\<open>Isabelle/C, Version 2.0\<close>, which this repository's \<^verbatim>\<open>C11/\<close> folder contains
  \<^cite>\<open>"tuong.ea:isabellec:2019" and "tuong.ea:deeply:2019"\<close>, after occam 2, Scala 3
  and MicroRust. It is built from the same parts and carries the same concepts
  over one for one: the \<^verbatim>\<open>ml_lex_yacc\<close> command of this repository (an
  ML-Lex/ML-Yacc integration \<^cite>\<open>"appel.ea:lexical:1994" and
  "tarditi.ea:ml-yacc:2000"\<close>) generates lexer and parser; every node of the
  abstract syntax tree carries a source position plus the comments and
  antiquotations attached to it; a per-theory environment tracks the declared
  names for declaration/use hyperlinking; programmable handlers, a navigation
  language and an evaluation order give meaning to the antiquotations; and a
  family of Isar commands (\<open>adaspark\<close>, \<open>adaspark_body\<close>, \<open>adaspark_file\<close>, \<open>\<dots>\<close>)
  drive all of it. Someone who knows the C11 manual will find the same structure
  in this one, and the same names with \<open>c11\<close> replaced by \<open>adaspark\<close>, \<open>cenv\<close> by
  \<open>aenv\<close>, and \<open>CEnv\<close> by \<open>AEnv\<close>. Like the other members it is \<^emph>\<open>re-entrant\<close>: it is
  built with \<open>ml_lex_yacc [state]\<close>, every parse has a state object of its own,
  and any number of parses may run at the same time.

  What differs is dictated by the language and takes up most of the remainder:
  a language that is case insensitive and in which a name is an expression
  (\<open>\<section>2.1\<close>), the single name space, the sequential visibility and the packages of
  Ada (\<open>\<section>2.2\<close>), and the shape of the abstract syntax (\<open>\<section>4\<close>).
\<close>

section\<open>Main Features of Isabelle/AdaSpark\<close>

text\<open>
  Four pieces fit together to give the \<open>adaspark\<close>-family commands (\<open>\<section>3\<close>) their
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
  The grammar (\<^verbatim>\<open>AdaSpark_Parser.thy\<close>) is an ordinary LALR(1) ml-yacc grammar,
  read directly from the lexer's tokens: Ada has no layout and needs no stream
  between lexer and parser. It covers

  \<^item> \<^bold>\<open>compilation units\<close>: context clauses (\<open>with\<close>, \<open>limited with\<close>, \<open>private with\<close>,
    \<open>use\<close>, \<open>use type\<close>), package specifications with a private part, package
    bodies (with an optional statement part), subprogram declarations and
    bodies;
  \<^item> \<^bold>\<open>declarations\<close>: objects and constants, number declarations, exceptions;
    enumeration, signed and modular integer, floating and fixed point types;
    constrained and unconstrained array types; records with discriminants and
    variant parts; tagged, abstract, limited, derived and private types, record
    extensions; access types; incomplete types; subtypes; procedures, functions,
    expression functions, null procedures, \<open>overriding\<close>, abstract subprograms,
    operator designators (\<open>function "+" \<dots>\<close>); \<open>use\<close> clauses, attribute definition
    clauses, pragmas;
  \<^item> \<^bold>\<open>statements\<close>: \<open>null\<close>, assignment, procedure call, \<open>if\<close>, \<open>case\<close>, \<open>loop\<close> with
    \<open>while\<close> or \<open>for\<close> schemes (over a range or over a container, \<open>reverse\<close>), loop
    and block names, \<open>declare\<close> blocks, \<open>exit\<close>, \<open>return\<close>, \<open>raise\<close>, exception
    handlers, pragmas;
  \<^item> \<^bold>\<open>expressions\<close>: the six levels of operator precedence of Ada (logical,
    relational, adding, unary adding, multiplying, highest), the short-circuit
    forms \<open>and then\<close> and \<open>or else\<close>, membership tests (\<open>in\<close>, \<open>not in\<close>, with
    several choices), attributes (\<open>X'First\<close>, \<open>F'Result\<close>, \<open>X'Old\<close>), qualified
    expressions, selected components and \<open>.all\<close>, calls and indexed components
    and slices (which Ada writes the same way), aggregates (positional, named,
    with \<open>others\<close>, extension and delta aggregates), allocators, conditional
    expressions (\<open>if\<close> and \<open>case\<close>) and quantified expressions (\<open>for all\<close>, \<open>for
    some\<close>);
  \<^item> \<^bold>\<open>SPARK contracts\<close>: the aspect specifications \<open>with Pre => \<dots>, Post => \<dots>,
    Global => \<dots>, Depends => \<dots>, Contract_Cases => \<dots>, SPARK_Mode, Ghost, \<dots>\<close> on
    packages, subprograms, objects and types, and the SPARK pragmas (\<open>Assert\<close>,
    \<open>Loop_Invariant\<close>, \<open>Loop_Variant\<close>, \<open>Assume\<close>, \<open>Annotate\<close>).

  \<^bold>\<open>Case.\<close> Ada is case insensitive. The lexer recognises the reserved words in
  any case and the parser prints them in lower case; identifiers are kept \<^emph>\<open>as
  written\<close> in the AST, and the environment compares them in lower case.

  \<^bold>\<open>A name is an expression.\<close> Ada does not tell a call from an indexed component,
  a slice or a type conversion, \<open>F (X)\<close>, and a selected name \<open>P.X\<close> may denote a
  package member or a record component: the syntax is the same, and so is the
  AST (\<open>EApply\<close>, \<open>ESel\<close>). What a name denotes is decided by the analysis, which
  resolves it against the declarations in scope (\<open>\<section>2.2\<close>).

  \<^bold>\<open>Contracts are aspects.\<close> An aspect \<open>Pre => X > 0\<close> is a name (\<open>Pre\<close>), an
  optional attribute (\<open>Pre'Class\<close>) and an optional expression. The conditional
  and the quantified expression, which Ada 2012 requires to be parenthesised,
  are \<^emph>\<open>associations\<close> inside the parentheses of their context, as in the
  Reference Manual; an expression function \<open>is (\<dots>)\<close> reads its parenthesised
  expression the same way.

  \<^bold>\<open>A deliberate limitation of the lexer.\<close> The apostrophe is both the attribute
  tick and the delimiter of a character literal. The lexer reads \<open>'x'\<close> as a
  character literal whenever three characters make one; the qualified expression
  \<open>T'('a')\<close>, whose operand is a parenthesised character literal, is therefore
  not read.

  \<^bold>\<open>Positions and comments.\<close> Every node carries the exact source range of its
  text, from its first to its last token; a name carries the range of the name.
  Comments, and the antiquotations among them (\<open>\<section>2.3\<close>), are not part of the
  grammar: the lexer collects them and attaches them to the node of the next
  real token. Ada comments are \<open>--\<close> to the end of the line; the annotations of
  the older SPARK language (\<open>--# pre \<dots>\<close>) are plain comments.

  A first example, a package specification with two contracts, the second in the
  style of SPARK 2014 (an expression function, a quantified expression, an
  attribute on a function result):
\<close>

adaspark\<open>
package Sorting
  with SPARK_Mode
is
   type Int_Array is array (Positive range <>) of Integer;

   function Sorted (A : Int_Array) return Boolean is
     (for all I in A'First .. A'Last - 1 => A (I) <= A (I + 1));

   function Max (A : Int_Array) return Integer
     with Pre  => A'Length > 0,
          Post => (for all I in A'Range => A (I) <= Max'Result);
end Sorting;
\<close>

text\<open>
  Ada's lexical structure is part of the grammar too: underscores and based
  literals, exponents, doubled quotes in strings, and reserved words in any
  case. The first two of the following fragments are accepted, the third is not
  (\<open>**\<close> is not associative in Ada):
\<close>

adaspark_expr\<open>16#FF# + 2#1010_1010# * 1_000 + Integer'Last\<close>

adaspark_expr\<open>NOT Done AND THEN (X IN 1 .. 10 OR ELSE Y NOT IN 2 | 4)\<close>

adaspark_expr_reject\<open>2 ** 3 ** 4\<close>

subsection\<open>The AdaSpark Environment, and Declaration/Use Navigation\<close>

text\<open>
  \<^verbatim>\<open>AdaSpark_Env.thy\<close> defines \<open>aenv\<close>, the counterpart of C11's \<open>cenv\<close>: a record
  stored as ordinary \<^verbatim>\<open>Generic_Data\<close>, so that it persists across commands within
  a theory and merges correctly under Isabelle's parallel, incremental checking.
  It holds

  \<^enum> \<open>names\<close>, the declared names - \<^emph>\<open>one\<close> table, as Ada has one name space - each
    with what it was declared as (an object, a constant, a parameter, a type, an
    enumeration literal, a procedure, a function, a package, an exception, a
    component or discriminant, a label);
  \<^enum> \<open>ada_antiq\<close>, the registry of antiquotation handlers (\<open>\<section>2.3\<close>); and
  \<^enum> a per-theory unit counter, used to name the sections processed by an
    \<open>adaspark\<close> command.

  \<^verbatim>\<open>AdaSpark_AnaEval.thy\<close>'s \<open>analyse_and_eval\<close> is a single, purely functional,
  scoped walk over a parsed root that fills \<open>aenv\<close> as it goes. Every name \<^emph>\<open>use\<close>
  is hyperlinked to its declaration via \<^ML>\<open>Position.entity_markup\<close>, reported once
  at the declaration site and once at every use. \<^bold>\<open>A name that resolves nowhere
  is not marked\<close> - unlike C11 and occam 2, where it is underlined. In Ada a name
  routinely comes from a \<open>with\<close>ed unit or a predefined package, none of which
  this pass sees; underlining them would drown the useful markup. The \<^emph>\<open>scoping
  rules\<close> are those of Ada, implemented as shadow-and-restore (the environment is
  a value; a scope simply does not hand its extension back):

  \<^item> \<^bold>\<open>Case insensitivity.\<close> The table is keyed by the lower-case name; a
    declaration or a use is reported with its own spelling. \<open>Count\<close>, \<open>COUNT\<close> and
    \<open>count\<close> are one name.
  \<^item> \<^bold>\<open>Sequential visibility.\<close> A declaration is visible \<^emph>\<open>after\<close> its own
    declaration: there are no forward references, and an object's initial value
    does not see the object. A type sees itself (access types and records are
    recursive) and a subprogram sees itself (recursion). Enumeration literals
    are declared in the scope of their type.
  \<^item> \<^bold>\<open>Subprograms.\<close> The parameters, the aspects, the declarative part, the
    statements and the exception handlers of a subprogram are one scope; a
    parameter is visible in its aspects (\<open>Pre\<close>, \<open>Post\<close>) and in the body. A body
    whose specification is in the same declarative region is hyperlinked to that
    specification, not declared anew.
  \<^item> \<^bold>\<open>Loops and quantifiers.\<close> The variable of a \<open>for\<close> loop is visible in the
    loop's body, that of \<open>for all\<close> and \<open>for some\<close> in the predicate, and nowhere
    else; the range or the array that is iterated over does not see the
    variable. A loop or block name is visible inside it, for \<open>exit L\<close>.
  \<^item> \<^bold>\<open>Types.\<close> The discriminants of a type are visible in its components and
    variant part. The components themselves are declared (their declaration
    sites are reported) but not entered into the table: they are reached by
    selection, \<open>R.F\<close>, and this pass does not resolve selected components - that
    needs types.
  \<^item> \<^bold>\<open>Packages and selected names.\<close> The entities a package \<open>P\<close> declares are
    entered twice: under their own name, in the scope of the package, and under
    their \<^emph>\<open>qualified\<close> name \<open>p.x\<close>, which survives it. A selected name \<open>P.X\<close>
    hyperlinks \<open>P\<close> and, as \<open>p.x\<close> is known, \<open>X\<close>; nested packages work the same
    way (\<open>P.Q.X\<close>). The body of a package re-opens the scope of its specification
    (\<open>p.x\<close> becomes visible as \<open>x\<close>), and so does a \<open>use P;\<close> clause, which makes
    the names of a package directly visible; a \<open>use\<close> clause in a context clause
    is local to its compilation unit.
  \<^item> \<^bold>\<open>Calls and aggregates.\<close> The formal-parameter names of a call \<open>F (X => 1)\<close> are
    not resolved - they belong to the called subprogram, whose declaration the
    caller's scope does not show. The choices of an \<^emph>\<open>aggregate\<close>, on the other
    hand, are expressions, which is what the dependency aspects of SPARK need:
    in \<open>Depends => (Y => X)\<close> and \<open>Global => (Input => V)\<close> the names \<open>Y\<close>, \<open>X\<close> and
    \<open>V\<close> are hyperlinked to their declarations.
  \<^item> \<^bold>\<open>A compilation file is the one root whose names persist.\<close> After \<open>adaspark\<close>
    has analysed it, the names its units declare - and, for a package, its
    qualified names - stay in \<open>aenv\<close> for the following units, as the units of a
    program library do.

  Being persistent per-theory data - the same idiom a simp set uses - is what
  lets Ada fragments be freely \<^emph>\<open>interleaved\<close> with arbitrary Isar content and
  still resolve a name used in one fragment back to its declaration in an
  earlier one. The flip side is that \<open>aenv\<close> only ever grows across a theory; the
  commands \<open>set_aenv_default\<close> and \<open>reset_aenv\<close> (\<open>\<section>3\<close>) give a theory explicit
  control. A small example of the library mechanism and the scoping rules (hover
  over the names in jEdit): a package, a client that selects from it, and a body
  that re-opens the specification and completes it.
\<close>

adaspark\<open>
package Arith is
   Limit : constant := 100;
   function Twice (N : Integer) return Integer;
end Arith;
\<close>

adaspark\<open>
with Arith;
procedure Total is
   Sum : Integer := Arith.Twice (Arith.Limit);
begin
   for I in 1 .. Arith.Limit loop
      Sum := Sum + I;
   end loop;
end Total;
\<close>

adaspark\<open>
package body Arith is
   function Twice (N : Integer) return Integer is
   begin
      return 2 * N;
   end Twice;
end Arith;
\<close>

text\<open>
  The name \<open>Twice\<close> of the function body is a use of its specification, the
  parameter \<open>N\<close> is visible in the \<open>return\<close> statement only. A declaration is
  visible after itself - \<open>Later\<close> is not yet declared in the initial value of
  \<open>First\<close> and is therefore not marked, \<open>First\<close> and the names \<open>Put_Line\<close> and
  \<open>Hello\<close>, which no declaration in this theory introduces, are not marked
  either:
\<close>

adaspark\<open>
procedure Scopes is
   First : Integer := Later;
   Later : Integer := First;
begin
   Put_Line ("Hello");
   first := LATER;
end Scopes;
\<close>

subsection\<open>Programmable AdaSpark-Antiquotations, and Handlers\<close>

text\<open>
  A comment of the shape \<open>@tag[navi](level) \<open>body\<close>\<close> - an \<open>@\<close>-prefixed tag, an
  optional bracketed navigation string (\<open>\<section>2.4\<close>), an optional parenthesised
  integer \<open>level\<close> (\<open>0\<close> when omitted), and a body written as a nested Isabelle
  cartouche or, equivalently, a double-quoted string - is recognised lexically
  inside a \<open>--\<close> comment, and attached to whichever AST node it resolves against
  (\<open>\<section>2.4\<close>). Any other comment is kept as plain text (\<open>Raw_txt\<close>). A comment is
  attached to the AST node that begins at the \<^emph>\<open>next real token\<close>, so an
  annotation is written on the line(s) \<^emph>\<open>above\<close> what it annotates:

  \<^verbatim>\<open>--@ highlight\<close>

  (a tag alone is a complete antiquotation with an empty body). A \<^emph>\<open>bodyless\<close> tag
  is recognised only directly after the comment opener (\<open>--@\<close>), so that an \<open>@\<close>
  in running text - an e-mail address, a documentation tag - is not mistaken for
  an antiquotation; a tag followed by a body is one anywhere in a comment.

  The \<open>tag\<close> selects a \<^emph>\<open>handler\<close>: an ordinary ML function of type

  \<^verbatim>\<open>type type_antiq_fun =
    aenv * pos AdaSpark_Ast.root * int -> (string * pos) ->
    Context.generic -> Context.generic\<close>

  registered once, ahead of time, via \<open>AEnv.store_antiq (tag, handler)\<close>. When
  \<open>analyse_and_eval\<close> reaches a node carrying an \<open>@tag \<dots>\<close> antiquotation, it
  resolves the navigation string against the closest-surrounding-context stack
  (\<open>\<section>2.4\<close>) into a single concrete \<open>root\<close> value, then instantiates the handler
  with \<open>(aenv, resolved_root, level)\<close> and the body text together with its own
  source position; a handler is never itself responsible for interpreting
  \<open>u\<close>/\<open>U\<close>/\<open>r\<close>/\<open>d\<close>.

  \<open>Context.generic\<close> rather than \<open>theory\<close>, deliberately: a handler may do
  anything a genuine Isar toplevel command can, including running real ML code
  at the ML environment level (the \<open>ML\<close> antiquotation, below). All collected
  actions are folded into one \<open>Context.generic -> Context.generic\<close> function by
  ordinary composition and lifted to the toplevel exactly once, at the end
  (\<open>full_eval_and_store\<close> in \<^verbatim>\<open>AdaSpark.thy\<close>). Most handlers never need this
  generality: an ordinary \<open>theory -> theory\<close> function is \<^emph>\<open>recaptured\<close> by
  \<open>AEnv.lift_theory_antiq\<close> when it is registered. A first handler, which turns a
  plain comment into a checked diagnostic reported against the exact node the
  comment resolves to:
\<close>

ML\<open>
val todo_antiq =
  let
    fun handler (_ : AEnv.aenv, ast, level) (body, _ : Position.T) thy =
      (warning ("TODO (level " ^ Int.toString level ^ ") at " ^
                Position.here (AnaEval.pos_of_root ast) ^ ": " ^ body);
       thy)
  in AEnv.store_antiq ("todo", AEnv.lift_theory_antiq handler) end
\<close>
setup\<open>todo_antiq\<close>

adaspark\<open>
procedure Clear (X : out Integer) is
begin
   --@ todo \<open>check the range of X first\<close>
   X := 0;
end Clear;
\<close>

text\<open>
  A tag with no registered handler is a hard error: every tag that can appear in
  a theory's source must be registered before that theory's \<open>adaspark\<close>-family
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
  nodes share its leftmost source position (the classic case in Ada: a
  compilation unit, its declaration and the name that begins it all start at the
  same token).

  \<^bold>\<open>Context.\<close> Every antiquotation resolves, by default, to its \<^emph>\<open>closest
  surrounding context\<close>: the walk threads a stack of enclosing nodes. Four kinds
  of node push themselves on that stack at every level of nesting:
  \<^emph>\<open>expressions\<close>, \<^emph>\<open>subtype indications\<close>, \<^emph>\<open>statements\<close> and \<^emph>\<open>declarations\<close> - the
  root type has the variants \<open>Expr\<close>, \<open>Type\<close>, \<open>Stmt\<close>, \<open>Decl\<close> in addition to \<open>Id\<close>
  for a bare name, \<open>Body\<close> for a statement sequence and \<open>Crate\<close> for a source
  file. Everything else - compilation units, parameters, components, aspects,
  associations, choices, exception handlers - never pushes and resolves to what
  is on top, which is what makes every node kind a valid place for a comment. A
  comment in front of a compilation unit is therefore in the context of the
  source file, and \<open>[d]\<close> reaches the unit's declaration.

  \<^bold>\<open>Navigation.\<close> The bracketed \<open>[navi]\<close> string points an antiquotation \<^emph>\<open>away\<close>
  from its closest context. Its syntax and its rules are exactly those of C11:
  written \<open>(u|U)*(r|d)*\<close>, zero or more ascend steps followed by zero or more
  descend steps. \<open>u\<close> ascends one level (a lone, final \<open>u\<close> is a no-op); \<open>U\<close>
  ascends past a whole run of consecutive ancestors of the same category; \<open>r\<close>
  advances a 1-based cursor among the current node's children in source order
  and \<open>d\<close> descends into the child at the cursor (cursor 1 if no \<open>r\<close> preceded
  it). There is no wrapping: a cursor beyond the children, or \<open>d\<close> on a leaf, is
  a hard error reported at the antiquotation's own tag position. The children of
  a node, in source order, are its sub-expressions, subtype indications,
  statements and declarations; the associations, choices, parameters, components
  and aspects of a node are \<^emph>\<open>flattened into it\<close>, so the children of an
  assignment are its two sides, those of a call its function name followed by
  the expressions of its arguments, and those of a subprogram declaration the
  types of its parameters, the result type and the expressions of its aspects. A
  few examples (the node a handler receives, on the statement \<open>X := X + Y;\<close>):

  \<^item> no navigation: the statement itself;
  \<^item> \<open>[d]\<close> or \<open>[rd]\<close>: its first child, \<open>X\<close>; \<open>[rrd]\<close>: its second child, \<open>X + Y\<close>;
  \<^item> \<open>[uu]\<close>: the enclosing subprogram.

\<close>

adaspark\<open>
procedure Sum (X, Y : in out Integer) is
begin
   --@ probe_ast[rrd]
   --@ highlight[rrd]
   X := X + Y;
end Sum;
\<close>

ML\<open>
val _ = if AdaSpark_Pp.pp_root (!ADA_AST) = "X + Y"
  then writeln "[rrd] reaches the second operand"
        else error "navigation"
\<close>

subsection\<open>Standard Antiquotations\<close>

text\<open>
  \<^verbatim>\<open>AdaSpark_AnaEval.thy\<close> registers the same eight demonstration antiquotations
  as C11. All of them are written in a comment and see the node their navigation
  string selects:

  \<^descr> \<open>probe_aenv\<close> stores the current \<open>aenv\<close> into an ML reference (\<open>AENV\<close>) for
    inspection.
  \<^descr> \<open>probe_ast\<close> prints the resolved node, pretty-printed back to Ada, with its
    level, and stores it into \<open>ADA_AST\<close>.
  \<^descr> \<open>highlight\<close> marks the resolved node's source range in the editor - the
    quickest way to \<^emph>\<open>see\<close> what a navigation string selects.
  \<^descr> \<open>term \<open>t\<close>\<close> reads \<open>t\<close> as a HOL term in the theory's current context; a
    malformed or ill-typed term is a real Isabelle error positioned inside the
    Ada comment.
  \<^descr> \<open>ML \<open>code\<close>\<close> runs \<open>code\<close> as ML source, so a definition written in an Ada
    comment becomes a later-visible ML binding.
  \<^descr> \<open>text \<open>t\<close>\<close> runs \<open>t\<close> through the document machinery of Isabelle's \<open>text\<close>
    command, so that inner antiquotations are checked and hyperlinked (the
    result is stashed, not typeset; see \<open>\<section>6\<close>).
  \<^descr> \<open>definition \<open>d\<close>\<close> is Isabelle's \<open>definition\<close> command: the new constant is a
    genuine, later-visible theory constant.
  \<^descr> \<open>lemma \<open>l\<close>\<close> states \<open>l\<close> and proves it with one terminal \<open>by\<close> proof -
    proof-carrying code: a formal property of the program's constants, \<^emph>\<open>actually
    proved\<close>, right where the Ada text that motivates it lives. A failed proof is
    an Isabelle error positioned in the comment.

\<close>

section\<open>The AdaSpark Main Commands\<close>

text\<open>

  \<^descr> \<open>adaspark \<open>\<dots>\<close>\<close> parses its argument as a source file - a sequence of
    compilation units - runs \<open>analyse_and_eval\<close>, chains the collected
    antiquotation actions in level order, and stores the AST under a fresh key,
    reported as \<open>[stored as Theory#N]\<close>.
  \<^descr> \<open>adaspark_body \<open>\<dots>\<close>\<close> is the same for a statement sequence, as it stands
    between \<open>begin\<close> and \<open>end\<close>.
  \<^descr> \<open>adaspark_file \<open>path\<close>\<close> is the same as \<open>adaspark\<close>, reading the source file
    from an external file (resolved relative to the theory's master directory
    via \<^ML>\<open>Resources.parse_file\<close>, so file positions and build-dependency tracking
    come for free). The extension is the user's choice: \<open>.ads\<close> and \<open>.adb\<close> in the
    examples of this repository.
  \<^descr> \<open>adaspark_expr \<open>\<dots>\<close>\<close>, \<open>adaspark_type \<open>\<dots>\<close>\<close> and \<open>adaspark_ident \<open>\<dots>\<close>\<close> parse a
    bare expression, subtype indication, respectively name. The analysis still
    runs, for its hyperlinks, but its antiquotation actions are discarded: a
    standalone fragment is a syntax check, not a program.
  \<^descr> \<open>adaspark_reject\<close>, \<open>adaspark_body_reject\<close>, \<open>adaspark_expr_reject\<close>,
    \<open>adaspark_type_reject\<close> and \<open>adaspark_ident_reject\<close> document a fragment as
    correctly \<^emph>\<open>not\<close> accepted by the corresponding entry point. They are silent
    (no error markup is left on the expected failure) and are the means of
    writing negative tests.
  \<^descr> \<open>set_aenv_default\<close> and \<open>reset_aenv\<close> control the ever-growing \<open>aenv\<close>.
    \<open>set_aenv_default\<close> nominates what \<open>aenv\<close> holds \<^emph>\<open>right now\<close> as the snapshot a
    later \<open>reset_aenv\<close> restores; with no earlier \<open>set_aenv_default\<close> in scope
    \<open>reset_aenv\<close> falls back to the empty \<open>aenv\<close>. \<^verbatim>\<open>AdaSpark.thy\<close> itself
    nominates, as its last step, the environment holding exactly the standard
    antiquotation handlers.
  \<^descr> \<open>setup_backend \<open>f\<close>\<close> installs the \<^emph>\<open>semantic backend\<close>: \<open>f\<close> is an ML expression
    of type \<open>Position.T AdaSpark_Ast.root -> theory -> theory\<close>, evaluated like
    the argument of Isabelle's own \<open>setup\<close> command. At the very end of every
    \<open>adaspark\<close>, \<open>adaspark_body\<close> and \<open>adaspark_file\<close> - after the antiquotation
    actions have run and the AST is stored - the installed function is applied
    to the parsed root and the theory the command has produced, and its result
    is the theory the command returns; the fragment commands never trigger it.
    The default is \<open>K I\<close>, which \<open>setup_backend \<open>K I\<close>\<close> restores. The function is
    kept in the theory's context (separately from \<open>aenv\<close>, so \<open>reset_aenv\<close> does
    not uninstall it) and is inherited by later theories. This is where a
    generator of proof obligations from SPARK contracts would plug in.
  \<^descr> \<open>adaspark_export \<open>path\<close> exports \<open>key\<^sub>1\<close> \<open>\<dots>\<close> \<open>key\<^sub>n\<close>\<close> renders previously stored
    sections - given by the store keys the accepting commands report - back to
    Ada text with \<^ML>\<open>AdaSpark_Pp.pp_root\<close> and writes them to \<open>path.ada\<close>. With
    \<open>[verbatim]\<close> after the command name the original source text is written
    instead of the (deliberately simple, canonical three-space layout)
    pretty-printer's.

  The accepting commands are \<open>thy_decl\<close> commands, because they change theory
  data (\<open>adaspark_file\<close> is \<open>thy_load\<close>, so that Isabelle tracks the file
  dependency); the \<open>_reject\<close> commands, which store nothing, are \<open>diag\<close>. Isabelle
  evaluates a \<open>diag\<close> command asynchronously, in parallel with the commands that
  follow; that is harmless here, because every parse has its own state (\<open>\<section>2.1\<close>).
\<close>

subsection\<open>A Worked Example\<close>

text\<open>
  A package in the style of SPARK 2014: a constant mirrored in HOL, a loop with
  invariants, and a contract stated as an Ada expression. The first annotation
  introduces a HOL constant for the bound (a \<open>definition\<close>, evaluated at level
  0), the second proves a fact about it (level 1, so after the definition), the
  third checks a HOL term mentioning it (level 2).
\<close>

adaspark\<open>
--@ definition \<open>bound :: nat where "bound = 10"\<close>
--@ lemma(1) \<open>bound_double: "bound * 2 = 20" by (simp add: bound_def)\<close>
--@ term(2) \<open>bound + 1\<close>
package Counting
  with SPARK_Mode
is
   Bound : constant := 10;

   function Count_Up return Natural
     with Post => Count_Up'Result = Bound;
end Counting;
\<close>

adaspark\<open>
package body Counting
  with SPARK_Mode
is
   function Count_Up return Natural is
      I : Natural := 0;
   begin
      --@ highlight
      while I < Bound loop
         pragma Loop_Invariant (I <= Bound);
         I := I + 1;
      end loop;
      return I;
   end Count_Up;
end Counting;
\<close>

thm bound_def bound_double

subsection\<open>Source Files, Backends, Export\<close>

text\<open>
  \<open>adaspark_file\<close> reads an external file (here one of the examples of this
  repository: a bounded stack, with contracts in the specification and bodies in
  a second file) and stores its AST; the names of its units are visible to the
  following ones. A semantic backend is an ML function installed with
  \<open>setup_backend\<close>. The following one only counts the aspects that the subprogram
  declarations of a package carry; a real backend would translate them into
  proof obligations. It is applied to the \<^emph>\<open>parsed root\<close> and the theory, after
  the annotations have run:
\<close>

ML\<open>
val contract_counts = Unsynchronized.ref ([] : int list)
\<close>

setup_backend\<open>fn root => fn thy =>
  (case root of
     AdaSpark_Ast.Crate units =>
       let
         fun aspects (AdaSpark_Ast.DSpec (_, _, asps, _)) = length asps
           | aspects _ = 0
         fun in_unit
           (AdaSpark_Ast.Unit (_, AdaSpark_Ast.DPackage (_, _, vis, _, _), _)) =
               fold (fn d => fn n => n + aspects d) vis 0
           | in_unit _ = 0
       in (contract_counts := fold (fn u => fn n => n + in_unit u) units 0
                              :: !contract_counts; thy) end
   | _ => thy)\<close>

adaspark_file \<open>../examples/stacks.ads\<close>

adaspark_file \<open>../examples/stacks.adb\<close>

setup_backend\<open>K I\<close>

ML\<open>
val _ = writeln ("contracts per source file seen by the backend: " ^
                 commas (map Int.toString (rev (!contract_counts))))
\<close>

text\<open>
  A second set of examples - binary search with loop invariants, a global
  counter with abstract state and data-flow contracts, discriminated records
  with case expressions and contract cases, and a tagged type with a private
  extension:
\<close>

adaspark_file \<open>../examples/search.ads\<close>

adaspark_file \<open>../examples/search.adb\<close>

adaspark_file \<open>../examples/counters.ads\<close>

adaspark_file \<open>../examples/counters.adb\<close>

adaspark_file \<open>../examples/shapes.ads\<close>

adaspark_file \<open>../examples/animals.ads\<close>

text\<open>
  An accepted unit can be written back as Ada, in the canonical layout of the
  pretty-printer (or, with \<open>[verbatim]\<close>, as it was written): the aspects of a
  subprogram or package on lines of their own, three-space indentation, keywords
  in lower case. The key of the unit is the one the command reported when it was
  stored. This is the way a generated or normalised file is produced from a
  theory:
\<close>

adaspark\<open>
function Id (X : Integer) return Integer is begin return X; end Id;
\<close>

ML\<open>
val key_of_last =
  let val AEnv.mk {units, ...} = AEnv.get (Context.Theory @{theory})
  in AEnv.ast_store_key @{theory} (units - 1) end
val _ = writeln ("the last unit is stored as " ^ key_of_last)
val _ = writeln (case AEnv.get_ast key_of_last @{theory} of
                   SOME root => AdaSpark_Pp.pp_root root | NONE => "?")
\<close>

section\<open>The Abstract Syntax\<close>

text\<open>
  Unlike C11, whose AST is a pruned port of the Haskell \<^verbatim>\<open>language-c\<close> tree, there
  is no pre-existing reference AST for Ada to port. The AST in \<^verbatim>\<open>adaspark_ast.ML\<close>
  is therefore an educated design of this project, following the grammar of
  Annex P of the Reference Manual \<^cite>\<open>"ada:rm:2012"\<close>: one datatype per syntactic
  category, one constructor per alternative, close enough to the concrete syntax
  that \<^ML>\<open>AdaSpark_Pp.pp_root\<close> can print any parsed program back as Ada. Layout is
  \<^emph>\<open>not\<close> part of it: the printer regenerates a canonical layout. Parentheses
  \<^emph>\<open>are\<close> part of it (\<open>EParen\<close>), so the printer needs no precedence reasoning. All
  datatypes are parametrised by the position type \<open>'a\<close> (instantiated with
  \<^verbatim>\<open>Position.T\<close>), and every constructor but the pure wrappers carries a \<open>'a
  nodeInfo\<close> as its last field.

  \<^bold>\<open>Annotations\<close>, shared with C11 and so with everything built on it: \<open>nodeInfo\<close>
  is a bare position or a position with the comments attached; a \<open>comment\<close> is
  raw text or an antiquotation (tag, navigation steps, level, cartouche with its
  position); \<open>ident\<close> is a name with its \<open>nodeInfo\<close>.

  \<^bold>\<open>Syntactic categories\<close> (the constructors are those of \<^verbatim>\<open>adaspark_ast.ML\<close>; the
  prefix \<open>a\<close> stands for ``Ada''):

  \<^item> \<open>aExpr\<close>: the literals \<open>EInt\<close>, \<open>EReal\<close>, \<open>EChar\<close>, \<open>EStr\<close> (all as written),
    \<open>ENull\<close>, names \<open>EId\<close> and \<open>ESel\<close> (\<open>P.X\<close>) and \<open>EDeref\<close> (\<open>X.all\<close>), \<open>EApply\<close> (a
    call, an indexed component, a slice or a conversion), \<open>EAttr\<close> and \<open>EQual\<close>,
    the operators \<open>EUn\<close>, \<open>EBin\<close> (with the \<open>binop\<close>s, among them \<open>AndThen\<close> and
    \<open>OrElse\<close>) and \<open>EIn\<close> (a membership test with its choices, \<open>not in\<close> by a
    flag), \<open>EParen\<close>, the aggregates \<open>EAgg\<close>, \<open>EExtAgg\<close> and \<open>EDeltaAgg\<close>, the
    allocator \<open>ENew\<close>, and the conditional and quantified expressions \<open>EIf\<close>,
    \<open>ECase\<close> and \<open>EQuant\<close>; with \<open>aAssoc\<close> (\<open>APos\<close>, \<open>ARange\<close>, \<open>ANamed\<close>), \<open>aChoice\<close>
    (\<open>ChExpr\<close>, \<open>ChRange\<close>, \<open>ChOthers\<close>) and \<open>aIter\<close> (\<open>IterIn\<close>, \<open>IterOf\<close>, each with
    a flag for \<open>reverse\<close>).
  \<^item> \<open>aSub\<close>, a subtype indication: a subtype mark (an expression, as Ada does not
    separate names from expressions) with an optional \<open>not null\<close> and an optional
    range constraint.
  \<^item> \<open>aTypeDef\<close>: \<open>TEnum\<close>, \<open>TRange\<close>, \<open>TMod\<close>, \<open>TDigits\<close>, \<open>TDelta\<close>, \<open>TArray\<close> (with
    its \<open>aIdx\<close> list), \<open>TRecord\<close> (an \<open>aRecDef\<close> with components and a variant
    part, flags for \<open>abstract\<close>, \<open>tagged\<close> and \<open>limited\<close>), \<open>TDerived\<close> (with an
    \<open>aExt\<close>: no extension, a record extension, \<open>with private\<close>), \<open>TPrivate\<close> and
    \<open>TAccess\<close>.
  \<^item> \<open>aDecl\<close>: \<open>DObject\<close>, \<open>DNumber\<close>, \<open>DException\<close>, \<open>DType\<close>, \<open>DIncomplete\<close>,
    \<open>DSubtype\<close>, the subprograms \<open>DSpec\<close>, \<open>DNullProc\<close>, \<open>DExprFun\<close> and \<open>DBody\<close> (on
    an \<open>aSpec\<close>: its \<open>aParam\<close>s, with a mode, and the result), the packages
    \<open>DPackage\<close> and \<open>DPackageBody\<close>, \<open>DUse\<close>, \<open>DPragma\<close> and \<open>DAttrDef\<close>; every
    declaration that can carry aspects has a list of \<open>aAspect\<close>s.
  \<^item> \<open>aStmt\<close>: \<open>SNull\<close>, \<open>SAssign\<close>, \<open>SCall\<close>, \<open>SIf\<close>, \<open>SCase\<close>, \<open>SLoop\<close> (with an
    \<open>aScheme\<close>: plain, \<open>while\<close>, \<open>for\<close>), \<open>SBlock\<close>, \<open>SExit\<close>, \<open>SReturn\<close>, \<open>SRaise\<close>,
    \<open>SPragma\<close>, and the exception \<open>aHandler\<close>s.
  \<^item> \<open>aUnit\<close>: a compilation unit, a list of context clauses (\<open>CWith\<close>, \<open>CUse\<close>) and
    a declaration.
  \<^item> \<open>root\<close>: the result of a parse by entry point - \<open>Id\<close>, \<open>Expr\<close>, \<open>Type\<close>, \<open>Body\<close>
    or \<open>Crate\<close> - plus \<open>Stmt\<close> and \<open>Decl\<close>, never produced by a parse but used by
    the analysis as the closest context of an annotation on a statement or a
    declaration.

  Where the grammar is ambiguous without name resolution, the AST follows the
  syntactic reading and leaves the decision to the analysis: \<open>F (X)\<close> is an
  \<open>EApply\<close> whether \<open>F\<close> is a function, an array or a type, and \<open>P.X\<close> is an \<open>ESel\<close>
  whether \<open>P\<close> is a package or a record. The name that closes a unit (\<open>end
  Total;\<close>) is syntactically read but not kept, and not checked against the name
  that opened it.
\<close>

section\<open>The Test Corpus: the SPARK Sources of Isabelle\<close>

text\<open>
  A grammar is only as good as the programs it has been tested on. The test
  theory \<^verbatim>\<open>AdaSpark_Tests.thy\<close> therefore ends with a corpus test: every \<^verbatim>\<open>.ads\<close>
  and \<^verbatim>\<open>.adb\<close> file below the directory \<^verbatim>\<open>src/HOL/SPARK\<close> of the Isabelle
  distribution - the examples of the HOL-SPARK verification environment
  \<^cite>\<open>"berghofer:holspark:2011"\<close>, twenty files, among them a greatest common
  divisor, a longest increasing subsequence, an integer square root, a
  RIPEMD-160 implementation, word operations and a package of complex numbers -
  is read as a source file, printed back, and read again; the two prints must be
  equal. All twenty pass. They are SPARK 83 and Ada 95 programs, whose \<^verbatim>\<open>--#\<close>
  annotations are comments for this parser; the contracts of SPARK 2014 are
  exercised by the round-trip tests for every construct and by the examples of
  this repository (\<^verbatim>\<open>examples/\<close>).

  Besides the corpus, the test theories contain round-trip tests (a program in
  the printer's canonical layout comes back unchanged, and every accepted
  program is a fixed point of parse-then-print), rejection tests, and, in
  \<^verbatim>\<open>AdaSpark_Cmd_Tests.thy\<close>, tests of the commands: the number of entity markups
  for each scoping rule (for instance that a name is not visible before its
  declaration, that a body is hyperlinked to its specification, that a \<open>use\<close>
  clause makes the names of a package visible), navigation, the evaluation
  order, \<open>adaspark_file\<close> on the examples, export and the backend hook.
\<close>

section\<open>Limitations\<close>

text\<open>
  Isabelle/AdaSpark is a deliberately modest slice of the language, and the
  navigation language is the narrowed one of Isabelle/C 2.0. Concretely:

  \<^item> \<^bold>\<open>A subset, chosen for verification.\<close> There are no generic units, no tasks and
    protected objects, no \<open>goto\<close> and no labels, no interfaces, no renaming
    declarations, no \<open>separate\<close> subunits, no representation clauses other than
    attribute definitions, no entries, and no pragmas on a compilation unit
    before its context clauses. The reserved words of the left-out constructs
    are lexed, and a program that uses one is rejected, so that a fragment is
    never silently misread. A program in the left-out part of Ada is not read at
    all.
  \<^item> \<^bold>\<open>Eleven shift/reduce conflicts, no reduce/reduce conflict\<close> are reported by
    ml-yacc (visible in the exported \<^verbatim>\<open>AdaSpark.grm.desc\<close> when \<open>ml_lex_yacc\<close> is
    run with \<open>[verbose]\<close>). Each is resolved by shifting, and each is intended:
    the keyword \<open>null\<close> (a null statement or the literal, and the \<open>not null\<close> of a
    subtype indication), the bar that extends the choices of a membership test,
    the range \<open>L .. H\<close> as an association against a choice, the commas of a
    \<open>case\<close> expression against those of the association list around it, \<open>not\<close>
    after a parameter's mode, and \<open>with\<close> after a derived type, which opens a
    record extension. As a consequence an object declaration \<open>X : not null T\<close>
    and a derived type definition that is directly followed by aspects are not
    read (a \<open>not null access\<close> parameter is).
  \<^item> \<^bold>\<open>Character literals and the tick.\<close> The qualified expression \<open>T'('a')\<close> is not
    read (\<open>\<section>2.1\<close>).
  \<^item> \<^bold>\<open>No semantics.\<close> There is no type checker, no overload resolution, no static
    semantics. A name that resolves nowhere is silently left unmarked, a
    selected component or an attribute is never resolved (a package member \<open>P.X\<close>
    is, when \<open>P\<close> is known to this theory), formal-parameter names in a call are
    not resolved, and one name has one entry - an overloaded name has the entry
    of its latest declaration, and an overloaded subprogram body is linked to
    the first specification of that name in its declarative region.
  \<^item> \<^bold>\<open>A deliberate leniency.\<close> What the Reference Manual forbids after parsing is
    not checked: the logical operators \<open>and\<close>, \<open>or\<close> and \<open>xor\<close> may be mixed
    without parentheses (\<open>A and B or C\<close> reads as \<open>(A and B) or C\<close>), the name
    after \<open>end\<close> is not compared with the name of the unit, a \<open>function\<close> without
    a \<open>return\<close> statement or an \<open>in\<close> parameter that is assigned to is accepted.
  \<^item> \<^bold>\<open>Contracts are not interpreted.\<close> An aspect is a name and an expression; that
    \<open>Pre\<close> is a precondition and \<open>Depends\<close> a flow contract is the business of a
    semantic backend. The one exception is the resolution of the names a
    contract mentions (\<open>\<section>2.2\<close>).
  \<^item> \<^bold>\<open>Comment placement.\<close> A comment is attached to the node starting at the next
    real token. A comment before a name that does not begin its line is attached
    to that name, not to the construct around it; an annotation meant for a
    statement belongs on its own line above it.
  \<^item> \<^bold>\<open>The \<open>text\<close> antiquotation never reaches the generated document.\<close> It runs the
    body through the real \<^ML>\<open>Document_Output.output_document\<close>, but the result only
    reaches a probe reference. This is a limitation of Isabelle itself, not of
    this front-end: the presentation of a command is only consulted for
    document-class commands, which a \<open>thy_decl\<close> command can never be.
  \<^item> \<^bold>\<open>Navigation is not total.\<close> An \<open>Id\<close> root is a leaf and is never navigable by
    \<open>r\<close>/\<open>d\<close>; there is no wrapping; and nodes without a \<open>root\<close> variant
    (associations, parameters, components, aspects, handlers) cannot be
    navigation targets.

\<close>

section\<open>Conclusion\<close>

text\<open>
  Isabelle/AdaSpark shows that the design of Isabelle/C Version 2.0 carries over
  to a language that has a real, published grammar, and for which the subset
  used by a verification community is defined by a standard document - the Ada
  Reference Manual and the SPARK 2014 Reference Manual - rather than by a tool.
  The grammar of the subset is an ordinary ml-yacc grammar over an ordinary
  ml-lex lexer, with no stream in between; the language-specific difficulties
  are of a different kind than in the other front-ends - a case-insensitive
  language, names that are expressions, a tick that is also a quote - and are
  resolved in the lexer, in the AST and in the analysis. Everything on top of
  the parser - positions, environment, hyperlinks, antiquotations, navigation,
  commands - is the C11 design instantiated for a new AST. What is documented in
  \<open>\<section>6\<close> as missing is, in every case, a scoping decision rather than an accident:
  the natural next steps are a semantic backend that generates proof obligations
  from the contracts of \<open>\<section>2.1\<close> - the antiquotations of \<open>\<section>2.5\<close> then discharge
  them in the comments next to the program, as the \<open>lemma\<close> above - and the
  generic units and tasking constructs that a larger subset of Ada needs.

  \pagebreak
\<close>

section\<open>Annex: The AdaSpark Grammar as Railroad Diagrams\<close>

subsection\<open>Lexical Structure\<close>

text\<open>
  The lexer is a small ml-lex specification in \<^verbatim>\<open>AdaSpark_Parser.thy\<close>. The
  reserved words of the subset are recognised in any case (\<open>abs\<close>, \<open>abstract\<close>,
  \<open>access\<close>, \<open>aliased\<close>, \<open>all\<close>, \<open>and\<close>, \<open>array\<close>, \<open>begin\<close>, \<open>body\<close>, \<open>case\<close>,
  \<open>constant\<close>, \<open>declare\<close>, \<open>delta\<close>, \<open>digits\<close>, \<open>else\<close>, \<open>elsif\<close>, \<open>end\<close>, \<open>exception\<close>,
  \<open>exit\<close>, \<open>for\<close>, \<open>function\<close>, \<open>if\<close>, \<open>in\<close>, \<open>is\<close>, \<open>limited\<close>, \<open>loop\<close>, \<open>mod\<close>, \<open>new\<close>,
  \<open>not\<close>, \<open>null\<close>, \<open>of\<close>, \<open>or\<close>, \<open>others\<close>, \<open>out\<close>, \<open>overriding\<close>, \<open>package\<close>, \<open>pragma\<close>,
  \<open>private\<close>, \<open>procedure\<close>, \<open>raise\<close>, \<open>range\<close>, \<open>record\<close>, \<open>rem\<close>, \<open>return\<close>,
  \<open>reverse\<close>, \<open>some\<close>, \<open>subtype\<close>, \<open>tagged\<close>, \<open>then\<close>, \<open>type\<close>, \<open>use\<close>, \<open>when\<close>,
  \<open>while\<close>, \<open>with\<close>, \<open>xor\<close>); the words of the left-out constructs (\<open>abort\<close>,
  \<open>accept\<close>, \<open>at\<close>, \<open>delay\<close>, \<open>do\<close>, \<open>entry\<close>, \<open>generic\<close>, \<open>goto\<close>, \<open>interface\<close>,
  \<open>protected\<close>, \<open>renames\<close>, \<open>requeue\<close>, \<open>select\<close>, \<open>separate\<close>, \<open>synchronized\<close>,
  \<open>task\<close>, \<open>terminate\<close>, \<open>until\<close>) are reserved too and rejected. An \<^emph>\<open>identifier\<close>
  is a letter followed by letters, digits and single underscores. A decimal
  literal has underscores between digits, an optional fraction and exponent; a
  based literal is \<open>16#FF#\<close>, \<open>2#1010#\<close> with a base from 2 to 16 (also with a
  fraction and an exponent). A character literal is \<open>'x'\<close>, a string \<open>"\<dots>"\<close> with
  doubled quotes for a quote; an operator symbol (\<open>"+"\<close>, \<open>"and"\<close>) is a string
  used as a designator. The comment machinery lives in the lexer, as in the
  other front-ends: \<open>--\<close> enters a comment state that runs to the end of the
  line, and an antiquotation is recognised by a regular expression for its head,
  followed by a nesting-depth counter for a cartouche body. The syntax of the
  head:

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
  The grammar is reproduced here slightly simplified: the operator productions
  are abbreviated by their precedence table, from the loosest to the tightest
  binding: the logical operators \<open>and\<close>, \<open>or\<close>, \<open>xor\<close>, \<open>and then\<close>, \<open>or else\<close>; the
  relations \<open>=\<close>, \<open>/=\<close>, \<open><\<close>, \<open><=\<close>, \<open>>\<close>, \<open>>=\<close> and the membership tests \<open>in\<close>, \<open>not
  in\<close> (non-associative); the binary adding operators \<open>+\<close>, \<open>-\<close>, \<open>&\<close>; the unary
  adding operators \<open>+\<close>, \<open>-\<close>; the multiplying operators \<open>*\<close>, \<open>/\<close>, \<open>mod\<close>, \<open>rem\<close>;
  \<open>**\<close> (non-associative); the prefix operators \<open>abs\<close>, \<open>not\<close>; and the postfix
  forms \<open>.\<close>, \<open>'\<close> and calls.

  \<^rail>\<open>
    source__file : (compilation__unit *)
    ;
    compilation__unit : (context__clause *) (package__declaration
                      | package__body | subprogram__declaration
                      | subprogram__body)
    ;
    context__clause : ('limited' | 'private')? 'with' (name + ',') ';'
                    | 'use' 'type'? (name + ',') ';'
    ;
    package__declaration : 'package' name (aspects ?) 'is' (declaration *)
                           ('private' (declaration *))? 'end' name? ';'
    ;
    package__body : 'package' 'body' name (aspects ?) 'is' (declaration *)
                    ('begin' statements (handlers ?))? 'end' name? ';'
  \<close>

  \<^rail>\<open>
    subprogram__declaration : subprogram__specification
                              ('is' ('abstract' | 'null' | '(' expression ')'))?
                              (aspects ?) ';'
    ;
    subprogram__body : subprogram__specification (aspects ?) 'is'
                       (declaration *) 'begin' statements (handlers ?)
                       'end' name? ';'
    ;
    subprogram__specification : 'overriding'? ('procedure' name
                              | 'function' designator) formal__part?
                              ('return' subtype__indication)?
    ;
    formal__part : '(' (parameter + ';') ')'
    ;
    parameter : (identifier + ',') ':'
                (('in' | 'out' | 'in' 'out')? subtype__indication
                | 'not' 'null' 'access' subtype__indication
                | 'access' subtype__indication) (':=' expression)?
    ;
    aspects : 'with' (aspect + ',')
    ;
    aspect : name ('\'' name)? ('=>' expression)?
  \<close>

  \<^rail>\<open>
    declaration : object__declaration | number__declaration
                | exception__declaration | type__declaration
                | subtype__declaration
                | subprogram__declaration | subprogram__body
                | package__declaration | package__body | use__clause | pragma
                | attribute__definition
    ;
    object__declaration : (identifier + ',') ':' 'aliased'? 'constant'?
                          (subtype__indication | array__definition)
                          (':=' expression)? (aspects ?) ';'
    ;
    number__declaration : (identifier + ',') ':' 'constant' ':=' expression ';'
    ;
    exception__declaration : (identifier + ',') ':' 'exception' ';'
    ;
    subtype__declaration : 'subtype' identifier 'is' subtype__indication
                           (aspects ?) ';'
    ;
    attribute__definition : 'for' name '\'' name 'use' expression ';'
    ;
    use__clause : 'use' 'type'? (name + ',') ';'
  \<close>

  \<^rail>\<open>
    type__declaration : 'type' identifier (discriminants ?)
                        ('is' type__definition)? (aspects ?) ';'
    ;
    discriminants : '(' (parameter + ';') ')'
    ;
    type__definition : '(' (identifier + ',') ')'
                     | 'range' expression '..' expression
                     | 'mod' expression
                     | 'digits' expression ('range' expression '..' expression)?
                     | 'delta' expression ('range' expression '..' expression)?
                     | array__definition
                     | ('abstract'? 'tagged'? 'limited'?)
                       ('record' record__definition 'end' 'record'
                       | 'null' 'record' | 'private')
                     | 'abstract'? 'limited'? 'new' subtype__indication
                       ('with' ('record' record__definition 'end' 'record'
                                | 'null' 'record' | 'private'))?
                     | 'not'? 'null'? 'access' ('all' | 'constant')?
                       subtype__indication
    ;
    array__definition : 'array' '(' (index + ',') ')' 'of' 'aliased'?
                        subtype__indication
    ;
    index : expression '..' expression | expression
          | expression 'range' '<>'
    ;
    record__definition : (component *) (variant__part ?) | 'null' ';'
    ;
    component : (identifier + ',') ':' 'aliased'? subtype__indication
                (':=' expression)? ';'
    ;
    variant__part : 'case' identifier 'is'
                    (('when' (choice + '|') '=>' record__definition) +)
                    'end' 'case' ';'
  \<close>

  \<^rail>\<open>
    statements : (statement *)
    ;
    statement : 'null' ';' | name ':=' expression ';' | name ';'
              | 'if' expression 'then' statements
                (('elsif' expression 'then' statements) *)
                ('else' statements)? 'end' 'if' ';'
              | 'case' expression 'is'
                (('when' (choice + '|') '=>' statements) +) 'end' 'case' ';'
              | (identifier ':')? iteration__scheme? 'loop' statements
                'end' 'loop' identifier? ';'
              | (identifier ':')? ('declare' (declaration *))? 'begin'
                statements (handlers ?) 'end' identifier? ';'
              | 'exit' name? ('when' expression)? ';'
              | 'return' expression? ';'
              | 'raise' name? ('with' expression)? ';'
              | pragma
    ;
    iteration__scheme : 'while' expression
                      | 'for' identifier 'in' 'reverse'? discrete__range
                      | 'for' identifier 'of' 'reverse'? expression
    ;
    handlers : 'exception' (('when' (choice + '|') '=>' statements) +)
    ;
    pragma : 'pragma' identifier ('(' (association + ',') ')')? ';'
  \<close>

  \<^rail>\<open>
    expression : name | literal | 'null' | 'new' expression
               | expression binary__operator expression
               | prefix__operator expression
               | expression ('not'? 'in') (choice + '|')
               | '(' (association + ',') ')'
               | '(' expression 'with' 'delta'? (association + ',') ')'
               | expression '\'' '(' (association + ',') ')'
    ;
    name : identifier | name '.' identifier | name '.' 'all'
         | name '(' (association + ',') ')' | name '\'' attribute__designator
    ;
    association : expression | expression '..' expression
                | (choice + '|') '=>' expression
                | conditional__expression | quantified__expression
    ;
    choice : expression | expression '..' expression | 'others'
    ;
    conditional__expression : 'if' expression 'then' expression
                              (('elsif' expression 'then' expression) *)
                              ('else' expression)?
                            | 'case' expression 'is'
                              (('when' (choice + '|') '=>' expression ',') *)
    ;
    quantified__expression : 'for' ('all' | 'some') identifier
                             ('in' 'reverse'? discrete__range
                              | 'of' 'reverse'? expression) '=>' expression
    ;
    subtype__indication : 'not'? 'null'? name
                          ('range' expression '..' expression)?
  \<close>
\<close>

(*<*)
end
(*>*)
