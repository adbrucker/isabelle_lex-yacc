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
theory Go_Manual
  imports "Golang1_27.Go"
begin
(*>*)

section\<open>What is Isabelle/Go\<close>

text\<open>
  Isabelle/Go is a front-end that lets Go source text live inside an Isabelle theory as a
  first-class citizen: parsed by a real grammar, checked incrementally under Isabelle/PIDE (so a
  syntax error or a malformed annotation is reported like any other Isabelle error, with the
  usual jEdit markup, hyperlinking and hovering), and open to attaching arbitrary
  Isabelle-level content - proof obligations, HOL terms, arbitrary Isar commands - to specific
  points of the Go source via a comment-based antiquotation mechanism. It is not a Go compiler,
  nor a verification tool in its own right: it is the \<^emph>\<open>front-end layer\<close> on which one builds a
  verification tool (a semantic backend, for instance a translation of Go programs into HOL), a
  documentation generator, or a static analysis.
\<close>

subsection\<open>Context\<close>

text\<open>
  \<^bold>\<open>Go has an official grammar, and a short one.\<close> \<^emph>\<open>The Go Programming Language
  Specification\<close> \<^cite>\<open>"go:spec:2026"\<close> defines the syntax in an EBNF of about a hundred
  productions, and the language was designed so that it can be parsed without a symbol table. This
  front-end follows the specification for the \<^emph>\<open>whole\<close> language, in the version go1.27: there
  is no subset. That includes the generics of Go 1.18 (type parameters of functions, methods and
  types, constraints with \<open>~T\<close> and unions, instantiation), the aliases with type parameters of
  Go 1.24, range-over-integer and range-over-function loops, and the two additions of Go 1.27:
  methods that declare type parameters, and any field selector as a key of a struct literal.

  The grammar is \<^emph>\<open>checked against the real thing\<close>. The Go source tree
  \<^cite>\<open>"go:source:2026"\<close> (release branch go1.27) contains 6\,821 Go files that are not test data:
  the standard library, the compiler and the tools. All of them are read by this front-end,
  printed back, and read again to the same text (\<open>\<section>5\<close>). The test suite of the compiler itself
  (3\,406 files) is accepted but for the 73 files that it contains \<^emph>\<open>in order to be
  rejected\<close>.

  The folder of this front-end is called \<^verbatim>\<open>Golang1.27\<close>, after the language version it
  implements; the session is \<open>Golang1_27\<close> (a dot cannot occur in a session name), the theories
  and the commands are called \<open>Go\<close> and \<open>go\<close>.

  Isabelle/Go is the sixth language front-end built on the design of \<^bold>\<open>Isabelle/C, Version
  2.0\<close>, which this repository's \<^verbatim>\<open>C11/\<close> folder contains \<^cite>\<open>"tuong.ea:isabellec:2019" and
  "tuong.ea:deeply:2019"\<close>, after occam 2, Scala 3, MicroRust and AdaSpark. It is built from the same
  parts and carries the same concepts over one for one: the \<^verbatim>\<open>ml_lex_yacc\<close> command of this
  repository (an ML-Lex/ML-Yacc integration \<^cite>\<open>"appel.ea:lexical:1994" and
  "tarditi.ea:ml-yacc:2000"\<close>) generates lexer and parser; every node of the abstract syntax tree
  carries a source position plus the comments and antiquotations attached to it; a per-theory
  environment tracks the declared names for declaration/use hyperlinking; programmable handlers, a
  navigation language and an evaluation order give meaning to the antiquotations; and a family of
  Isar commands (\<open>go\<close>, \<open>go_stmt\<close>, \<open>go_file\<close>, \<open>\<dots>\<close>) drive all of it. Someone who knows the C11
  manual will find the same structure in this one, and the same names with \<open>c11\<close> replaced by
  \<open>go\<close>, \<open>cenv\<close> by \<open>genv\<close>, and \<open>CEnv\<close> by \<open>GEnv\<close>. Like the other members it is \<^emph>\<open>re-entrant\<close>: it
  is built with \<open>ml_lex_yacc [state]\<close>, every parse has a state object of its own, and any
  number of parses may run at the same time.

  What differs is dictated by the language and takes up most of the remainder: the two things in
  Go's lexical structure that an LALR(1) grammar cannot see over the tokens - the semicolons that
  the lexer inserts, and the two meanings of an opening brace (\<open>\<section>2.1\<close>); the fact that types
  are expressions (\<open>\<section>4\<close>); and the block scoping of Go with its package-level forward
  references (\<open>\<section>2.2\<close>).
\<close>

section\<open>Main Features of Isabelle/Go\<close>

text\<open>
  Four pieces fit together to give the \<open>go\<close>-family commands (\<open>\<section>3\<close>) their behaviour: a
  lexer and parser that produce a real AST with genuine source positions at every node
  (\<open>\<section>2.1\<close>); a per-theory environment tracking every declared name, used to hyperlink each
  name \<^emph>\<open>use\<close> back to its declaration (\<open>\<section>2.2\<close>); a mechanism for attaching programmable content
  to a specific AST node via a comment (\<open>\<section>2.3\<close>); and a well-defined order and navigation
  language governing exactly \<^emph>\<open>which\<close> node an antiquotation resolves to and \<^emph>\<open>when\<close> it runs
  (\<open>\<section>2.4\<close>).
\<close>

subsection\<open>Parsing\<close>

text\<open>
  The grammar (\<^verbatim>\<open>Go_Parser.thy\<close>) is an ordinary LALR(1) ml-yacc grammar, and it is
  \<^emph>\<open>conflict free\<close>: ml-yacc reports neither a shift/reduce nor a reduce/reduce conflict. It
  covers

  \<^item> \<^bold>\<open>source files\<close>: the package clause, import declarations (plain, aliased, dot and
    blank imports, grouped), and the top-level declarations;
  \<^item> \<^bold>\<open>declarations\<close>: \<open>const\<close> (with implicit repetition), \<open>var\<close>, \<open>type\<close> (definitions, aliases,
    generic types), functions and methods (receivers, type parameters, variadic parameters,
    named results, no body), each also as a parenthesised group;
  \<^item> \<^bold>\<open>types\<close>: type names, qualified and instantiated; pointers, arrays (also \<open>[...]T\<close>),
    slices, maps, channels in both directions, function types, structs (embedded fields, tags),
    interfaces (methods, embedded types, unions, \<open>~T\<close>);
  \<^item> \<^bold>\<open>statements\<close>: expression statements, sends, increments, assignments (all operators),
    short variable declarations, \<open>go\<close>, \<open>defer\<close>, \<open>return\<close>, \<open>break\<close>, \<open>continue\<close> (with labels),
    \<open>goto\<close>, \<open>fallthrough\<close>, labels, blocks, \<open>if\<close>, \<open>switch\<close> (expression and type switches),
    \<open>select\<close>, and \<open>for\<close> in all its forms (infinite, condition, three clauses, \<open>range\<close>);
  \<^item> \<^bold>\<open>expressions\<close>: the five levels of binary operator precedence, the seven unary operators,
    literals (numbers with prefixes, underscores, hexadecimal floats and imaginary suffixes;
    runes; interpreted and raw strings), composite literals (with elided types and keys),
    function literals, selectors, indexing, slicing (also with three indices), type assertions,
    calls (with \<open>...\<close>), conversions and instantiations.

  \<^bold>\<open>Types are expressions.\<close> As in the standard library's \<open>go/ast\<close>, a type is an expression of
  the AST. Go does not tell a call from a conversion, an index from an instantiation, a selector
  from a qualified name, or \<open>*p\<close> from \<open>*T\<close> by syntax, and the type literals (\<open>[]int\<close>, \<open>map[K]V\<close>,
  \<open>struct{...}\<close>, \<open>func(...)\<close>, \<open>chan T\<close>) are operands of the expression grammar as well. The
  grammar keeps a separate nonterminal \<open>typ\<close> for the places that must be types (the type of a
  variable, a field, a parameter, a result), because a type name there is not the beginning of a
  composite literal, and the place where a name stands for a parameter name or for a type
  (\<open>func(a, b int)\<close> against \<open>func(int, string)\<close>) is read as a list of entries and decided when the
  list is complete, as the Go parser does. What a name denotes is decided by the analysis.

  \<^bold>\<open>Two things an LALR(1) grammar cannot see\<close> are resolved in a small \<^emph>\<open>stream\<close> between lexer
  and parser (\<open>Go_Parse.go_stream\<close>), so that the grammar itself stays an ordinary context-free
  one:

  \<^enum> \<^emph>\<open>Semicolons.\<close> Go's lexer inserts a \<open>;\<close> after a line's final token if that token is an
    identifier, a literal, one of \<open>break\<close>, \<open>continue\<close>, \<open>fallthrough\<close>, \<open>return\<close>, one of \<open>++\<close>,
    \<open>--\<close>, \<open>)\<close>, \<open>]\<close>, \<open>}\<close>, and at the end of the input. The lexer of this front-end counts the
    newlines before a token (those inside a general comment as well, as the specification says),
    and the stream inserts the semicolon. A trailing comma before a closing bracket or brace is
    thus the only way to break a call or a literal over several lines, as in Go.
  \<^enum> \<^emph>\<open>A brace is a block or a composite literal.\<close> In the header of an \<open>if\<close>, \<open>for\<close> or \<open>switch\<close>, a
    \<open>{\<close> that follows a bare type name opens the \<^emph>\<open>block\<close>: \<open>if x == T{} {\<close> is not valid Go, the
    literal needs parentheses. After a type \<^emph>\<open>literal\<close> it opens a composite literal (\<open>for _, v :=
    range []int{1, 2} {\<close>), as it does after a function literal's signature. The stream keeps
    a stack of the regions it is in - a header, a bracketed or braced part, the body of a struct
    or interface type - and a flag for a type literal in progress, and delivers the \<open>{\<close> that
    ends a header as its own token. This is the \<^emph>\<open>expression level\<close> of Go's own parser.

  \<^bold>\<open>Positions and comments.\<close> Every node carries the exact source range of its text, from its
  first to its last token; a name carries the range of the name. Comments, and the
  antiquotations among them (\<open>\<section>2.3\<close>), are not part of the grammar: the lexer collects them and
  attaches them to the node of the next real token. Go comments are \<open>//\<close> to the end of the line
  and \<open>/* \<dots> */\<close>, which do \<^emph>\<open>not\<close> nest.

  A first example, a generic stack with a method and a generic function (the type parameter of the
  method comes from its receiver):
\<close>

go\<open>
package stack

import "errors"

var ErrEmpty = errors.New("stack is empty")

type Stack[T any] struct {
    items []T
}

func (s *Stack[T]) Push(x T) {
    s.items = append(s.items, x)
}

func (s *Stack[T]) Pop() (T, error) {
    var zero T
    n := len(s.items)
    if n == 0 {
        return zero, ErrEmpty
    }
    x := s.items[n-1]
    s.items = s.items[:n-1]
    return x, nil
}

func Map[T, U any](xs []T, f func(T) U) []U {
    ys := make([]U, 0, len(xs))
    for _, x := range xs {
        ys = append(ys, f(x))
    }
    return ys
}
\<close>

text\<open>
  Literals and the lexical structure are part of the grammar: number literals with prefixes,
  underscores and imaginary suffixes, runes, raw strings, and the constructs that need the stream.
  The fragments below are accepted; the last one is not (a composite literal in the header of an
  \<open>if\<close> must be parenthesised):
\<close>

go_expr\<open>0x_FF + 0b1010 + 0o17 + 1_000 + 1.5e3 + 0x1p-2 + 2i\<close>

go_expr\<open>map[string][]int{"a": {1, 2}, "b": nil}\<close>

go_stmt\<open>
for _, v := range []int{1, 2, 3} {
    if v == (T{}).n {
        continue
    }
}
\<close>

go_stmt_reject\<open>if x == T{} { f() }\<close>

subsection\<open>The Go Environment, and Declaration/Use Navigation\<close>

text\<open>
  \<^verbatim>\<open>Go_Env.thy\<close> defines \<open>genv\<close>, the counterpart of C11's \<open>cenv\<close>: a record stored as ordinary
  \<^verbatim>\<open>Generic_Data\<close>, so that it persists across commands within a theory and merges correctly
  under Isabelle's parallel, incremental checking. It holds

  \<^enum> \<open>names\<close>, the declared names - \<^emph>\<open>one\<close> table, as Go has one lexical name space - each with
    what it was declared as (a variable, a constant, a parameter, a type, a function, an imported
    package, a label, a type parameter, a field, a method);
  \<^enum> \<open>go_antiq\<close>, the registry of antiquotation handlers (\<open>\<section>2.3\<close>); and
  \<^enum> a per-theory unit counter, used to name the sections processed by a \<open>go\<close> command.

  \<^verbatim>\<open>Go_AnaEval.thy\<close>'s \<open>analyse_and_eval\<close> is a single, purely functional, scoped walk over a
  parsed root that fills \<open>genv\<close> as it goes. Every name \<^emph>\<open>use\<close> is hyperlinked to its declaration
  via \<^ML>\<open>Position.entity_markup\<close>, reported once at the declaration site and once at every use.
  \<^bold>\<open>A name that resolves nowhere is not marked\<close> - unlike C11 and occam 2, where it is underlined.
  In Go a name very often comes from the universe block (\<open>int\<close>, \<open>len\<close>, \<open>nil\<close>), a dot import or
  another file of the package, none of which this pass sees; underlining them would drown the
  useful markup. The \<^emph>\<open>scoping rules\<close> are those of Go, implemented as shadow-and-restore (the
  environment is a value; a scope simply does not hand its extension back):

  \<^item> \<^bold>\<open>Case sensitivity, one name space.\<close> The table is keyed by the name as written. Labels
    have a name space of their own: a label and a variable of the same name do not clash.
  \<^item> \<^bold>\<open>Block scoping.\<close> A name is visible from the end of its declaration to the end of the
    innermost block. A block, a function (its parameters, results and receiver are in the scope
    of its body, not outside), the header of an \<open>if\<close>, \<open>for\<close> or \<open>switch\<close> together with the
    statements it governs, a \<open>case\<close> clause and a \<open>select\<close> clause are scopes. A variable is not
    visible in its own initial value (\<open>x := x\<close>), and a type is visible in its own definition.
  \<^item> \<^bold>\<open>Package-level forward references.\<close> The names declared at the top level of a package are
    visible throughout it: a function may call one that is defined further down, a variable may
    have a type defined after it. In a function body a declaration is visible only after
    itself.
  \<^item> \<^bold>\<open>Short variable declarations.\<close> \<open>a, b := f()\<close> declares the names that are new in the
    current block; the others are assigned to, which is a use. The blank identifier declares
    nothing. The expression of a \<open>range\<close> clause is not in the scope of the clause's variables.
  \<^item> \<^bold>\<open>Type switches.\<close> The variable of \<open>switch x := v.(type)\<close> is declared once, at the guard,
    and is visible in every clause.
  \<^item> \<^bold>\<open>Generics.\<close> The type parameters of a function or type are declared in a scope of their
    own, all before any of their constraints is read (\<open>[S ~[]E, E any]\<close>); a method's receiver
    type declares the type parameters of the type it names (\<open>func (l *List[T]) Push(x T)\<close>), which
    are visible in the signature and the body.
  \<^item> \<^bold>\<open>Imports\<close> declare the package name - the alias, or the last element of the import path
    (without a major version suffix) - at the import path; a use \<open>fmt.Println\<close> is hyperlinked
    to it. The standard library is not seen by this pass.
  \<^item> \<^bold>\<open>Selections are resolved with types, and only when that is certain.\<close> Fields and methods are
    declared (their declaration sites are reported) but not entered into the table, since they
    are reached by selection. A selection \<open>x.f\<close> is hyperlinked to the field or method \<open>f\<close> when
    the type of \<open>x\<close> is known well enough to tell, and left unmarked otherwise. The type of an
    expression is computed by a pure function over the environment, which records the type of
    each name next to the name (scoped with it), the declaration of each type, and the methods
    of each type. A name has the type it was declared with or that of the value that defined
    it (\<open>:=\<close>, \<open>var x = v\<close>, a range variable, the variable of a type switch in each clause); a
    call has the result type of its callee's signature, and conversions, \<open>*p\<close>, \<open>&x\<close>, indexing,
    slicing, type assertions, composite literals and function literals have their natural types.
    A named type is a reference to its declaration, so that types, fields and methods may be
    mutually recursive and declared in any order; the types, signatures and methods of a
    package are registered before anything is walked. Lookup follows the language: automatic
    dereferencing, promotion through embedded fields (the shallowest depth wins, a tie is
    ambiguous and gives no link), the methods of embedded interfaces, the methods of the
    constraint of a type parameter, aliases, and type arguments substituted in an explicitly
    instantiated generic type, and the inference of the type arguments of a call of a generic
    function or method (from the typed arguments, from the core types of the constraints, and
    from untyped constants by their default type; whatever is doubtful stays unknown). The keys
    of a composite literal are fields of its struct type, also in elided elements
    (\<open>[]T{{a: 1}}\<close>); the keys of a map literal are expressions. What is not known - the standard
    library and every imported type - gives no link, and neither does a match that an embedded
    type of unknown content could have provided nearer.
  \<^item> \<^bold>\<open>The top level persists.\<close> After \<open>go\<close> has analysed a source file (or \<open>go_decl\<close> a declaration),
    the names it declares at the top level, imports included, stay in \<open>genv\<close> for the following
    commands, as the files of a package do for each other. Nothing else does.

  Being persistent per-theory data - the same idiom a simp set uses - is what lets Go fragments
  be freely \<^emph>\<open>interleaved\<close> with arbitrary Isar content and still resolve a name used in one
  fragment back to its declaration in an earlier one. The flip side is that \<open>genv\<close> only ever
  grows across a theory; the commands \<open>set_genv_default\<close> and \<open>reset_genv\<close> (\<open>\<section>3\<close>) give a theory
  explicit control. A small example of the scoping rules (hover over the names in jEdit): a
  package with a forward reference, a short variable declaration that redeclares, a shadowing
  block, a labelled loop and a type switch.
\<close>

go\<open>
package scopes

import "fmt"

func Run(items []any) int {
    total := 0
    for i, item := range items {
        total, err := add(total, item)
        if err != nil {
            fmt.Println(i, err)
            continue
        }
        _ = total
    }
outer:
    for i := 0; i < 3; i++ {
        for {
            break outer
        }
    }
    return total
}

func add(total int, item any) (int, error) {
    switch v := item.(type) {
    case int:
        return total + v, nil
    case string:
        return total + len(v), nil
    }
    return total, fmt.Errorf("unexpected %T", item)
}
\<close>

subsection\<open>Programmable Go-Antiquotations, and Handlers\<close>

text\<open>
  A comment of the shape \<open>@tag[navi](level) \<open>body\<close>\<close> - an \<open>@\<close>-prefixed tag, an optional bracketed
  navigation string (\<open>\<section>2.4\<close>), an optional parenthesised integer \<open>level\<close> (\<open>0\<close> when omitted), and
  a body written as a nested Isabelle cartouche or, equivalently, a double-quoted string - is
  recognised lexically inside a \<open>//\<close> or \<open>/* \<dots> */\<close> comment, and attached to whichever AST node
  it resolves against (\<open>\<section>2.4\<close>). The cartouche may span several lines, which a \<open>//\<close> comment
  cannot. Any other comment is kept as plain text (\<open>Raw_txt\<close>). A comment is attached to the AST
  node that begins at the \<^emph>\<open>next real token\<close>, so an annotation is written on the line(s) \<^emph>\<open>above\<close>
  what it annotates:

  \<^verbatim>\<open>//@ highlight\<close>

  (a tag alone is a complete antiquotation with an empty body). A \<^emph>\<open>bodyless\<close> tag is recognised
  only directly after the comment opener (\<open>//@\<close>, \<open>/*@\<close>), so that an \<open>@\<close> in running text - an
  e-mail address, a documentation tag - is not mistaken for an antiquotation; a tag followed by
  a body is one anywhere in a comment.

  The \<open>tag\<close> selects a \<^emph>\<open>handler\<close>: an ordinary ML function of type

  \<^verbatim>\<open>type type_antiq_fun =
    genv * pos Go_Ast.root * int -> (string * pos) ->
    Context.generic -> Context.generic\<close>

  registered once, ahead of time, via \<open>GEnv.store_antiq (tag, handler)\<close>. When
  \<open>analyse_and_eval\<close> reaches a node carrying an \<open>@tag \<dots>\<close> antiquotation, it resolves the
  navigation string against the closest-surrounding-context stack (\<open>\<section>2.4\<close>) into a single
  concrete \<open>root\<close> value, then instantiates the handler with \<open>(genv, resolved_root, level)\<close> and
  the body text together with its own source position; a handler is never itself responsible
  for interpreting \<open>u\<close>/\<open>U\<close>/\<open>r\<close>/\<open>d\<close>.

  \<open>Context.generic\<close> rather than \<open>theory\<close>, deliberately: a handler may do anything a genuine
  Isar toplevel command can, including running real ML code at the ML environment level (the
  \<open>ML\<close> antiquotation, below). All collected actions are folded into one \<open>Context.generic ->
  Context.generic\<close> function by ordinary composition and lifted to the toplevel exactly once, at
  the end (\<open>full_eval_and_store\<close> in \<^verbatim>\<open>Go.thy\<close>). Most handlers never need this generality: an
  ordinary \<open>theory -> theory\<close> function is \<^emph>\<open>recaptured\<close> by \<open>GEnv.lift_theory_antiq\<close> when it is
  registered. A first handler, which turns a plain comment into a checked diagnostic reported
  against the exact node the comment resolves to:
\<close>

ML\<open>
val todo_antiq =
  let
    fun handler (_ : GEnv.genv, ast, level) (body, _ : Position.T) thy =
      (warning ("TODO (level " ^ Int.toString level ^ ") at " ^
                Position.here (AnaEval.pos_of_root ast) ^ ": " ^ body);
       thy)
  in GEnv.store_antiq ("todo", GEnv.lift_theory_antiq handler) end
\<close>
setup\<open>todo_antiq\<close>

go\<open>
package p

func clear(x *int) {
    //@ todo \<open>check the range of x first\<close>
    *x = 0
}
\<close>

text\<open>
  A tag with no registered handler is a hard error: every tag that can appear in a theory's
  source must be registered before that theory's \<open>go\<close>-family commands run.
\<close>

subsection\<open>Execution (Order, Navigation, etc.)\<close>

text\<open>
  \<^bold>\<open>Order.\<close> A unit can carry several antiquotations whose handlers have side effects that
  depend on one another (a \<open>definition\<close> must precede the \<open>lemma\<close> that mentions it). \<open>level\<close> is
  the author's explicit ordering knob: \<open>full_eval_and_store\<close> collects every \<open>(level, action)\<close> pair
  the walk produces, sorts by \<open>level\<close> - a stable sort, so equal levels keep their textual order -
  and chains them, each against the context the previous one produced. A physical antiquotation
  is dispatched \<^emph>\<open>exactly once\<close>, no matter how many AST nodes share its leftmost source position
  (the classic case in Go: a statement, its expression and the name that begins it all start at
  the same token).

  \<^bold>\<open>Context.\<close> Every antiquotation resolves, by default, to its \<^emph>\<open>closest surrounding
  context\<close>: the walk threads a stack of enclosing nodes. Three kinds of node push themselves on
  that stack at every level of nesting: \<^emph>\<open>expressions\<close> (and types, which are expressions),
  \<^emph>\<open>statements\<close> and \<^emph>\<open>declarations\<close> - the root type has the variants \<open>Expr\<close>, \<open>Stmt\<close>, \<open>Decl\<close> in
  addition to \<open>Id\<close> for a bare name, \<open>Stmts\<close> for a statement list, \<open>Decls\<close> for top-level
  declarations and \<open>Source\<close> for a source file. Everything else - parameters, fields,
  specifications, composite literal elements, clauses, blocks - never pushes and resolves to what
  is on top, which is what makes every node kind a valid place for a comment. A comment in front
  of a top-level declaration is therefore in the context of the source file, and \<open>[d]\<close> reaches
  the declaration.

  \<^bold>\<open>Navigation.\<close> The bracketed \<open>[navi]\<close> string points an antiquotation \<^emph>\<open>away\<close> from its closest
  context. Its syntax and its rules are exactly those of C11: written \<open>(u|U)*(r|d)*\<close>, zero or
  more ascend steps followed by zero or more descend steps. \<open>u\<close> ascends one level (a lone, final
  \<open>u\<close> is a no-op); \<open>U\<close> ascends past a whole run of consecutive ancestors of the same category;
  \<open>r\<close> advances a 1-based cursor among the current node's children in source order and \<open>d\<close>
  descends into the child at the cursor (cursor 1 if no \<open>r\<close> preceded it). There is no wrapping: a
  cursor beyond the children, or \<open>d\<close> on a leaf, is a hard error reported at the antiquotation's
  own tag position. The children of a node, in source order, are its sub-expressions,
  statements and declarations; the parameters, fields, elements, clauses and specifications of a
  node are \<^emph>\<open>flattened into it\<close>, so the children of an assignment are the expressions of its two
  sides, those of a call its function followed by its arguments, and those of an \<open>if\<close> its
  initialisation, its condition and the statements of its blocks. A few examples (the node a
  handler receives, on the statement \<open>x = x + y\<close>):

  \<^item> no navigation: the statement itself;
  \<^item> \<open>[d]\<close> or \<open>[rd]\<close>: its first child, \<open>x\<close>; \<open>[rrd]\<close>: its second child, \<open>x + y\<close>;
  \<^item> \<open>[uu]\<close>: the enclosing function.

\<close>

go\<open>
package p

func sum(x, y int) int {
    //@ probe_ast[rrd]
    //@ highlight[rrd]
    x = x + y
    return x
}
\<close>

ML\<open>
val _ = if Go_Pp.pp_root (!GO_AST) = "x + y"
  then writeln "[rrd] reaches the second operand"
        else error "navigation"
\<close>

subsection\<open>Standard Antiquotations\<close>

text\<open>
  \<^verbatim>\<open>Go_AnaEval.thy\<close> registers the same eight demonstration antiquotations as C11. All of them
  are written in a comment and see the node their navigation string selects:

  \<^descr> \<open>probe_genv\<close> stores the current \<open>genv\<close> into an ML reference (\<open>GENV\<close>) for inspection.
  \<^descr> \<open>probe_ast\<close> prints the resolved node, pretty-printed back to Go, with its level, and
    stores it into \<open>GO_AST\<close>.
  \<^descr> \<open>highlight\<close> marks the resolved node's source range in the editor - the quickest way to
    \<^emph>\<open>see\<close> what a navigation string selects.
  \<^descr> \<open>term \<open>t\<close>\<close> reads \<open>t\<close> as a HOL term in the theory's current context; a malformed or
    ill-typed term is a real Isabelle error positioned inside the Go comment.
  \<^descr> \<open>ML \<open>code\<close>\<close> runs \<open>code\<close> as ML source, so a definition written in a Go comment becomes a
    later-visible ML binding.
  \<^descr> \<open>text \<open>t\<close>\<close> runs \<open>t\<close> through the document machinery of Isabelle's \<open>text\<close> command, so that
    inner antiquotations are checked and hyperlinked (the result is stashed, not typeset; see
    \<open>\<section>6\<close>).
  \<^descr> \<open>definition \<open>d\<close>\<close> is Isabelle's \<open>definition\<close> command: the new constant is a genuine,
    later-visible theory constant.
  \<^descr> \<open>lemma \<open>l\<close>\<close> states \<open>l\<close> and proves it with one terminal \<open>by\<close> proof - proof-carrying code: a
    formal property of the program's constants, \<^emph>\<open>actually proved\<close>, right where the Go text that
    motivates it lives. A failed proof is an Isabelle error positioned in the comment.

\<close>

section\<open>The Go Main Commands\<close>

text\<open>

  \<^descr> \<open>go \<open>\<dots>\<close>\<close> parses its argument as a source file - a package clause, imports and top-level
    declarations - runs \<open>analyse_and_eval\<close>, chains the collected antiquotation actions in level
    order, and stores the AST under a fresh key, reported as \<open>[stored as Theory#N]\<close>.
  \<^descr> \<open>go_decl \<open>\<dots>\<close>\<close> is the same for top-level declarations \<^emph>\<open>without\<close> a package clause - the
    way to add a function or a type to a package one piece at a time - and \<open>go_stmt \<open>\<dots>\<close>\<close> for a
    statement list, as it stands between the braces of a function.
  \<^descr> \<open>go_file \<open>path\<close>\<close> is the same as \<open>go\<close>, reading the source file from an external file
    (resolved relative to the theory's master directory via \<^ML>\<open>Resources.parse_file\<close>, so file
    positions and build-dependency tracking come for free).
  \<^descr> \<open>go_expr \<open>\<dots>\<close>\<close>, \<open>go_type \<open>\<dots>\<close>\<close> and \<open>go_ident \<open>\<dots>\<close>\<close> parse a bare expression, type, respectively
    name. The analysis still runs, for its hyperlinks, but its antiquotation actions are
    discarded: a standalone fragment is a syntax check, not a program.
  \<^descr> \<open>go_reject\<close>, \<open>go_decl_reject\<close>, \<open>go_stmt_reject\<close>, \<open>go_expr_reject\<close>, \<open>go_type_reject\<close> and
    \<open>go_ident_reject\<close> document a fragment as correctly \<^emph>\<open>not\<close> accepted by the corresponding entry
    point. They are silent (no error markup is left on the expected failure) and are the means
    of writing negative tests.
  \<^descr> \<open>set_genv_default\<close> and \<open>reset_genv\<close> control the ever-growing \<open>genv\<close>. \<open>set_genv_default\<close>
    nominates what \<open>genv\<close> holds \<^emph>\<open>right now\<close> as the snapshot a later \<open>reset_genv\<close> restores; with
    no earlier \<open>set_genv_default\<close> in scope \<open>reset_genv\<close> falls back to the empty \<open>genv\<close>.
    \<^verbatim>\<open>Go.thy\<close> itself nominates, as its last step, the environment holding exactly the standard
    antiquotation handlers.
  \<^descr> \<open>setup_backend \<open>f\<close>\<close> installs the \<^emph>\<open>semantic backend\<close>: \<open>f\<close> is an ML expression of type
    \<open>Position.T Go_Ast.root -> theory -> theory\<close>, evaluated like the argument of Isabelle's own
    \<open>setup\<close> command. At the very end of every \<open>go\<close>, \<open>go_decl\<close>, \<open>go_stmt\<close> and \<open>go_file\<close> -
    after the antiquotation actions have run and the AST is stored - the installed function is
    applied to the parsed root and the theory the command has produced, and its result is the
    theory the command returns; the fragment commands never trigger it. The default is \<open>K I\<close>,
    which \<open>setup_backend \<open>K I\<close>\<close> restores. The function is kept in the theory's context
    (separately from \<open>genv\<close>, so \<open>reset_genv\<close> does not uninstall it) and is inherited by later
    theories. This is where a translation of Go programs into HOL would plug in.
  \<^descr> \<open>go_export \<open>path\<close> exports \<open>key\<^sub>1\<close> \<open>\<dots>\<close> \<open>key\<^sub>n\<close>\<close> renders previously stored sections - given by
    the store keys the accepting commands report - back to Go text with \<^ML>\<open>Go_Pp.pp_root\<close> and
    writes them to \<open>path.go\<close>. With \<open>[verbatim]\<close> after the command name the original source
    text is written instead of the pretty-printer's, whose layout is that of \<^verbatim>\<open>gofmt\<close> in its
    essentials.

  The accepting commands are \<open>thy_decl\<close> commands, because they change theory data (\<open>go_file\<close> is
  \<open>thy_load\<close>, so that Isabelle tracks the file dependency); the \<open>_reject\<close> commands, which store
  nothing, are \<open>diag\<close>. Isabelle evaluates a \<open>diag\<close> command asynchronously, in parallel with the
  commands that follow; that is harmless here, because every parse has its own state (\<open>\<section>2.1\<close>).
\<close>

subsection\<open>A Worked Example\<close>

text\<open>
  A program in the style of a verified library: a constant mirrored in HOL, a loop, and a
  property proved about the constant. The first annotation introduces a HOL constant for the bound
  (a \<open>definition\<close>, evaluated at level 0), the second proves a fact about it (level 1, so after
  the definition), the third checks a HOL term mentioning it (level 2).
\<close>

go\<open>
//@ definition \<open>bound :: nat where "bound = 10"\<close>
//@ lemma(1) \<open>bound_double: "bound * 2 = 20" by (simp add: bound_def)\<close>
//@ term(2) \<open>bound + 1\<close>
package counting

const Bound = 10

func CountUp() int {
    i := 0
    //@ highlight
    for i < Bound {
        i++
    }
    return i
}
\<close>

thm bound_def bound_double

subsection\<open>Source Files, Backends, Export\<close>

text\<open>
  \<open>go_file\<close> reads an external file (here two of the examples of this repository: a program with
  imports and loops, and a generic stack) and stores its AST; the names of its declarations are
  visible to the following commands. A semantic backend is an ML function installed with
  \<open>setup_backend\<close>. The following one only counts the functions and methods of every source
  file it is applied to; a real backend would translate them. It is applied to the \<^emph>\<open>parsed
  root\<close> and the theory, after the annotations have run:
\<close>

ML\<open>
val func_counts = Unsynchronized.ref ([] : int list)
\<close>

setup_backend\<open>fn root => fn thy =>
  (case root of
     Go_Ast.Source (Go_Ast.File (_, decls, _)) =>
       let
         fun is_func (Go_Ast.DFunc _) = true
           | is_func (Go_Ast.DMethod _) = true
           | is_func _ = false
       in (func_counts := length (filter is_func decls) :: !func_counts; thy) end
   | _ => thy)\<close>

go_file \<open>../examples/hello.go\<close>

go_file \<open>../examples/stack.go\<close>

setup_backend\<open>K I\<close>

ML\<open>
val _ = writeln ("functions per source file seen by the backend: " ^
                 commas (map Int.toString (rev (!func_counts))))
\<close>

text\<open>
  Further examples: interfaces with a type switch, a worker pool with channels, \<open>select\<close> and
  \<open>defer\<close>, and a collection of control flow (labels, \<open>range\<close> over an integer, a typed
  \<open>switch\<close> without a tag):
\<close>

go_file \<open>../examples/shapes.go\<close>

go_file \<open>../examples/worker.go\<close>

go_file \<open>../examples/flow.go\<close>

text\<open>
  An accepted unit can be written back as Go, in the canonical layout of the pretty-printer
  (or, with \<open>[verbatim]\<close>, as it was written): a tab per level of indentation, one statement
  per line, a blank line between top-level declarations. The key of the unit is the one the
  command reported when it was stored. This is the way a generated or normalised file is
  produced from a theory:
\<close>

go\<open>
package p; func id(x int) int { return x }
\<close>

ML\<open>
val key_of_last =
  let val GEnv.mk {units, ...} = GEnv.get (Context.Theory @{theory})
  in GEnv.ast_store_key @{theory} (units - 1) end
val _ = writeln ("the last unit is stored as " ^ key_of_last)
val _ = writeln (case GEnv.get_ast key_of_last @{theory} of
                   SOME root => Go_Pp.pp_root root | NONE => "?")
\<close>

section\<open>The Abstract Syntax\<close>

text\<open>
  Go has no pre-existing reference AST in ML to port; the closest is the \<open>go/ast\<close> package of the
  standard library, and the AST in \<^verbatim>\<open>go_ast.ML\<close> is modelled on it: one datatype per syntactic
  category, one constructor per alternative, close enough to the concrete syntax that
  \<^ML>\<open>Go_Pp.pp_root\<close> can print any parsed program back as Go. Layout is \<^emph>\<open>not\<close> part of it: the
  printer regenerates a canonical layout. Parentheses \<^emph>\<open>are\<close> part of it (\<open>EParen\<close>), so the printer
  needs no precedence reasoning. All datatypes are parametrised by the position type \<open>'a\<close>
  (instantiated with \<^verbatim>\<open>Position.T\<close>), and every constructor but the pure wrappers carries a \<open>'a
  nodeInfo\<close> as its last field.

  \<^bold>\<open>Annotations\<close>, shared with C11 and so with everything built on it: \<open>nodeInfo\<close> is a bare
  position or a position with the comments attached; a \<open>comment\<close> is raw text or an antiquotation
  (tag, navigation steps, level, cartouche with its position); \<open>ident\<close> is a name with its
  \<open>nodeInfo\<close>.

  \<^bold>\<open>Syntactic categories\<close> (the constructors are those of \<^verbatim>\<open>go_ast.ML\<close>; the prefix \<open>g\<close> stands for
  ``Go''):

  \<^item> \<open>gExpr\<close>, expressions \<^emph>\<open>and types\<close>: the literals \<open>EInt\<close>, \<open>EFloat\<close>, \<open>EImag\<close>, \<open>ERune\<close>, \<open>EString\<close>
    (all as written), names \<open>EIdent\<close> and \<open>ESelector\<close>, \<open>EParen\<close>, \<open>EIndex\<close> (an index or an
    instantiation), \<open>ESlice\<close>, \<open>ETypeAssert\<close> (\<open>x.(type)\<close> is the case without a type), \<open>ECall\<close>
    (with the flag of \<open>...\<close>), \<open>EStar\<close> (a dereference or a pointer type), \<open>EUnary\<close>, \<open>EBinary\<close>
    (with the \<open>binop\<close>s), \<open>ECompLit\<close> (the type is optional: an elided type, in a literal inside a
    literal) with its \<open>gElement\<close>s, \<open>EFuncLit\<close>; and the type literals \<open>EArrayType\<close> (a slice if the
    length is missing), \<open>EEllipsisArray\<close>, \<open>EMapType\<close>, \<open>EChanType\<close> (with its direction), \<open>EFuncType\<close>,
    \<open>EStructType\<close>, \<open>EInterfaceType\<close>, \<open>ETilde\<close> and \<open>EUnion\<close> of the constraints.
  \<^item> \<open>gSig\<close>, a signature: \<open>gParam\<close>s for the parameters and for the results, each with its names
    (none for an unnamed parameter), its type and a flag for \<open>...\<close>; \<open>gField\<close> (a struct field, with
    its tag, embedded if it has no name), \<open>gIElem\<close> (a method or a type element of an interface),
    \<open>gTParam\<close> (type parameters, with their constraint).
  \<^item> \<open>gStmt\<close>: \<open>SExpr\<close>, \<open>SSend\<close>, \<open>SIncDec\<close>, \<open>SAssign\<close> (with the operator of a compound assignment),
    \<open>SShortVar\<close>, \<open>SDecl\<close>, \<open>SLabeled\<close>, \<open>SGo\<close>, \<open>SDefer\<close>, \<open>SReturn\<close>, \<open>SBreak\<close>, \<open>SContinue\<close>, \<open>SGoto\<close>,
    \<open>SFallthrough\<close>, \<open>SBlock\<close>, \<open>SIf\<close>, \<open>SSwitch\<close> and \<open>STypeSwitch\<close> (with their \<open>gCase\<close> clauses),
    \<open>SSelect\<close> (with \<open>gComm\<close> clauses), \<open>SFor\<close> and \<open>SRange\<close>.
  \<^item> \<open>gDecl\<close>: \<open>DConst\<close>, \<open>DVar\<close>, \<open>DType\<close> and \<open>DImport\<close> (each a list of \<open>gSpec\<close>s - \<open>ConstSpec\<close>,
    \<open>VarSpec\<close>, \<open>TypeSpec\<close>, \<open>ImportSpec\<close> - with a flag for a parenthesised group), \<open>DFunc\<close> and
    \<open>DMethod\<close>.
  \<^item> \<open>gFile\<close>: a package name and the declarations of the file (imports included).
  \<^item> \<open>root\<close>: the result of a parse by entry point - \<open>Id\<close>, \<open>Expr\<close>, \<open>Stmts\<close>, \<open>Decls\<close> or \<open>Source\<close> -
    plus \<open>Stmt\<close> and \<open>Decl\<close>, never produced by a parse but used by the analysis as the closest
    context of an annotation on a statement or a declaration.

  Where the grammar is ambiguous without name resolution, the AST follows the syntactic reading
  and leaves the decision to the analysis: \<open>f(x)\<close> is an \<open>ECall\<close> whether \<open>f\<close> is a function or a
  type, \<open>a[i]\<close> an \<open>EIndex\<close> whether \<open>a\<close> is an array or a generic function, \<open>p.x\<close> an \<open>ESelector\<close>
  whether \<open>p\<close> is a package or a value. The empty statement is not kept (a semicolon alone is
  nothing), a labelled empty statement is a \<open>SLabeled\<close> with an \<open>SEmpty\<close>.
\<close>

section\<open>The Test Corpus: the Go Source Tree\<close>

text\<open>
  A grammar is only as good as the programs it has been tested on, and Go has the best corpus
  one could wish for: its own source tree. The test theory \<^verbatim>\<open>Go_Tests.thy\<close> therefore ends with a
  corpus test: if the environment variable \<^verbatim>\<open>GO_SRC\<close> names a Go source tree - the \<^verbatim>\<open>src\<close>
  directory of an installation, or of a checkout of \<^verbatim>\<open>github.com/golang/go\<close> - every \<^verbatim>\<open>.go\<close>
  file below it (but for the directories called \<^verbatim>\<open>testdata\<close>) is read, printed back, and read
  again; the two prints must be equal. In the release branch go1.27 (version 1.27.4) these are
  6\,821 files, the standard library with its tests, the compiler, the linker, the runtime and
  the tools, and all of them pass. The 3\,406 Go files of the \<^verbatim>\<open>test\<close> directory, which holds the
  compiler's regression tests, are read as well: 3\,333 pass, and the 73 that do not are,
  without exception, tests marked \<^verbatim>\<open>errorcheck\<close> (programs written to be rejected) and test
  drivers that are not Go files at all.

  The test found a number of facts about Go that its specification says in prose. The
  disambiguation of \<open>type T[P *C | string, Q any] \<dots>\<close>, an array type or a type parameter list,
  is decided by a comma after the first expression, as in the parser of Go; a type literal such
  as \<open>[]byte(s)\<close> in the header of a \<open>range\<close> clause ends at its closing parenthesis, whereas the
  parentheses of \<open>func(a int) T {\<close> belong to a function type; \<open>chan<- chan int\<close> and
  \<open>chan (<-chan int)\<close> differ by a pair of parentheses, since \<open><-\<close> binds to the leftmost \<open>chan\<close>;
  \<open>if ; cond {\<close> has an empty initialisation; a hexadecimal float may have no digit before the
  point. (And the tip of
  the development of the standard library already uses a syntax - an untyped composite literal as
  an argument - that is not in Go 1.27; the corpus is therefore the release branch.)

  Besides the corpus, the test theories contain round-trip tests for every construct (a program
  in the printer's canonical layout comes back unchanged, and every accepted program is a fixed
  point of parse-then-print), rejection tests, and, in \<^verbatim>\<open>Go_Cmd_Tests.thy\<close>, tests of the commands:
  the number of entity markups for each scoping rule, navigation, the evaluation order,
  \<open>go_file\<close> on the examples, export and the backend hook.
\<close>

section\<open>Limitations\<close>

text\<open>
  Isabelle/Go covers the language but is deliberately modest about what it does with it, and the
  navigation language is the narrowed one of Isabelle/C 2.0. Concretely:

  \<^item> \<^bold>\<open>Braces and composite literals follow the specification, and the stream is a
    heuristic.\<close> A composite literal in the header of an \<open>if\<close>, \<open>for\<close> or \<open>switch\<close> whose type is
    a bare name has to be parenthesised (\<open>if x == (T{}) {\<close>), as in Go. The stream decides block
    against literal from the tokens alone, without knowing types: in such a header a \<open>{\<close> that
    follows a type literal, a function literal's signature or a conversion's parentheses is
    read as a literal or a function body and not as the block. A program that Go accepts with a
    different reading of such a brace is not read; the corpus contains none.
  \<^item> \<^bold>\<open>One conventional resolution.\<close> \<open>type T[P *C] \<dots>\<close> is an array type unless a comma
    follows (\<open>type T[P *C, Q any] \<dots>\<close> has type parameters), which is also what the parser of Go
    does; \<open>func(a [n]int)\<close> is a parameter \<open>a\<close> of an array type, \<open>func(List[int])\<close> an unnamed
    parameter of an instantiated type.
  \<^item> \<^bold>\<open>Identifiers.\<close> An identifier is an ASCII letter or \<open>_\<close> followed by letters, digits and
    \<open>_\<close>, where every non-ASCII byte counts as a letter: Go's \<open>unicode_letter\<close> and
    \<open>unicode_digit\<close> are not checked. The semantic restrictions of the specification are not
    checked either (that a \<open>:=\<close> declares a new variable, that the left and right sides of an
    assignment have the same length, that a label is used, the order of \<open>case\<close> and \<open>default\<close>).
  \<^item> \<^bold>\<open>No semantics.\<close> There is no type checker, no method sets, no constant evaluation (\<open>iota\<close>
    is a name), no escape analysis. A name that resolves nowhere is silently left unmarked, a
    selection \<open>x.f\<close> is resolved only through types the pass knows (see \<open>\<section>2.2\<close>: a package
    member \<open>pkg.Name\<close> hyperlinks \<open>pkg\<close>, and nothing is known about the standard library), the names of a function type's
    parameters are declared nowhere, and the keys of a composite literal are resolved only when
    the type of the literal is known.
  \<^item> \<^bold>\<open>Contract-free.\<close> Go has no contract language, and the front-end adds none: what a
    comment means is up to its antiquotation, and what a program means is up to a semantic
    backend.
  \<^item> \<^bold>\<open>Comment placement.\<close> A comment is attached to the node starting at the next real token.
    A comment before a name that does not begin its line is attached to that name, not to the
    construct around it; an annotation meant for a statement belongs on its own line above it.
  \<^item> \<^bold>\<open>The \<open>text\<close> antiquotation never reaches the generated document.\<close> It runs the body
    through the real \<^ML>\<open>Document_Output.output_document\<close>, but the result only reaches a probe
    reference. This is a limitation of Isabelle itself, not of this front-end: the presentation
    of a command is only consulted for document-class commands, which a \<open>thy_decl\<close> command can
    never be.
  \<^item> \<^bold>\<open>Navigation is not total.\<close> An \<open>Id\<close> root is a leaf and is never navigable by \<open>r\<close>/\<open>d\<close>; there
    is no wrapping; and nodes without a \<open>root\<close> variant (parameters, fields, elements, clauses,
    specifications) cannot be navigation targets.

\<close>

section\<open>Conclusion\<close>

text\<open>
  Isabelle/Go shows that the design of Isabelle/C Version 2.0 carries over to a language whose
  specification is short, regular and precise: the grammar of the whole language is an ordinary
  ml-yacc grammar over an ordinary ml-lex lexer, with no conflict, and the Go toolchain's own
  source tree - well over six thousand files - is its test suite. The language-specific
  difficulties of Go are few and isolated in a small stream between lexer and parser: the
  semicolons that the lexer inserts, and a brace that is a block or a composite literal.
  Everything on top of the parser - positions, environment, hyperlinks, antiquotations,
  navigation, commands - is the C11 design instantiated for a new AST. What is documented in
  \<open>\<section>6\<close> as missing is, in every case, a scoping decision rather than an accident: the natural
  next steps are a semantic backend that translates Go programs into HOL - the antiquotations of
  \<open>\<section>2.5\<close> then state and discharge the specifications in the comments next to the program, as
  the \<open>lemma\<close> above - and, on the analysis side, the loading of imported packages, which would
  extend the type information the resolution of selections already has to the standard
  library.

  \pagebreak
\<close>

section\<open>Annex: The Go Grammar as Railroad Diagrams\<close>

subsection\<open>Lexical Structure\<close>

text\<open>
  The lexer is a small ml-lex specification in \<^verbatim>\<open>Go_Parser.thy\<close>. The 25 keywords of Go
  (\<open>break\<close>, \<open>case\<close>, \<open>chan\<close>, \<open>const\<close>, \<open>continue\<close>, \<open>default\<close>, \<open>defer\<close>, \<open>else\<close>, \<open>fallthrough\<close>,
  \<open>for\<close>, \<open>func\<close>, \<open>go\<close>, \<open>goto\<close>, \<open>if\<close>, \<open>import\<close>, \<open>interface\<close>, \<open>map\<close>, \<open>package\<close>, \<open>range\<close>,
  \<open>return\<close>, \<open>select\<close>, \<open>struct\<close>, \<open>switch\<close>, \<open>type\<close>, \<open>var\<close>) are reserved; every other word is an
  identifier, the blank identifier \<open>_\<close> and the predeclared names (\<open>int\<close>, \<open>nil\<close>, \<open>true\<close>, \<open>len\<close>,
  \<open>any\<close>, \<open>iota\<close>) included. Integer literals are decimal, binary (\<open>0b\<close>), octal (\<open>0\<close>, \<open>0o\<close>) or
  hexadecimal (\<open>0x\<close>), with underscores between digits; floating-point literals have a fraction
  or an exponent, or are hexadecimal with a binary exponent (\<open>0x1.8p3\<close>); a literal with an \<open>i\<close> is
  imaginary. A rune literal is \<open>'x'\<close> with the escapes of the specification; a string is
  interpreted (\<open>"\<dots>"\<close>) or raw (a backquote, which may contain newlines). The comment machinery lives
  in the lexer, as in the other front-ends: \<open>//\<close> enters a comment state that runs to the end of
  the line, \<open>/*\<close> one that runs to the next \<open>*/\<close>, and an antiquotation is recognised by a regular
  expression for its head, followed by a nesting-depth counter for a cartouche body. The syntax of
  the head:

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
  The grammar is reproduced here after the specification, slightly simplified: the two kinds of
  opening brace (\<open>LBRACE\<close>, \<open>BLOCKLB\<close>) are shown as \<open>{\<close>, the optional trailing separators are
  left out, and the binary operators are abbreviated by their precedence table, from the loosest
  to the tightest binding: \<open>||\<close>; \<open>&&\<close>; the comparisons \<open>==\<close>, \<open>!=\<close>, \<open><\<close>, \<open><=\<close>, \<open>>\<close>, \<open>>=\<close>; the
  adding operators \<open>+\<close>, \<open>-\<close>, \<open>|\<close>, \<open>^\<close>; the multiplying operators \<open>*\<close>, \<open>/\<close>, \<open>%\<close>, \<open><<\<close>, \<open>>>\<close>,
  \<open>&\<close>, \<open>&^\<close>; all left-associative.

  \<^rail>\<open>
    source__file : 'package' identifier ';' ((import__decl ';') *) ((top__level__decl ';') *)
    ;
    import__decl : 'import' (import__spec | '(' ((import__spec ';') *) ')')
    ;
    import__spec : ('.' | identifier)? string__lit
    ;
    top__level__decl : declaration | function__decl | method__decl
    ;
    declaration : const__decl | type__decl | var__decl
    ;
    const__decl : 'const' (const__spec | '(' ((const__spec ';') *) ')')
    ;
    const__spec : (identifier + ',') ((type? '=' (expression + ',')) ?)
    ;
    var__decl : 'var' (var__spec | '(' ((var__spec ';') *) ')')
    ;
    var__spec : (identifier + ',') (type ('=' (expression + ',')) ? | '=' (expression + ','))
    ;
    type__decl : 'type' (type__spec | '(' ((type__spec ';') *) ')')
    ;
    type__spec : identifier type__parameters? '='? type
    ;
    type__parameters : '[' ((identifier + ',') type__constraint + ',') ','? ']'
    ;
    type__constraint : (('~'? type) + '|')
  \<close>

  \<^rail>\<open>
    function__decl : 'func' identifier type__parameters? signature block?
    ;
    method__decl : 'func' parameters identifier type__parameters? signature block?
    ;
    signature : parameters (parameters | type)?
    ;
    parameters : '(' ((parameter + ',') ?) ','? ')'
    ;
    parameter : (identifier + ',')? '...'? type
  \<close>

  \<^rail>\<open>
    type : type__name type__args? | type__lit | '(' type ')'
    ;
    type__name : identifier ('.' identifier)?
    ;
    type__args : '[' (type + ',') ','? ']'
    ;
    type__lit : '[' expression? ']' type | '[' '...' ']' type
              | 'struct' '{' ((field__decl ';') *) '}' | '*' type | 'func' signature
              | 'interface' '{' ((interface__elem ';') *) '}'
              | 'map' '[' type ']' type | ('chan' | 'chan' '<-' | '<-' 'chan') type
    ;
    field__decl : ((identifier + ',') type | '*'? type__name type__args?) string__lit?
    ;
    interface__elem : identifier signature | (('~'? type) + '|')
  \<close>

  \<^rail>\<open>
    expression : unary__expr | expression binary__op expression
    ;
    unary__expr : primary__expr | ('+' | '-' | '!' | '^' | '*' | '&' | '<-') unary__expr
    ;
    primary__expr : operand
                  | primary__expr '.' identifier
                  | primary__expr '.' '(' (type | 'type') ')'
                  | primary__expr '[' (expression + ',') ','? ']'
                  | primary__expr '[' expression? ':' expression? (':' expression)? ']'
                  | primary__expr '(' ((expression + ',') '...'? ','?)? ')'
                  | primary__expr literal__value
    ;
    operand : literal | identifier | '(' expression ')' | 'func' signature block
            | type__lit
    ;
    literal__value : '{' (((key ':')? element) + ',') ','? '}'
    ;
    key : expression | literal__value
    ;
    element : expression | literal__value
  \<close>

  \<^rail>\<open>
    block : '{' ((statement ';') *) '}'
    ;
    statement : declaration | identifier ':' statement | simple__stmt | 'go' expression
              | 'defer' expression | 'return' (expression + ',')? | 'break' identifier?
              | 'continue' identifier? | 'goto' identifier | 'fallthrough' | block | if__stmt
              | switch__stmt | select__stmt | for__stmt
    ;
    simple__stmt : expression | expression '<-' expression | expression ('++' | '--')
                 | (expression + ',') assign__op (expression + ',')
                 | (identifier + ',') ':=' (expression + ',')
    ;
    assign__op : (('+' | '-' | '|' | '^' | '*' | '/' | '%' | '<<' | '>>' | '&' | '&^') ?) '='
    ;
    if__stmt : 'if' (simple__stmt ';')? expression block ('else' (if__stmt | block))?
    ;
    switch__stmt : 'switch' (simple__stmt ';')?
                   (expression | (identifier ':=')? primary__expr '.' '(' 'type' ')')?
                   '{' ((('case' (expression + ',') | 'default') ':' ((statement ';') *)) *) '}'
    ;
    select__stmt : 'select' '{' ((('case' simple__stmt | 'default') ':' ((statement ';') *)) *) '}'
    ;
    for__stmt : 'for' ((expression | (simple__stmt? ';' expression? ';' simple__stmt?)
                      | (((expression + ',') ('=' | ':='))? 'range' expression)) ?) block
  \<close>
\<close>

(*<*)
end
(*>*)
