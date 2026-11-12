# Isabelle/Go

A front-end for **Go** (language version 1.27) inside Isabelle/HOL: the Go member of the family of
verification front-ends (`../C11`, `../occam2`, `../scala3`, `../MicroRust`, `../AdaSpark`). Go
source text lives inside an Isabelle theory, is parsed by a real grammar and is checked
incrementally under Isabelle/PIDE. It is not a compiler and has no semantics (no type checker, no
method sets, no escape analysis); it is the front-end layer on which a semantic backend can be
built (see `setup_backend` below).

## Why Go, and where the grammar comes from

Go has an official, short and regular grammar: *The Go Programming Language Specification*
(<https://go.dev/ref/spec>) defines the syntax in EBNF. This front-end follows it for the whole
language, including generics (type parameters on functions, methods and types, constraints with
`~T` and unions, instantiation), range-over-int and range-over-function loops, and the additions of
the language versions up to 1.27 (generic methods, any field selector as a key of a struct literal).
Two things need help from a layout stream between lexer and parser, both explained in
`Go_Parser.thy`: the semicolons the lexer of Go inserts at the end of a line, and the two kinds of
opening brace (a block, and a composite literal in the header of an `if`, `for` or `switch`).

Following `go/ast`, a **type is an expression**: Go does not tell a call from a conversion, an index
from an instantiation, or `*p` from `*T` by syntax. The test corpus is the Go standard library: all
6 821 `.go` files of Go 1.27 (outside `testdata`) are read, and printed back to text that parses to
the same text; of the 3 406 files of the compiler's own `test/` directory, 3 333 are accepted, and
the 73 that are rejected are all tests meant to be rejected (`errorcheck`) or stubs that are not Go
files.

## What is there

The concepts are those of the C11 project, carried over one for one:

* **Parsing** with `ml_lex_yacc [state]` into a real abstract syntax tree (`go_ast.ML`) with a
  source position at every node; every parse has its own state object, so parses are re-entrant.
  The grammar is LALR(1) and **conflict free**.
* **Binding**: every declaration and every resolved name use is reported with Isabelle's entity
  markup (hover, click-through), with Go's block scoping, the forward visibility of package-level
  names, short variable declarations, imports, generics and labels; names that resolve nowhere
  (the universe block, a dot import) are not marked.
* **Antiquotations** in `//` and `/* */` comments, `//@ tag[navi](level) \<open>body\<close>`,
  with the same navigation (`u`, `U`, `r`, `d`), evaluation levels and the eight standard
  antiquotations as in the other front-ends (`probe_genv`, `probe_ast`, `highlight`, `term`, `ML`,
  `text`, `definition`, `lemma`).
* **Commands**: `go` (a source file), `go_decl` (top-level declarations without a package clause),
  `go_stmt` (a statement list), `go_expr`, `go_type`, `go_ident`, `go_file` (an external `.go`
  file), the silent negative-test variants `*_reject`, `go_export`, `set_genv_default` /
  `reset_genv`, and `setup_backend` (the semantic-backend hook: an ML function `root -> theory ->
  theory`, `K I` by default, run at the end of `go`, `go_decl`, `go_stmt` and `go_file`).

```isabelle
theory Demo imports Go begin

go\<open>
package stack

// Stack is a generic stack.
type Stack[T any] struct {
	items []T
}

func (s *Stack[T]) Push(x T) {
	//@ highlight
	s.items = append(s.items, x)
}
\<close>

end
```

## Contents

| Path | What |
| --- | --- |
| `Go.thy` | core theory: keywords and the Isar commands |
| `Go_Parser.thy` | lexer, layout stream, yacc grammar (`ml_lex_yacc`) |
| `Go_Ast.thy`, `go_ast.ML`, `go_pp.ML` | the abstract syntax tree and its pretty-printer (the layout of `gofmt`) |
| `Go_Env.thy` | environment (`GEnv`), AST store, antiquotation registry |
| `Go_AnaEval.thy` | scoped analysis: hyperlinking, navigation, antiquotation dispatch, standard antiquotations |
| `Go_Tests.thy` | parser-level tests (round trip, idempotence, rejection) and the Go source tree corpus |
| `Go_Cmd_Tests.thy` | command-level tests: binding, navigation, levels, `go_file`, export, backend |
| `examples/` | Go programs (`hello`, `stack`, `shapes`, `worker`, `flow`), read by `go_file` in the tests and the manual |
| `manual/` | the manual (`Go_Manual.thy`) as a sub-session that produces the PDF |

## Building

The folder is called `Golang1.27`, after the language version it implements; the session, the
theories and the commands are called `Go` and `go`. The session is independent of the other
sessions of this repository: build it on its own, never together with them. Isabelle2026 is the
supported version.

```sh
isabelle build -d Golang1.27 Go            # all theories and tests
isabelle build -d Golang1.27 Go_Manual     # the manual: manual/output/document.pdf
```

The manual is generated, not stored in the repository: building `Go_Manual` writes it to
`Golang1.27/manual/output/document.pdf` (the `output` folders are git-ignored). Building with `-c`
regenerates it from scratch. `Golang1.27/ROOTS` makes the manual's sub-session visible to
`-d Golang1.27`. To work interactively, open a theory importing `Go` with
`isabelle jedit -d Golang1.27 -l Go`.

## Tests

`Go_Tests.thy` has round-trip tests for every construct. Its corpus test reads a Go source tree if
the environment variable `GO_SRC` names one (for instance `$GOROOT/src`, or the `src` directory of a
checkout of `github.com/golang/go`), skipping `testdata` directories:

```sh
GO_SRC=/path/to/go/src isabelle build -d Golang1.27 Go
```

`Go_Cmd_Tests.thy` counts the entity markups for each scoping rule and exercises navigation, levels,
`go_file` on `examples/`, export and the backend hook. `go_export` writes `.go` files next to the
exporting theory; those are generated on every build and are git-ignored (`examples/` holds the real
sources).

## Status and limitations

Everything described above builds and passes its tests. Deliberate choices and gaps: a composite
literal in the header of an `if`, `for` or `switch` whose type is a bare name must be parenthesised
(`if x == (T{}) {`), as the specification says; the stream decides block against literal from the
tokens alone, so a function literal or type literal in such a header that is directly followed by a
brace is read as a literal; `type T[P *C] ...` is an array type unless a comma follows (as in Go's
own parser); identifiers are ASCII letters, digits and `_` plus every non-ASCII byte; the keys of a
composite literal that are bare names are resolved only if the type of the literal is known,
selections `x.f` are resolved by a type pass that links a field or method only when it is certain
(same-package types, signatures and methods in any order; embedding, pointers, interfaces, aliases
and explicitly instantiated generic types are handled, while the standard library and the
inference of type arguments are not seen), a name that resolves nowhere is not marked; the empty
statement is not kept in the tree; and the untyped composite literal as an argument that the development version of Go
(after 1.27) experiments with is not Go 1.27 and is rejected.

The yacc grammar has no shift/reduce and no reduce/reduce conflict. Where shifting is the reading
Go intends (a type name followed by `[`, `.` or `{`; a result type after a parameter list) the
grammar declares it with precedences.

## License

BSD-style, see the SPDX headers of the theory files and `../LICENSE`.
