# Isabelle/C 2.0 (C11)

A front-end for **ISO C11** inside Isabelle/HOL, and the original of the family of
verification front-ends of this repository (`../occam2`, `../scala3`,
`../MicroRust`, `../AdaSpark` carry its design over to other languages). C source
text lives inside an Isabelle theory, is parsed by a real grammar and is checked
incrementally under Isabelle/PIDE. It is not a compiler and has no semantics; it
is the front-end layer on which a semantic backend can be built (see
`setup_backend`). It is a from-scratch re-design of the `Isabelle_C` AFP entry
on top of the generic `ml_lex_yacc` command of this repository.

## What is there

* **Parsing** with `ml_lex_yacc` of the ANSI C11 grammar (ported from the
  reference Lex/Yacc grammar of <https://www.quut.com/c/>) into a real abstract
  syntax tree (`c11_ast.ML`, a pruned port of the `language-c` tree used by
  `Isabelle_C`) with a source position at every node. A small fragment of the
  preprocessor (`#include`, `#define`, `#ifdef`/`#ifndef`) is kept as syntax.
* **Binding**: every declaration and every use of a name is reported with
  Isabelle's entity markup (hover, click-through); an unresolved name is marked.
* **Antiquotations** in comments, `/*@ tag[navi](level) \<open>body\<close> */`
  or `//@ ...`, with a navigation language (`u`, `U`, `r`, `d`), evaluation
  levels and standard antiquotations (`probe_cenv`, `probe_ast`, `highlight`,
  `term`, `ML`, `text`, `definition`, `lemma`).
* **Commands**: `c11` (a translation unit), `c11_ident`, `c11_expr`,
  `c11_statement`, `c11_predef` (declare a header's effect), `c11_file` (an
  external `.c`/`.h` file), the silent negative-test variants `*_reject`,
  `c11_export_h` / `c11_export_c`, `set_cenv_default` / `reset_cenv`, and
  `setup_backend` (the semantic-backend hook).

## Contents

| Path | What |
| --- | --- |
| `C11.thy` | core theory: keywords and the Isar commands |
| `C11_Parser.thy` | lexer and yacc grammar (`ml_lex_yacc`) |
| `C11_Ast.thy`, `c11_ast.ML` | the abstract syntax tree |
| `C11_Env.thy` | environment (`CEnv`), AST store, antiquotation registry |
| `C11_AnaEval.thy` | scoped analysis: hyperlinking, navigation, antiquotation dispatch |
| `C11_Tests.thy` | tests |
| `AntiqProbe.thy`, `SelectionSort.thy`, `BinarySearch.thy`, `MergeSort.thy` | worked examples: C programs with HOL specifications and proofs in antiquotations |
| `C11_Manual.thy`, `document/` | the manual |
| `examples/` | C sources read by `c11_file` (see `examples/README.md`) |

## Building and the manual

The session is independent of the other sessions of this repository: build it on
its own, never together with them. Isabelle2026 is the supported version. Unlike
the other front-ends the manual is part of the session itself (there is no
`ROOTS` file and no sub-session):

```sh
isabelle build -d C11 C11      # all theories, tests and the manual
```

The manual is generated, not stored in the repository: building `C11` writes it
to `C11/output/document.pdf` (the `output` folders are git-ignored). Building
with `-c` regenerates it from scratch. To work interactively, open a theory
importing `C11` with `isabelle jedit -d C11 -l C11`.

`c11_export_h` and `c11_export_c` write `.c` and `.h` files next to the exporting
theory; those are generated on every build and are git-ignored (`examples/` holds
the real sources).

## Status and limitations

Everything described above builds and passes its tests. The grammar has two
shift/reduce conflicts (the dangling `else`, and `_Atomic` as a qualifier or a
type specifier) and one reduce/reduce conflict (a bare identifier is an `Id`, not
an `Expr`), all resolved in the intended way. The lexer has one piece of
feedback from the parser: the names declared by a `typedef` are lexed as type
names from then on (`C11_Typedefs`, kept for the rest of the session and merged
only from accepted parses; `c11_predef` uses it for headers). It is a flat set,
not block-scoped, so a local variable that shadows a typedef name is still lexed
as a type name. The preprocessor is only recognised, not run. The manual's *Limitations* section has the details.

## License

BSD-style, see the SPDX headers of the theory files and `../LICENSE`.
