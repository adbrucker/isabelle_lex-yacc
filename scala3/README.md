# Isabelle/Scala 3

A front-end for **Scala 3** inside Isabelle/HOL: the Scala 3 analogue of the C11
and occam 2 projects (folders `../C11`, `../occam2`), built on the same
architecture. Scala 3 source text lives inside an Isabelle theory, is parsed by
a real grammar that follows the [Scala 3 syntax
summary](https://docs.scala-lang.org/scala3/reference/syntax.html), and is
analysed incrementally under Isabelle/PIDE. It is not a compiler and has no
semantics (no type checker, no implicits resolution); it is the front-end layer
on which such tools can be built, e.g. for Isabelle's own Scala sources.

* **Parsing** with `ml_lex_yacc [state]` into a real abstract syntax tree
  (`scala3_ast.ML`) with a source position at every node. Parses are re-entrant
  (one state object per parse).
* **Binding**: name uses are hyperlinked to their definitions, in two name
  spaces (terms and types), with Scala's scoping: members of templates and the
  top level are mutually visible (forward references), block-local names only
  after their definition, parameters, pattern variables, generators, `given`s,
  `enum` cases, `extension` parameters. Unresolved names (library names) are
  left unmarked.
* **Antiquotations** in `//@ tag[navi](level) \<open>body\<close>` and
  `/*@ ... */` comments, with the same navigation (`u`, `U`, `r`, `d`) and
  level rules as in C11, and the standard set (`probe_senv`, `probe_ast`,
  `highlight`, `term`, `ML`, `text`, `definition`, `lemma`).
* Commands: `scala3`, `scala3_expr`, `scala3_type`, `scala3_ident`,
  `scala3_file`, the silent negative-test variants (`*_reject`),
  `scala3_export`, `set_senv_default` / `reset_senv`, `setup_backend`.

## Scope: what the grammar covers

* **Brace syntax only.** Scala 3's optional braces / significant indentation
  are *not* covered; the grammar is the Scala 3 syntax with explicit braces
  (which Scala 3 still accepts everywhere). Newlines act as statement
  separators according to the language's inference rules (a layout stream
  between lexer and parser tracks parentheses, braces and `case` regions).
* **Soft keywords** (`given`, `using`, `extension`, `inline`, `opaque`, `open`,
  `transparent`, `infix`, `end`, `derives`, `as`, `?`, `*`, `-`, `+`,
  `|`, `&` ...) are accepted as ordinary names where Scala permits it, and
  recognised as keywords by their position. `inline`, `open`, `infix`, `opaque`
  and `transparent` are told apart (modifier or name) by the layout stream with
  one or two tokens of look-ahead, as the Scala scanner does.
* Interpolated strings are kept as raw tokens (embedded expressions are not
  parsed); nested block comments are supported.
* The Scaladoc-style `@tags` are *not* antiquotations; an antiquotation needs
  the `//@` / `/*@` marker.

## Grammar status: conflict free

ml-yacc reports **no shift/reduce and no reduce/reduce conflict** for the
grammar (it had 123 and 71). Where shifting is the reading Scala intends (a type
continuing with an operator, a refinement or `with`; `(implicit`, `(using`; a
statement list absorbing a separator ...), the grammar declares it with
precedences rather than leaving it to the tool's default: the reducing rules
carry the pseudo-precedence `TYLOW`, the continuing tokens a higher one. The soft
modifiers are decided by the layout stream, and `given` has a clause list of
its own without the empty clause `()`. Each step was checked by comparing the
AST of all 380 Isabelle Scala files before and after.

## Tested against Isabelle's own sources

The parser reads all 380 `.scala` files of the Isabelle distribution, and the
pretty-printer's output for each parses again to the same text (idempotence).

## Contents

| Path | What |
| --- | --- |
| `Scala3.thy` | core theory: keywords and the Isar commands |
| `Scala3_Parser.thy` | lexer, layout stream, yacc grammar (`ml_lex_yacc`) |
| `Scala3_Ast.thy`, `scala3_ast.ML`, `scala3_pp.ML` | AST and pretty-printer |
| `Scala3_Env.thy` | environment (`SEnv`), AST store, antiquotation registry |
| `Scala3_AnaEval.thy` | scoped analysis, navigation, antiquotation dispatch |
| `Scala3_Tests.thy` | parser-level tests (round trip, idempotence, rejection, parallel parses) |
| `Scala3_Cmd_Tests.thy` | command-level tests (binding, navigation, levels, files, export, backend) |
| `examples/` | `Lists.scala`, `Pipeline.scala`, read by `scala3_file` in the tests |
| `manual/` | the manual (`Scala3_Manual.thy`) as a sub-session that produces the PDF |

## Building

Build the session on its own, never together with the other sessions of this
repository. Isabelle2026 is the supported version.

```sh
isabelle build -d scala3 Scala3            # all theories and tests
isabelle build -d scala3 Scala3_Manual     # the manual: manual/output/document.pdf
```

`scala3/ROOTS` makes the manual's sub-session visible to `-d scala3`. To work
interactively, open a theory importing `Scala3` with
`isabelle jedit -d scala3 -l Scala3`.

`scala3_export` writes `.scala` files next to the exporting theory; they are
generated on every build and git-ignored.

## License

BSD-style, see the SPDX headers of the theory files and `../LICENSE`.
