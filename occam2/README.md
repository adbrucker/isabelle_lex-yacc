# Isabelle/occam

A front-end for the **occam 2** language inside Isabelle/HOL: the occam analogue
of the C11 project ("Isabelle/C, Version 2.0", folder `../C11`). occam 2 source
text lives inside an Isabelle theory, is parsed by a real grammar that follows
the INMOS [*occam 2 Reference
Manual*](https://www.transputer.net/obooks/isbn-013629312-3/oc20refman.pdf), and
is checked incrementally under Isabelle/PIDE. It is not a compiler and has no
semantics (no type checker, no usage rules); it is the front-end layer on which
such tools can be built.

The concepts are those of the C11 project, carried over one for one:

* **Parsing** with `ml_lex_yacc` into a real abstract syntax tree
  (`occam2_ast.ML`) with a source position at every node. occam has no
  brackets, only indentation (the *offside rule*): the lexer records line
  indentation and a small stream transformer between lexer and parser turns it
  into `NEWLINE`/`INDENT`/`OUTDENT` tokens, so the grammar itself is an
  ordinary context-free yacc grammar. occam also has no operator precedence,
  and the grammar mirrors that.
* **Binding**: every name use is hyperlinked to its declaration (hover and
  click in jEdit), following occam's scoping rules (a specification scopes
  over the process it prefixes; no recursion; replicator indices scope over
  their body). Undeclared names are underlined, not rejected.
* **Antiquotations** in `--` comments,
  `--@ tag[navi](level) \<open>body\<close>`, with programmable handlers, an
  evaluation order given by the level, and eight standard ones (`probe_oenv`,
  `probe_ast`, `highlight`, `term`, `ML`, `text`, `definition`, `lemma`).
* **Navigation**: the optional `[navi]` string (`u`, `U`, `r`, `d`) re-targets
  an antiquotation from the node it is attached to to a parent, sibling or
  child, with the same rules as in C11.

## A first look

```isabelle
theory Demo imports Occam2 begin

occam2\<open>
INT x:
SEQ
  --@ highlight[rrd]
  x := 42
  x := x + 1
\<close>

end
```

The commands are `occam2` (a program unit), `occam2_expr`, `occam2_ident`,
`occam2_file` (an external `.occ` file), the silent negative-test variants
`occam2_reject`, `occam2_expr_reject`, `occam2_ident_reject`,
`occam2_export` (stored sections back to occam text),
`set_oenv_default` / `reset_oenv`, and `setup_backend`, which installs a
semantic backend (an ML function `root -> theory -> theory`, `K I` by default)
run at the end of every `occam2` / `occam2_file`.

## Contents

| Path | What |
| --- | --- |
| `Occam2.thy` | core theory: keywords and the Isar commands |
| `Occam2_Parser.thy` | lexer, layout stream transformer, yacc grammar (`ml_lex_yacc`) |
| `Occam2_Ast.thy`, `occam2_ast.ML` | the abstract syntax tree and its pretty-printer |
| `Occam2_Env.thy` | environment (`OEnv`), AST store, antiquotation registry |
| `Occam2_AnaEval.thy` | scoped analysis: hyperlinking, navigation, antiquotation dispatch, standard antiquotations |
| `Occam2_Tests.thy` | parser-level tests (round trip, idempotence, rejection) |
| `Occam2_Cmd_Tests.thy` | command-level tests: binding, navigation, levels, `occam2_file`, export |
| `Occam2_Example.thy` | worked example: Euclid's algorithm with contract annotations, and a one-place buffer in a `PAR` |
| `examples/` | `mathlib.occ` and `pipeline.occ`, read by `occam2_file` in the tests |
| `manual/` | the manual (`Occam2_Manual.thy`) as a sub-session that produces the PDF |

## Building

The session is independent of the other sessions of this repository (the
parent `../ROOT` and `../C11/ROOT`): build it on its own, never together with
them. Isabelle2026 is the supported version.

```sh
isabelle build -d occam2 Occam2            # all theories and tests
isabelle build -d occam2 Occam2_Manual     # the manual: manual/output/document.pdf
```

`occam2/ROOTS` makes the manual's sub-session visible to `-d occam2`. To work
interactively, open a theory importing `Occam2` with
`isabelle jedit -d occam2 -l Occam2`.

`occam2_export` writes `.occ` files next to the exporting theory; those are
generated on every build and are git-ignored (`examples/` holds the real
sources).

## Status and limitations

Everything described above builds and passes its tests. Deliberate gaps,
documented in the manual's *Limitations* section: indentation is checked for
consistency, not for exact width; compiler directives (`#USE`, `#INCLUDE`, ...)
are not recognised; there is no type or usage checking; four benign yacc
conflicts are resolved in the intended way. The parser is re-entrant: it is
built with `ml_lex_yacc [state]`, so every parse has its own state object and
any number of parses may run at the same time.

## License

BSD-style, see the SPDX headers of the theory files and `../LICENSE`.
