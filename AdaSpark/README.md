# Isabelle/AdaSpark

A front-end for **Ada 2012 and its SPARK 2014 subset** inside Isabelle/HOL: the
Ada member of the family of verification front-ends (`../C11`, `../occam2`,
`../scala3`, `../MicroRust`). Ada source text lives inside an Isabelle theory,
is parsed by a real grammar and is checked incrementally under Isabelle/PIDE. It
is not a compiler and has no semantics (no type checker, no overload
resolution); it is the front-end layer on which a semantic backend - for
instance a generator of proof obligations from SPARK contracts - can be built
(see `setup_backend` below).

## Why Ada, and where the grammar comes from

Ada has an official grammar: Annex P of the Ada Reference Manual (ISO/IEC
8652:2012) is an EBNF syntax summary of the whole language, and SPARK 2014
(the Ada subset designed for formal proof) is a subset of Ada 2012 whose
contracts - `Pre`, `Post`, `Global`, `Depends`, `Contract_Cases`,
`Abstract_State`, ghost code - are *aspects*, ordinary Ada 2012 syntax. This
front-end follows Annex P for the subset that SPARK uses (packages, subprograms
including expression functions, scalar, array, record, tagged and private
types, statements, the full expression language with conditional and quantified
expressions, aspects and pragmas) and leaves out generics, tasking, `goto`,
interfaces, renamings and `separate` units. The test corpus is the twenty Ada
sources of Isabelle's own HOL-SPARK examples (`src/HOL/SPARK`): all are read.

## What is there

The concepts are those of the C11 project, carried over one for one:

* **Parsing** with `ml_lex_yacc [state]` into a real abstract syntax tree
  (`adaspark_ast.ML`) with a source position at every node; every parse has its
  own state object, so parses are re-entrant. The grammar is LALR(1) over the
  lexer's tokens (Ada has no layout, so no stream in between). Ada is case
  insensitive: keywords in any case, identifiers kept as written.
* **Binding**: every declaration and every resolved name use is reported with
  Isabelle's entity markup (hover, click-through), with Ada's single name space,
  sequential visibility, scopes (subprograms, loops, quantifiers, discriminants)
  and packages (qualified names, package bodies, `use` clauses); names that
  resolve nowhere (a `with`ed unit, a predefined package) are not marked.
* **Antiquotations** in `--` comments,
  `--@ tag[navi](level) \<open>body\<close>`, with the same navigation (`u`,
  `U`, `r`, `d`), evaluation levels and the eight standard antiquotations as in
  the other front-ends (`probe_aenv`, `probe_ast`, `highlight`, `term`, `ML`,
  `text`, `definition`, `lemma`).
* **Commands**: `adaspark` (a source file: compilation units), `adaspark_body`
  (a statement sequence), `adaspark_expr`, `adaspark_type`, `adaspark_ident`,
  `adaspark_file` (an external `.ads`/`.adb` file), the silent negative-test
  variants `*_reject`, `adaspark_export`, `set_aenv_default` / `reset_aenv`, and
  `setup_backend` (the semantic-backend hook: an ML function
  `root -> theory -> theory`, `K I` by default, run at the end of `adaspark`,
  `adaspark_body` and `adaspark_file`).

```isabelle
theory Demo imports AdaSpark begin

adaspark\<open>
package Stacks
  with SPARK_Mode
is
   Capacity : constant := 100;

   procedure Push (Top : in out Natural; X : Integer)
     with Pre  => Top < Capacity,
          Post => Top = Top'Old + 1;
end Stacks;
\<close>

end
```

## Contents

| Path | What |
| --- | --- |
| `AdaSpark.thy` | core theory: keywords and the Isar commands |
| `AdaSpark_Parser.thy` | lexer, yacc grammar (`ml_lex_yacc`) |
| `AdaSpark_Ast.thy`, `adaspark_ast.ML`, `adaspark_pp.ML` | the abstract syntax tree and its pretty-printer |
| `AdaSpark_Env.thy` | environment (`AEnv`), AST store, antiquotation registry |
| `AdaSpark_AnaEval.thy` | scoped analysis: hyperlinking, navigation, antiquotation dispatch, standard antiquotations |
| `AdaSpark_Tests.thy` | parser-level tests (round trip, idempotence, rejection) and the HOL-SPARK corpus |
| `AdaSpark_Cmd_Tests.thy` | command-level tests: binding, navigation, levels, `adaspark_file`, export, backend |
| `examples/` | SPARK 2014 examples (`stacks`, `search`, `counters`, `shapes`, `animals`, `hello`), read by `adaspark_file` in the tests and the manual |
| `manual/` | the manual (`AdaSpark_Manual.thy`) as a sub-session that produces the PDF |

## Building

The session is independent of the other sessions of this repository: build it on
its own, never together with them. Isabelle2026 is the supported version.

```sh
isabelle build -d AdaSpark AdaSpark            # all theories and tests
isabelle build -d AdaSpark AdaSpark_Manual     # the manual: manual/output/document.pdf
```

The manual is generated, not stored in the repository: building
`AdaSpark_Manual` writes it to `AdaSpark/manual/output/document.pdf` (the
`output` folders are git-ignored). Building the session with `-c` regenerates it
from scratch.

`AdaSpark/ROOTS` makes the manual's sub-session visible to `-d AdaSpark`. To
work interactively, open a theory importing `AdaSpark` with
`isabelle jedit -d AdaSpark -l AdaSpark`.

## Tests

`AdaSpark_Tests.thy` has round-trip tests for every construct. Its corpus test
reads every `.ads` and `.adb` file below `~~/src/HOL/SPARK` (twenty files: SPARK
83 / Ada 95 programs whose `--#` annotations are plain comments for this
parser), checks that the text printed back from the AST parses again to the same
text, and fails otherwise. `AdaSpark_Cmd_Tests.thy` counts the entity markups
for each scoping rule and exercises navigation, levels, `adaspark_file` on
`examples/`, export and the backend hook.

`adaspark_export` writes `.ada` files next to the exporting theory; those are
generated on every build and are git-ignored (`examples/` holds the real
sources).

## Status and limitations

Everything described above builds and passes its tests. Deliberate gaps: generic
units, tasks and protected objects, `goto`, interfaces, renamings, `separate`
units, representation clauses other than attribute definitions (the reserved
words of these are rejected, never misread); the qualified expression `T'('a')`
(the lexer reads `'('` as a character literal); an object declaration
`X : not null T` and a derived type definition directly followed by aspects; a
selected component or attribute is not resolved (a package member `P.X` is, when
`P` is known), nor are the formal-parameter names of a call. The name closing a
unit (`end P;`) is not compared with the name that opened it, and
`and`/`or`/`xor` may be mixed without parentheses.

The yacc grammar has 11 shift/reduce conflicts and no reduce/reduce conflict,
all resolved by shifting, in the intended way: `null` as a statement or as a
literal, the `not null` of a subtype indication, the bar of a membership test's
choices, `..` as an association against a choice, the commas of a `case`
expression, `not` after a parameter's mode, and `with` after a derived type.

## License

BSD-style, see the SPDX headers of the theory files and `../LICENSE`.
