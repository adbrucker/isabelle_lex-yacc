# Isabelle/MicroRust

A front-end for **MicroRust** inside Isabelle/HOL: the Rust member of the family
of verification front-ends (`../C11`, `../occam2`, `../scala3`). MicroRust is
the Rust-like language **uRust** of the
[AutoCorrode](https://github.com/awslabs/AutoCorrode) verification framework,
plus a thin layer of Rust items (`fn`, `struct`, `enum`, `impl`, `trait`,
`const`, `static`, `type`, `use`, `mod`) so that a whole source file can be read
and not only the body of a function. Source text lives inside an Isabelle
theory, is parsed by a real grammar and is checked incrementally under
Isabelle/PIDE. It is not a compiler and has no semantics (no type checker, no
borrow checker); it is the front-end layer on which a translation to
AutoCorrode's shallow embedding, or any other semantic backend, can be built
(see `setup_backend` below).

## Why uRust, and where the grammar comes from

There is no official, machine-usable grammar of Rust: `rustc` is the
specification; the Rust Reference describes the syntax in a PEG-style notation
(ordered choice and a "hard cut"), which cannot be turned into an LALR grammar
mechanically; the grammar of `rust-analyzer` (`rust.ungram`) says itself that it
"does not specify parsing rules (ambiguities, precedence, etc)". uRust, on the
other hand, is a *chosen subset with an explicit syntax table*: in AutoCorrode
it is an Isabelle syntax category with about 130 mixfix rules and priorities
(`Micro_Rust_Syntax.thy`). This front-end follows that table for the constructs
and the Rust Reference for the operator precedences, and extends it by the
items. The test corpus is AutoCorrode itself: every uRust body of its sources is
read (see *Tests*).

## What is there

The concepts are those of the C11 project, carried over one for one:

* **Parsing** with `ml_lex_yacc [state]` into a real abstract syntax tree
  (`microrust_ast.ML`) with a source position at every node; every parse has its
  own state object, so parses are re-entrant. The grammar is LALR(1); the stream
  between lexer and parser classifies braces (struct expression or block) and
  glues `>` for `>>`, `>=`, `>>=`.
* **Binding**: every declaration and every resolved name use is reported with
  Isabelle's entity markup (hover, click-through), with Rust's scoping and its
  two name spaces; names that resolve nowhere (the prelude, glob imports) are
  not marked.
* **Antiquotations** in `//` and `/* */` comments,
  `//@ tag[navi](level) \<open>body\<close>`, with the same navigation (`u`,
  `U`, `r`, `d`), evaluation levels and the eight standard antiquotations as in
  the other front-ends (`probe_renv`, `probe_ast`, `highlight`, `term`, `ML`,
  `text`, `definition`, `lemma`).
* **Commands**: `microrust` (a source file), `microrust_body` (a uRust function
  body, as written between `FunctionBody \<lbrakk>` and `\<rbrakk>`: statements
  and a final expression, no braces), `microrust_expr`, `microrust_type`,
  `microrust_ident`, `microrust_file` (an external `.rs` file), the silent
  negative-test variants `*_reject`, `microrust_export`, `set_renv_default` /
  `reset_renv`, and `setup_backend` (the semantic-backend hook: an ML function
  `root -> theory -> theory`, `K I` by default, run at the end of `microrust`,
  `microrust_body` and `microrust_file`).

```isabelle
theory Demo imports MicroRust begin

microrust_body\<open>
let mut x = \<llangle>0 :: nat\<rrangle>;
//@ highlight
while *x < 10 {
    x += 1;
}
*x
\<close>

end
```

uRust's HOL escapes (`\<llangle>...\<rrangle>`, `\<epsilon>\<open>...\<close>`),
`yield`, `log a b`, parenthesized statement sequences and Isabelle's
`\<comment>\<open>...\<close>` comments are part of the language here; they are
kept as opaque text.

## Contents

| Path | What |
| --- | --- |
| `MicroRust.thy` | core theory: keywords and the Isar commands |
| `MicroRust_Parser.thy` | lexer, brace-classifying stream, yacc grammar (`ml_lex_yacc`) |
| `MicroRust_Ast.thy`, `microrust_ast.ML`, `microrust_pp.ML` | the abstract syntax tree and its pretty-printer |
| `MicroRust_Env.thy` | environment (`REnv`), AST store, antiquotation registry |
| `MicroRust_AnaEval.thy` | scoped analysis: hyperlinking, navigation, antiquotation dispatch, standard antiquotations |
| `MicroRust_Tests.thy` | parser-level tests (round trip, idempotence, rejection) and the AutoCorrode corpus |
| `MicroRust_Cmd_Tests.thy` | command-level tests: binding, navigation, levels, `microrust_file`, export, backend |
| `examples/` | `shapes.rs` and `counter.rs`, read by `microrust_file` in the tests |
| `manual/` | the manual (`MicroRust_Manual.thy`) as a sub-session that produces the PDF |

## Building

The session is independent of the other sessions of this repository: build it on
its own, never together with them. Isabelle2026 is the supported version.

```sh
isabelle build -d MicroRust MicroRust            # all theories and tests
isabelle build -d MicroRust MicroRust_Manual     # the manual: manual/output/document.pdf
```

The manual is generated, not stored in the repository: building
`MicroRust_Manual` writes it to `MicroRust/manual/output/document.pdf` (the
`output` folders are git-ignored). Building the session with `-c` regenerates it
from scratch.

`MicroRust/ROOTS` makes the manual's sub-session visible to `-d MicroRust`. To
work interactively, open a theory importing `MicroRust` with
`isabelle jedit -d MicroRust -l MicroRust`.

## Tests

`MicroRust_Tests.thy` has round-trip tests for every construct. Its corpus test
reads the uRust bodies of the AutoCorrode sources, if the environment variable
`AUTOCORRODE_HOME` names a checkout of `github.com/awslabs/AutoCorrode`:

```sh
AUTOCORRODE_HOME=/path/to/AutoCorrode isabelle build -d MicroRust MicroRust
```

It extracts every `\<lbrakk> ... \<rbrakk>` of the `.thy` files (962 in the
version used when this was written), reads it as a function body, and checks
that the text printed back from the AST parses again to the same text: 936 pass;
the other 26 are not uRust (Isabelle statement assumptions
`\<lbrakk>A; B\<rbrakk>`, mixfix templates such as `\<lbrakk>_\<rbrakk>`) and
are listed explicitly in the test.

`microrust_export` writes `.rs` files next to the exporting theory; those are
generated on every build and are git-ignored (`examples/` holds the real
sources).

## Status and limitations

Everything described above builds and passes its tests. Deliberate gaps: macro
definitions and general token-tree macros (a macro call must have expressions as
arguments), `async`, `union`, `extern`, higher-ranked bounds, `Fn(A) -> B`
sugar, let chains, lifetimes in `dyn`, `ref` patterns (`ref` is an ordinary
identifier, as in uRust), a name path longer than one segment is resolved only
at its first segment, and `a > > b` (with a blank) is accepted as a shift.

The yacc grammar has 15 shift/reduce and 48 reduce/reduce conflicts, all
resolved in the intended way and all of one of these kinds: a block-like
expression at the start of a statement (or as a match arm) ends it (rustc's
rule; 48 entries are the same two states, one per lookahead token); an `impl<`
is read as generics, not as a qualified type; `a as u32 < b` reads `<` as the
start of generic arguments (as rustc does); `pub (` starts a visibility; `..`
and `return`/`break` take an operand if one follows.

## License

BSD-style, see the SPDX headers of the theory files and `../LICENSE`.
