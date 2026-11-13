# Isabelle/Java

A front-end for **Java** (language version 25) inside Isabelle/HOL: the Java member of the family of
verification front-ends (`../C11`, `../occam2`, `../scala3`, `../MicroRust`, `../AdaSpark`,
`../Golang1.27`). Java source text lives inside an Isabelle theory, is parsed by a real grammar and
is checked incrementally under Isabelle/PIDE. It is not a compiler and has no semantics (no type
checker, no overload resolution beyond the arity, no definite assignment); it is the front-end
layer on which a semantic backend can be built (see `setup_backend` below).

## Why Java, and where the grammar comes from

Java has an official grammar: *The Java Language Specification, Java SE 25 Edition*
(<https://docs.oracle.com/javase/specs/jls/se25/html/>) repeats the syntax in its chapter 19, and
this front-end follows it for the whole language as the specification has it, that is with
everything that became final up to Java 25 (records, sealed classes, text blocks, pattern matching
for `instanceof` and `switch` with record patterns and guards, the unnamed variable `_`, module
import declarations, compact source files with instance `main` methods, constructors with
statements before `this(...)`/`super(...)`), and without the preview features.

Java cannot be read by an LALR(1) parser over the tokens of its lexer, as everybody who has
written a Java parser knows: a `<` begins type arguments or is a comparison, a `(` begins a lambda,
a cast, a record pattern or a parenthesis, `>>` can close two lists of type arguments, and `var`,
`yield`, `record`, `sealed`, `permits`, `when`, `module`, `open`, `requires`, `exports`, `opens`,
`uses`, `provides`, `to`, `with` and `transitive` are keywords or names by their surroundings. As
javac does, a small stream between the lexer and the parser (`Java_Parse.java_stream`, explained in
`Java_Parser.thy`) looks ahead in the token list, scans a type without building any tree, and hands
the parser tokens that say which it is. The grammar itself is then an ordinary context-free one,
and it is **conflict free**.

The test corpus is the platform itself: Isabelle2026 comes with a JDK 25 whose `lib/src.zip`
holds the 15 371 `.java` files of OpenJDK 25 (the class library, the compiler `javac`, the tools,
69 module declarations). **All of them** are read by this front-end, printed back to text with
exactly the tokens of the source, and read again to the same text.

## What is there

The concepts are those of the C11 project, carried over one for one:

* **Parsing** with `ml_lex_yacc [state]` into a real abstract syntax tree (`java_ast.ML`) with a
  source position at every node; every parse has its own state object, so parses are re-entrant.
* **Binding**: every declaration and every resolved name use is reported with Isabelle's entity
  markup (hover, click-through), with Java's several name spaces (variables, types, methods,
  packages, labels), the scope of the members of a class throughout its body, block scoping, the
  *flow scoping* of pattern variables (`if (!(o instanceof String s)) return; ... s ...`), imports,
  type parameters and overloading by arity; names that resolve nowhere (an inherited member, an
  on-demand import, the platform) are not marked.
* **Antiquotations** in `//` and `/* */` comments, `//@ tag[navi](level) \<open>body\<close>`, with the
  same navigation (`u`, `U`, `r`, `d`), evaluation levels and the eight standard antiquotations as
  in the other front-ends (`probe_jenv`, `probe_ast`, `highlight`, `term`, `ML`, `text`,
  `definition`, `lemma`). The `@param` and `@return` of Javadoc are not antiquotations.
* **Commands**: `java` (a compilation unit: ordinary, modular or compact), `java_decl` (member
  declarations without a class around them), `java_stmt` (block statements), `java_expr`,
  `java_type`, `java_ident`, `java_file` (an external `.java` file), the silent negative-test
  variants `*_reject`, `java_export`, `set_jenv_default` / `reset_jenv`, and `setup_backend` (the
  semantic-backend hook: an ML function `root -> theory -> theory`, `K I` by default, run at the end
  of `java`, `java_decl`, `java_stmt` and `java_file`).

```isabelle
theory Demo imports Java begin

java\<open>
package demo;

public class Counter {
    private int n;

    public int next() {
        //@ highlight
        return ++n;
    }
}
\<close>

end
```

## Contents

| Path | What |
| --- | --- |
| `Java.thy` | core theory: keywords and the Isar commands |
| `Java_Parser.thy` | lexer, layout stream, yacc grammar (`ml_lex_yacc`) |
| `Java_Ast.thy`, `java_ast.ML`, `java_pp.ML` | the abstract syntax tree and its pretty-printer |
| `Java_Env.thy` | environment (`JEnv`), AST store, antiquotation registry |
| `Java_AnaEval.thy` | scoped analysis: hyperlinking, navigation, antiquotation dispatch, standard antiquotations |
| `Java_Tests.thy` | parser-level tests (round trip, idempotence, the decisions of the stream, rejection) and the JDK corpus |
| `Java_Cmd_Tests.thy` | command-level tests: binding, navigation, levels, `java_file`, export, backend |
| `examples/` | Java programs (`Hello`, `Stack`, `Shapes`, `Flow`, a compact source file, a module declaration), read by `java_file` in the tests |

## Building

The session is `Java25`, the theories and the commands are called `Java` and `java`. The session is
independent of the other sessions of this repository: build it on its own, never together with
them. Isabelle2026 is the supported version.

```sh
isabelle build -d Java25 Java25      # all theories and tests
```

To work interactively, open a theory importing `Java` with `isabelle jedit -d Java25 -l Java25`.

## Tests

`Java_Tests.thy` has round-trip tests for every construct, tests of the tokens the layout stream
delivers (type arguments against comparisons, casts, lambdas, record patterns, contextual
keywords) and of the shape of the tree. Its corpus test reads a directory of Java sources if the
environment variable `JAVA_SRC` names one, for instance the source archive of Isabelle's JDK:

```sh
unzip $ISABELLE_JDK_HOME/lib/src.zip -d /tmp/jdksrc
JAVA_SRC=/tmp/jdksrc isabelle build -d Java25 Java25
```

`Java_Cmd_Tests.thy` counts the entity markups for each scoping rule and exercises navigation,
levels, `java_file` on `examples/`, export and the backend hook. `java_export` writes `.java`
files next to the exporting theory; those are generated on every build and are git-ignored
(`examples/` holds the real sources, which `javac --release 25` compiles).

## Status and limitations

Everything described above builds and passes its tests. Deliberate choices and gaps: the front-end
does not know types, so `x.f` and `x.m()` are not resolved (only a call without receiver is linked,
and only if the arity leaves one candidate), and a simple name that is inherited from a super class
is not found; the stream decides by tokens alone, so in the arguments of a call `f(a < b, c > d)`
is two comparisons (as javac reads it), and a member declaration `Foo(Map<A, B> m)` in the body of
an enum constant is read as a call if it is the first in a block; Unicode escapes (`A`) are
translated by the specification before lexing, here they are recognised inside literals and
comments, where they occur in practice; identifiers are ASCII letters, digits, `_` and `$` plus
every non-ASCII byte; the preview features of Java 25 (primitive types in patterns) are not
Java 25 and are rejected.

The yacc grammar has no shift/reduce and no reduce/reduce conflict (the one place where shifting
is the reading Java intends - a lambda body that extends as far as it can - is declared with a
precedence).

## License

BSD-style, see the SPDX headers of the theory files and `../LICENSE`.
