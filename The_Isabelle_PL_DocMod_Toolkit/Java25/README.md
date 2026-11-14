# Isabelle/Java

A front-end for **Java** (language version 25) inside Isabelle/HOL: the Java member of the family of
verification front-ends (`../C11`, `../occam2`, `../scala3`, `../MicroRust`, `../AdaSpark`,
`../Golang1.27`). Java source text lives inside an Isabelle theory, is parsed by a real grammar and
is checked incrementally under Isabelle/PIDE. It is not a compiler and has no semantics (no type
checker, no definite assignment, no inference of lambdas); it is the front-end
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
  *flow scoping* of pattern variables (`if (!(o instanceof String s)) return; ... s ...`), imports
  and type parameters; names that resolve nowhere are not marked. **Selections and calls are
  resolved with types**, when that is certain: `x.f`, `x.m(a)`,
  `this.f`, `Color.RED`, `self().next().x`, a field or method inherited from a declared class, an
  overloaded method selected by the types of its arguments (the most specific one), type arguments
  substituted (`Box<U> b; b.get().f()`), the type of a `var`, of a pattern variable, of a cast.
  **The classes of the platform are read from a JDK**: `String`, `List<String>`, `System.out`,
  `java.util.Map.Entry` are known (see *The platform* below), so `s.length()` and
  `m.get(k).intValue()` link to the declarations in the JDK sources.
  **Lambdas, method references and `switch` expressions are typed**: the parameters of a lambda
  get the types of the functional interface the context expects (`l.forEach(p -> p.v = 1)` links
  `v`), the result of a lambda or of a method reference binds the type parameters of the method
  that takes it (`l.stream().map(p -> p.name()).forEach(n -> n.length())`), a method reference is
  linked to its method, and a `switch` expression has the type its arms agree on.
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
| `manual/` | the manual (`Java_Manual.thy`, a sub-session `Java_Manual` with live examples; `ROOTS` makes it visible to `-d Java25`) |
| `examples/` | Java programs (`Hello`, `Stack`, `Shapes`, `Flow`, a compact source file, a module declaration), read by `java_file` in the tests |

## Building

The session is `Java25`, the theories and the commands are called `Java` and `java`. The session is
independent of the other sessions of this repository: build it on its own, never together with
them. Isabelle2026 is the supported version.

```sh
isabelle build -d Java25 Java25      # all theories and tests
```

The manual, with live examples run against the real commands, is a sub-session:

```sh
isabelle build -d Java25 Java_Manual     # writes Java25/manual/output/document.pdf
```

To work interactively, open a theory importing `Java` with `isabelle jedit -d Java25 -l Java25`.

## The platform

The classes that a program does not declare - those it imports, those of `java.lang`, those it
names by their package (`java.util.List<String>`) - are read from the sources of a JDK. The theory
option `java_src` names where: a `src.zip` or a directory with the same layout (the packages below
a directory per module, or directly below it); `none` switches the platform off. By default it is
the `lib/src.zip` of the JDK of Isabelle (`$ISABELLE_JDK_HOME`), else of `$JAVA_HOME`:

```isabelle
declare [[java_src = "/usr/lib/jvm/java-25-openjdk/lib/src.zip"]]
```

A class is parsed the first time it is needed (a file out of the archive is extracted to
`$ISABELLE_TMP_PREFIX`, which is what a hyperlink opens) and its definitions are kept for the
session, shared by all theories, so the cost is paid once: `java.lang.String` or `java.util.List`
take a second or less. Of a class of the platform the members that a program can see (public,
protected, those of an interface) are known; `Object`'s public methods belong to every class, the
`Enum` and `Record` of an enum and a record are the real ones, member classes
(`Map.Entry`) are found, and a static import brings in the static methods of its class. Without a
JDK, or with `none`, nothing is known of the platform and nothing is linked on that basis, as
before.

## Tests

`Java_Tests.thy` has round-trip tests for every construct, tests of the tokens the layout stream
delivers (type arguments against comparisons, casts, lambdas, record patterns, contextual
keywords) and of the shape of the tree. Its corpus test reads a directory of Java sources if the
environment variable `JAVA_SRC` names one, for instance the source archive of Isabelle's JDK:

```sh
unzip $ISABELLE_JDK_HOME/lib/src.zip -d /tmp/jdksrc
JAVA_SRC=/tmp/jdksrc isabelle build -d Java25 Java25
```

`Java_Cmd_Tests.thy` counts the entity markups for each scoping rule (without the platform, so
that the counts do not depend on a JDK; the platform has its own tests, on a small tree written to
a temporary directory and on the JDK of Isabelle) and exercises navigation, levels, `java_file` on `examples/`, export and the backend hook. `java_export` writes `.java`
files next to the exporting theory; those are generated on every build and are git-ignored
(`examples/` holds the real sources, which `javac --release 25` compiles).

## Status and limitations

Everything described above builds and passes its tests; the analysis of the whole JDK (15 371
files, about 3 million entity markups, no crash) takes about 2 minutes on 8 threads with the
platform (45 seconds without it, 2.5 million markups; the count depends on which file happens to
be the first to load a class): the classes the files use are read once and everything they say
about types is looked up, a file that calls a method a thousand times in a row (`XKeysym`) takes
seconds. Deliberate choices and gaps: nothing is linked
that is inherited through a supertype that cannot be found (a library other than the JDK);
the declarations of the program that are in other files than the unit being analysed are not seen
(only the platform is read from a tree); a lambda or a method reference has a type
only where the context gives one (a parameter, a declared variable, a field, a `return`, a cast),
and a lambda whose body is more than an expression or one `return` binds no type parameter; a
`switch` expression is typed by its arms when none of them declares locals; a comment `//@Name` at its start is an antiquotation tag, as in the
other front-ends, so JML-like comments need a handler or a space (`// @Name`); the stream decides by tokens alone, so in the arguments of a call `f(a < b, c > d)`
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

BSD-style, see the SPDX headers of the theory files and `../../LICENSE`.
