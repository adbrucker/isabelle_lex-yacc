# Examples of Java 25 read by `java_file`

| File | What it shows |
| --- | --- |
| `Hello.java` | a package, an import, a static field and methods, a `for` loop |
| `Stack.java` | generics, a nested class, an anonymous class, a bounded generic method |
| `Shapes.java` | sealed interfaces, records with a compact constructor, pattern switches with guards and record patterns, the unnamed pattern `_` |
| `Flow.java` | labels, flow scoping of pattern variables, try with resources, multi-catch, lambdas, enum constants with bodies, an old-style `switch` |
| `Compact.java` | a compact source file (JEP 512): top-level fields and methods, an instance `main` |
| `module-info.java` | a module declaration |

They are valid Java 25: `javac --release 25 -d out Hello.java Stack.java Shapes.java Flow.java`
compiles them, and `java Compact.java` runs the compact one.
