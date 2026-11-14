# The Isabelle PL DocMod Toolkit

A family of front-ends that embed programming languages into Isabelle/PIDE as *document models*:
the source text lives inside theory files, is parsed by a real grammar, is bound and (to a
language-specific degree) typed, shows up in the editor with hyperlinks, hovers and markup, and can
carry antiquotations and be evaluated or exported. All members are built with the `ml_lex_yacc`
framework in [`../Isabelle_Lex-Yacc`](../Isabelle_Lex-Yacc) (the engine, which is not itself a
member of the family) and follow the design of Isabelle/C, Version 2.0 (`C11`).

| Folder          | Language                          | Session         | Manual session     |
|-----------------|-----------------------------------|-----------------|--------------------|
| `C11/`          | C11 (Isabelle/C, Version 2.0)     | `C11`           | (inside `C11`)     |
| `occam2/`       | occam 2                           | `Occam2`        | `Occam2_Manual`    |
| `scala3/`       | Scala 3                           | `Scala3`        | `Scala3_Manual`    |
| `MicroRust/`    | MicroRust                         | `MicroRust`     | `MicroRust_Manual` |
| `AdaSpark/`     | Ada / SPARK 2014                  | `AdaSpark`      | `AdaSpark_Manual`  |
| `Golang1.27/`   | Go 1.27                           | `Golang1_27`    | `Go_Manual`        |
| `Java25/`       | Java 25                           | `Java25`        | `Java_Manual`      |
| `ARM_CortexM7/` | ARM Cortex-M7 (Thumb-2, GNU `as`) | `ARM_CortexM7`  | `ARM_Manual`       |

Each folder has its own `README.md` with the details of that front-end.

## Building

Every front-end is an independent session: it reaches `LexYacc.thy` and `YaccLib.thy` of the
engine through `directories "../../Isabelle_Lex-Yacc"` and a relative import. A directory can be
claimed by one session only, so the sessions cannot share one build graph (and there is
deliberately no `ROOTS` file in this folder): build the members **one at a time**, each with its
own `-d`. From the root of the repository:

```sh
isabelle build -d The_Isabelle_PL_DocMod_Toolkit/Java25 Java25
isabelle build -d The_Isabelle_PL_DocMod_Toolkit/Java25 Java_Manual
```

Each member folder except `C11` has a `ROOTS` file that makes its manual sub-session visible to that `-d`. From
inside this folder the same builds read `isabelle build -d Java25 Java25`, as in the READMEs of the
individual front-ends. Isabelle2026 is the supported version.
