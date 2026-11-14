# Isabelle/ARM

A front-end for the **assembly language of the ARM Cortex-M7** (ARMv7E-M: Thumb-2 with the DSP
extension and the single and double precision floating point unit FPv5) in the syntax of the **GNU
assembler**, inside Isabelle/HOL: the assembler member of the family of front-ends (`../C11`,
`../occam2`, `../scala3`, `../MicroRust`, `../AdaSpark`, `../Golang1.27`, `../Java25`). Assembly
text lives inside an Isabelle theory, is parsed by a real grammar and is checked incrementally
under Isabelle/PIDE. It is not an assembler (it does not encode instructions and does not check
that the operands fit the instruction) and has no semantics; it is the front-end layer on which a
semantic backend can be built (see `setup_backend` below) - a machine model of the Cortex-M7 in
HOL, an interpreter in the style of a processor simulator, a translation of assembly to HOL.

## What is accepted

The unified assembler syntax of `as`, as the compilers and the startup files of the vendors write it:

* **Lines.** A file is a list of lines; a line holds, separated by `;`, any number of labels
  (`name:`, `.L1:`, the numeric `1:`) and at most one statement: an *instruction*
  (`add.w r1, r2, r3, lsl #2`, `ldr r0, [r1, #4]!`, `push {r4-r7, lr}`, `vfma.f32 s0, s1, s2`,
  `ldr r0, =label`, `movw r0, #:lower16:sym`, `tbb [pc, r0]`), a *directive* (`.word 1, 2`,
  `.section .text,"ax",%progbits`, `.type f, %function`, `.size f, . - f`, `.loc 1 5 3 prologue_end`),
  a symbol assignment (`sym = expr`), a register alias (`acc .req r4`), or a *macro call*.
* **Mnemonics** are decoded by the parser into an opcode of a closed enumeration
  (`ARM_Ast.opcode`: the 268 instructions of ARMv7E-M and FPv5), a condition, the S flag, the width
  (`.n`, `.w`) and the data types (`.f32`, `.s32`): `adds`, `addeq`, `addseq`, `ldrsb.w`, `bleq`,
  `vcvtr.s32.f32`, `ite`. The tree is an ML datatype of its own, in the style of a machine model
  (registers, opcodes, conditions and shifts are enumerations to match on); the text of the
  mnemonic is kept, so the tree prints back to the very text.
* **Operands**: registers (`r0`-`r15`, `sp`, `lr`, `pc`, `ip`, `fp`, `sl`, `sb`, `s0`-`s31`,
  `d0`-`d15`, `apsr`, `primask`, `basepri`, `fpscr`, ..., also with write-back `r0!`), immediates,
  shifts (`lsl #2`, `asr r3`, `rrx`), memory references (`[r0]`, `[r0, #4]!`, `[r0, r1, lsl #2]`,
  `[r0, :64]`), register lists with ranges, scalars (`d0[1]`), literal pool entries, and the
  expressions of the assembler with its precedences (numbers, `'c`, strings, `.`, `1b`/`1f`,
  `sym(PLT)`, `:lower16:`/`:upper16:`).
* **Structure.** Macros (`.macro name a, b=1, c:req` ... `.endm`, with `\arg`, `\@` and `\()`),
  conditional assembly (`.if` and its relatives, `.elseif`, `.else`, `.endif`) and the loops `.rept`,
  `.irp`, `.irpc` (`.endr`) are blocks of lines, nested as written. Comments are `@`, `//`, `/* */`
  and `#` at the start of a line.

The grammar is conflict free. Each parse has its own state, so parses are re-entrant.

## What is there

The concepts are those of the C11 project, carried over one for one:

* **Binding**: every declaration and every resolved name use is reported with Isabelle's entity
  markup (hover, click-through): the labels and symbols (`=`, `.set`, `.equ`, `.comm`; visible
  before their definition), the numeric labels (`1b` is the nearest definition before, `1f` the
  nearest after), the register aliases (`.req`, until `.unreq`), the macros (from their definition
  until `.purgem`; a macro hides the instruction of its name; keyword arguments are linked to the
  parameters) and the macro parameters, wherever `\name` stands in a word (`mov r\n, #\v`,
  `\name\():`). Names that resolve nowhere (the symbols of other files, of the linker script) are not
  marked.
* **Antiquotations** in comments, `@@ tag[navi](level) \<open>body\<close>` (also `//@ ...` and
  `/*@ ... */`; the first `@` is the comment), with the same navigation (`u`, `U`, `r`, `d`), the
  evaluation levels and the eight standard antiquotations as in the other front-ends
  (`probe_armenv`, `probe_ast`, `highlight`, `term`, `ML`, `text`, `definition`, `lemma`).
* **Commands**: `arm` (a file), `arm_stmt` (lines), `arm_expr`, `arm_ident`, `arm_file` (an
  external `.s` file), the silent negative-test variants `*_reject`, `arm_export`,
  `set_armenv_default` / `reset_armenv`, and `setup_backend` (the semantic-backend hook: an ML
  function `root -> theory -> theory`, `K I` by default, run at the end of `arm`, `arm_stmt` and
  `arm_file`).

```isabelle
theory Demo imports ARM begin

arm\<open>
    .syntax unified
    .thumb
@@ term \<open>(8::nat) * 4\<close>
sum:
    movs r1, #0
1:  adds r1, r1, r0
    subs r0, r0, #1
    bne 1b
    mov r0, r1
    bx lr
\<close>

end
```

## Contents

| Path | What |
| --- | --- |
| `ARM.thy` | core theory: keywords and the Isar commands |
| `ARM_Parser.thy` | lexer and yacc grammar (`ml_lex_yacc`), the parse driver |
| `ARM_Ast.thy`, `arm_ast.ML`, `arm_isa.ML`, `arm_pp.ML` | the abstract syntax tree (registers, opcodes, conditions, operands, statements), the decoding of mnemonics and registers, the pretty-printer |
| `ARM_Env.thy` | environment (`ARMEnv`), AST store, antiquotation registry |
| `ARM_AnaEval.thy` | scoped analysis: hyperlinking, navigation, antiquotation dispatch, standard antiquotations |
| `ARM_Tests.thy` | parser-level tests (round trip, decoding, expressions, macros, comments) and the corpus test |
| `ARM_Cmd_Tests.thy` | command-level tests: binding, navigation, levels, `arm_file`, export, backend |
| `examples/` | Cortex-M7 programs (startup code, `memcpy`, macros, floating point, a context switch), read by `arm_file` in the tests |
| `manual/` | the manual (`ARM_Manual.thy`, a sub-session with live examples) |

## Building

The session is `ARM_CortexM7`, the theories and the commands are called `ARM` and `arm`. The session
is independent of the other sessions of this repository: build it on its own, never together with
them. Isabelle2026 is the supported version.

```sh
isabelle build -d ARM_CortexM7 ARM_CortexM7      # all theories and tests
isabelle build -d ARM_CortexM7 ARM_Manual        # the manual: ARM_CortexM7/manual/output/document.pdf
```

To work interactively, open a theory importing `ARM` with `isabelle jedit -d ARM_CortexM7 -l ARM_CortexM7`.

## Tests

`ARM_Tests.thy` has round-trip tests for the instructions, the operands, the expressions, the
directives, the macros and the comments, tests of the decoding of the mnemonics and of the shape of
the tree. Its corpus test reads a directory of assembly files if the environment variable `ARM_SRC`
names one. A corpus of real Cortex-M7 assembly is what a compiler writes: with LLVM, which has the
target,

```sh
clang --target=thumbv7em-none-eabihf -mcpu=cortex-m7 -O2 -S -o out.s file.c
ARM_SRC=/path/to/the/s/files isabelle build -d ARM_CortexM7 ARM_CortexM7
```

(also with `-g`, `-fPIC`, `-ffunction-sections`, `-mcpu=cortex-m4`, soft float, C++ with exceptions: the
test used 46 files, 34\,000 lines.) Every file is read, printed back with the very tokens of the
source, and read again to the same text. The examples are checked by the assembler:
`clang --target=thumbv7em-none-eabihf -mcpu=cortex-m7 -c examples/*.s`.

`ARM_Cmd_Tests.thy` counts the entity markups for each scoping rule and exercises navigation,
levels, `arm_file` on `examples/`, export and the backend hook. `arm_export` writes `.s` files next
to the exporting theory; those are generated on every build and are git-ignored (`examples/` holds
the real sources).

## Status and limitations

Everything described above builds and passes its tests. Deliberate choices and gaps: the operands are
not checked against the instruction (which forms an instruction takes, ranges of immediates, the
registers it may use) and nothing is encoded; the arguments of a macro call are separated by commas
(not by blanks); `.file` and `.loc` take the rest of the line as written, the other directives
commas (their operands are expressions, strings and `%words`); the binary operator `!` of `as`
(or-not) is not supported, `!` being the write-back marker; angle-bracket quoting of macro arguments
and `.altmacro` are not supported; an operand that is a register alias is a symbol until the analysis
resolves it, and the analysis does not follow `.include`; the instructions of the ARM (A32)
instruction set, of NEON and of the M-profile vector extension are not in the enumeration of
opcodes (a word that is not a known mnemonic is a macro call). The code skipped by a false
condition of `.if` is read as well, and must be syntactically right.

## License

BSD 2-Clause, as the rest of this repository. See the headers of the files.
