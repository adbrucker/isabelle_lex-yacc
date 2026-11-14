(******************************************************************************
 * Copyright (c) University of Paris-Saclay
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 ******************************************************************************)

(*<*)
theory ARM_Manual
  imports "ARM_CortexM7.ARM"
begin
(*>*)

section\<open>What is Isabelle/ARM\<close>

text\<open>
  Isabelle/ARM is a front-end that lets the assembly language of the ARM Cortex-M7 live inside an
  Isabelle theory as a first-class citizen: parsed by a real grammar, checked incrementally under
  Isabelle/PIDE (so a syntax error or a malformed annotation is reported like any other Isabelle
  error, with the usual jEdit markup, hyperlinking and hovering), and open to attaching
  arbitrary Isabelle-level content - proof obligations, HOL terms, arbitrary Isar commands - to
  specific points of the assembly text via a comment-based antiquotation mechanism. It is not an
  assembler, nor a verification tool in its own right: it is the \<^emph>\<open>front-end layer\<close> on which one
  builds a verification tool - a semantic backend, for instance a machine model of the processor
  in HOL and a translation of programs into it -, a documentation generator, or a static
  analysis.
\<close>

subsection\<open>Context\<close>

text\<open>
  \<^bold>\<open>The language.\<close> The Cortex-M7 is a processor of the ARMv7E-M architecture
  \<^cite>\<open>"arm:armv7m:2021" and "arm:cortexm7:2018"\<close>: it executes only the Thumb instruction set,
  that is Thumb-2 with its mix of 16 and 32 bit instructions, with the DSP extension (saturating
  and parallel arithmetic, multiplications with accumulation) and, optionally, the floating point
  unit FPv5 for single and double precision. The syntax is the one of the GNU assembler
  \<^cite>\<open>"gnu:as:2026"\<close> in its \<^emph>\<open>unified\<close> form (\<open>.syntax unified\<close>), which is also what LLVM's integrated
  assembler \<^cite>\<open>"llvm:2026"\<close> reads and what the compilers write: the mnemonics with the suffixes
  for the S flag, the condition, the width and the data types, the operands of ARM
  (shifted registers, indexed memory references, register lists), and, above all, the
  \<^emph>\<open>directives\<close> of \<open>as\<close> - sections, symbols, data, alignment, unwinding information, debug
  information - with its \<^emph>\<open>labels\<close>, its numeric local labels, its \<^emph>\<open>macros\<close>, its conditional
  assembly and its loops. An assembler has no grammar in the sense of a specification: the front-end
  follows the documentation of \<open>as\<close> and is tested on what compilers write.

  \<^bold>\<open>An abstract syntax of its own.\<close> The tree of Isabelle/ARM is not borrowed from another language:
  it is an ML datatype in the style of a machine model, as one writes it for a course on compilers
  or for a verified processor simulator. The registers, the instructions, the conditions and the
  shifts are closed enumerations of constructors, \<open>R0 | R1 | \<dots> | SP | LR | PC\<close>, \<open>MOV | ADD | LDR | \<dots>\<close>
  (268 opcodes of ARMv7E-M and FPv5), \<open>EQ | NE | \<dots>\<close>, so that a semantic backend matches on them; a
  statement is an instruction with its operands, a directive, a label, a macro. The mnemonic is
  \<^emph>\<open>decoded\<close> by the parser: \<open>addseq.w\<close> is the opcode \<open>ADD\<close> with the condition \<open>EQ\<close>, the S flag and the
  width \<open>Wide\<close>. The text of the mnemonic is kept as well, so that the tree prints back to the very
  text.

  Isabelle/ARM is the eighth language front-end built on the design of \<^bold>\<open>Isabelle/C, Version
  2.0\<close>, which this repository's \<^verbatim>\<open>C11/\<close> folder contains \<^cite>\<open>"tuong.ea:isabellec:2019" and
  "tuong.ea:deeply:2019"\<close>, after occam 2, Scala 3, MicroRust, AdaSpark, Go and Java. It is built from
  the same parts and carries the same concepts over one for one: the \<^verbatim>\<open>ml_lex_yacc\<close> command of this
  repository (an ML-Lex/ML-Yacc integration \<^cite>\<open>"appel.ea:lexical:1994" and
  "tarditi.ea:ml-yacc:2000"\<close>) generates lexer and parser; every node of the abstract syntax tree
  carries a source position plus the comments and antiquotations attached to it; a per-theory
  environment tracks the declared names for declaration/use hyperlinking; programmable handlers, a
  navigation language and an evaluation order give meaning to the antiquotations; and a family of
  Isar commands (\<open>arm\<close>, \<open>arm_stmt\<close>, \<open>arm_file\<close>, \<open>\<dots>\<close>) drive all of it. Someone who knows the C11
  manual will find the same structure in this one, and the same names with \<open>c11\<close> replaced by \<open>arm\<close>,
  \<open>cenv\<close> by \<open>armenv\<close>, and \<open>CEnv\<close> by \<open>ARMEnv\<close>. Like the other members it is \<^emph>\<open>re-entrant\<close>: it is
  built with \<open>ml_lex_yacc [state]\<close>, every parse has a state object of its own, and any number of
  parses may run at the same time.

  The folder is \<^verbatim>\<open>ARM_CortexM7\<close>, the session \<open>ARM_CortexM7\<close>, the theory and the commands are called
  \<open>ARM\<close> and \<open>arm\<close>. What differs from the other members is dictated by the language: the \<^emph>\<open>lines\<close> are
  the unit (\<open>\<section>2.1\<close>); the several name spaces of an assembler, among them the numeric labels and
  the parameters of macros (\<open>\<section>2.2\<close>); and the fact that the tree is a machine model that can be
  \<^emph>\<open>run\<close> (\<open>\<section>3.2\<close>).
\<close>

section\<open>Main Features of Isabelle/ARM\<close>

text\<open>
  Four pieces fit together to give the \<open>arm\<close>-family commands (\<open>\<section>3\<close>) their behaviour: a lexer
  and parser that produce a real AST with genuine source positions at every node (\<open>\<section>2.1\<close>); a
  per-theory environment tracking every declared name, used to hyperlink each name \<^emph>\<open>use\<close> back to
  its declaration (\<open>\<section>2.2\<close>); a mechanism for attaching programmable content to a specific AST node
  via a comment (\<open>\<section>2.3\<close>); and a well-defined order and navigation language governing exactly
  \<^emph>\<open>which\<close> node an antiquotation resolves to and \<^emph>\<open>when\<close> it runs (\<open>\<section>2.4\<close>).
\<close>

subsection\<open>Parsing\<close>

text\<open>
  The grammar (\<^verbatim>\<open>ARM_Parser.thy\<close>) is an ordinary LALR(1) ml-yacc grammar, and it is \<^emph>\<open>conflict
  free\<close>: ml-yacc reports neither a shift/reduce nor a reduce/reduce conflict. There is no stream
  between lexer and parser, as the one that Java needs: the ends of the lines are tokens of the
  grammar, and what looks ambiguous is decided by the position in the line. It covers

  \<^item> \<^bold>\<open>lines\<close>: a line holds any number of labels (\<open>name:\<close>, \<open>.L1:\<close>, and the numeric \<open>1:\<close>) and at most
    one statement; statements on a line are separated by \<open>;\<close>;
  \<^item> \<^bold>\<open>instructions\<close>: a mnemonic and its operands, separated by commas. The parser decodes the
    mnemonic (\<^verbatim>\<open>ARM_Isa.decode\<close>) into its \<^emph>\<open>opcode\<close>, its \<^emph>\<open>condition\<close> (\<open>addeq\<close>, \<open>bleq\<close>, \<open>movls\<close>), its
    \<^emph>\<open>S flag\<close> (\<open>adds\<close>, in either order with the condition), its \<^emph>\<open>width\<close> (\<open>.n\<close>, \<open>.w\<close>) and its \<^emph>\<open>data types\<close>
    (\<open>vcvt.s32.f32\<close>). Where a name could be read in two ways, the reading is the one of the assembler:
    \<open>strhs\<close> is \<open>str\<close> with the condition \<open>hs\<close>, \<open>bls\<close> is \<open>b\<close> with \<open>ls\<close>; the lower and the upper case are
    the same (\<open>ADD\<close>); \<open>it\<close>, \<open>ite\<close>, \<open>itte\<close> are the opcode \<open>IT\<close>. A word at the start of a statement
    that is not a mnemonic is a \<^emph>\<open>macro call\<close> (or an instruction this front-end does not know);
  \<^item> \<^bold>\<open>operands\<close>: registers (\<open>r0\<close>-\<open>r15\<close> and their names \<open>sp\<close>, \<open>lr\<close>, \<open>pc\<close>, \<open>ip\<close>, \<open>fp\<close>, \<open>sl\<close>, \<open>sb\<close>; \<open>s0\<close>-\<open>s31\<close>,
    \<open>d0\<close>-\<open>d15\<close>; the special registers \<open>apsr\<close>, \<open>primask\<close>, \<open>basepri\<close>, \<open>fpscr\<close>, \<open>\<dots>\<close>), with the
    write-back mark (\<open>r0!\<close>); immediates (\<open>#4\<close>, \<open>#:lower16:sym\<close>); shifts (\<open>lsl #2\<close>, \<open>asr r3\<close>, \<open>rrx\<close>);
    memory references (\<open>[r0]\<close>, \<open>[r0, #4]!\<close>, \<open>[r0, r1, lsl #2]\<close>, \<open>[r0, :64]\<close>, and the post-indexed
    \<open>[r0], #4\<close> as two operands); register lists with ranges (\<open>{r4-r7, lr}\<close>); scalars (\<open>d0[1]\<close>);
    literal pool entries (\<open>=sym\<close>, \<open>=0x20000000\<close>); keyword arguments of macro calls (\<open>name=value\<close>);
  \<^item> \<^bold>\<open>expressions\<close> with the operators of the assembler and its precedences, which are not those of
    C: \<open>*\<close> \<open>/\<close> \<open>%\<close> \<open><<\<close> \<open>>>\<close> bind tighter than \<open>|\<close> \<open>&\<close> \<open>^\<close>, which bind tighter than \<open>+\<close> \<open>-\<close>, then
    the comparisons, then \<open>&&\<close> and \<open>||\<close>; numbers (decimal, \<open>0x\<close>, \<open>0b\<close>, octal), floating point
    numbers (\<open>1.5\<close>, \<open>0f1.5\<close>), characters (\<open>'a\<close>), strings, the location counter \<open>.\<close>, the references
    \<open>1b\<close> and \<open>1f\<close> to numeric labels, relocation specifiers (\<open>sym(PLT)\<close>);
  \<^item> \<^bold>\<open>directives\<close>: \<open>.name\<close> and operands separated by commas, which are expressions, strings and
    \<open>%words\<close> (\<open>.section .text,"ax",%progbits\<close>, \<open>.type f, %function\<close>); \<open>.file\<close> and \<open>.loc\<close>, whose
    arguments are separated by blanks, take the rest of the line as it stands;
  \<^item> \<^bold>\<open>blocks\<close>: macros (\<open>.macro\<close> with its parameters, their defaults and qualifiers, \<open>.endm\<close>),
    conditional assembly (\<open>.if\<close>, \<open>.ifdef\<close>, \<open>.ifc\<close>, \<open>\<dots>\<close> with \<open>.elseif\<close> and \<open>.else\<close>, \<open>.endif\<close>) and the loops
    \<open>.rept\<close>, \<open>.irp\<close>, \<open>.irpc\<close> (\<open>.endr\<close>) are blocks of lines, nested as they are written. In the
    body of a macro \<^verbatim>\<open>\name\<close>, \<^verbatim>\<open>\@\<close> and \<^verbatim>\<open>\()\<close> may stand wherever a letter may, in a name, a
    register, a number: \<^verbatim>\<open>mov r\n, #\v\<close>.

  \<^bold>\<open>Comments.\<close> A comment is \<open>@\<close> to the end of the line, \<open>//\<close> to the end of the line, \<open>/* \<dots> */\<close> (they
  do not nest), or \<open>#\<close> at the start of a line, which is how the assembler treats the line markers
  of the C preprocessor. Positions and comments: every node carries the exact source range of its
  text, from its first to its last token; comments, and the antiquotations among them
  (\<open>\<section>2.3\<close>), are not part of the grammar: the lexer collects them and attaches them to the node of
  the next real token.

  A first example, in the style of the code a compiler writes: a function that sums an array,
  with a numeric label, and the directives around it.
\<close>

arm\<open>
    .syntax unified
    .cpu cortex-m7
    .thumb
    .text
    .global sum
    .type sum, %function
    .thumb_func
sum:                            @ int sum(const int *a, int n)
    movs r2, #0
    cbz r1, 2f
1:  ldr r3, [r0], #4
    adds r2, r2, r3
    subs r1, r1, #1
    bne 1b
2:  mov r0, r2
    bx lr
    .size sum, . - sum
\<close>

text\<open>
  The operands of the instructions are checked for their syntax, not for their fit: \<open>mov r0, r1\<close>
  and \<open>mov r0, [r1]\<close> are both accepted. The fragments below are accepted; the last two are not:
\<close>

arm_stmt\<open>
    add.w r1, r2, r3, lsl #2
    ldr r0, [r1, r2, lsl #2]!
    stmdb sp!, {r4-r11, lr}
    vfma.f32 s0, s1, s2
    movw r0, #:lower16:table
    ldr r0, =0x20000000
    it eq
    addeq r0, r0, #1
    tbb [pc, r0]
\<close>

arm_expr\<open>(end - start) / 4 + 1<< 2\<close>

arm_stmt_reject\<open>mov r0,\<close>

arm_stmt_reject\<open>ldr r0, [r1\<close>

subsection\<open>The ARM Environment, and Declaration/Use Navigation\<close>

text\<open>
  \<^verbatim>\<open>ARM_Env.thy\<close> defines \<open>armenv\<close>, the counterpart of C11's \<open>cenv\<close>: a record stored as ordinary
  \<^verbatim>\<open>Generic_Data\<close>, so that it persists across commands within a theory and merges correctly
  under Isabelle's parallel, incremental checking. It holds

  \<^enum> \<open>names\<close>, the declared names, with what each was declared as (a label, a symbol, a register
    alias, a macro, a macro parameter); an assembler has \<^emph>\<open>several name spaces\<close>, which are kept apart
    by a prefix in the key;
  \<^enum> \<open>macros\<close>, the parameters of the macros, for the keyword arguments of their calls;
  \<^enum> \<open>locals\<close>, the numeric labels of the unit being analysed;
  \<^enum> \<open>arm_antiq\<close>, the registry of antiquotation handlers (\<open>\<section>2.3\<close>); and
  \<^enum> a per-theory unit counter, used to name the sections processed by an \<open>arm\<close> command.

  \<^verbatim>\<open>ARM_AnaEval.thy\<close>'s \<open>analyse_and_eval\<close> is a single, purely functional, scoped walk over a parsed
  root that fills \<open>armenv\<close> as it goes. Every name \<^emph>\<open>use\<close> is hyperlinked to its declaration via
  \<^ML>\<open>Position.entity_markup\<close>, reported once at the declaration site and once at every use.
  \<^bold>\<open>A name that resolves nowhere is not marked\<close> - unlike C11 and occam 2, where it is underlined.
  In assembly a name very often comes from another file, a library or the linker script
  (\<open>memcpy\<close>, \<open>_estack\<close>), none of which this pass sees; underlining them would drown the useful
  markup. The \<^emph>\<open>scoping rules\<close> are those of the assembler, implemented as shadow-and-restore (the
  environment is a value; a scope simply does not hand its extension back):

  \<^item> \<^bold>\<open>Symbols.\<close> The labels (\<open>start:\<close>) and the symbols that \<open>=\<close>, \<open>.set\<close>, \<open>.equ\<close>, \<open>.equiv\<close>,
    \<open>.thumb_set\<close> and \<open>.comm\<close> define are visible in the whole unit, before as well as after their
    definition: a branch to a label further down, a literal \<open>=table\<close> that points to data after the
    code. A symbol that is defined more than once (\<open>.set\<close> may redefine) is linked to its first
    definition until the walk reaches the next one. The directives \<open>.global\<close>, \<open>.weak\<close>, \<open>.type\<close>,
    \<open>.size\<close> and the like have symbols as operands, which are uses.
  \<^item> \<^bold>\<open>Numeric labels.\<close> \<open>1:\<close> may be defined many times; \<open>1b\<close> refers to the nearest definition
    before, \<open>1f\<close> to the nearest after, by their position in the text (also in the body of a macro,
    where the label and its uses are on the same side of the \<open>.endm\<close>).
  \<^item> \<^bold>\<open>Register aliases\<close> (\<open>acc .req r4\<close>) are visible from their definition on, in the order of the
    text, and end at \<open>.unreq\<close>.
  \<^item> \<^bold>\<open>Macros\<close> are visible from their definition on and end at \<open>.purgem\<close>. A macro hides the
    instruction of its name: \<open>.macro nop\<close> makes every \<open>nop\<close> after it a call. A call is hyperlinked
    to the macro, and a keyword argument \<open>m a=1\<close> to the parameter \<open>a\<close>.
  \<^item> \<^bold>\<open>Macro parameters.\<close> In the body of a macro (and of \<open>.irp\<close> and \<open>.irpc\<close>, whose variable is a
    parameter of the body) a reference \<^verbatim>\<open>\name\<close> is hyperlinked to the parameter, wherever it stands
    in a word: \<^verbatim>\<open>mov r\n, #\v\<close>, \<^verbatim>\<open>\name\():\<close>. A name that contains such a reference is a
    template, and declares and resolves nothing else. The labels in the body of a macro are
    visible in the body, and nothing in the body survives it.
  \<^item> \<^bold>\<open>Conditionals and loops.\<close> Both branches of a conditional are analysed, and what they
    declare is declared: the assembler decides at assembly time, the front-end reads the text.
  \<^item> \<^bold>\<open>The top level persists.\<close> After \<open>arm\<close> has analysed a file (or \<open>arm_stmt\<close> some statements), the
    symbols, aliases and macros it defines at the top level stay in \<open>armenv\<close> for the following
    commands, as the files of a program do for each other. Nothing else does.

  Being persistent per-theory data - the same idiom a simp set uses - is what lets assembly
  fragments be freely \<^emph>\<open>interleaved\<close> with arbitrary Isar content and still resolve a name used in
  one fragment back to its declaration in an earlier one. The flip side is that \<open>armenv\<close> only ever
  grows across a theory; the commands \<open>set_armenv_default\<close> and \<open>reset_armenv\<close> (\<open>\<section>3\<close>) give a
  theory explicit control. A small example of the scoping rules (hover over the names in jEdit):
  a macro with a default and a keyword argument, a register alias, a numeric label used before and
  after, a conditional, a loop, and a symbol used before its definition.
\<close>

arm\<open>
    .syntax unified
    .thumb

LEN = 8
acc .req r4

    .macro load_base reg, sym=table
    ldr \reg, =\sym
    .endm

    .macro count_down n
    movs r0, #\n
1:  subs r0, r0, #1
    bne 1b
    .endm

    .text
scan:
    push {acc, lr}
    load_base r1
    load_base reg=r2, sym=table2
    movs acc, #LEN
    b 3f
2:  ldr r3, [r1], #4
    add acc, acc, r3
3:  subs acc, acc, #1
    bpl 2b
    .if LEN > 4
    count_down 4
    .else
    nop
    .endif
    .rept 2
    nop
    .endr
    pop {acc, pc}

    .section .rodata
table:
    .word 1, 2, 3
table2:
    .word end - table
end:
\<close>

subsection\<open>Programmable ARM-Antiquotations, and Handlers\<close>

text\<open>
  A comment of the shape \<open>@tag[navi](level) \<open>body\<close>\<close> - an \<open>@\<close>-prefixed tag, an optional bracketed
  navigation string (\<open>\<section>2.4\<close>), an optional parenthesised integer \<open>level\<close> (\<open>0\<close> when omitted), and a
  body written as a nested Isabelle cartouche or, equivalently, a double-quoted string - is
  recognised lexically inside a comment, and attached to whichever AST node it resolves against
  (\<open>\<section>2.4\<close>). The cartouche may span several lines, which a line comment cannot. Any other comment
  is kept as plain text (\<open>Raw_txt\<close>). A comment is attached to the AST node that begins at the \<^emph>\<open>next
  real token\<close>, so an annotation is written on the line(s) \<^emph>\<open>above\<close> what it annotates. Since \<open>@\<close> begins a
  comment in this assembler, the antiquotation of an \<open>@\<close>-comment begins with a second \<open>@\<close>; the other
  comments have it after the opener:

  \<^verbatim>\<open>@@ highlight\<close>     \<^verbatim>\<open>//@ highlight\<close>     \<^verbatim>\<open>/*@ highlight */\<close>

  (a tag alone is a complete antiquotation with an empty body). A tag with a double-quoted body, or
  without a body, is an antiquotation only directly after the comment opener, so that an \<open>@\<close> in
  running text - an e-mail address, a remark - is not mistaken for one; a tag followed by a
  cartouche is one anywhere in a comment.

  The \<open>tag\<close> selects a \<^emph>\<open>handler\<close>: an ordinary ML function of type

  \<^verbatim>\<open>type type_antiq_fun =
    armenv * pos ARM_Ast.root * int -> (string * pos) ->
    Context.generic -> Context.generic\<close>

  registered once, ahead of time, via \<open>ARMEnv.store_antiq (tag, handler)\<close>. When \<open>analyse_and_eval\<close>
  reaches a node carrying an \<open>@tag \<dots>\<close> antiquotation, it resolves the navigation string against the
  closest-surrounding-context stack (\<open>\<section>2.4\<close>) into a single concrete \<open>root\<close> value, then instantiates
  the handler with \<open>(armenv, resolved_root, level)\<close> and the body text together with its own source
  position; a handler is never itself responsible for interpreting \<open>u\<close>/\<open>U\<close>/\<open>r\<close>/\<open>d\<close>.

  \<open>Context.generic\<close> rather than \<open>theory\<close>, deliberately: a handler may do anything a genuine Isar
  toplevel command can, including running real ML code at the ML environment level (the \<open>ML\<close>
  antiquotation, below). All collected actions are folded into one \<open>Context.generic ->
  Context.generic\<close> function by ordinary composition and lifted to the toplevel exactly once, at the
  end (\<open>full_eval_and_store\<close> in \<^verbatim>\<open>ARM.thy\<close>). Most handlers never need this generality: an ordinary
  \<open>theory -> theory\<close> function is \<^emph>\<open>recaptured\<close> by \<open>ARMEnv.lift_theory_antiq\<close> when it is registered. A
  first handler, which turns a plain comment into a checked diagnostic reported against the exact
  node the comment resolves to:
\<close>

ML\<open>
val todo_antiq =
  let
    fun handler (_ : ARMEnv.armenv, ast, level) (body, _ : Position.T) thy =
      (warning ("TODO (level " ^ Int.toString level ^ ") at " ^
                Position.here (AnaEval.pos_of_root ast) ^ ": " ^ body);
       thy)
  in ARMEnv.store_antiq ("todo", ARMEnv.lift_theory_antiq handler) end
\<close>
setup\<open>todo_antiq\<close>

arm\<open>
clear:
    @@ todo \<open>check that the pointer is not null first\<close>
    movs r1, #0
    str r1, [r0]
    bx lr
\<close>

text\<open>
  A tag with no registered handler is a hard error: every tag that can appear in a theory's source
  must be registered before that theory's \<open>arm\<close>-family commands run.
\<close>

subsection\<open>Execution (Order, Navigation, etc.)\<close>

text\<open>
  \<^bold>\<open>Order.\<close> A unit can carry several antiquotations whose handlers have side effects that depend
  on one another (a \<open>definition\<close> must precede the \<open>lemma\<close> that mentions it). \<open>level\<close> is the author's
  explicit ordering knob: \<open>full_eval_and_store\<close> collects every \<open>(level, action)\<close> pair the walk
  produces, sorts by \<open>level\<close> - a stable sort, so equal levels keep their textual order - and chains
  them, each against the context the previous one produced. A physical antiquotation is dispatched
  \<^emph>\<open>exactly once\<close>, no matter how many AST nodes share its leftmost source position (a statement,
  its first operand, the register in it).

  \<^bold>\<open>Context.\<close> Every antiquotation resolves, by default, to its \<^emph>\<open>closest surrounding context\<close>: the
  walk threads a stack of enclosing nodes. Three kinds of node push themselves on that stack at
  every level of nesting: \<^emph>\<open>expressions\<close>, \<^emph>\<open>operands\<close> and \<^emph>\<open>statements\<close> - the root type has the
  variants \<open>Expr\<close>, \<open>Operand\<close>, \<open>Stmt\<close> in addition to \<open>Id\<close> for a bare name, \<open>Stmts\<close> for a list of lines and
  \<open>Source\<close> for a file. Everything else - the parameters of a macro, the branches of a conditional -
  never pushes and resolves to what is on top, which is what makes every node kind a valid place
  for a comment.

  \<^bold>\<open>Navigation.\<close> The bracketed \<open>[navi]\<close> string points an antiquotation \<^emph>\<open>away\<close> from its closest
  context. Its syntax and its rules are exactly those of C11: written \<open>(u|U)*(r|d)*\<close>, zero or more
  ascend steps followed by zero or more descend steps. \<open>u\<close> ascends one level (a lone, final \<open>u\<close> is a
  no-op); \<open>U\<close> ascends past a whole run of consecutive ancestors of the same category; \<open>r\<close> advances
  a 1-based cursor among the current node's children in source order and \<open>d\<close> descends into the
  child at the cursor (cursor 1 if no \<open>r\<close> preceded it). There is no wrapping: a cursor beyond the
  children, or \<open>d\<close> on a leaf, is a hard error reported at the antiquotation's own tag position. The
  children of a node, in source order, are its operands, expressions and statements; the
  parameters of a macro are flattened away, and the bodies of macros, conditionals and loops are
  children of their directive. A few examples (the node a handler receives, on the statement
  \<open>add r0, r1, r2\<close>):

  \<^item> no navigation: the statement itself;
  \<^item> \<open>[d]\<close> or \<open>[rd]\<close>: its first operand, \<open>r0\<close>; \<open>[rrd]\<close>: its second operand, \<open>r1\<close>;
  \<^item> \<open>[uu]\<close>: the enclosing node - the unit, or the macro around the statement.

\<close>

arm\<open>
sum3:
    @@ probe_ast[rrd]
    @@ highlight[rrd]
    add r0, r1, r2
    bx lr
\<close>

ML\<open>
val _ = if ARM_Pp.pp_root (!ARM_AST) = "r1"
  then writeln "[rrd] reaches the second operand"
        else error "navigation"
\<close>

subsection\<open>Standard Antiquotations\<close>

text\<open>
  \<^verbatim>\<open>ARM_AnaEval.thy\<close> registers the same eight demonstration antiquotations as C11. All of them are
  written in a comment and see the node their navigation string selects:

  \<^descr> \<open>probe_armenv\<close> stores the current \<open>armenv\<close> into an ML reference (\<open>ARMENV\<close>) for inspection.
  \<^descr> \<open>probe_ast\<close> prints the resolved node, pretty-printed back to assembly, with its level, and
    stores it into \<open>ARM_AST\<close>.
  \<^descr> \<open>highlight\<close> marks the resolved node's source range in the editor - the quickest way to \<^emph>\<open>see\<close>
    what a navigation string selects.
  \<^descr> \<open>term \<open>t\<close>\<close> reads \<open>t\<close> as a HOL term in the theory's current context; a malformed or ill-typed
    term is a real Isabelle error positioned inside the assembly comment.
  \<^descr> \<open>ML \<open>code\<close>\<close> runs \<open>code\<close> as ML source, so a definition written in an assembly comment becomes a
    later-visible ML binding.
  \<^descr> \<open>text \<open>t\<close>\<close> runs \<open>t\<close> through the document machinery of Isabelle's \<open>text\<close> command, so that inner
    antiquotations are checked and hyperlinked (the result is stashed, not typeset; see \<open>\<section>6\<close>).
  \<^descr> \<open>definition \<open>d\<close>\<close> is Isabelle's \<open>definition\<close> command: the new constant is a genuine, later-visible
    theory constant.
  \<^descr> \<open>lemma \<open>l\<close>\<close> states \<open>l\<close> and proves it with one terminal \<open>by\<close> proof - proof-carrying code: a
    formal property of the program's constants, \<^emph>\<open>actually proved\<close>, right where the assembly text
    that motivates it lives. A failed proof is an Isabelle error positioned in the comment.

\<close>

section\<open>The ARM Main Commands\<close>

text\<open>

  \<^descr> \<open>arm \<open>\<dots>\<close>\<close> parses its argument as an assembly file, runs \<open>analyse_and_eval\<close>, chains the collected
    antiquotation actions in level order, and stores the AST under a fresh key, reported as
    \<open>[stored as Theory#N]\<close>.
  \<^descr> \<open>arm_stmt \<open>\<dots>\<close>\<close> is the same for a list of lines, as they stand in a file - the way to add a
    routine or a macro to a program one piece at a time.
  \<^descr> \<open>arm_file \<open>path\<close>\<close> is the same as \<open>arm\<close>, reading the file from an external file (resolved relative
    to the theory's master directory via \<^ML>\<open>Resources.parse_file\<close>, so file positions and
    build-dependency tracking come for free).
  \<^descr> \<open>arm_expr \<open>\<dots>\<close>\<close> and \<open>arm_ident \<open>\<dots>\<close>\<close> parse a bare expression, respectively name. The analysis still
    runs, for its hyperlinks, but its antiquotation actions are discarded: a standalone fragment
    is a syntax check, not a program.
  \<^descr> \<open>arm_reject\<close>, \<open>arm_stmt_reject\<close>, \<open>arm_expr_reject\<close> and \<open>arm_ident_reject\<close> document a fragment as
    correctly \<^emph>\<open>not\<close> accepted by the corresponding entry point. They are silent (no error markup is
    left on the expected failure) and are the means of writing negative tests.
  \<^descr> \<open>set_armenv_default\<close> and \<open>reset_armenv\<close> control the ever-growing \<open>armenv\<close>. \<open>set_armenv_default\<close>
    nominates what \<open>armenv\<close> holds \<^emph>\<open>right now\<close> as the snapshot a later \<open>reset_armenv\<close> restores; with no
    earlier \<open>set_armenv_default\<close> in scope \<open>reset_armenv\<close> falls back to the empty \<open>armenv\<close>. \<^verbatim>\<open>ARM.thy\<close>
    itself nominates, as its last step, the environment holding exactly the standard antiquotation
    handlers.
  \<^descr> \<open>setup_backend \<open>f\<close>\<close> installs the \<^emph>\<open>semantic backend\<close>: \<open>f\<close> is an ML expression of type
    \<open>Position.T ARM_Ast.root -> theory -> theory\<close>, evaluated like the argument of Isabelle's own
    \<open>setup\<close> command. At the very end of every \<open>arm\<close>, \<open>arm_stmt\<close> and \<open>arm_file\<close> - after the
    antiquotation actions have run and the AST is stored - the installed function is applied to the
    parsed root and the theory the command has produced, and its result is the theory the command
    returns; the fragment commands never trigger it. The default is \<open>K I\<close>, which
    \<open>setup_backend \<open>K I\<close>\<close> restores. The function is kept in the theory's context (separately from
    \<open>armenv\<close>, so \<open>reset_armenv\<close> does not uninstall it) and is inherited by later theories. This is
    where a machine model and a translation of programs into HOL would plug in (\<open>\<section>3.2\<close>).
  \<^descr> \<open>arm_export \<open>path\<close> exports \<open>key\<^sub>1\<close> \<open>\<dots>\<close> \<open>key\<^sub>n\<close>\<close> renders previously stored sections - given by the
    store keys the accepting commands report - back to assembly text with \<^ML>\<open>ARM_Pp.pp_root\<close> and
    writes them to \<open>path.s\<close>. With \<open>[verbatim]\<close> after the command name the original source text is
    written instead of the pretty-printer's.

  The accepting commands are \<open>thy_decl\<close> commands, because they change theory data (\<open>arm_file\<close> is
  \<open>thy_load\<close>, so that Isabelle tracks the file dependency); the \<open>_reject\<close> commands, which store
  nothing, are \<open>diag\<close>. Isabelle evaluates a \<open>diag\<close> command asynchronously, in parallel with the
  commands that follow; that is harmless here, because every parse has its own state (\<open>\<section>2.1\<close>).
\<close>

subsection\<open>A Worked Example\<close>

text\<open>
  A program in the style of a verified library: a constant mirrored in HOL, a loop, and a property
  proved about the constant. The first annotation introduces a HOL constant for the number of
  iterations (a \<open>definition\<close>, evaluated at level 0), the second proves a fact about it (level 1, so
  after the definition), the third checks a HOL term mentioning it (level 2).
\<close>

arm\<open>
    .syntax unified
    .thumb
@@ definition \<open>iterations :: nat where "iterations = 10"\<close>
@@ lemma(1) \<open>iterations_double: "iterations * 2 = 20" by (simp add: iterations_def)\<close>
@@ term(2) \<open>iterations + 1\<close>
ITERATIONS = 10

count_up:
    movs r0, #0
    @@ highlight
1:  adds r0, r0, #1
    cmp r0, #ITERATIONS
    bne 1b
    bx lr
\<close>

thm iterations_def iterations_double

subsection\<open>A Machine Model: Running the Tree\<close>

text\<open>
  The tree is a datatype of the machine, as in a course on compilers: the registers, the opcodes
  and the conditions are constructors. A small interpreter shows what that gives. It runs a
  program of the Thumb instructions \<open>mov\<close>, \<open>add\<close>, \<open>sub\<close>, \<open>cmp\<close>, \<open>b\<close> and \<open>bx\<close> on the core registers and the
  flags N and Z - the labels, the conditions \<open>eq\<close> and \<open>ne\<close> and the numeric references \<open>1b\<close> and \<open>1f\<close>
  included - by matching on the \<^emph>\<open>decoded\<close> instruction; whatever else it meets is an error. The
  program counter is the index of the instruction in the list of the instructions of the program.
\<close>

ML\<open>
structure Sim = struct

open ARM_Ast

fun idx r = (case r of
    R0 => 0 | R1 => 1 | R2 => 2 | R3 => 3 | R4 => 4 | R5 => 5 | R6 => 6 | R7 => 7 | R8 => 8
  | R9 => 9 | R10 => 10 | R11 => 11 | R12 => 12 | SP => 13 | LR => 14 | PC => 15)

(* the program: its instructions, and where each label points (the index of the next
   instruction) *)
fun load (ss : Position.T stmt list) =
  let
    fun go (SLabel (LName (Ident (n, _, _)), _) :: rest) (k, ls, is) = go rest (k, (n, k) :: ls, is)
      | go (SLabel (LNum (n, _), _) :: rest) (k, ls, is) = go rest (k, (n, k) :: ls, is)
      | go (SInsn i :: rest) (k, ls, is) = go rest (k + 1, ls, i :: is)
      | go (SDir _ :: rest) acc = go rest acc
      | go (_ :: _) _ = error "Sim: a statement that is not an instruction, a label or a directive"
      | go [] (_, ls, is) = (rev ls, rev is)
  in go ss (0, [], []) end

fun run (ss : Position.T stmt list) : int Array.array =
  let
    val (labels, prog) = load ss
    val regs = Array.array (16, 0)
    val z = Unsynchronized.ref false
    val n = Unsynchronized.ref false
    fun num s = (case Int.fromString s of SOME v => v | NONE => error ("Sim: number " ^ s))
    fun value o1 = (case o1 of
        OReg (Core r, _, _, _) => Array.sub (regs, idx r)
      | OImm (ENum (s, _), _) => num s
      | OImm (EUnary (Neg, ENum (s, _), _), _) => ~ (num s)
      | _ => error "Sim: an operand")
    fun dest o1 = (case o1 of OReg (Core r, _, _, _) => idx r | _ => error "Sim: a destination")
    fun flags v = (z := (v = 0); n := (v < 0))
    fun holds c = (case c of
        NONE => true | SOME AL => true | SOME EQ => !z | SOME NE => not (!z)
      | SOME MI => !n | SOME PL => not (!n) | _ => error "Sim: a condition")
    (* the target of a branch, from the instruction at index pc *)
    fun target pc o1 = (case o1 of
        OExpr (ESym (Ident (l, _, _))) => the (AList.lookup (op =) labels l)
      | OExpr (ELocal (s, _)) =>
          let
            val num_s = String.substring (s, 0, size s - 1)
            val ls = filter (fn (m, _) => m = num_s) labels
          in
            if String.isSuffix "b" s then #2 (List.last (filter (fn (_, k) => k <= pc) ls))
            else #2 (the (find_first (fn (_, k) => k > pc) ls))
          end
      | _ => error "Sim: a branch target")
    fun arith f s ops =
      (case ops of
         [d, a, b] => let val v = f (value a, value b) in Array.update (regs, dest d, v);
                          if s then flags v else () end
       | [d, b] => let val v = f (value d, value b) in Array.update (regs, dest d, v);
                       if s then flags v else () end
       | _ => error "Sim: the operands of an arithmetic instruction")
    fun step pc fuel =
      if fuel = 0 then error "Sim: out of fuel"
      else if pc >= length prog then ()
      else
        (case List.nth (prog, pc) of
           Insn ({opc, cond, setflags, ...}, ops, _) =>
             if not (holds cond) then step (pc + 1) (fuel - 1)
             else
               (case (opc, ops) of
                  (MOV, [d, s]) =>
                    (Array.update (regs, dest d, value s);
                     if setflags then flags (value s) else (); step (pc + 1) (fuel - 1))
                | (ADD, _) => (arith (op +) setflags ops; step (pc + 1) (fuel - 1))
                | (SUB, _) => (arith (op -) setflags ops; step (pc + 1) (fuel - 1))
                | (CMP, [a, b]) => (flags (value a - value b); step (pc + 1) (fuel - 1))
                | (B, [t]) => step (target pc t) (fuel - 1)
                | (BX, _) => ()
                | (NOP, _) => step (pc + 1) (fuel - 1)
                | _ => error "Sim: an instruction"))
  in (step 0 100000; regs) end

fun run_text text =
  (case ARM_Parse.parse_quiet ARM_Parse.Entry_Stmts @{context} (Input.string text) of
     SOME (Stmts ss) => run ss
   | _ => error "Sim: statements expected")

end
\<close>

text\<open>
  The program of the worked example above, with its loop on a numeric label and its conditional
  branch, sums the numbers from 5 down to 1; the model computes it from the tree (the check
  stops the build if it were not 15):
\<close>

ML\<open>
val sum_regs = Sim.run_text
  (cat_lines
    ["    movs r1, #0", "    movs r2, #5",
     "1:  adds r1, r1, r2", "    subs r2, r2, #1", "    bne 1b", "    bx lr"])
val _ = if Array.sub (sum_regs, 1) = 15 then writeln ("r1 = 15: the sum of 5, 4, 3, 2, 1")
        else error "the model computed another result"
\<close>

text\<open>
  A \<open>setup_backend\<close> hook gives the model the programs of a theory as they are processed, so that
  an annotation can state and prove what a routine computes. Here a backend counts the
  instructions by opcode of every file it is applied to - \<open>case\<close> on the enumeration - and the file
  is one of the examples of this repository:
\<close>

ML\<open>
val opcode_counts = Unsynchronized.ref ([] : (string * int) list)
fun count_in_stmts (ss : Position.T ARM_Ast.stmt list) =
  fold (fn s => fn acc =>
          (case s of
             ARM_Ast.SInsn (ARM_Ast.Insn ({opc, ...}, _, _)) =>
               let val name = (case opc of
                                 ARM_Ast.LDR => "ldr" | ARM_Ast.STR => "str" | ARM_Ast.B => "b"
                               | ARM_Ast.BL => "bl" | ARM_Ast.BX => "bx" | _ => "other")
               in AList.map_default (op =) (name, 0) (fn n => n + 1) acc end
           | ARM_Ast.SMacro (_, _, body, _) => count_in_stmts body @ acc
           | _ => acc)) ss []
\<close>

setup_backend\<open>fn root => fn thy =>
  (case root of
     ARM_Ast.Source (ARM_Ast.File (ss, _)) => (opcode_counts := count_in_stmts ss; thy)
   | _ => thy)\<close>

subsection\<open>Source Files, Backends, Export\<close>

text\<open>
  \<open>arm_file\<close> reads an external file (here the startup code of a Cortex-M7, and a file of memory
  routines) and stores its AST; the names of its declarations are visible to the following
  commands. The backend above counts the instructions of the last file:
\<close>

arm_file \<open>../examples/startup.s\<close>

arm_file \<open>../examples/memcpy.s\<close>

setup_backend\<open>K I\<close>

ML\<open>
val _ = writeln ("loads, stores and branches in the last file: " ^
                 commas (map (fn (n, c) => n ^ " " ^ Int.toString c) (rev (!opcode_counts))))
\<close>

text\<open>
  Further examples: register aliases, macros with defaults and keyword arguments, conditional
  assembly and loops; single and double precision floating point (FPv5); and the context switch
  of a small operating system:
\<close>

arm_file \<open>../examples/macros.s\<close>

arm_file \<open>../examples/fpu.s\<close>

arm_file \<open>../examples/context.s\<close>

text\<open>
  An accepted unit can be written back as assembly, in the canonical layout of the pretty-printer
  (or, with \<open>[verbatim]\<close>, as it was written): labels and the directives that structure the text at
  the first column, everything else four blanks in, one statement per line. The key of the unit is
  the one the command reported when it was stored. This is the way a generated or normalised file is
  produced from a theory:
\<close>

arm\<open>
f: movs r0,#1 ; bx lr
\<close>

ML\<open>
val key_of_last =
  let val ARMEnv.mk {units, ...} = ARMEnv.get (Context.Theory @{theory})
  in ARMEnv.ast_store_key @{theory} (units - 1) end
val _ = writeln ("the last unit is stored as " ^ key_of_last)
val _ = writeln (case ARMEnv.get_ast key_of_last @{theory} of
                   SOME root => ARM_Pp.pp_root root | NONE => "?")
\<close>

section\<open>The Abstract Syntax\<close>

text\<open>
  The AST in \<^verbatim>\<open>arm_ast.ML\<close> is a datatype of the machine, in the style of a model for a course on
  compilers, close enough to the concrete syntax that \<^ML>\<open>ARM_Pp.pp_root\<close> can print any parsed
  program back as assembly, \<^emph>\<open>with exactly the tokens of the source\<close> - that is what the corpus test
  checks (\<open>\<section>5\<close>). Layout is \<^emph>\<open>not\<close> part of it: the printer regenerates a canonical layout.
  Parentheses \<^emph>\<open>are\<close> part of it (\<open>EParen\<close>), so the printer needs no precedence reasoning. All the
  datatypes of syntax are parametrised by the position type \<open>'a\<close> (instantiated with
  \<^verbatim>\<open>Position.T\<close>), and every constructor but the pure wrappers carries a \<open>'a nodeInfo\<close> as its last
  field.

  \<^bold>\<open>Annotations\<close>, shared with C11 and so with everything built on it: \<open>nodeInfo\<close> is a bare position or
  a position with the comments attached; a \<open>comment\<close> is raw text or an antiquotation (tag, navigation
  steps, level, cartouche with its position); \<open>ident\<close> is a name with its \<open>nodeInfo\<close>.

  \<^bold>\<open>The machine\<close> (no positions):

  \<^item> \<open>regcode\<close>: \<open>R0\<close> \<open>\<dots>\<close> \<open>R12\<close>, \<open>SP\<close>, \<open>LR\<close>, \<open>PC\<close>; \<open>reg\<close>: \<open>Core\<close> of a \<open>regcode\<close>, \<open>Single\<close> (\<open>s0\<close> \<open>\<dots>\<close> \<open>s31\<close>),
    \<open>Double\<close> (\<open>d0\<close> \<open>\<dots>\<close>), \<open>Special\<close> (\<open>apsr\<close>, \<open>primask\<close>, \<open>\<dots>\<close>, by name). \<open>ip\<close>, \<open>fp\<close>, \<open>sl\<close>, \<open>sb\<close> are \<open>R12\<close>,
    \<open>R11\<close>, \<open>R10\<close>, \<open>R9\<close>.
  \<^item> \<open>cond\<close>: \<open>EQ\<close> \<open>NE\<close> \<open>CS\<close> \<open>CC\<close> \<open>MI\<close> \<open>PL\<close> \<open>VS\<close> \<open>VC\<close> \<open>HI\<close> \<open>LS\<close> \<open>GE\<close> \<open>LT\<close> \<open>GT\<close> \<open>LE\<close> \<open>AL\<close> (\<open>hs\<close> is \<open>CS\<close>, \<open>lo\<close> is \<open>CC\<close>);
    \<open>width\<close>: \<open>Narrow\<close>, \<open>Wide\<close>; \<open>shiftop\<close>: \<open>Lsl\<close> \<open>Lsr\<close> \<open>Asr\<close> \<open>Ror\<close> \<open>Rrx\<close>.
  \<^item> \<open>opcode\<close>: the 268 instructions of ARMv7E-M and FPv5 by their base mnemonic: \<open>ADC\<close> \<open>ADD\<close> \<open>\<dots>\<close> \<open>LDR\<close>
    \<open>LDRB\<close> \<open>\<dots>\<close> \<open>PUSH\<close> \<open>POP\<close> \<open>\<dots>\<close> \<open>SMLAD\<close> \<open>\<dots>\<close> \<open>VADD\<close> \<open>VFMA\<close> \<open>VMOV\<close> \<open>\<dots>\<close>. The table is in
    \<^verbatim>\<open>arm_isa.ML\<close>, together with the decoding of the mnemonics and of the registers.

  \<^bold>\<open>The syntax\<close> (the constructors are those of \<^verbatim>\<open>arm_ast.ML\<close>):

  \<^item> \<open>expr\<close>: \<open>ENum\<close>, \<open>EFloat\<close>, \<open>EChar\<close>, \<open>EString\<close> (as written), \<open>ESym\<close> (a name), \<open>EReg\<close> (a register,
    as spelled), \<open>EDot\<close> (\<open>.\<close>), \<open>ELocal\<close> (\<open>1b\<close>, \<open>1f\<close>), \<open>EReloc\<close> (\<open>sym(PLT)\<close>), \<open>EPart\<close> (\<open>:lower16:sym\<close>), \<open>EUnary\<close>
    and \<open>EBinary\<close> (with the \<open>unop\<close>s and \<open>binop\<close>s), \<open>EParen\<close>.
  \<^item> \<open>operand\<close>: \<open>OExpr\<close> (a name, a number, a branch target), \<open>OReg\<close> (with the flag of write-back),
    \<open>OImm\<close> (\<open>#e\<close>), \<open>OShift\<close>, \<open>OLiteral\<close> (\<open>=e\<close>), \<open>OMem\<close> (the operands inside the brackets, the flag of
    write-back), \<open>OAlign\<close>, \<open>OList\<close> (a register list, the flag of \<open>^\<close>), \<open>ORange\<close>, \<open>OPercent\<close> (\<open>%function\<close>),
    \<open>OKeyword\<close> (\<open>name=value\<close>), \<open>ORaw\<close> (the rest of the line of \<open>.file\<close> and \<open>.loc\<close>), \<open>OScalar\<close>
    (\<open>d0[1]\<close>).
  \<^item> \<open>insn\<close>: \<open>Insn\<close> of the decoded mnemonic - its text, its \<open>opcode\<close>, its \<open>cond\<close> if any, the flag of
    \<open>S\<close>, the \<open>width\<close> if any, the data types - and the operands.
  \<^item> \<open>stmt\<close>: \<open>SLabel\<close> (a name or a number), \<open>SInsn\<close>, \<open>SDir\<close> (a directive and its operands),
    \<open>SAssign\<close> (\<open>sym = e\<close>), \<open>SReq\<close> (\<open>name .req r\<close>), \<open>SCall\<close> (a macro call, or an instruction that is
    not known), \<open>SMacro\<close> (with its \<open>mparam\<close>s: name, qualifier, default, whether a comma precedes),
    \<open>SCond\<close> (the \<open>branch\<close>es of \<open>.if\<close> and \<open>.elseif\<close>, and the \<open>.else\<close> body), \<open>SRep\<close> (\<open>.rept\<close>, \<open>.irp\<close>,
    \<open>.irpc\<close>), \<open>SExitm\<close>.
  \<^item> \<open>root\<close>: the result of a parse by entry point - \<open>Id\<close>, \<open>Expr\<close>, \<open>Operand\<close>, \<open>Stmts\<close> or \<open>Source\<close> (a
    \<open>file\<close>) - plus \<open>Stmt\<close>, never produced by a parse but used by the analysis as the closest context
    of an annotation on a statement.

  Where the text is ambiguous without name resolution, the tree follows the syntactic reading and
  leaves the decision to the analysis: a word in an expression is a register if it is the name of
  one, else a symbol - which may be a register alias, as the analysis finds; a word at the start of
  a statement that is not a mnemonic is a macro call, or an instruction of another instruction
  set; the end of a line and the \<open>;\<close> that separates statements are not in the tree.
\<close>

section\<open>The Test Corpus: What the Compilers Write\<close>

text\<open>
  A grammar is only as good as the programs it has been tested on. Assembly written by hand is
  rare and private; what exists in quantity is what compilers write, and the LLVM toolchain
  \<^cite>\<open>"llvm:2026"\<close> has the target of the Cortex-M7. The test theory \<^verbatim>\<open>ARM_Tests.thy\<close> therefore ends with a
  corpus test: if the environment variable \<^verbatim>\<open>ARM_SRC\<close> names a directory of assembly files, every
  \<^verbatim>\<open>.s\<close> and \<^verbatim>\<open>.S\<close> file below it is read, printed back, and read again; the two prints must be
  equal, and the tokens of the print are those of the source (but for the ends of the lines and
  the case of the words that end a block). The corpus used for this manual is the assembly that
  \<^verbatim>\<open>clang --target=thumbv7em-none-eabihf -mcpu=cortex-m7 -S\<close> writes for a collection of C and
  C++ programs - sorting, hashing, strings, a state machine, DSP kernels in single and double
  precision, an interrupt-driven ring buffer, classes with virtual functions, templates and
  exceptions - at \<open>-O0\<close>, \<open>-O1\<close>, \<open>-O2\<close>, \<open>-Os\<close>, \<open>-O3\<close>, with debug information (\<open>-g\<close>), position independent
  (\<open>-fPIC\<close>), with fast math, for the Cortex-M4 with soft float: 46 files, 34\,000 lines. All of them
  pass. The examples of this repository are written by hand and checked by the assembler:
  \<^verbatim>\<open>clang --target=thumbv7em-none-eabihf -mcpu=cortex-m7 -c\<close> accepts every one of them.

  The test found a number of facts about the syntax. The debug directives \<open>.file\<close> and \<open>.loc\<close> have
  arguments separated by blanks, and the directive \<open>.loc 1 5 3 prologue_end is_stmt 0\<close> is only read
  as the rest of its line; a numeric reference \<open>0b\<close> to the label \<open>0:\<close> is not the binary number \<open>0b\<close>
  but \<open>0b101\<close> is; \<open>#\<close> opens a comment at the start of a line and an immediate elsewhere; the comments
  the compilers write on nearly every line (\<open>@ %bb.3\<close>, \<open>@ =>This Loop Header: Depth=1\<close>) made the
  attachment of comments to tokens a hot spot, which a table indexed by the offset of the token
  solved; and the order of the S flag and the condition (\<open>addseq\<close>) differs between the unified and the
  divided syntax.

  Besides the corpus, the test theories contain round-trip tests for the instructions, the
  operands, the expressions, the directives, the macros and the comments (a program in the
  printer's canonical layout comes back unchanged, and every accepted program is a fixed point of
  parse-then-print), tests of the decoding of the mnemonics and registers, and, in
  \<^verbatim>\<open>ARM_Cmd_Tests.thy\<close>, tests of the commands: the number of entity markups for each scoping rule,
  navigation, the evaluation order, \<open>arm_file\<close> on the examples, export and the backend hook.
\<close>

section\<open>Limitations\<close>

text\<open>
  Isabelle/ARM covers the language of a Cortex-M7 program but is deliberately modest about what it
  does with it, and the navigation language is the narrowed one of Isabelle/C 2.0. Concretely:

  \<^item> \<^bold>\<open>No assembler.\<close> Nothing is encoded, and the operands are not checked against the
    instruction: which forms an instruction takes, the ranges of the immediates, which registers
    it may use, whether it is a 16 or a 32 bit instruction, whether an \<open>it\<close> block is complete. The
    enumeration of the opcodes is the one of ARMv7E-M and FPv5; the instructions of the ARM
    instruction set (A32), of NEON and of the vector extension are not in it.
  \<^item> \<^bold>\<open>Macros are read, not expanded.\<close> The body of a macro is a template and is analysed once, with
    its parameters; a call is linked to the macro and its arguments are analysed as operands.
    The arguments of a call are separated by commas (the assembler also takes blanks); angle
    brackets that quote an argument, \<open>.altmacro\<close> and the evaluation of conditions are not
    supported; the code that a false \<open>.if\<close> skips is read as well, and must be syntactically right.
  \<^item> \<^bold>\<open>Directives are generic.\<close> Every directive takes expressions, strings and \<open>%words\<close> separated by
    commas, but \<open>.file\<close> and \<open>.loc\<close>, which take the rest of the line; the binary operator \<open>!\<close> (or-not)
    of the assembler is not supported, \<open>!\<close> being the write-back marker. \<open>.include\<close> is not followed.
  \<^item> \<^bold>\<open>Names.\<close> A name that resolves nowhere is silently left unmarked. A register alias is a symbol
    until the analysis resolves it, and the analysis resolves it only from its \<open>.req\<close> on.
  \<^item> \<^bold>\<open>Contract-free.\<close> Assembly has no contract language, and the front-end adds none: what a
    comment means is up to its antiquotation, and what a program means is up to a semantic
    backend. The model of \<open>\<section>3.2\<close> is a demonstration, not a model of the processor.
  \<^item> \<^bold>\<open>Comment placement.\<close> A comment is attached to the node starting at the next real token. A
    comment at the end of a line is attached to the first token of the next line; an annotation
    meant for a statement belongs on its own line above it.
  \<^item> \<^bold>\<open>The \<open>text\<close> antiquotation never reaches the generated document.\<close> It runs the body through
    the real \<^ML>\<open>Document_Output.output_document\<close>, but the result only reaches a probe reference. This is
    a limitation of Isabelle itself, not of this front-end: the presentation of a command is only
    consulted for document-class commands, which a \<open>thy_decl\<close> command can never be.
  \<^item> \<^bold>\<open>Navigation is not total.\<close> An \<open>Id\<close> root is a leaf and is never navigable by \<open>r\<close>/\<open>d\<close>; there is
    no wrapping; and nodes without a \<open>root\<close> variant (the parameters of macros, the branches of a
    conditional) cannot be navigation targets.

\<close>

section\<open>Conclusion\<close>

text\<open>
  Isabelle/ARM shows that the design of Isabelle/C Version 2.0 carries over to the lowest level of
  a program: an assembly file is a list of lines, and the grammar of the unified syntax of the GNU
  assembler, with its macros and its conditional assembly, is an ordinary ml-yacc grammar over an
  ordinary ml-lex lexer, with no conflict and no stream between them. What is new is the tree: a
  datatype of the machine, whose registers, opcodes and conditions are enumerations, so that the
  semantics of the processor can be written as functions on it - the model of \<open>\<section>3.2\<close> is a few
  lines, a real one a few hundred. Everything on top of the parser - positions, environment,
  hyperlinks, antiquotations, navigation, commands - is the C11 design instantiated for a new
  AST. What is documented in \<open>\<section>6\<close> as missing is, in every case, a scoping decision rather than an
  accident: the natural next steps are a machine model of the Cortex-M7 in HOL (the registers, the
  flags, the memory, the Thumb-2 instructions with their encodings) with a translation of the
  tree into it - the antiquotations of \<open>\<section>2.3\<close> then state and discharge the specifications in the
  comments next to the code, as the \<open>lemma\<close> above - the expansion of macros, a check of the
  operands against the instructions, and a corpus of hand-written code of the vendors.

  \pagebreak
\<close>

section\<open>Annex: The Assembly Grammar as Railroad Diagrams\<close>

subsection\<open>Lexical Structure\<close>

text\<open>
  The lexer is a small ml-lex specification in \<^verbatim>\<open>ARM_Parser.thy\<close>. The words that structure the text
  are tokens of their own, in any case: \<open>.macro\<close>, \<open>.endm\<close>, \<open>.exitm\<close>, \<open>.if\<close> and its relatives,
  \<open>.elseif\<close>, \<open>.else\<close>, \<open>.endif\<close>, \<open>.rept\<close>, \<open>.irp\<close>, \<open>.irpc\<close>, \<open>.endr\<close>, \<open>.req\<close>; every other word is an
  identifier: a mnemonic, a register, a symbol, a directive. An identifier is a letter, \<open>_\<close>, \<open>$\<close> or
  \<open>.\<close> followed by letters, digits, \<open>_\<close>, \<open>$\<close> and \<open>.\<close>, where a reference to a macro parameter
  (\<^verbatim>\<open>\name\<close>, \<^verbatim>\<open>\@\<close>, \<^verbatim>\<open>\()\<close>) may stand wherever a letter or a digit may. Integers are decimal, octal
  (leading \<open>0\<close>), binary (\<open>0b\<close>) or hexadecimal (\<open>0x\<close>); a number followed by \<open>b\<close> or \<open>f\<close> is a reference to a
  numeric label; floating point numbers have a point, or the prefix \<open>0f\<close>, \<open>0e\<close>, \<open>0d\<close>; a character is
  \<open>'c\<close> (the closing quote is optional); a string is \<open>"\<dots>"\<close> with the escapes of C. The ends of the
  lines are tokens. The comment machinery lives in the lexer, as in the other front-ends: \<open>@\<close>, \<open>//\<close>
  and \<open>#\<close> at the start of a line enter a comment state that runs to the end of the line, \<open>/*\<close> one
  that runs to the next \<open>*/\<close>, and an antiquotation is recognised by a regular expression for its
  head, followed by a nesting-depth counter for a cartouche body. The syntax of the head:

  \<^rail>\<open>
    antiquotation : '@' tag navi? level? body?
    ;
    navi : '[' (step *) ']'
    ;
    step : 'u' | 'U' | 'r' | 'd'
    ;
    level : '(' integer ')'
    ;
    body : cartouche | '"' text '"'
  \<close>

  The bracket around the navigation steps is a delimiter on purpose: \<open>u\<close>, \<open>U\<close>, \<open>r\<close>, \<open>d\<close> are ordinary
  identifier characters, so a tag ending in one of them (\<open>@answer\<close>) would otherwise be ambiguous
  between a tag and a tag plus a step. A body in double quotes, and a tag without a body, are
  antiquotations only directly after the comment opener.
\<close>

subsection\<open>Grammar\<close>

text\<open>
  The grammar is reproduced here after the parser, slightly simplified: the ends of the lines
  (\<open>eol\<close>) are shown as such, the binary operators are abbreviated by their precedence table, from
  the loosest to the tightest binding: \<open>&&\<close> \<open>||\<close>; the comparisons \<open>==\<close>, \<open>!=\<close>, \<open><\<close>, \<open><=\<close>, \<open>>\<close>, \<open>>=\<close>; \<open>+\<close>,
  \<open>-\<close>; \<open>|\<close>, \<open>&\<close>, \<open>^\<close>; \<open>*\<close>, \<open>/\<close>, \<open>%\<close>, \<open><<\<close>, \<open>>>\<close>; all left-associative.

  \<^rail>\<open>
    file : (line *)
    ;
    line : (statement__line eol) | block
    ;
    statement__line : (item ((';' item) *))
    ;
    item : (label *) statement?
    ;
    label : (identifier | number) ':'
    ;
    statement : instruction | directive | assignment | alias | 'exitm'
    ;
    instruction : identifier (operand + ',')?
    ;
    directive : directive__name (operand + ',')? | raw__directive
    ;
    assignment : identifier '=' expression
    ;
    alias : identifier '.req' operand
  \<close>

  \<^rail>\<open>
    block : macro | conditional | loop
    ;
    macro : '.macro' identifier (macro__param (','? macro__param) *)? eol (line *) '.endm' eol
    ;
    macro__param : identifier (':' identifier)? ('=' expression)?
    ;
    conditional : conditional__directive (operand + ',') eol (line *)
                  (('.elseif' (operand + ',') eol (line *)) *)
                  ('.else' eol (line *))? '.endif' eol
    ;
    loop : ('.rept' | '.irp' | '.irpc') (operand + ',') eol (line *) '.endr' eol
  \<close>

  \<^rail>\<open>
    operand : register '!'? | '#' expression | '#' ':' identifier ':' expression
            | ':' identifier ':' expression | '=' expression | shift
            | '[' memory__operands ']' '!'? | '{' (register__item + ',') '}' '^'?
            | register '[' expression ']' | '%' identifier | identifier '=' expression
            | expression
    ;
    shift : ('lsl' | 'lsr' | 'asr' | 'ror') ('#' expression | register) | 'rrx'
    ;
    memory__operands : ((operand + ',') | operand ':' number)
    ;
    register__item : register | register '-' register
  \<close>

  \<^rail>\<open>
    expression : unary | expression binary__op expression
    ;
    unary : atom | ('-' | '+' | '!' | '~') unary | '(' expression ')'
    ;
    atom : number | float | character | string | identifier | '.' | local__reference
         | identifier '(' identifier ')'
  \<close>
\<close>

(*<*)
end
(*>*)
