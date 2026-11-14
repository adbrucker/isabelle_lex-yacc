(******************************************************************************
 * Copyright (c) University of Paris-Saclay
 *
 * All rights reserved.
 *
 * Authors: Burkhart Wolff, Claude Sonnet 5.5
 *
 * This is an LLM-generated replication of the Isabelle/C version 2 design to
 * the programming language Java (language version 25). It provides an efficient
 * parser for Java, deeply integrated into the Isabelle/PIDE document model,
 * allowing external files as well as in-theory code-snippets which are
 * transparent to the underlying theory. It provides an API for the generated
 * AST’s, and an API to hook up semantic backends that compile these AST’s to
 * theory extensions in Isabelle/HOL. Members of the family come with a
 * Java-specific antiquotation mechanism allowing programmable links to the
 * semantic backends as necessary for support of program-annotations with HOL
 * formulas.
 *
 * This session is part of the Isabelle Programming Language Toolkit
 * (Isabelle/PLTk). The generation has been done with Claude Sonnet 5.5; while
 * the replicants come with a detailed (generated) test-suite for Java, I
 * expect that human users might find errors or inconsistencies; experience
 * reports and comments are therefore welcomed. The concrete and abstract
 * syntax, being generated from Isabelle/LexYacc specifications, should be easy
 * to modify and adapt.
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


theory ARM_Cmd_Tests
  imports ARM ARM_Tests
begin

section\<open>Command-level Tests\<close>

text\<open>
  The Isar commands of \<^verbatim>\<open>ARM.thy\<close> and the binding pass of \<^verbatim>\<open>ARM_AnaEval.thy\<close>, exercised on the
  assembly of a Cortex-M7: the number of entity markups (a declaration is one, a resolved use is
  one, a name that resolves nowhere is none) for each scoping rule, navigation, the evaluation
  order of antiquotations, \<open>arm_file\<close> on the examples, export, the backend hook and the reset of the
  environment.
\<close>

subsection\<open>Accepting and rejecting commands\<close>

arm\<open>
    .syntax unified
    .thumb
main:
    movs r0, #0
    bx lr
\<close>

arm_stmt\<open>
loop:
    subs r0, r0, #1
    bne loop
\<close>

arm_expr\<open>1 + 2 * 3\<close>

arm_expr\<open>end - start\<close>

arm_ident\<open>Reset_Handler\<close>

arm_reject\<open>ldr r0, [r1\<close>

arm_stmt_reject\<open>mov r0,\<close>

arm_expr_reject\<open>1 +\<close>

arm_ident_reject\<open>1 2\<close>

subsection\<open>Binding\<close>

text\<open>
  The binding pass reports through \<^ML>\<open>Position.report\<close>; a position without a document id is
  never reported, so the tests parse a source carrying a dummy id and capture the protocol
  messages. Every declaration and every resolved use is one entity markup; a name that resolves
  nowhere produces nothing (and no error markup either).
\<close>

ML\<open>
fun reports_in entry thy text =
  let
    val pos = Position.id "4711"
    val source = Input.source false text (pos, pos)
    val collected = Unsynchronized.ref ([] : string list)
    val root = the (ARM_Parse.parse_quiet entry (Proof_Context.init_global thy) source)
    val _ = Unsynchronized.setmp Private_Output.report_fn
              (fn outs => collected := String.concat outs :: !collected)
              (fn () => AnaEval.analyse_and_eval root thy) ()
  in String.concat (!collected) end

fun count sub s =
  let fun go i n =
    case Substring.position sub (Substring.extract (s, i, NONE)) of
      (_, rest) => if Substring.isEmpty rest then n
                   else go (size s - Substring.size rest + size sub) (n + 1)
  in go 0 0 end

val fresh = ARMEnv.reset_armenv @{theory}

(* the number of entity markups: declarations plus resolved uses *)
fun entities_in entry thy text = count "entity" (reports_in entry thy text)
fun ent_in thy entry name text n =
  let val got = entities_in entry thy text
  in if got = n then writeln ("OK: " ^ name)
     else fail ("FAILED: " ^ name ^ ": expected " ^ Int.toString n ^ ", got " ^ Int.toString got)
  end
val ent = ent_in fresh ARM_Parse.Entry_Stmts
val ente = ent_in fresh ARM_Parse.Entry_Expr

fun lines ls = String.concatWith "\n" ls

(* labels and symbols *)
val _ = ent "a label" "start: nop" 1
val _ = ent "a label and its use" (lines ["loop:", "    b loop"]) 2
val _ = ent "a forward reference" (lines ["    b done", "done:", "    nop"]) 2
val _ = ent "a name that resolves nowhere" "    bl memcpy" 0
val _ = ent "a symbol assigned" (lines ["x = 5", "    mov r0, #x"]) 2
val _ = ent "a symbol used before its definition" (lines ["    mov r0, #x", "x = 5"]) 2
val _ = ent "a symbol set" (lines [".set y, 3", "    ldr r0, =y"]) 2
val _ = ent "a symbol of .equ" (lines [".equ n, 4", "    movs r0, #n"]) 2
val _ = ent "a symbol defined twice" (lines [".set a, 1", ".set a, 2", "    mov r0, #a"]) 3
val _ = ent "symbols in an expression" (lines ["start:", "end:", "size = end - start"]) 5
val _ = ent "global and its label" (lines ["    .global main", "main:", "    nop"]) 2
val _ = ent "a literal pool entry" (lines ["    ldr r0, =tbl", "tbl:", "    .word 1"]) 2
val _ = ent "a relocation on a symbol" (lines ["    bl f(PLT)", "f:", "    nop"]) 2
val _ = ent "the size of a function" (lines ["f:", "    nop", "    .size f, . - f"]) 3
val _ = ent "a common symbol" (lines ["    .comm buf, 128, 4", "    ldr r0, =buf"]) 2

(* numeric labels *)
val _ = ent "a backward numeric reference" (lines ["1:", "    nop", "    b 1b"]) 2
val _ = ent "a forward numeric reference" (lines ["    b 1f", "    nop", "1:"]) 2
val _ = ent "a numeric reference with no definition" "    b 1f" 0
val _ = ent "the nearest numeric label before" (lines ["1:", "    nop", "1:", "    b 1b"]) 3
val _ = ent "numeric labels of different numbers" (lines ["1:", "2:", "    b 1b", "    b 2b"]) 4
val _ = ent "a forward reference skips the labels before" (lines ["1:", "    b 1f", "1:"]) 3

(* register aliases *)
val _ = ent "an alias and its uses" (lines ["acc .req r4", "    add acc, acc, #1"]) 3
val _ = ent "an alias with write-back" (lines ["p .req r0", "    ldm p!, {r1}"]) 2
val _ = ent "an alias ends at .unreq"
  (lines ["acc .req r4", "    .unreq acc", "    mov acc, r0"]) 2
val _ = ent "a register is no name" "    mov r0, r1" 0

(* macros *)
val _ = ent "a macro, its parameter and its call"
  (lines [".macro m a", "    mov r0, \\a", ".endm", "    m r1"]) 4
val _ = ent "a macro without parameters" (lines [".macro m", ".endm", "    m"]) 2
val _ = ent "a keyword argument" (lines [".macro m a", ".endm", "    m a=1"]) 4
val _ = ent "a macro hides the instruction of its name"
  (lines [".macro nop", ".endm", "    nop"]) 2
val _ = ent "a parameter inside a word" (lines [".macro m n", "    mov r\\n, #0", ".endm"]) 3
val _ = ent "a parameter in a label" (lines [".macro m name", "\\name\\():", ".endm"]) 3
val _ = ent "a parameter does not leave its macro"
  (lines [".macro m a", ".endm", "    mov r0, \\a"]) 2
val _ = ent "a label inside a macro" (lines [".macro m", "in:", "    b in", ".endm"]) 3
val _ = ent "a macro is known from its definition on" (lines ["    m", ".macro m", ".endm"]) 1
val _ = ent "a macro can be purged"
  (lines [".macro m", ".endm", "    .purgem m", "    m"]) 2
val _ = ent "a default value uses a symbol" (lines ["v = 1", ".macro m a=v", ".endm"]) 4
val _ = ent "the variable of .irp" (lines [".irp r, r0, r1", "    mov \\r, #0", ".endr"]) 2
val _ = ent "the variable of .irpc" (lines [".irpc c, abc", "    .byte '\\c", ".endr"]) 2
val _ = ent "the loop variable ends with the loop"
  (lines [".irp v, 1", ".endr", "    mov r0, \\v"]) 1

(* conditional assembly and loops *)
val _ = ent "both branches declare"
  (lines [".if 1", "x:", "    nop", ".else", "y:", "    nop", ".endif", "    b x", "    b y"]) 4
val _ = ent "a symbol in a condition" (lines ["D = 1", ".if D", "    nop", ".endif"]) 2
val _ = ent "ifdef" (lines ["D = 1", ".ifdef D", ".endif"]) 2
val _ = ent "a label in a loop body" (lines [".rept 2", "l:", "    b l", ".endr"]) 2

(* fragments *)
val _ = ente "an expression with names that resolve nowhere" "end - start" 0
\<close>

text\<open>
  The top level persists: what a command defines at the top level of its text is known to the
  commands that follow in the same theory; the body of a macro does not leave anything behind.\<close>

arm_stmt\<open>
persistent:
    nop
total = 8
acc2 .req r7
.macro twice a
inner:
    nop
.endm
\<close>

ML\<open>
val thy_p = @{theory}
val names_p = (case ARMEnv.get (Context.Theory thy_p) of ARMEnv.mk {names, ...} => names)
val _ = check "labels, symbols, aliases and macros stay"
  (Symtab.defined names_p "persistent" andalso Symtab.defined names_p "total"
   andalso Symtab.defined names_p "reg:acc2" andalso Symtab.defined names_p "macro:twice")
val _ = check "what is local to a macro does not stay"
  (not (Symtab.defined names_p "inner") andalso not (Symtab.defined names_p "param:a"))
val _ = ent_in thy_p ARM_Parse.Entry_Stmts "a use of a label of the earlier command"
  "    b persistent" 1
val _ = ent_in thy_p ARM_Parse.Entry_Stmts "a use of an alias of the earlier command"
  "    mov acc2, r0" 1
val _ = ent_in thy_p ARM_Parse.Entry_Stmts "a call of a macro of the earlier command"
  "    twice 1" 1
\<close>

subsection\<open>Antiquotations and navigation\<close>

text\<open>
  A comment attaches to the node starting at the next token; with no navigation string the
  handler sees that node (here the whole statement). The comment of the assembler is \<open>@\<close>, and
  an antiquotation in it begins with a second \<open>@\<close>.\<close>

arm_stmt\<open>
f:
    @@ probe_ast
    @@ highlight
    add r0, r1, r2
    bx lr
\<close>

ML\<open>
val _ = check "probe_ast sees the commented statement"
  (ARM_Pp.pp_root (!ARM_AST) = "    add r0, r1, r2")
\<close>

text\<open>
  Navigation: \<open>[uu]\<close> (a lone final \<open>u\<close> is a no-op) re-targets to enclosing nodes,
  \<open>[d]\<close>/\<open>[rd]\<close> to the first child,
  \<open>[rrd]\<close> to the second (as in C11, the first \<open>r\<close> only starts the cursor at 1). The children of an
  instruction are its operands.\<close>

arm_stmt\<open>
    //@ probe_ast[d]
    add r0, r1, r2
\<close>

ML\<open>
val _ = check "[d] reaches the first operand" (ARM_Pp.pp_root (!ARM_AST) = "r0")
\<close>

arm_stmt\<open>
    /*@ probe_ast[rrd] */
    add r0, r1, r2
\<close>

ML\<open>
val _ = check "[rrd] reaches the second operand" (ARM_Pp.pp_root (!ARM_AST) = "r1")
\<close>

arm_stmt\<open>
    ldr r0, [r1, #4]
    @@ probe_ast[rrdd]
    str r0, [r2, #8]
\<close>

ML\<open>
val _ = check "[rrdd] reaches the first child of the memory operand"
  (ARM_Pp.pp_root (!ARM_AST) = "r2")
\<close>

arm_stmt\<open>
.macro m a
    @@ probe_ast[uu]
    mov r0, \a
.endm
\<close>

ML\<open>
val _ = check "[uu] reaches the enclosing macro"
  (String.isPrefix ".macro m a" (ARM_Pp.pp_root (!ARM_AST)))
\<close>

text\<open>
  An \<open>@\<close> in running comment text is not an antiquotation (it would fail with an unregistered
  tag), whereas a tag with a cartouche body is one anywhere in a comment:\<close>

arm_stmt\<open>
    nop @ call me at someone@example.org, see @param x
    nop /* a comment with an @sign */
\<close>

ML\<open>
val ORDER = Unsynchronized.ref ([] : int list)
val record = let fun probe (_, _, l) (_ : string * Position.T) thy = (ORDER := l :: !ORDER; thy)
             in ARMEnv.store_antiq ("record", ARMEnv.lift_theory_antiq probe) end
\<close>
setup\<open>record\<close>

text\<open>Evaluation order is by \<open>level\<close>, not by position:\<close>

arm_stmt\<open>
@@ record(1)
    mov r0, #1
/* an ordinary comment @record(1) \<open>\<close> */
@@ record(0)
    mov r1, #2
/*@ record(1) */
    mov r2, #3
\<close>

ML\<open>
val _ = check "levels order the evaluation" (rev (!ORDER) = [0, 1, 1, 1])
\<close>

text\<open>The real Isabelle machinery: a \<open>definition\<close> in a comment, then a \<open>lemma\<close> proved about it,
  then a \<open>term\<close> mentioning it.\<close>

arm_stmt\<open>
@ A constant of the assembly program, mirrored in HOL:
@@ definition \<open>arm_limit :: nat where "arm_limit = 100"\<close>
@@ lemma(1) \<open>arm_fact: "arm_limit * 2 = 200" by (simp add: arm_limit_def)\<close>
@@ term(2) \<open>arm_limit + 1\<close>
LIMIT = 100
\<close>

thm arm_limit_def arm_fact

subsection\<open>\<open>arm_file\<close> on external sources\<close>

arm_file \<open>examples/startup.s\<close>

ML\<open>
val thy_h = @{theory}
val key_h =
  (case ARMEnv.get (Context.Theory thy_h) of ARMEnv.mk {units, ...} =>
   ARMEnv.ast_store_key thy_h (units - 1))
val path_h = Path.append (Resources.master_directory thy_h) (Path.explode "examples/startup.s")
val _ = check "startup: stored as a file"
  (case ARMEnv.get_ast key_h thy_h of
     SOME (ARM_Ast.Source (ARM_Ast.File (ss, _))) => length ss > 40
   | _ => false)
val _ = check "startup: the source text stored is the file's own"
  (ARMEnv.get_source key_h thy_h = SOME (File.read path_h))
\<close>

arm_file \<open>examples/memcpy.s\<close>

arm_file \<open>examples/macros.s\<close>

arm_file \<open>examples/fpu.s\<close>

arm_file \<open>examples/context.s\<close>

ML\<open>
val thy_f = @{theory}
val names_f = (case ARMEnv.get (Context.Theory thy_f) of ARMEnv.mk {names, ...} => names)
val _ = check "the labels of the files stay"
  (Symtab.defined names_f "Reset_Handler" andalso Symtab.defined names_f "memcpy"
   andalso Symtab.defined names_f "sum_array" andalso Symtab.defined names_f "PendSV_Handler")
val _ = check "the aliases and macros of a file stay"
  (Symtab.defined names_f "reg:acc" andalso Symtab.defined names_f "macro:zero_reg"
   andalso Symtab.defined names_f "macro:weak_handler")
val _ = check "the numeric labels do not stay" (not (Symtab.defined names_f "1"))
\<close>

subsection\<open>Export\<close>

arm_stmt\<open>
exported:
    movs r0, #1
    adds r0, r0, r1
    bx lr
\<close>

ML\<open>
val thy_x = @{theory}
val key_x = (case ARMEnv.get (Context.Theory thy_x) of ARMEnv.mk {units, ...} =>
               ARMEnv.ast_store_key thy_x (units - 1))
val thy_x' = run_arm_export (false, "ARM_Cmd_Tests_x", [key_x]) thy_x
val thy_x'' = run_arm_export (true, "ARM_Cmd_Tests_v", [key_x]) thy_x'
\<close>

text\<open>
  \<open>arm_export\<close> writes the stored sections to a \<^verbatim>\<open>.s\<close> file next to the theory, printed back by the
  pretty-printer or, with \<open>[verbatim]\<close>, as originally written.\<close>

ML\<open>
val exported =
  File.read (Path.append (Resources.master_directory thy_x) (Path.explode "ARM_Cmd_Tests_x.s"))
val exported_v =
  File.read (Path.append (Resources.master_directory thy_x) (Path.explode "ARM_Cmd_Tests_v.s"))
val _ = check "the exported text is the pretty-printed unit"
  (exported = "exported:\n    movs r0, #1\n    adds r0, r0, r1\n    bx lr\n")
val _ = check "the verbatim export is the text as written"
  (String.isSubstring "    adds r0, r0, r1" exported_v)
val _ = check "the pretty-printed text of the section"
  (case ARMEnv.get_ast key_x thy_x of
     SOME r => ARM_Pp.pp_root r = "exported:\n    movs r0, #1\n    adds r0, r0, r1\n    bx lr"
   | NONE => false)
\<close>

subsection\<open>The semantic-backend hook\<close>

ML\<open>
val BACKEND_SEEN = Unsynchronized.ref ([] : string list)
\<close>

setup_backend\<open>fn root => fn thy => (BACKEND_SEEN := ARM_Pp.pp_root root :: !BACKEND_SEEN; thy)\<close>

arm_stmt\<open>
seen:
    nop
\<close>

ML\<open>
val _ = check "the backend saw the statements"
  (exists (String.isPrefix "seen:") (!BACKEND_SEEN))
\<close>

setup_backend\<open>K I\<close>

subsection\<open>Resetting the environment\<close>

ML\<open>
val names_before = (case ARMEnv.get (Context.Theory @{theory}) of ARMEnv.mk {names, ...} =>
  Symtab.size names)
\<close>

reset_armenv

ML\<open>
val names_after = (case ARMEnv.get (Context.Theory @{theory}) of ARMEnv.mk {names, ...} =>
  Symtab.size names)
val _ = check "reset_armenv forgets the declared names" (names_after = 0 andalso names_before > 0)
\<close>

ML\<open>val _ = report_failures ()\<close>

end
