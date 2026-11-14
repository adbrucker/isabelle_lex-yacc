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


theory ARM_Tests
  imports ARM_Parser
begin

section\<open>Parser-level Tests\<close>

text\<open>
  Exercised directly through \<^ML>\<open>ARM_Parse.parse_loud\<close>/\<^ML>\<open>ARM_Parse.parse_quiet\<close> and the
  pretty-printer \<^ML>\<open>ARM_Pp.pp_root\<close>, before any Isar command exists. A fragment already in the
  pretty-printer's canonical layout (labels and the directives that structure the text at the
  level of their block, instructions four blanks further in, blanks around binary operators) must
  come back unchanged (\<^emph>\<open>round trip\<close>), and every accepted program must be a fixed point of
  parse-then-print (\<^emph>\<open>idempotence\<close>). The decoding of the mnemonics, which is what the parser
  adds to the text, is tested on the tree that results.
\<close>

ML\<open>
fun prog lines = String.concatWith "\n" lines

fun parse_entry entry s = ARM_Parse.parse_loud entry @{context} (Input.string s)

fun show_entry entry s =
  (case parse_entry entry s of
     SOME r => ARM_Pp.pp_root r
   | NONE => error "parser returned NONE")

val show = show_entry ARM_Parse.Entry_File
val show_stmts = show_entry ARM_Parse.Entry_Stmts
val show_expr = show_entry ARM_Parse.Entry_Expr
val show_operand = show_entry ARM_Parse.Entry_Operand

fun idempotent_with show' lines =
  let
    val s = prog lines
    val out = show' s
    val out2 = show' out
  in if out = out2 then out
    else error ("not idempotent:\n" ^ out ^ "\n--- vs ---\n" ^ out2) end

(* The failures of all tests are collected and reported together at the end of the theory. *)
val failures : string list Unsynchronized.ref = Unsynchronized.ref []
fun fail msg = failures := msg :: !failures
fun report_failures () =
  if null (!failures) then ()
  else
    let
      val msg = string_of_int (length (!failures)) ^ " test(s) failed:\n\n"
                ^ space_implode "\n\n" (rev (!failures))
      (* a development aid: the full report in a file, as a build log cuts long messages *)
      val _ = (case getenv "ARM_TEST_LOG" of "" => () | f => File.write (Path.explode f) msg)
    in error msg end

fun roundtrip_with show' lines =
  let
    val s = prog lines
  in
    (case Exn.capture (idempotent_with show') lines of
       Exn.Res out => if out = s then ()
                      else fail ("round trip mismatch for:\n" ^ s ^ "\n--- got ---\n" ^ out)
     | Exn.Exn e => fail (Runtime.exn_message e ^ "\n  while reading:\n" ^ s))
  end

val roundtrip = roundtrip_with show_stmts
val roundtrip_expr = roundtrip_with show_expr
val roundtrip_operand = roundtrip_with show_operand

(* Accepted, and a fixed point of read-then-print; the layout of the text is not compared. *)
fun accepts_with show' lines =
  (case Exn.capture (idempotent_with show') lines of
     Exn.Res _ => ()
   | Exn.Exn e => fail (Runtime.exn_message e ^ "\n  while reading:\n" ^ prog lines))

val accepts = accepts_with show_stmts
val accepts_file = accepts_with show
val accepts_expr = accepts_with show_expr

(* Reading "lines" must print as "expected" (a layout-normalising read). *)
fun reads_as_with show' lines expected =
  (case Exn.capture (fn () => show' (prog lines)) () of
     Exn.Res out => if out = prog expected then ()
                    else fail ("reads-as mismatch for:\n" ^ prog lines ^ "\n--- got ---\n" ^ out)
   | Exn.Exn e => fail (Runtime.exn_message e ^ "\n  while reading:\n" ^ prog lines))

val reads_as = reads_as_with show_stmts
val reads_as_expr = reads_as_with show_expr

(* The text must be rejected by the entry point. *)
fun rejects_with entry lines =
  (case Exn.capture
          (fn () => ARM_Parse.parse_quiet entry @{context} (Input.string (prog lines))) () of
     Exn.Exn (ARM_Parse.Rejected _) => ()
   | Exn.Exn _ => ()
   | Exn.Res _ => fail ("accepted, but should be rejected:\n" ^ prog lines))

val rejects = rejects_with ARM_Parse.Entry_Stmts
val rejects_expr = rejects_with ARM_Parse.Entry_Expr

(* a check on the tree *)
fun check name b = if b then () else fail ("check failed: " ^ name)

fun stmts_of s =
  (case parse_entry ARM_Parse.Entry_Stmts s of
     SOME (ARM_Ast.Stmts ss) => ss
   | _ => error "statements expected")
\<close>

subsection\<open>Instructions\<close>

ML\<open>
val _ = roundtrip ["    mov r0, #1"]
val _ = roundtrip ["    movs r0, r1"]
val _ = roundtrip ["    add.w r1, r2, r3, lsl #2"]
val _ = roundtrip ["    add r1, r2, r3, lsl r4"]
val _ = roundtrip ["    mov r0, r1, rrx"]
val _ = roundtrip ["    ldr r0, [r1]"]
val _ = roundtrip ["    ldr r0, [r1, #4]"]
val _ = roundtrip ["    ldr r0, [r1, #-4]!"]
val _ = roundtrip ["    ldr r0, [r1, r2]"]
val _ = roundtrip ["    ldr r0, [r1, r2, lsl #2]"]
val _ = roundtrip ["    ldr r0, [r1, -r2]"]
val _ = roundtrip ["    ldr r0, [r1], #4"]
val _ = roundtrip ["    ldr r0, =0x20000000"]
val _ = roundtrip ["    ldr r0, =msg"]
val _ = roundtrip ["    str r0, [sp, #-4]!"]
val _ = roundtrip ["    ldrd r0, r1, [r2, #8]"]
val _ = roundtrip ["    push {r4, r5, r6, lr}"]
val _ = roundtrip ["    pop {r4-r7, pc}"]
val _ = roundtrip ["    ldmia r0!, {r1-r3}"]
val _ = roundtrip ["    stmdb sp!, {r4-r11, lr}"]
val _ = roundtrip ["    bl func"]
val _ = roundtrip ["    bx lr"]
val _ = roundtrip ["    beq 1f"]
val _ = roundtrip ["    bne 2b"]
val _ = roundtrip ["    cbz r0, done"]
val _ = roundtrip ["    movw r0, #:lower16:table"]
val _ = roundtrip ["    movt r0, #:upper16:table"]
val _ = roundtrip ["    adr r0, table + 8"]
val _ = roundtrip ["    mrs r0, primask"]
val _ = roundtrip ["    msr basepri, r1"]
val _ = roundtrip ["    cpsid i"]
val _ = roundtrip ["    dsb"]
val _ = roundtrip ["    isb"]
val _ = roundtrip ["    nop"]
val _ = roundtrip ["    wfi"]
val _ = roundtrip ["    svc #0"]
val _ = roundtrip ["    bkpt #1"]
val _ = roundtrip ["    ite eq"]
val _ = roundtrip ["    addeq r0, r0, #1"]
val _ = roundtrip ["    addseq r0, r0, #1"]
val _ = roundtrip ["    ldrsb.w r0, [r1, #3]"]
val _ = roundtrip ["    ubfx r0, r1, #4, #8"]
val _ = roundtrip ["    smlal r0, r1, r2, r3"]
val _ = roundtrip ["    sdiv r0, r1, r2"]
val _ = roundtrip ["    tbb [pc, r0]"]
val _ = roundtrip ["    ldr pc, [r0, #4]"]
val _ = roundtrip ["    mov r0, #(1 << 5) | 3"]
val _ = roundtrip ["    mov r0, #~0"]
val _ = roundtrip ["    ldr r0, [r1, :64]"]
val _ = roundtrip ["    bl memcpy(PLT)"]
val _ = roundtrip ["    ldr r0, .L1"]
val _ = roundtrip ["    adr r1, ."]
val _ = roundtrip ["    mov r0, #'a"]
val _ = roundtrip ["    movs r0, #'\\n'"]

\<close>

text\<open>Floating point.\<close>

ML\<open>
val _ = roundtrip ["    vadd.f32 s0, s1, s2"]
val _ = roundtrip ["    vmul.f64 d0, d1, d2"]
val _ = roundtrip ["    vldr s0, [r0, #4]"]
val _ = roundtrip ["    vstr d0, [r0]"]
val _ = roundtrip ["    vmov r0, s1"]
val _ = roundtrip ["    vmov.f32 s0, #1.0"]
val _ = roundtrip ["    vcvt.s32.f32 s0, s1"]
val _ = roundtrip ["    vpush {d8-d15}"]
val _ = roundtrip ["    vpop {s16-s31}"]
val _ = roundtrip ["    vmrs APSR_nzcv, fpscr"]
val _ = roundtrip ["    vldmia r0!, {s0-s3}"]
val _ = roundtrip ["    vsqrt.f64 d0, d1"]
val _ = roundtrip ["    vmov.32 d0[1], r2"]
val _ = roundtrip ["    vfma.f32 s0, s1, s2"]
\<close>

subsection\<open>Decoding the mnemonics\<close>

ML\<open>
fun decoded text = ARM_Isa.decode text

fun d_is text opc cnd s width dts =
  (case decoded text of
     SOME {opc = o1, cond = c1, setflags = s1, width = w1, dtypes = d1, ...} =>
       check ("decode " ^ text) (o1 = opc andalso c1 = cnd andalso s1 = s andalso w1 = width
                                 andalso d1 = dts)
   | NONE => fail ("not decoded: " ^ text))

open ARM_Ast

val _ = d_is "add" ADD NONE false NONE []
val _ = d_is "ADD" ADD NONE false NONE []
val _ = d_is "adds" ADD NONE true NONE []
val _ = d_is "addeq" ADD (SOME EQ) false NONE []
val _ = d_is "addseq" ADD (SOME EQ) true NONE []
val _ = d_is "addeqs" ADD (SOME EQ) true NONE []
val _ = d_is "add.w" ADD NONE false (SOME Wide) []
val _ = d_is "add.n" ADD NONE false (SOME Narrow) []
val _ = d_is "addw" ADDW NONE false NONE []
val _ = d_is "bls" B (SOME LS) false NONE []
val _ = d_is "bl" BL NONE false NONE []
val _ = d_is "ble" B (SOME LE) false NONE []
val _ = d_is "bleq" BL (SOME EQ) false NONE []
val _ = d_is "blt" B (SOME LT) false NONE []
val _ = d_is "bne" B (SOME NE) false NONE []
val _ = d_is "bne.w" B (SOME NE) false (SOME Wide) []
val _ = d_is "blo" B (SOME CC) false NONE []
val _ = d_is "bx" BX NONE false NONE []
val _ = d_is "bxne" BX (SOME NE) false NONE []
val _ = d_is "blx" BLX NONE false NONE []
val _ = d_is "movt" MOVT NONE false NONE []
val _ = d_is "movw" MOVW NONE false NONE []
val _ = d_is "movs" MOV NONE true NONE []
val _ = d_is "movls" MOV (SOME LS) false NONE []
val _ = d_is "ldr" LDR NONE false NONE []
val _ = d_is "ldrb" LDRB NONE false NONE []
val _ = d_is "ldrsh" LDRSH NONE false NONE []
val _ = d_is "ldrhs" LDR (SOME CS) false NONE []
val _ = d_is "strhs" STR (SOME CS) false NONE []
val _ = d_is "ldmia" LDMIA NONE false NONE []
val _ = d_is "ldmiaeq" LDMIA (SOME EQ) false NONE []
val _ = d_is "push" PUSH NONE false NONE []
val _ = d_is "it" IT NONE false NONE []
val _ = d_is "ittee" IT NONE false NONE []
val _ = d_is "vadd.f32" VADD NONE false NONE ["f32"]
val _ = d_is "vaddeq.f32" VADD (SOME EQ) false NONE ["f32"]
val _ = d_is "vcvt.s32.f32" VCVT NONE false NONE ["s32", "f32"]
val _ = d_is "vcvtr.s32.f32" VCVTR NONE false NONE ["s32", "f32"]
val _ = d_is "cpsid" CPSID NONE false NONE []
val _ = d_is "ldrex" LDREX NONE false NONE []
val _ = d_is "tbb" TBB NONE false NONE []
val _ = d_is "rrxs" RRX NONE true NONE []

val _ = check "an unknown word is not a mnemonic" (is_none (decoded "frobnicate"))
val _ = check "a macro name is not a mnemonic" (is_none (decoded "save_regs"))
val _ = check "a directive is not a mnemonic" (is_none (decoded "x"))

val _ = check "r0" (ARM_Isa.reg_of "r0" = SOME (Core R0))
val _ = check "R12" (ARM_Isa.reg_of "R12" = SOME (Core R12))
val _ = check "sp is r13"
  (ARM_Isa.reg_of "r13" = SOME (Core SP) andalso ARM_Isa.reg_of "sp" = SOME (Core SP))
val _ = check "ip is r12" (ARM_Isa.reg_of "ip" = SOME (Core R12))
val _ = check "fp is r11" (ARM_Isa.reg_of "fp" = SOME (Core R11))
val _ = check "lr" (ARM_Isa.reg_of "lr" = SOME (Core LR))
val _ = check "pc" (ARM_Isa.reg_of "PC" = SOME (Core PC))
val _ = check "s31" (ARM_Isa.reg_of "s31" = SOME (Single 31))
val _ = check "d7" (ARM_Isa.reg_of "d7" = SOME (Double 7))
val _ = check "primask" (ARM_Isa.reg_of "primask" = SOME (Special "primask"))
val _ = check "r16 is no register" (is_none (ARM_Isa.reg_of "r16"))
val _ = check "a symbol is no register" (is_none (ARM_Isa.reg_of "main"))

val _ = check "the opcode of a parsed statement"
  (case stmts_of "adds r0, r1, #1" of
     [SInsn (Insn ({opc = ADD, setflags = true, cond = NONE, ...}, [_, _, _], _))] => true
   | _ => false)
val _ = check "a macro call"
  (case stmts_of "save_regs r4, r5" of
     [SCall (Ident ("save_regs", _, _), [_, _], _)] => true
   | _ => false)
val _ = check "a register operand"
  (case stmts_of "mov r0, r1" of
     [SInsn (Insn (_, [OReg (Core R0, "r0", false, _), OReg (Core R1, "r1", false, _)], _))] => true
   | _ => false)
val _ = check "a write-back register"
  (case stmts_of "ldm r0!, {r1}" of
     [SInsn (Insn (_, [OReg (Core R0, _, true, _),
                       OList ([OReg (Core R1, _, false, _)], false, _)], _))] => true
   | _ => false)
val _ = check "a register range"
  (case stmts_of "push {r4-r7}" of
     [SInsn (Insn (_, [OList ([ORange (OReg (Core R4, _, _, _), OReg (Core R7, _, _, _), _)],
                              _, _)], _))] => true
   | _ => false)
val _ = check "a shifted operand"
  (case stmts_of "add r0, r1, r2, lsl #3" of
     [SInsn (Insn (_, [_, _, _, OShift (Lsl, "lsl", SOME (OImm _), _)], _))] => true
   | _ => false)
val _ = check "a memory operand with write-back"
  (case stmts_of "ldr r0, [r1, #4]!" of
     [SInsn (Insn (_, [_, OMem ([OReg _, OImm _], true, _)], _))] => true
   | _ => false)
val _ = check "a literal"
  (case stmts_of "ldr r0, =x" of
     [SInsn (Insn (_, [_, OLiteral (ESym _, _)], _))] => true
   | _ => false)
val _ = check "a local reference"
  (case stmts_of "b 1f" of
     [SInsn (Insn (_, [OExpr (ELocal ("1f", _))], _))] => true
   | _ => false)
\<close>

subsection\<open>Expressions\<close>

ML\<open>
val _ = roundtrip_expr ["1 + 2"]
val _ = roundtrip_expr ["a - b - c"]
val _ = roundtrip_expr ["(1 + 2) * 3"]
val _ = roundtrip_expr ["-x"]
val _ = roundtrip_expr ["~x"]
val _ = roundtrip_expr ["1 << 4 | 2"]
val _ = roundtrip_expr ["end - start"]
val _ = roundtrip_expr ["table_end - table"]
val _ = roundtrip_expr ["0x1f + 0b101 + 017 + 10"]
val _ = roundtrip_expr ["a == b && c != d || e <= f"]
val _ = roundtrip_expr ["\"text\""]
val _ = roundtrip_expr ["sym(GOT)"]
val _ = roundtrip_expr [". - start"]
val _ = roundtrip_expr ["1.5"]
val _ = roundtrip_expr ["0f1.5"]
val _ = roundtrip_expr ["r0"]

(* the precedences of the assembler: * / % << >> bind tighter than | & ^, which bind tighter than
   + -, then the comparisons, then && and || *)
val _ = check "precedence: * binds tighter than +"
  (case parse_entry ARM_Parse.Entry_Expr "1 + 2 * 3" of
     SOME (Expr (EBinary (Add, ENum _, EBinary (Mul, _, _, _), _))) => true
   | _ => false)
val _ = check "precedence: | binds tighter than +"
  (case parse_entry ARM_Parse.Entry_Expr "1 + 2 | 3" of
     SOME (Expr (EBinary (Add, ENum _, EBinary (Or, _, _, _), _))) => true
   | _ => false)
val _ = check "precedence: + binds tighter than =="
  (case parse_entry ARM_Parse.Entry_Expr "1 == 2 + 3" of
     SOME (Expr (EBinary (Equal, _, EBinary (Add, _, _, _), _))) => true
   | _ => false)
val _ = check "left associative"
  (case parse_entry ARM_Parse.Entry_Expr "8 - 4 - 2" of
     SOME (Expr (EBinary (Sub, EBinary (Sub, _, _, _), ENum _, _))) => true
   | _ => false)

val _ = rejects_expr ["1 +"]
val _ = rejects_expr ["(1"]
val _ = rejects_expr ["1 2"]
\<close>

subsection\<open>Labels, symbols, directives\<close>

ML\<open>
val _ = roundtrip ["main:"]
val _ = roundtrip ["1:"]
val _ = roundtrip [".L1:"]
val _ = roundtrip ["start:", "    mov r0, #0", "loop:", "    b loop"]
val _ = roundtrip ["BUFSIZE = 256"]
val _ = roundtrip ["end = start + 4"]
val _ = roundtrip ["acc .req r4"]
val _ = roundtrip ["    .word 1, 2, 3"]
val _ = roundtrip ["    .word 0x20000000, Reset_Handler"]
val _ = roundtrip ["    .byte 'a, 'b"]
val _ = roundtrip ["    .asciz \"Hello\\n\""]
val _ = roundtrip ["    .align 2"]
val _ = roundtrip ["    .syntax unified"]
val _ = reads_as ["    .cpu cortex-m7"] ["    .cpu cortex - m7"]
val _ = reads_as ["    .fpu fpv5-d16"] ["    .fpu fpv5 - d16"]
val _ = roundtrip ["    .thumb"]
val _ = roundtrip ["    .thumb_func"]
val _ = roundtrip ["    .global main"]
val _ = roundtrip ["    .type main, %function"]
val _ = roundtrip ["    .size main, . - main"]
val _ = roundtrip ["    .section .text, \"ax\", %progbits"]
val _ = roundtrip ["    .section .isr_vector, \"a\", %progbits"]
val _ = roundtrip ["    .space 64, 0"]
val _ = roundtrip ["    .set sym, 5"]
val _ = roundtrip ["    .equ size, end - start"]
val _ = roundtrip ["    .float 1.5, 2.5"]
val _ = roundtrip ["    .eabi_attribute 28, 1"]
val _ = roundtrip ["    .include \"defs.inc\""]
val _ = roundtrip ["    .weak foo"]
val _ = roundtrip ["    .comm buf, 128, 4"]
val _ = roundtrip ["    .fnstart"]
val _ = roundtrip ["    .save {r4, lr}"]
val _ = roundtrip ["    .ltorg"]
val _ = roundtrip ["    .file 1 \"/home/x\" \"main.c\""]
val _ = roundtrip ["    .loc 1 12 5 prologue_end"]
val _ = roundtrip ["    .loc 1 12 5 is_stmt 0 discriminator 3"]
val _ = roundtrip ["    .file \"main.c\""]

val _ = check "an instruction with the S flag after a label"
  (case stmts_of "loop: subs r0, r0, #1" of
     [SLabel (LName (Ident ("loop", _, _)), _),
      SInsn (Insn ({opc = SUB, setflags = true, ...}, _, _))] => true
   | _ => false)
val _ = check "several labels"
  (length (stmts_of "a: b: 1: nop") = 4)
val _ = check "statements separated by semicolons"
  (length (stmts_of "mov r0, #1; mov r1, #2; nop") = 3)
val _ = check "a directive"
  (case stmts_of ".word 1, 2" of [SDir (Ident (".word", _, _), [_, _], _)] => true | _ => false)
val _ = check "a symbol assignment"
  (case stmts_of "x = 3" of [SAssign (Ident ("x", _, _), ENum ("3", _), _)] => true | _ => false)
val _ = check "a register alias"
  (case stmts_of "acc .req r4" of
     [SReq (Ident ("acc", _, _), OReg (Core R4, _, _, _), _)] => true | _ => false)
val _ = check "a percent word"
  (case stmts_of ".type f, %function" of
     [SDir (_, [_, OPercent (Ident ("function", _, _), _)], _)] => true | _ => false)

val _ = rejects ["mov r0,"]
val _ = rejects ["ldr r0, [r1"]
val _ = rejects ["ldr r0, r1]"]
val _ = rejects ["push {r0"]
val _ = rejects ["mov r0, #"]
val _ = rejects ["add r0, , r1"]
val _ = rejects ["x ="]
val _ = rejects ["mov r0, \"unterminated"]
\<close>

subsection\<open>Macros, conditional assembly, loops\<close>

ML\<open>
val _ = roundtrip [".macro save a, b", "    push {\\a, \\b}", ".endm"]
val _ = roundtrip [".macro swap a, b, tmp=r12", "    mov \\tmp, \\a", "    mov \\a, \\b",
                   "    mov \\b, \\tmp", ".endm"]
val _ = roundtrip [".macro vec name:req, handler=Default_Handler", "    .word \\handler", ".endm"]
val _ = roundtrip [".macro regs n", "    mov r\\n, #\\n", "label_\\@:", "\\name\\():", ".endm"]
val _ = roundtrip [".macro none", ".endm"]
val _ = reads_as [".macro m, a, b", ".endm"] [".macro m a, b", ".endm"]
val _ = roundtrip [".macro outer", ".macro inner", "    nop", ".endm", ".endm"]
val _ = roundtrip [".if 1", "    nop", ".endif"]
val _ = roundtrip [".if DEBUG", "    bl trace", ".else", "    nop", ".endif"]
val _ = roundtrip [".if A == 1", "    nop", ".elseif A == 2", "    wfi", ".else", "    wfe",
                   ".endif"]
val _ = roundtrip [".ifdef FOO", "    nop", ".endif"]
val _ = roundtrip [".ifndef FOO", "FOO = 1", ".endif"]
val _ = roundtrip [".ifc \\a, r0", "    nop", ".endif"]
val _ = roundtrip [".if 1", ".if 2", "    nop", ".endif", ".endif"]
val _ = roundtrip [".rept 4", "    nop", ".endr"]
val _ = roundtrip [".irp reg, r0, r1, r2", "    mov \\reg, #0", ".endr"]
val _ = roundtrip [".irpc c, abc", "    .byte '\\c", ".endr"]
val _ = roundtrip [".macro m", ".if 1", ".rept 2", "    nop", ".endr", ".endif", ".endm"]

val _ = check "a macro definition"
  (case stmts_of ".macro save a, b=1\n  push {\\a}\n.endm" of
     [SMacro (Ident ("save", _, _),
              [MParam (_, NONE, NONE, false, _), MParam (_, NONE, SOME _, true, _)],
              [SInsn _], _)] => true
   | _ => false)
val _ = check "a conditional with elseif and else"
  (case stmts_of ".if 1\n nop\n.elseif 2\n nop\n.else\n nop\n.endif" of
     [SCond ([_, _], SOME [_], _)] => true
   | _ => false)
val _ = check "a loop"
  (case stmts_of ".rept 3\n nop\n.endr" of
     [SRep (Ident (".rept", _, _), [_], [_], _)] => true
   | _ => false)
val _ = check "case does not matter for the words that end a block"
  (case stmts_of ".IF 1\n nop\n.ENDIF" of [SCond _] => true | _ => false)
val _ = check "a macro parameter with a qualifier"
  (case stmts_of ".macro m a:req\n.endm" of
     [SMacro (_, [MParam (_, SOME "req", NONE, false, _)], [], _)] => true
   | _ => false)

val _ = rejects [".macro m", "nop"]
val _ = rejects [".endm"]
val _ = rejects [".if 1", "nop"]
val _ = rejects [".else"]
val _ = rejects [".rept 2", "nop"]
val _ = rejects [".if", "nop", ".endif"]
\<close>

subsection\<open>Comments and whole files\<close>

ML\<open>
val _ = reads_as ["mov r0, #1 @ a comment"] ["    mov r0, #1"]
val _ = reads_as ["@ only a comment", "nop"] ["    nop"]
val _ = reads_as ["mov r0, #1 // c++ style", "nop"] ["    mov r0, #1", "    nop"]
val _ = reads_as ["mov r0, /* inside */ #1"] ["    mov r0, #1"]
val _ = reads_as ["/* a", "multi-line", "comment */", "nop"] ["    nop"]
val _ = reads_as ["# 12 \"file.S\"", "nop"] ["    nop"]
val _ = reads_as ["nop @ it is @@ not a tag"] ["    nop"]
val _ = reads_as ["  mov r0, #1  ", "", "", "  nop"] ["    mov r0, #1", "    nop"]
val _ = reads_as ["nop;nop"] ["    nop", "    nop"]

(* a whole file: the last line need not end with a newline *)
val _ = check "a file without a final newline"
  (show "nop" = "    nop\n")
val _ = check "an empty file" (show "" = "")
val _ = check "a file of comments" (show "@ x\n@ y\n" = "")
val _ = check "a file with a final newline" (show "nop\n" = "    nop\n")

val _ = accepts_file
  [".syntax unified", ".cpu cortex-m7", ".thumb", "", ".section .text", ".global _start",
   ".type _start, %function", "_start:", "    ldr sp, =_estack", "    bl main", "1:", "    b 1b",
   ".size _start, . - _start"]

val _ = accepts_file
  [".text", ".align 2", "memcpy:", "    cbz r2, 2f", "1:", "    ldrb r3, [r1], #1",
   "    strb r3, [r0], #1", "    subs r2, r2, #1", "    bne 1b", "2:", "    bx lr"]
\<close>

subsection\<open>The corpus\<close>

text\<open>
  The real test: if the environment variable \<^verbatim>\<open>ARM_SRC\<close> names a directory with assembly files
  (\<^verbatim>\<open>.s\<close> and \<^verbatim>\<open>.S\<close>; for instance the output of \<^verbatim>\<open>clang --target=thumbv7em-none-eabihf
  -mcpu=cortex-m7 -S\<close> on some C code, or the startup files of a vendor's library), every file below
  it is read and printed back; the printed text must have the very tokens of the source (but for
  the ends of the lines and the case of the words that end a block) and must read again to the
  same text. Without the variable the test does nothing.
\<close>

ML\<open>
local
  fun asm_files p =
    if File.is_dir p
    then maps (fn n => asm_files (Path.append p (Path.basic n))) (sort_strings (File.read_dir p))
    else if String.isSuffix ".s" (Path.implode p) orelse String.isSuffix ".S" (Path.implode p)
    then [p] else []

  val root = getenv "ARM_SRC"
  val files = if root = "" orelse not (File.is_dir (Path.explode root)) then []
              else asm_files (Path.explode root)

  (* the ends of lines and statements are not compared, nor the case of the closing words *)
  fun norm_token t =
    let
      val u = String.map Char.toUpper t
      (* ".file" and ".loc" are lexed with the rest of their line: one blank between *)
      fun squeeze x = String.concatWith " " (String.tokens Char.isSpace x)
    in
      if member (op =) [".ENDM", ".ENDIF", ".ELSE", ".ENDR", ".REQ", ".EXITM"] u
      then String.map Char.toLower t
      else if String.isPrefix ".FILE" u orelse String.isPrefix ".LOC" u
           andalso size t > 4 andalso Char.isSpace (String.sub (t, 4))
      then squeeze t
      else t
    end

  fun norm_tokens ts = map norm_token (filter (fn t => t <> "\n" andalso t <> ";") ts)

  fun check_file path =
    let
      val name = Path.implode path
      val text = File.read path
      fun toks t = norm_tokens (ARM_Parse.lex_texts @{context} (Input.string t))
      fun parse t =
        ARM_Parse.parse_quiet ARM_Parse.Entry_File @{context}
          (Input.source true t (Position.file name, Position.none))
    in
      (case Exn.capture parse text of
         Exn.Exn (ARM_Parse.Rejected msg) => SOME (name ^ ": rejected: " ^ msg)
       | Exn.Exn e => SOME (name ^ ": " ^ Runtime.exn_message e)
       | Exn.Res NONE => SOME (name ^ ": no result")
       | Exn.Res (SOME r) =>
           let val p1 = ARM_Pp.pp_root r
           in
             (case Exn.capture parse p1 of
                Exn.Res (SOME r2) =>
                  if ARM_Pp.pp_root r2 <> p1 then SOME (name ^ ": not idempotent")
                  else if toks p1 <> toks text then SOME (name ^ ": the tokens differ")
                  else NONE
              | _ => SOME (name ^ ": the printed text does not parse"))
           end)
    end
in
  val corpus_size = length files
  val corpus_failures = map_filter I (Par_List.map check_file files)
  val _ =
    if corpus_size = 0 then ()
    else
      let
        val summary =
          "ARM_Tests: " ^ string_of_int corpus_size ^ " assembly file(s) read, "
          ^ string_of_int (corpus_size - length corpus_failures) ^ " parsed and printed back, "
          ^ string_of_int (length corpus_failures) ^ " failure(s)"
        (* a development aid: the summary in a file, as the log of a build does not show it *)
        val _ = (case getenv "ARM_TEST_LOG" of
                   "" => () | f => File.write (Path.explode (f ^ ".corpus")) (summary ^ "\n"))
      in (writeln summary; List.app fail corpus_failures) end
end
\<close>

ML\<open>val _ = report_failures ()\<close>

end
