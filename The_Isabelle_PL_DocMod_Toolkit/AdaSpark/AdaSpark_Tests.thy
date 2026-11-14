(******************************************************************************
 * Copyright (c) University of Paris-Saclay
 *
 * All rights reserved.
 *
 * Authors: Burkhart Wolff, Claude Sonnet 5.5
 *
 * This is an LLM-generated replication of the Isabelle/C version 2 design to
 * the programming language Ada 2012 and its SPARK 2014 subset (AdaSpark). It
 * provides an efficient parser for AdaSpark, deeply integrated into the
 * Isabelle/PIDE document model, allowing external files as well as in-theory
 * code-snippets which are transparent to the underlying theory. It provides an
 * API for the generated AST’s, and an API to hook up semantic backends that
 * compile these AST’s to theory extensions in Isabelle/HOL. Members of the
 * family come with a AdaSpark-specific antiquotation mechanism allowing
 * programmable links to the semantic backends as necessary for support of
 * program-annotations with HOL formulas.
 *
 * This session is part of the Isabelle Programming Language Toolkit
 * (Isabelle/PLTk). The generation has been done with Claude Sonnet 5.5; while
 * the replicants come with a detailed (generated) test-suite for AdaSpark, I
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

theory AdaSpark_Tests
  imports AdaSpark_Parser
begin

section\<open>Parser-level Tests\<close>

text\<open>
  Exercised directly through
  \<^ML>\<open>AdaSpark_Parse.parse_loud\<close>/\<^ML>\<open>AdaSpark_Parse.parse_quiet\<close> and the
  pretty-printer \<^ML>\<open>AdaSpark_Pp.pp_root\<close>, before any Isar command exists. A
  program already in the pretty-printer's canonical layout must come back
  unchanged (\<^emph>\<open>round trip\<close>), and every accepted program must be a fixed point of
  parse-then-print (\<^emph>\<open>idempotence\<close>).
\<close>

ML\<open>
fun prog lines = String.concatWith "\n" lines

fun parse_entry entry s =
  AdaSpark_Parse.parse_loud entry @{context} (Input.string s)

fun show_entry entry s =
  (case parse_entry entry s of
     SOME r => AdaSpark_Pp.pp_root r
   | NONE => error "parser returned NONE")

val show = show_entry AdaSpark_Parse.Entry_Crate
val show_body = show_entry AdaSpark_Parse.Entry_Body
val show_expr = show_entry AdaSpark_Parse.Entry_Expr
val show_type = show_entry AdaSpark_Parse.Entry_Type

fun idempotent_with show' lines =
  let
    val s = prog lines
    val out = show' s
    val out2 = show' out
  in if out = out2 then out
    else error ("not idempotent:\n" ^ out ^ "\n--- vs ---\n" ^ out2) end

(* The failures of all tests are collected and reported together at the end of
   the theory. *)
val failures : string list Unsynchronized.ref = Unsynchronized.ref []
fun fail msg = failures := msg :: !failures
fun report_failures () =
  if null (!failures) then ()
  else error (string_of_int (length (!failures))
              ^ " test(s) failed:\n\n"
              ^ space_implode "\n\n" (rev (!failures)))

fun roundtrip_with show' lines =
  let
    val s = prog lines
  in
    (case Exn.capture (idempotent_with show') lines of
       Exn.Res out => if out = s then ()
                      else fail
                        ("round trip mismatch for:\n" ^ s ^ "\n--- got ---\n"
                         ^ out)
     | Exn.Exn e => fail (Runtime.exn_message e ^ "\n  while reading:\n" ^ s))
  end

val roundtrip = roundtrip_with show
val roundtrip_body = roundtrip_with show_body
val roundtrip_expr = roundtrip_with show_expr
val roundtrip_type = roundtrip_with show_type

(* Reading "lines" must print as "expected" (a case-normalising or
   layout-normalising read). *)
fun reads_as_with show' lines expected =
  (case Exn.capture (fn () => show' (prog lines)) () of
     Exn.Res out => if out = prog expected then ()
                    else fail ("reads-as mismatch for:\n" ^ prog lines ^
                               "\n--- got ---\n" ^ out)
   | Exn.Exn e => fail (Runtime.exn_message e ^ "\n  while reading:\n" ^
                        prog lines))

val reads_as = reads_as_with show
val reads_as_body = reads_as_with show_body
val reads_as_expr = reads_as_with show_expr

fun rejects_entry entry lines =
  (case Exn.capture (fn () =>  AdaSpark_Parse.parse_quiet entry @{context}
                                               (Input.string (prog lines))) ()
   of Exn.Exn (AdaSpark_Parse.Rejected _) => ()
    | Exn.Exn e => fail ("unexpected exception: " ^ Runtime.exn_message e)
    | Exn.Res _ => fail ("should have been rejected: " ^ prog lines))

val rejects = rejects_entry AdaSpark_Parse.Entry_Crate
val rejects_body = rejects_entry AdaSpark_Parse.Entry_Body
val rejects_expr = rejects_entry AdaSpark_Parse.Entry_Expr
\<close>

subsection\<open>Expressions\<close>

ML\<open>
val _ = roundtrip_expr ["A + B * C"]
val _ = roundtrip_expr ["A - B - C"]
val _ = roundtrip_expr ["(A + B) * C"]
val _ = roundtrip_expr ["-A * B"]
val _ = roundtrip_expr ["A & B & \"s\""]
val _ = roundtrip_expr ["A mod B rem C"]
val _ = roundtrip_expr ["abs X + 1"]
val _ = roundtrip_expr ["not A"]
val _ = roundtrip_expr ["A and then B or else C"]
val _ = roundtrip_expr ["A xor B"]
val _ = roundtrip_expr ["X /= Y"]
val _ = roundtrip_expr ["X <= Y"]
val _ = roundtrip_expr ["2 ** N"]
val _ = roundtrip_expr ["A in 1 .. 5 and B"]
val _ = roundtrip_expr ["X not in 1 | 2"]
val _ = roundtrip_expr ["X in A | B .. C"]
val _ = roundtrip_expr ["F (X, Y => 1)"]
val _ = roundtrip_expr ["A (I).B (J)"]
val _ = roundtrip_expr ["A (1 .. 3)"]
val _ = roundtrip_expr ["P.Q.R"]
val _ = roundtrip_expr ["P.Q.all"]
val _ = roundtrip_expr ["X'First"]
val _ = roundtrip_expr ["S.Top'Old + 1"]
val _ = roundtrip_expr ["F'Result"]
val _ = roundtrip_expr ["Integer'Last"]
val _ = roundtrip_expr ["T'(1, 2)"]
val _ = roundtrip_expr ["new T"]
val _ = roundtrip_expr ["null"]
val _ = roundtrip_expr ["'a'"]
val _ = roundtrip_expr ["\"a\"\"b\""]
val _ = roundtrip_expr ["16#FF# + 1_000"]
val _ = roundtrip_expr ["1.5e3"]
val _ = roundtrip_expr ["(1, 2, 3)"]
val _ = roundtrip_expr ["(others => 0)"]
val _ = roundtrip_expr ["(A => 1, B | C => 2, 3 .. 4 => 5)"]
val _ = roundtrip_expr ["(X with A => 1)"]
val _ = roundtrip_expr ["(X with delta A => 1)"]
val _ = roundtrip_expr ["(if A then 1 elsif B then 2 else 3)"]
val _ = roundtrip_expr ["(if A then B)"]
val _ = roundtrip_expr ["(case X is when 1 | 2 => A, when others => B)"]
val _ = roundtrip_expr ["(for all I in 1 .. N => A (I) > 0)"]
val _ = roundtrip_expr ["(for some I in reverse 1 .. N => A (I) = 0)"]
val _ = roundtrip_expr ["(for all E of A => E > 0)"]
val _ = roundtrip_expr ["(for all E of reverse A => E > 0)"]
val _ = roundtrip_expr ["(for some I in Integer range 1 .. 3 => P (I))"]
\<close>

text\<open>
  Ada is case insensitive: keywords may be written in any case, and are printed
  in lower case; identifiers are kept as written. The precedence of the
  relational operators is below the adding operators, \<open>in\<close> and \<open>not in\<close> bind
  like them, and \<open>**\<close> is not associative.\<close>

ML\<open>
val _ = reads_as_expr ["A AND THEN B OR ELSE C"] ["A and then B or else C"]
val _ = reads_as_expr ["A In 1 .. 5"] ["A in 1 .. 5"]
val _ = reads_as_expr ["not Foo_Bar"] ["not Foo_Bar"]
val _ = reads_as_expr ["(A+B)*C"] ["(A + B) * C"]
val _ = reads_as_expr ["X'first"] ["X'first"]
val _ = reads_as_expr ["F(1,2)"] ["F (1, 2)"]
val _ = rejects_expr ["2 ** 3 ** 4"]
val _ = rejects_expr ["A < B < C"]
val _ = rejects_expr ["A +"]
val _ = rejects_expr ["(A"]
\<close>

subsection\<open>Statements\<close>

ML\<open>
val _ = roundtrip_body ["null;"]
val _ = roundtrip_body ["X := 1;", "Y := X + 1;"]
val _ = roundtrip_body ["P (A, B => 2);"]
val _ = roundtrip_body ["Pkg.Proc;"]
val _ = roundtrip_body
  ["if A then", "   X := 1;", "elsif B then", "   null;", "else",
   "   Y := 2;", "end if;"]
val _ = roundtrip_body
  ["case X is", "   when 1 | 2 =>", "      A := 1;", "   when 3 .. 5 =>",
   "      null;", "   when others =>", "      B := 2;", "end case;"]
val _ = roundtrip_body ["loop", "   exit when X > 1;", "end loop;"]
val _ = roundtrip_body ["L : loop", "   exit L when X > 1;", "end loop L;"]
val _ = roundtrip_body
  ["while X < 3 loop", "   X := X + 1;", "end loop;"]
val _ = roundtrip_body ["for I in 1 .. 3 loop", "   null;", "end loop;"]
val _ = roundtrip_body
  ["for I in reverse 1 .. 3 loop", "   null;", "end loop;"]
val _ = roundtrip_body
  ["for I in Integer range 1 .. 3 loop", "   null;", "end loop;"]
val _ = roundtrip_body ["for E of A loop", "   null;", "end loop;"]
val _ = roundtrip_body
  ["declare", "   X : Integer := 1;", "begin", "   X := 2;", "exception",
   "   when others =>", "      null;", "end;"]
val _ = roundtrip_body ["B : begin", "   null;", "end B;"]
val _ = roundtrip_body ["raise Constraint_Error;"]
val _ = roundtrip_body ["raise Constraint_Error with \"x\";"]
val _ = roundtrip_body ["return;"]
val _ = roundtrip_body ["return X + 1;"]
val _ = roundtrip_body ["exit;"]
val _ = roundtrip_body ["pragma Assert (X > 0, \"msg\");"]
val _ = roundtrip_body
  ["pragma Loop_Invariant (for all I in A'Range => A (I) > 0);"]
val _ = reads_as_body ["IF A THEN X := 1; END IF;"]
  ["if A then", "   X := 1;", "end if;"]
val _ = reads_as_body ["-- a comment", "X := 1; -- another", "Y := 2;"]
  ["X := 1;", "Y := 2;"]
val _ = rejects_body ["X := ;"]
val _ = rejects_body ["if A then X := 1;"]
val _ = rejects_body ["loop null;"]
val _ = rejects_body ["X := 1"]
\<close>

subsection\<open>Declarations and program units\<close>

ML\<open>
val _ = roundtrip
  ["procedure P (X : access Integer; Y : not null access T) is", "begin",
   "   null;", "end P;"]
val _ = roundtrip
  ["package P is", "   type T is (A, B, C);", "   type R is record",
   "      X, Y : Integer;", "   end record;", "end P;"]
val _ = roundtrip
  ["package P is", "   type T is new Q with record", "      X : Integer;",
   "   end record;", "end P;"]
val _ = roundtrip
  ["package P is", "   type T is new Q with null record;", "end P;"]
val _ = roundtrip
  ["package P is", "   type T is abstract tagged limited private;",
   "private", "   type T is abstract tagged limited null record;", "end P;"]
val _ = roundtrip
  ["package P is", "   type A is array (Integer range <>) of Integer;",
   "   type B is array (1 .. 3, Boolean) of aliased Integer;", "end P;"]
val _ = roundtrip
  ["package P is", "   type A is access all Integer;",
   "   type B is not null access constant Integer;", "   type I;", "end P;"]
val _ = roundtrip
  ["package P is", "   type M is mod 2 ** 8;",
   "   type D is digits 6 range 0.0 .. 1.0;",
   "   type F is delta 0.01 range 0.0 .. 1.0;", "end P;"]
val _ = roundtrip
  ["package P is", "   E : exception;", "   N : constant := 5;",
   "   X : aliased constant Integer := 3;",
   "   Z : array (1 .. 3) of Integer;", "end P;"]
val _ = roundtrip
  ["package P is", "   for X'Size use 8;", "   pragma Pure;",
   "   use Ada.Text_IO;", "   use type T;", "end P;"]
val _ = roundtrip
  ["package P is",
   "   subtype S is Integer range 1 .. 3 with Static_Predicate => S /= 2;",
   "end P;"]
val _ = roundtrip
  ["package P is", "   type T is range 1 .. 10 with Size => 8;", "end P;"]
val _ = roundtrip
  ["package P is", "   type S (K : Kind := A) is record", "      X : Integer;",
   "      case K is", "         when A =>", "            Y : Integer;",
   "         when others =>", "            null;", "      end case;",
   "   end record;", "end P;"]
val _ = roundtrip
  ["package body P is", "begin", "   null;", "end P;"]
val _ = roundtrip
  ["package body P is", "   X : Integer;", "begin", "   X := 1;",
   "exception", "   when others =>", "      null;", "end P;"]
val _ = roundtrip
  ["with A;", "with B.C;", "limited with D;", "private with E;", "use A;",
   "use type B.C;", "procedure Main is", "begin", "   null;", "end Main;"]
val _ = roundtrip ["package P.Q is", "end P.Q;"]
val _ = roundtrip
  ["function F (X : Integer := 1; Y, Z : in out Integer) return Boolean",
   "   with Pre => X > 0,", "        Post => F'Result,",
   "        Global => null", "is", "begin", "   return True;", "end F;"]
val _ = roundtrip ["procedure P is null;"]
val _ = roundtrip ["function F return Integer is abstract;"]
val _ = roundtrip ["function F return Integer is (1);"]
val _ = roundtrip ["overriding procedure P (X : T);"]
val _ = roundtrip ["function \"+\" (L, R : T) return T;"]
val _ = roundtrip
  ["package P", "   with SPARK_Mode,", "        Abstract_State => S", "is",
   "   function F return Integer", "      with Global => (Input => S);",
   "end P;"]
\<close>

text\<open>The subprogram bodies of a package may carry aspects, and the constructs
  that are not (yet) supported are rejected rather than misread.\<close>

ML\<open>
val _ = reads_as ["PACKAGE P IS END P;"] ["package P is", "end P;"]
val _ = rejects ["package P is"]
val _ = rejects ["procedure P is begin null; end"]
val _ = rejects ["task T;"]
val _ = rejects ["generic type T is private; procedure P;"]
val _ = rejects ["package P is X : Integer := ; end P;"]
val _ = rejects ["package P is procedure Q renames R; end P;"]
val _ = rejects ["procedure P is begin goto L; end P;"]
\<close>

subsection\<open>Subtype indications\<close>

ML\<open>
val _ = roundtrip_type ["Integer"]
val _ = roundtrip_type ["Natural range 0 .. 10"]
val _ = roundtrip_type ["not null Foo"]
val _ = roundtrip_type ["Foo (1 .. 3)"]
\<close>

section\<open>The SPARK Sources of Isabelle\<close>

text\<open>
  The real test: the Ada sources (\<^verbatim>\<open>.ads\<close>, \<^verbatim>\<open>.adb\<close>) below Isabelle's own
  \<^verbatim>\<open>src/HOL/SPARK\<close> directory - the examples of the SPARK verification
  environment. Each file must parse as a source file, and print back to text
  that parses again to the same text. The files are SPARK 83/Ada 95 programs
  whose \<^verbatim>\<open>--#\<close> annotations are, for this parser, plain comments.
\<close>

ML\<open>
local
  fun ada_files p =
    if File.is_dir p
    then maps (fn n => ada_files (Path.append p (Path.basic n)))
           (sort_strings (File.read_dir p))
    else if exists (fn e => String.isSuffix e (Path.implode p))
              [".ads", ".adb"]
    then [p] else []

  val root = Path.explode "~~/src/HOL/SPARK"

  val files = if File.is_dir root then ada_files root else []

  fun check path =
    let
      val text = File.read path
      val name = Path.implode (Path.base path)
      fun parse t =
        AdaSpark_Parse.parse_quiet
          AdaSpark_Parse.Entry_Crate @{context} (Input.string t)
    in
      (case Exn.capture parse text of
         Exn.Exn (AdaSpark_Parse.Rejected msg) =>
           SOME (name ^ ": rejected: " ^ msg)
       | Exn.Exn e => SOME (name ^ ": " ^ Runtime.exn_message e)
       | Exn.Res NONE => SOME (name ^ ": no result")
       | Exn.Res (SOME r) =>
           let val p1 = AdaSpark_Pp.pp_root r
           in
             (case Exn.capture parse p1 of
                Exn.Res (SOME r2) =>
                  if AdaSpark_Pp.pp_root r2 = p1 then NONE
                  else SOME (name ^ ": not idempotent")
              | _ => SOME (name ^ ": the printed text does not parse"))
           end)
    end
in
  val corpus_size = length files
  val corpus_failures = map_filter I (Par_List.map check files)
  val _ =
    (writeln ("AdaSpark_Tests: " ^ string_of_int corpus_size
              ^ " SPARK source file(s) read, "
              ^ string_of_int (corpus_size - length corpus_failures)
              ^ " parsed and printed back, "
              ^ string_of_int (length corpus_failures) ^ " failure(s)");
     List.app fail corpus_failures)
end
\<close>

ML\<open>val _ = report_failures ()\<close>

end
