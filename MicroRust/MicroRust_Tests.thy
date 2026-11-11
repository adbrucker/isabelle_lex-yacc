(******************************************************************************
 * Copyright (c) University of Paris-Saclay
 *
 * All rights reserved.
 *
 * Authors: Burkhart Wolff, Claude Sonnet 5.5
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

theory MicroRust_Tests
  imports MicroRust_Parser
begin

section\<open>Parser-level Tests\<close>

text\<open>
  Exercised directly through
  \<^ML>\<open>MicroRust_Parse.parse_loud\<close>/\<^ML>\<open>MicroRust_Parse.parse_quiet\<close> and the
  pretty-printer \<^ML>\<open>MicroRust_Pp.pp_root\<close>, before any Isar command exists. A
  program already in the pretty-printer's canonical layout must come back
  unchanged (\<^emph>\<open>round trip\<close>), and every accepted program must be a fixed point of
  parse-then-print (\<^emph>\<open>idempotence\<close>).
\<close>

ML\<open>
fun prog lines = String.concatWith "\n" lines

fun parse_entry entry s =
  MicroRust_Parse.parse_loud entry @{context} (Input.string s)

fun show_entry entry s =
  (case parse_entry entry s of
     SOME r => MicroRust_Pp.pp_root r
   | NONE => error "parser returned NONE")

val show = show_entry MicroRust_Parse.Entry_Crate
val show_body = show_entry MicroRust_Parse.Entry_Body
val show_expr = show_entry MicroRust_Parse.Entry_Expr

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

fun rejects_entry entry lines =
  (case Exn.capture (fn () =>  MicroRust_Parse.parse_quiet entry @{context} 
                                               (Input.string (prog lines))) () 
   of Exn.Exn (MicroRust_Parse.Rejected _) => ()
    | Exn.Exn e => fail ("unexpected exception: " ^ Runtime.exn_message e)
    | Exn.Res _ => fail ("should have been rejected: " ^ prog lines))

val rejects = rejects_entry MicroRust_Parse.Entry_Crate
val rejects_body = rejects_entry MicroRust_Parse.Entry_Body
\<close>

subsection\<open>Expressions\<close>

ML\<open>
val _ = roundtrip_expr ["a + b * c"]
val _ = roundtrip_expr ["a - b - c"]
val _ = roundtrip_expr ["(a + b) * c"]
val _ = roundtrip_expr ["x = y + 1"]
val _ = roundtrip_expr ["x += 1"]
val _ = roundtrip_expr ["x >>= 2"]
val _ = roundtrip_expr ["x <<= 2"]
val _ = roundtrip_expr ["a >> 1 > b"]
val _ = roundtrip_expr ["a > b >> 1"]
val _ = roundtrip_expr ["a >= b"]
val _ = roundtrip_expr ["a <= b && c != d || e == f"]
val _ = roundtrip_expr ["-x + !y"]
val _ = roundtrip_expr ["*x = &mut y"]
val _ = roundtrip_expr ["&&x"]
val _ = roundtrip_expr ["a as u32 + 1"]
val _ = roundtrip_expr ["f(x, y)(z)"]
val _ = roundtrip_expr ["a.b.c(d, e).f"]
val _ = roundtrip_expr ["t.0.1"]
val _ = roundtrip_expr ["a[i][j]"]
val _ = roundtrip_expr ["x?.y?"]
val _ = roundtrip_expr ["0..n"]
val _ = roundtrip_expr ["a..=b"]
val _ = roundtrip_expr ["..n"]
val _ = roundtrip_expr ["a.."]
val _ = roundtrip_expr ["(a, b)"]
val _ = roundtrip_expr ["(a,)"]
val _ = roundtrip_expr ["()"]
val _ = roundtrip_expr ["[1, 2, 3]"]
val _ = roundtrip_expr ["[0; 16]"]
val _ = roundtrip_expr ["Foo { a: 1, b }"]
val _ = roundtrip_expr ["Foo { a: 1, ..base }"]
val _ = roundtrip_expr ["Foo::Bar::new(1)"]
val _ = roundtrip_expr ["Vec::<u8>::new()"]
val _ = roundtrip_expr ["x.collect::<Vec<u8>>()"]
val _ = roundtrip_expr ["<T as Trait>::f(x)"]
val _ = roundtrip_expr ["|x| x + 1"]
val _ = roundtrip_expr ["|x, y| x + y"]
val _ = roundtrip_expr ["|| 1"]
val _ = roundtrip_expr ["move |x: u8| x"]
val _ = roundtrip_expr ["panic!(\"boom\")"]
val _ = roundtrip_expr ["vec![0; n]"]
val _ = roundtrip_expr ["matches!(x, Some(_))"]
val _ = roundtrip_expr ["if a {", "    1", "} else {", "    2", "}"]
val _ = roundtrip_expr ["if a == B {", "    1", "} else {", "    2", "}"]
val _ = roundtrip_expr
  ["if let Some(x) = o {", "    x", "} else {", "    0", "}"]
val _ = roundtrip_expr
  ["if let Foo { a } = o {", "    a", "} else {", "    0", "}"]
val _ = roundtrip_expr
  ["match x {", "    1 => a,", "    2 | 3 => b,", "    _ => c,", "}"]
val _ = roundtrip_expr
  ["match x {", "    Some(y) if y > 0 => y,", "    None => 0,", "}"]
val _ = roundtrip_expr
  ["match x {", "    Foo { a, .. } => a,", "    [first, .., last] => first,",
   "    1..=5 => 0,", "}"]
val _ = roundtrip_expr ["for i in 0..n {", "    s += i;", "}"]
val _ = roundtrip_expr ["for i in v.iter() {", "    s += i;", "}"]
val _ = roundtrip_expr ["while x < 10 {", "    x += 1;", "}"]
val _ = roundtrip_expr ["'a: loop {", "    break 'a;", "}"]
val _ = roundtrip_expr ["loop {", "    break 1;", "}"]
val _ = roundtrip_expr ["return x"]
val _ = roundtrip_expr ["unsafe {", "    *p", "}"]
val _ = roundtrip_expr ["x.0.1"]
val _ = roundtrip_expr ["0xFF_u8 + 1_000u32"]
val _ = roundtrip_expr ["\"a\\n\" == s"]
val _ = roundtrip_expr ["'x' == c"]
val _ = roundtrip_expr ["b'x'"]
val _ = roundtrip_expr ["r#\"raw \" string\"#"]
\<close>

subsection\<open>Function bodies, statements, items\<close>

ML\<open>
val _ = roundtrip_body ["let mut x = 0;", "x += 1;", "x"]
val _ = roundtrip_body ["let (a, b) = p;", "let c: u32 = a + b;", "c"]
val _ = roundtrip_body ["let Some(x) = o else {", "    return 0;", "};", "x"]
val _ = roundtrip_body ["const k = 4;", "k"]
val _ = roundtrip_body ["#[fuel(n)] while x < 10 {", "    x += 1;", "}", "*x"]
val _ = roundtrip_body ["if a {", "    b();", "}", "*x"]
val _ = roundtrip_body
  ["if a {", "    b();", "} else {", "    c();", "};", "d()"]
val _ = roundtrip_body ["match x {", "    1 => a,", "    _ => b,", "}", "-1"]
val _ = roundtrip_body ["{", "    f();", "}", "g()"]
val _ = roundtrip_body
  ["match x {", "    1 => {", "        a", "    },", "    _ => {", "        b",
   "    },", "}"]
val _ = roundtrip_body
  ["yield;", "log \092<llangle>a\092<rrangle> \092<llangle>b\092<rrangle>;",
   "x"]
val _ = roundtrip_body
  ["let v = \092<llangle>0 :: nat\092<rrangle>;",
   "v + \092<epsilon>\092<open>n\092<close>"]
val _ = roundtrip_body [""]
val _ = roundtrip_body ["let mut (a, b) = p;", "a"]
val _ = roundtrip_body ["f(ref, 1)"]
val _ = roundtrip_body ["(", "    a = 1;", "    a", ")"]
val _ = roundtrip_body ["assert!((", "    let _ = false;", "    x", "))"]
val _ = roundtrip_body ["trace!(l\092<llangle>\"x\"\092<rrangle>)"]
val _ = roundtrip_expr
  ["match x {", "    &mut (a, b) => a,", "    &x => x,", "}"]
val _ = roundtrip ["fn f(x: u32, y: &mut u32) -> u32 {", "    x + *y", "}"]
val _ = roundtrip
  ["pub fn f<T: Copy + Eq>(self, x: T) -> T where T: Default {", "    x", "}"]
val _ = roundtrip ["fn f(&self);"]
val _ = roundtrip ["struct S {", "    a: u32,", "    pub b: Vec<Vec<u8>>,", "}"]
val _ = roundtrip ["struct T(u32, pub u8);"]
val _ = roundtrip ["struct U;"]
val _ = roundtrip
  ["enum E {", "    A,", "    B(u32),", "    C {", "        x: u8,", "    },",
   "    D = 3,", "}"]
val _ = roundtrip
  ["impl<T> Foo<T> {", "    fn new() -> Self {", "        Self { x: 0 }",
   "    }", "}"]
val _ = roundtrip
  ["impl Trait for Foo {", "    fn f(&self) -> u32 {", "        1", "    }",
   "}"]
val _ = roundtrip ["trait Tr: Sized {", "    fn f(&self) -> u32;", "}"]
val _ = roundtrip
  ["const N: usize = 4;", "static mut X: u32 = 0;", "type A = Vec<u8>;"]
val _ = roundtrip ["use a::b::{c, d as e, *};", "use f::g;"]
val _ = roundtrip ["mod m {", "    fn f() {}", "}"]
\<close>

subsection\<open>Rejection\<close>

ML\<open>
val _ = rejects ["fn f( {"]
val _ = rejects ["struct S { a: }"]
val _ = rejects_body ["let = 1;"]
val _ = rejects_body ["a < b < c;"]
val _ = rejects_body ["if x { 1 "]
\<close>


section\<open>The AutoCorrode Sources\<close>

text\<open>
  The real test: the uRust bodies of the AutoCorrode framework. Every \<open>\<lbrakk> ... \<rbrakk>\<close>
  of the \<open>.thy\<close> files below the directory named by the environment variable
  \<^verbatim>\<open>AUTOCORRODE_HOME\<close> (a checkout of \<^verbatim>\<open>github.com/awslabs/AutoCorrode\<close>) is read as
  a function body; a body that parses must print back to text that parses again
  to the same text. Without the variable the test does nothing. A few of the
  bracketed texts are not uRust at all (they are Isabelle's own \<open>\<lbrakk> A; B \<rbrakk>\<close>
  assumptions in statements, or Isabelle text in comments); they are listed
  explicitly in \<open>not_urust\<close>.
\<close>

ML\<open>
local
  val lbrakk = "\092<lbrakk>"
  val rbrakk = "\092<rbrakk>"

  fun thy_files dir =
    let
      fun walk p =
        if File.is_dir p
        then maps (fn n => walk (Path.append p (Path.basic n)))
          (sort_strings (File.read_dir p))
        else if String.isSuffix ".thy" (Path.implode p) then [p] else []
    in walk dir end

  (* the bracketed texts of a file, with the line each starts on *)
  fun bodies text =
    let
      fun find pat s = let val (pre, post) = Substring.position pat s
        in if Substring.isEmpty post then NONE else SOME (pre, post) end
      fun lines_in ss =
        length (filter
                (fn c => c = #"\n") (String.explode (Substring.string ss)))
      fun loop line s acc =
        (case find lbrakk s of
           NONE => rev acc
         | SOME (pre, post) =>
             let
               val line' = line + lines_in pre
               val after = Substring.triml (size lbrakk) post
             in
               (case find rbrakk after of
                  NONE => rev acc
                | SOME (body, rest) =>
                    loop (line' + lines_in body)
                      (Substring.triml (size rbrakk) rest)
                      ((line', Substring.string body) :: acc))
             end)
    in loop 1 (Substring.full text) [] end

  (* The bracketed texts that are not uRust: assumptions of Isabelle statements,
     mixfix templates (a lone "_", "_-_"), Isabelle text with "..." *)
  val not_urust =
    [("BraunTrees.thy", 1351), ("Sorted_Association_List.thy", 101),
     ("Basic_Micro_Rust.thy", 67),
     ("Basic_Micro_Rust.thy", 70), ("MLKEM_Zq.thy", 126),
       ("Raw_Physical_Memory_Trie_Core.thy", 295),
     ("Raw_Physical_Memory_Trie_Core.thy", 2647),
       ("Raw_Physical_Memory_Trie_Core.thy", 3117),
     ("Raw_Physical_Memory_Trie_PP.thy", 19),
       ("Raw_Physical_Memory_Trie_PP.thy", 20),
     ("Raw_Physical_Memory_Trie_PP.thy", 21),
       ("Raw_Physical_Memory_Trie_PP.thy", 22),
     ("Micro_Rust_Notations_Test.thy", 6),
       ("Micro_Rust_Notations_Test.thy", 102),
     ("Micro_Rust_Shallow_Embedding.thy", 227), ("SSA.thy", 33),
       ("Simple_Word_Enum_uRust.thy", 20),
     ("Permissioned_Heap.thy", 706), ("Separation_Algebra.thy", 36),
       ("Separation_Algebra.thy", 37),
     ("Separation_Algebra.thy", 38), ("Shareable_Value.thy", 267),
       ("Tutorial_SLWorked.thy", 267),
     ("Tutorial_SLWorked.thy", 271), ("Tutorial_SLWorked.thy", 279),
       ("Tutorial_SLWorked.thy", 283)]

  val root = getenv "AUTOCORRODE_HOME"

  val items =
    if root = "" orelse not (File.is_dir (Path.explode root)) then []
    else
      maps (fn f => let val name = Path.implode (Path.base f)
                    in map (fn (line, b) => (name, line, b))
                      (bodies (File.read f)) end)
        (thy_files (Path.explode root))

  fun check (name, line, body) =
    let
      fun parse t =
        MicroRust_Parse.parse_quiet
          MicroRust_Parse.Entry_Body @{context} (Input.string t)
      val where_ = name ^ ":" ^ string_of_int line
    in
      (case Exn.capture parse body of
         Exn.Exn (MicroRust_Parse.Rejected msg) =>
           SOME (where_, "rejected: " ^ msg, body)
       | Exn.Exn e => SOME (where_, Runtime.exn_message e, body)
       | Exn.Res NONE => SOME (where_, "no result", body)
       | Exn.Res (SOME r) =>
           let val p1 = MicroRust_Pp.pp_root r
           in
             (case Exn.capture parse p1 of
                Exn.Res (SOME r2) =>
                  if MicroRust_Pp.pp_root r2 = p1 then NONE
                    else SOME (where_, "not idempotent", body)
              | _ => SOME (where_, "the printed text does not parse", p1))
           end)
    end
in
  val corpus_size = length items
  val corpus_failures = map_filter I (Par_List.map check items)
  fun is_not_urust (w, _, _) =
    (case String.fields (fn c => c = #":") w of
       [name, line] =>
         member (op =) not_urust (name, the_default 0 (Int.fromString line))
     | _ => false)
  val (expected_failures, unexpected_failures) =
    List.partition is_not_urust corpus_failures
  val _ =
    if corpus_size = 0 then ()
    else
      (writeln ("MicroRust_Tests: " ^ string_of_int corpus_size
                ^ " AutoCorrode body(ies) read, " ^
                string_of_int (corpus_size - length corpus_failures)
                  ^ " parsed and printed back, " ^
                string_of_int (length expected_failures)
                  ^ " not uRust (listed), " ^
                string_of_int (length unexpected_failures)
                  ^ " unexpected failure(s)");
       List.app (fn (w, msg, body) => fail (w ^ ": " ^ msg ^ "\n      " ^
                   (String.concatWith
                    "\n      " (take 6
                                (String.fields
                                 (fn c => c =
                                  #"\n") body))))) unexpected_failures)
end
\<close>

ML\<open>val _ = report_failures ()\<close>

end
