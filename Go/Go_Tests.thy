(******************************************************************************
 * Copyright (c) University of Paris-Saclay
 *
 * All rights reserved.
 *
 * Authors: Burkhart Wolff, Claude Sonnet 5.5
 *
 * This is an LLM-generated replication of the Isabelle/C version 2 design to
 * the programming language Go (language version 1.27). It provides an efficient
 * parser for Go, deeply integrated into the Isabelle/PIDE document model,
 * allowing external files as well as in-theory code-snippets which are
 * transparent to the underlying theory. It provides an API for the generated
 * AST’s, and an API to hook up semantic backends that compile these AST’s to
 * theory extensions in Isabelle/HOL. Members of the family come with a
 * Go-specific antiquotation mechanism allowing programmable links to the
 * semantic backends as necessary for support of program-annotations with HOL
 * formulas.
 *
 * This session is part of the Isabelle Programming Language Toolkit
 * (Isabelle/PLTk). The generation has been done with Claude Sonnet 5.5; while
 * the replicants come with a detailed (generated) test-suite for Go, I
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

theory Go_Tests
  imports Go_Parser
begin

section\<open>Parser-level Tests\<close>

text\<open>
  Exercised directly through \<^ML>\<open>Go_Parse.parse_loud\<close>/\<^ML>\<open>Go_Parse.parse_quiet\<close> and the
  pretty-printer \<^ML>\<open>Go_Pp.pp_root\<close>, before any Isar command exists. A program already in
  the pretty-printer's canonical layout (the layout of \<^verbatim>\<open>gofmt\<close> in its essentials: a tab per
  level of indentation, \<^verbatim>\<open>case\<close> at the indentation of its \<^verbatim>\<open>switch\<close>) must come back unchanged
  (\<^emph>\<open>round trip\<close>), and every accepted program must be a fixed point of parse-then-print
  (\<^emph>\<open>idempotence\<close>).
\<close>

ML\<open>
fun prog lines = String.concatWith "\n" lines

fun parse_entry entry s = Go_Parse.parse_loud entry @{context} (Input.string s)

fun show_entry entry s =
  (case parse_entry entry s of
     SOME r => Go_Pp.pp_root r
   | NONE => error "parser returned NONE")

val show = show_entry Go_Parse.Entry_File
val show_decls = show_entry Go_Parse.Entry_Decls
val show_stmts = show_entry Go_Parse.Entry_Stmts
val show_expr = show_entry Go_Parse.Entry_Expr
val show_type = show_entry Go_Parse.Entry_Type

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
  else error (string_of_int (length (!failures)) ^ " test(s) failed:\n\n"
              ^ space_implode "\n\n" (rev (!failures)))

fun roundtrip_with show' lines =
  let
    val s = prog lines
  in
    (case Exn.capture (idempotent_with show') lines of
       Exn.Res out => if out = s then ()
                      else fail ("round trip mismatch for:\n" ^ s ^ "\n--- got ---\n" ^ out)
     | Exn.Exn e => fail (Runtime.exn_message e ^ "\n  while reading:\n" ^ s))
  end

val roundtrip = roundtrip_with show
val roundtrip_decls = roundtrip_with show_decls
val roundtrip_stmts = roundtrip_with show_stmts
val roundtrip_expr = roundtrip_with show_expr
val roundtrip_type = roundtrip_with show_type

(* Reading "lines" must print as "expected" (a layout-normalising read). *)
fun reads_as_with show' lines expected =
  (case Exn.capture (fn () => show' (prog lines)) () of
     Exn.Res out => if out = prog expected then ()
                    else fail ("reads-as mismatch for:\n" ^ prog lines ^ "\n--- got ---\n" ^ out)
   | Exn.Exn e => fail (Runtime.exn_message e ^ "\n  while reading:\n" ^ prog lines))

val reads_as = reads_as_with show
val reads_as_stmts = reads_as_with show_stmts
val reads_as_expr = reads_as_with show_expr

fun rejects_entry entry lines =
  (case Exn.capture (fn () => Go_Parse.parse_quiet entry @{context} (Input.string (prog lines))) ()
   of Exn.Exn (Go_Parse.Rejected _) => ()
    | Exn.Exn e => fail ("unexpected exception: " ^ Runtime.exn_message e)
    | Exn.Res _ => fail ("should have been rejected: " ^ prog lines))

val rejects = rejects_entry Go_Parse.Entry_File
val rejects_stmts = rejects_entry Go_Parse.Entry_Stmts
val rejects_expr = rejects_entry Go_Parse.Entry_Expr
\<close>

subsection\<open>Expressions\<close>

ML\<open>
val _ = roundtrip_expr ["a + b * c - d / e % f"]
val _ = roundtrip_expr ["a && b || c == d"]
val _ = roundtrip_expr ["a != b && c <= d || e >= f"]
val _ = roundtrip_expr ["x << 2 | y &^ z ^ w"]
val _ = roundtrip_expr ["-a + +b - !c + ^d"]
val _ = roundtrip_expr ["*p + &q"]
val _ = roundtrip_expr ["<-ch"]
val _ = roundtrip_expr ["(a + b) * c"]
val _ = roundtrip_expr ["f(a, b)"]
val _ = roundtrip_expr ["f(a, b...)"]
val _ = roundtrip_expr ["f()"]
val _ = roundtrip_expr ["a[i][j]"]
val _ = roundtrip_expr ["a[i, j]"]
val _ = roundtrip_expr ["a[1:2]"]
val _ = roundtrip_expr ["a[:]"]
val _ = roundtrip_expr ["a[:n]"]
val _ = roundtrip_expr ["a[i:]"]
val _ = roundtrip_expr ["a[i:j:k]"]
val _ = roundtrip_expr ["a[:j:k]"]
val _ = roundtrip_expr ["x.(T)"]
val _ = roundtrip_expr ["x.(type)"]
val _ = roundtrip_expr ["pkg.Name.field.method(arg)"]
val _ = roundtrip_expr ["F[int](x)"]
val _ = roundtrip_expr ["F[[]int, map[string]T](x)"]
val _ = roundtrip_expr ["'a' + '\\n' + '\\u00e9'"]
val _ = roundtrip_expr ["\"a\\tb\" + `raw`"]
val _ = roundtrip_expr ["0x_FF + 0b1010 + 0o17 + 1_000"]
val _ = roundtrip_expr ["1.5e3 + .5 + 1. + 0x1p-2 + 0x.8p1"]
val _ = roundtrip_expr ["2i + 1.5i + 0x1p3i"]
val _ = roundtrip_expr ["[]int{1, 2, 3}"]
val _ = roundtrip_expr ["[...]string{\"a\", \"b\"}"]
val _ = roundtrip_expr ["map[string]int{\"a\": 1, \"b\": 2}"]
val _ = roundtrip_expr ["T{a: 1, b: 2}"]
val _ = roundtrip_expr ["pkg.T{}"]
val _ = roundtrip_expr ["Pair[int, string]{1, \"a\"}"]
val _ = roundtrip_expr ["[]T{{a: 1}, {b: 2}}"]
val _ = roundtrip_expr ["map[K][]V{k: {1, 2}}"]
val _ = roundtrip_expr ["[]*T{{}, nil}"]
val _ = roundtrip_expr ["struct{}{}"]
val _ = roundtrip_expr ["[][2]int{{1, 2}, {3, 4}}"]
val _ = roundtrip_expr ["chan int"]
val _ = roundtrip_expr ["<-chan int"]
val _ = roundtrip_expr ["chan<- int"]
val _ = roundtrip_expr ["chan<- chan int"]
val _ = roundtrip_expr ["chan (<-chan int)"]
val _ = roundtrip_expr ["make(chan<- int, 3)"]
val _ = roundtrip_expr ["map[string][]int"]
val _ = roundtrip_expr ["func(int) bool"]
val _ = roundtrip_expr ["[]func(int) int{f, g}"]
val _ = roundtrip_expr ["(*T)(p)"]
val _ = roundtrip_expr ["[]byte(s)"]
val _ = roundtrip_expr ["interface{}(x)"]
val _ = roundtrip_expr ["new(int)"]
val _ = roundtrip_expr ["struct {", "\ta int", "\tb, c string `json:\"b\"`", "}"]
val _ = roundtrip_expr ["interface {", "\tM(x int) int", "\tfmt.Stringer", "\t~int | string", "}"]
val _ = roundtrip_expr ["func(x int) int {", "\treturn x + 1", "}"]
val _ = roundtrip_expr ["func(a, b int, c ...string) (n int, err error) {", "\treturn", "}"]
val _ = roundtrip_expr ["func(int, string) (int, error)"]
val _ = roundtrip_expr ["func() func() int"]
\<close>

text\<open>The operators and the literals: the specification's five precedence levels, number literals
  with prefixes, underscores and imaginary suffixes. A conversion, a call and an instantiation are
  all syntactically calls and indexings; \<open>x.(type)\<close> is an expression that only a type switch
  accepts. A call with a trailing comma is a call.\<close>

ML\<open>
val _ = reads_as_expr ["f(a,", "b,", ")"] ["f(a, b)"]
val _ = reads_as_expr ["a[i,]"] ["a[i]"]
val _ = reads_as_expr ["[]int{1,", "2,", "}"] ["[]int{1, 2}"]
val _ = reads_as_expr ["x  +  y"] ["x + y"]
val _ = rejects_expr ["a +"]
val _ = rejects_expr ["(a"]
val _ = rejects_expr ["a b"]
val _ = rejects_expr ["f(,)"]
val _ = rejects_expr ["{1, 2}"]
val _ = rejects_expr ["x := 1"]
\<close>

subsection\<open>Statements\<close>

ML\<open>
val _ = roundtrip_stmts ["x := 1"]
val _ = roundtrip_stmts ["x, y := 1, 2"]
val _ = roundtrip_stmts ["x, y = y, x"]
val _ = roundtrip_stmts ["x += 1"]
val _ = roundtrip_stmts ["x <<= 2"]
val _ = roundtrip_stmts ["x &^= y"]
val _ = roundtrip_stmts ["x++"]
val _ = roundtrip_stmts ["x--"]
val _ = roundtrip_stmts ["ch <- v"]
val _ = roundtrip_stmts ["f(x)"]
val _ = roundtrip_stmts ["<-ch"]
val _ = roundtrip_stmts ["a[i], a[j] = a[j], a[i]"]
val _ = roundtrip_stmts ["go f(x)"]
val _ = roundtrip_stmts ["defer mu.Unlock()"]
val _ = roundtrip_stmts ["defer func() {", "\trecover()", "}()"]
val _ = roundtrip_stmts ["return"]
val _ = roundtrip_stmts ["return x, nil"]
val _ = roundtrip_stmts ["break"]
val _ = roundtrip_stmts ["continue outer"]
val _ = roundtrip_stmts ["goto L"]
val _ = roundtrip_stmts ["fallthrough"]
val _ = roundtrip_stmts ["{", "\tx := 1", "\t_ = x", "}"]
val _ = roundtrip_stmts ["if x > 0 {", "\treturn", "}"]
val _ = roundtrip_stmts ["if x := f(); x > 0 {", "\treturn", "} else if y {", "\tg()", "} else {",
          "\th()", "}"]
val _ = roundtrip_stmts ["for {", "\tbreak", "}"]
val _ = roundtrip_stmts ["for cond {", "\tx()", "}"]
val _ = roundtrip_stmts ["for i := 0; i < n; i++ {", "\tcontinue", "}"]
val _ = reads_as_stmts ["for ; i < n; {", "\ti++", "}"] ["for i < n {", "\ti++", "}"]
val _ = roundtrip_stmts ["for range ch {", "}"]
val _ = roundtrip_stmts ["for i := range n {", "\tf(i)", "}"]
val _ = roundtrip_stmts ["for k, v := range m {", "\tf(k, v)", "}"]
val _ = roundtrip_stmts ["for k, v = range m {", "\tf(k, v)", "}"]
val _ = roundtrip_stmts ["switch x {", "case 1, 2:", "\tf()", "case 3:", "\tg()", "default:",
          "\th()", "}"]
val _ = roundtrip_stmts ["switch {", "case x > 0:", "\tf()", "}"]
val _ = roundtrip_stmts ["switch x := f(); x {", "case 1:", "}"]
val _ = roundtrip_stmts ["switch y := v.(type) {", "case int:", "\tf(y)", "case string, bool:",
          "\tg()", "default:", "\th()", "}"]
val _ = roundtrip_stmts ["switch v.(type) {", "case nil:", "case []int, map[string]int:", "}"]
val _ = roundtrip_stmts ["select {", "case v := <-ch:", "\tf(v)", "case ch2 <- 1:", "\tg()",
          "case <-done:", "\treturn", "default:", "}"]
val _ = roundtrip_stmts ["L:", "for {", "\tbreak L", "}"]
val _ = roundtrip_stmts ["var x, y int = 1, 2"]
val _ = roundtrip_stmts ["var x = f()"]
val _ = roundtrip_stmts ["var x []string"]
val _ = roundtrip_stmts ["const (", "\tA = iota", "\tB", "\tC", ")"]
val _ = roundtrip_stmts ["type T struct {", "\ta int", "}"]
val _ = roundtrip_stmts ["type (", "\tA int", "\tB = string", ")"]
\<close>

text\<open>Semicolons: a newline after a token that can end a statement is a semicolon, one after any
  other token is not; semicolons and newlines separate statements alike; the last statement of a
  block needs neither. A composite literal in the header of an \<open>if\<close>, \<open>for\<close> or \<open>switch\<close> is a
  literal, if it is not a bare type name followed by its brace; the parentheses of \<open>(T{})\<close> make
  it one.\<close>

ML\<open>
val _ = reads_as_stmts ["x := 1; y := 2"] ["x := 1", "y := 2"]
val _ = reads_as_stmts ["x := f(a,", "\tb)", "y := 2"] ["x := f(a, b)", "y := 2"]
val _ = reads_as_stmts ["x := a +", "\tb"] ["x := a + b"]
val _ = reads_as_stmts ["if x { f() }"] ["if x {", "\tf()", "}"]
val _ = reads_as_stmts ["if x { f(); g() }"] ["if x {", "\tf()", "\tg()", "}"]
val _ = reads_as_stmts ["if x {", "\treturn", "}", "else_ := 1"] ["if x {", "\treturn", "}",
          "else_ := 1"]
val _ = reads_as_stmts ["if x == (T{}) { f() }"] ["if x == (T{}) {", "\tf()", "}"]
val _ = reads_as_stmts ["for _, v := range []int{1, 2} { f(v) }"]
          ["for _, v := range []int{1, 2} {", "\tf(v)", "}"]
val _ = reads_as_stmts ["for k := range map[string]int{\"a\": 1} { f(k) }"]
          ["for k := range map[string]int{\"a\": 1} {", "\tf(k)", "}"]
val _ = reads_as_stmts ["for _, t := range []struct{ a int }{{a: 1}} { f(t) }"]
          ["for _, t := range []struct {", "\ta int", "}{{a: 1}} {", "\tf(t)", "}"]
val _ = reads_as_stmts ["if f := func() bool { return true }; f() { g() }"]
          ["if f := func() bool {", "\treturn true", "}; f() {", "\tg()", "}"]
val _ = reads_as_stmts ["for _, b := range []byte(s) { f(b) }"]
          ["for _, b := range []byte(s) {", "\tf(b)", "}"]
val _ = reads_as_stmts ["switch x := v.(type) { }"] ["switch x := v.(type) {", "}"]
val _ = reads_as_stmts ["x := T{", "\ta: 1,", "\tb: 2,", "}"] ["x := T{a: 1, b: 2}"]
val _ = reads_as_stmts ["x := 1 // a comment", "y := 2 /* another */ // and one more"]
          ["x := 1", "y := 2"]
val _ = reads_as_stmts ["x := 1 /* a comment", "that spans two lines */ y := 2"] ["x := 1",
          "y := 2"]
val _ = reads_as_stmts ["if ; x { f() }"] ["if x {", "\tf()", "}"]
val _ = reads_as_stmts ["L:", ";"] ["L:;"]
val _ = rejects_stmts ["x :="]
val _ = rejects_stmts ["if x"]
val _ = rejects_stmts ["for i := 0; i < 3 {", "}"]
val _ = rejects_stmts ["1 := x"]
val _ = rejects_stmts ["a, b"]
val _ = rejects_stmts ["x := T{1,"]
val _ = rejects_stmts ["if x == T{} { f() }"]
\<close>

subsection\<open>Declarations and source files\<close>

ML\<open>
val _ = roundtrip ["package main"]
val _ = roundtrip ["package main", "", "import \"fmt\"", "", "func main() {",
          "\tfmt.Println(\"hi\")", "}"]
val _ = roundtrip ["package p", "", "import (", "\t\"fmt\"", "\tm \"math\"", "\t. \"strings\"",
          "\t_ \"embed\"", ")"]
val _ = roundtrip ["package p", "", "const N = 10"]
val _ = roundtrip ["package p", "", "const (", "\tA, B = 1, 2", "\tC float64 = 3", ")"]
val _ = roundtrip ["package p", "", "var x int", "", "var y, z = 1, \"a\"", "", "var (", "\ta int",
          "\tb = 2", ")"]
val _ = roundtrip ["package p", "", "type T int"]
val _ = roundtrip ["package p", "", "type A = B"]
val _ = roundtrip ["package p", "", "type S struct {", "\ta, b int", "\tc []string `json:\"c\"`",
          "\tfmt.Stringer", "\t*T", "}"]
val _ = roundtrip ["package p", "", "type I interface {", "\tM(x int) (int, error)",
          "\tfmt.Stringer", "\tError() string", "}"]
val _ = roundtrip ["package p", "", "type F func(int, ...string) error"]
val _ = roundtrip ["package p", "", "type M map[string][]*T"]
val _ = roundtrip ["package p", "", "type A [5]int"]
val _ = roundtrip ["package p", "", "type A [N * 2]int"]
val _ = roundtrip ["package p", "", "type C <-chan int"]
val _ = roundtrip ["package p", "", "func f()"]
val _ = roundtrip ["package p", "", "func f(x int) int {", "\treturn x", "}"]
val _ = roundtrip ["package p", "", "func f(a, b int, c string) (d int, err error) {", "\treturn",
          "}"]
val _ = roundtrip ["package p", "", "func f(int, string) (int, error) {", "\treturn 0, nil", "}"]
val _ = roundtrip ["package p", "", "func f(xs ...int) {", "}"]
val _ = roundtrip ["package p", "", "func f(a [3]int, b []int, c [N]int) {", "}"]
val _ = roundtrip ["package p", "", "func f(L List[int], P Pair[int, string]) {", "}"]
val _ = roundtrip ["package p", "", "func f(List[int], Pair[int, string]) {", "}"]
val _ = roundtrip ["package p", "", "func f(pkg.T, *pkg.U[int]) {", "}"]
val _ = roundtrip ["package p", "", "func (t T) m() {", "}"]
val _ = roundtrip ["package p", "", "func (t *T) m(x int) int {", "\treturn x", "}"]
val _ = roundtrip ["package p", "", "func (T) m() {", "}"]
val _ = roundtrip ["package p", "", "func (l *List[T]) Push(x T) {", "}"]
val _ = roundtrip ["package p", "", "func (l *List[K, V]) Get(k K) V {", "\treturn l.m[k]", "}"]
val _ = roundtrip ["package p", "", "func Map[T, U any](xs []T, f func(T) U) []U {", "\treturn nil",
          "}"]
val _ = roundtrip ["package p", "", "func Sum[N Number](xs ...N) N {", "\treturn 0", "}"]
val _ = roundtrip ["package p", "", "func Keys[M ~map[K]V, K comparable, V any](m M) []K {",
          "\treturn nil", "}"]
val _ = roundtrip ["package p", "", "func (t T) Map[P any](f func(P) P) T {", "\treturn t", "}"]
val _ = roundtrip ["package p", "", "func (l *List[T]) Do[U any](f func(T) U) []U {",
          "\treturn nil", "}"]
val _ = roundtrip ["package p", "", "var x = T{a.b: 1, c: 2}"]
val _ = roundtrip ["package p", "", "func f() {", "\tfor i := range 3 {", "\t\t_ = i", "\t}",
          "\tfor x := range seq {", "\t\t_ = x", "\t}", "}"]
val _ = roundtrip ["package p", "", "type Number interface {", "\t~int | ~int64 | ~float64", "}"]
val _ = roundtrip ["package p", "", "type List[T any] struct {", "\titems []T", "}"]
val _ = roundtrip ["package p", "", "type Pair[K comparable, V any] struct {", "\tk K", "\tv V",
          "}"]
val _ = roundtrip ["package p", "", "type Set[T comparable] map[T]struct{}"]
val _ = roundtrip ["package p", "", "type Alias[T any] = []T"]
val _ = roundtrip ["package p", "", "type G[P *int | string, Q any] struct{}"]
val _ = roundtrip ["package p", "", "type G2[P interface {", "\t*int", "}] struct{}"]
val _ = roundtrip ["package p", "", "type H[P, Q any] struct {", "\tp P", "\tq Q", "}"]
\<close>

text\<open>The ambiguity of \<open>type T[P *C] ...\<close> (an array length, or a type parameter?) is resolved as in
  Go's own parser: it is an array unless a comma follows the first expression.\<close>

ML\<open>
val _ = reads_as ["package p", "type A [N * 2]int"] ["package p", "", "type A [N * 2]int"]
val _ = reads_as ["package p", "type G[P *int | string, Q any] struct{}"]
          ["package p", "", "type G[P *int | string, Q any] struct{}"]
val _ = reads_as ["package p", "type G[P *int,] struct{}"] ["package p", "",
          "type G[P *int] struct{}"]
val _ = reads_as ["package p;import \"a\";func f(){}"]
          ["package p", "", "import \"a\"", "", "func f() {", "}"]
val _ = rejects ["func f() {}"]
val _ = rejects ["package"]
val _ = rejects ["package p", "func f() {"]
val _ = rejects ["package p", "var x int ="]
val _ = rejects ["package p", "x := 1"]
val _ = rejects ["package p", "type T struct { a int b int }"]
val _ = rejects ["package p", "func f(a, b) int, c {", "}"]
val _ = rejects ["package p", "func f(a int, b) {", "}"]
\<close>

subsection\<open>Declarations without a package clause\<close>

ML\<open>
val _ = roundtrip_decls ["func f() {", "}", "", "var x = 1"]
val _ = roundtrip_decls ["import \"fmt\""]
val _ = roundtrip_decls ["type T struct{}"]
val _ = rejects_entry Go_Parse.Entry_Decls ["x := 1"]
val _ = roundtrip_type ["[]map[string]*pkg.T[int]"]
val _ = roundtrip_type ["func(a, b int) (c int, err error)"]
val _ = roundtrip_type ["chan<- <-chan int"]
val _ = rejects_entry Go_Parse.Entry_Type ["x + y"]
\<close>

section\<open>The Go Sources\<close>

text\<open>
  The real test: if the environment variable \<^verbatim>\<open>GO_SRC\<close> names a Go source tree (for instance
  \<^verbatim>\<open>$GOROOT/src\<close>, or a checkout of \<^verbatim>\<open>github.com/golang/go\<close>), every \<^verbatim>\<open>.go\<close> file below it is
  read as a source file and printed back, and the printed text must read again to the same text;
  directories called \<^verbatim>\<open>testdata\<close> are skipped, as their files are mostly meant to be rejected. The
  standard library of Go 1.27 is 6\,821 files, and all of them pass. Without the variable the
  test does nothing.
\<close>

ML\<open>
local
  fun go_files p =
    if File.is_dir p
    then (if Path.implode (Path.base p) = "testdata" then []
          else maps (fn n => go_files (Path.append p (Path.basic n)))
                 (sort_strings (File.read_dir p)))
    else if String.isSuffix ".go" (Path.implode p) then [p] else []

  val root = getenv "GO_SRC"
  val files = if root = "" orelse not (File.is_dir (Path.explode root)) then []
              else go_files (Path.explode root)

  fun check path =
    let
      val text = File.read path
      val name = Path.implode path
      fun parse t = Go_Parse.parse_quiet Go_Parse.Entry_File @{context} (Input.string t)
    in
      (case Exn.capture parse text of
         Exn.Exn (Go_Parse.Rejected msg) => SOME (name ^ ": rejected: " ^ msg)
       | Exn.Exn e => SOME (name ^ ": " ^ Runtime.exn_message e)
       | Exn.Res NONE => SOME (name ^ ": no result")
       | Exn.Res (SOME r) =>
           let val p1 = Go_Pp.pp_root r
           in
             (case Exn.capture parse p1 of
                Exn.Res (SOME r2) =>
                  if Go_Pp.pp_root r2 = p1 then NONE else SOME (name ^ ": not idempotent")
              | _ => SOME (name ^ ": the printed text does not parse"))
           end)
    end
in
  val corpus_size = length files
  val corpus_failures = map_filter I (Par_List.map check files)
  val _ =
    if corpus_size = 0 then ()
    else
      (writeln ("Go_Tests: " ^ string_of_int corpus_size ^ " Go source file(s) read, "
                ^ string_of_int (corpus_size - length corpus_failures)
                ^ " parsed and printed back, "
                ^ string_of_int (length corpus_failures) ^ " failure(s)");
       List.app fail corpus_failures)
end
\<close>

ML\<open>val _ = report_failures ()\<close>

end
