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

theory Java_Tests
  imports Java_Parser
begin

section\<open>Parser-level Tests\<close>

text\<open>
  Exercised directly through \<^ML>\<open>Java_Parse.parse_loud\<close>/\<^ML>\<open>Java_Parse.parse_quiet\<close> and the
  pretty-printer \<^ML>\<open>Java_Pp.pp_root\<close>, before any Isar command exists. A fragment already in the
  pretty-printer's canonical layout (four blanks per level of indentation, braces at the end of
  the line, blanks around binary operators) must come back unchanged (\<^emph>\<open>round trip\<close>), and
  every accepted program must be a fixed point of parse-then-print (\<^emph>\<open>idempotence\<close>). The
  decisions that the layout stream makes - type arguments or comparison, cast or parenthesis,
  lambda, record pattern, keyword or name - are tested on the tokens it delivers (\<open>kinds\<close>) and
  on the tree that results.
\<close>

ML\<open>
fun prog lines = String.concatWith "\n" lines

fun parse_entry entry s = Java_Parse.parse_loud entry @{context} (Input.string s)

fun show_entry entry s =
  (case parse_entry entry s of
     SOME r => Java_Pp.pp_root r
   | NONE => error "parser returned NONE")

val show = show_entry Java_Parse.Entry_Unit
val show_decls = show_entry Java_Parse.Entry_Decls
val show_stmts = show_entry Java_Parse.Entry_Stmts
val show_expr = show_entry Java_Parse.Entry_Expr
val show_type = show_entry Java_Parse.Entry_Type

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
      val _ = (case getenv "JAVA_TEST_LOG" of "" => () | f => File.write (Path.explode f) msg)
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

val roundtrip = roundtrip_with show
val roundtrip_decls = roundtrip_with show_decls
val roundtrip_stmts = roundtrip_with show_stmts
val roundtrip_expr = roundtrip_with show_expr
val roundtrip_type = roundtrip_with show_type

(* Accepted, and a fixed point of read-then-print; the layout of the text is not compared. *)
fun accepts_with show' lines =
  (case Exn.capture (idempotent_with show') lines of
     Exn.Res _ => ()
   | Exn.Exn e => fail (Runtime.exn_message e ^ "\n  while reading:\n" ^ prog lines))

val accepts = accepts_with show
val accepts_decls = accepts_with show_decls
val accepts_stmts = accepts_with show_stmts
val accepts_expr = accepts_with show_expr

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
  (case Exn.capture
          (fn () => Java_Parse.parse_quiet entry @{context} (Input.string (prog lines))) ()
   of Exn.Exn (Java_Parse.Rejected _) => ()
    | Exn.Exn e => fail ("unexpected exception: " ^ Runtime.exn_message e)
    | Exn.Res _ => fail ("should have been rejected: " ^ prog lines))

val rejects = rejects_entry Java_Parse.Entry_Unit
val rejects_decls = rejects_entry Java_Parse.Entry_Decls
val rejects_stmts = rejects_entry Java_Parse.Entry_Stmts
val rejects_expr = rejects_entry Java_Parse.Entry_Expr
val rejects_type = rejects_entry Java_Parse.Entry_Type

(* the kinds of the tokens that the stream hands to the parser, for a fragment *)
fun kinds_with entry s =
  let
    val _ = Java_Parse.trace := []
    val _ = Java_Parse.trace_on := true
    val r = Exn.capture (fn () => parse_entry entry s) ()
    val _ = Java_Parse.trace_on := false
    val ks = rev (!Java_Parse.trace)
  in
    (case r of
       Exn.Res _ => map (fn k => (case String.fields (fn c => c = #">") k of [_,
         k1] => k1 | _ => k)) ks
     | Exn.Exn e => error (Runtime.exn_message e))
  end

fun kinds_are_with entry s expected =
  (case Exn.capture (kinds_with entry) s of
     Exn.Res ks => if space_implode " " ks = expected then ()
                   else fail ("token kinds of " ^ s ^ ": expected\n  " ^ expected ^ "\ngot\n  "
                              ^ space_implode " " ks)
   | Exn.Exn e => fail (Runtime.exn_message e ^ "\n  while reading:\n" ^ s))

val kinds_are = kinds_are_with Java_Parse.Entry_Expr
val kinds_are_stmts = kinds_are_with Java_Parse.Entry_Stmts
val kinds_are_decls = kinds_are_with Java_Parse.Entry_Decls

(* the tree of an expression or statement, for the checks of its shape *)
fun expr_of s = (case parse_entry Java_Parse.Entry_Expr s of
                   SOME (Java_Ast.Expr e) => e | _ => error ("not an expression: " ^ s))
fun stmts_of s = (case parse_entry Java_Parse.Entry_Stmts s of
                    SOME (Java_Ast.Stmts ss) => ss | _ => error ("not statements: " ^ s))
fun check name b = if b then () else fail ("FAILED: " ^ name)
\<close>

subsection\<open>Expressions\<close>

ML\<open>
val _ = roundtrip_expr ["a + b * c - d / e % f"]
val _ = roundtrip_expr ["a && b || c == d"]
val _ = roundtrip_expr ["a | b ^ c & d"]
val _ = roundtrip_expr ["a << 2 >> 3 >>> 4"]
val _ = roundtrip_expr ["x = y = z"]
val _ = roundtrip_expr ["x += 1"]
val _ = roundtrip_expr ["x >>>= 2"]
val _ = roundtrip_expr ["a ? b : c ? d : e"]
val _ = roundtrip_expr ["-x + +y - -z"]
val _ = roundtrip_expr ["!a && ~b"]
val _ = roundtrip_expr ["++i + j++"]
val _ = roundtrip_expr ["- -x"]
val _ = roundtrip_expr ["a[i][j + 1]"]
val _ = roundtrip_expr ["this.x"]
val _ = roundtrip_expr ["Outer.this.x"]
val _ = roundtrip_expr ["super.foo(1, 2)"]
val _ = roundtrip_expr ["Foo.super.bar()"]
val _ = roundtrip_expr ["a.b.c(d).e[f]"]
val _ = roundtrip_expr ["int.class"]
val _ = roundtrip_expr ["String[].class"]
val _ = roundtrip_expr ["void.class"]
val _ = roundtrip_expr ["java.util.List.class"]
val _ = roundtrip_expr ["\"text\" + 'c' + 1_000L + 0x1F + 0b101 + 1.5e3f + 0x1.8p3 + .5"]
val _ = roundtrip_expr ["null == (Object) null"]
val _ = roundtrip_expr ["true || false"]
\<close>

subsection\<open>Casts, parentheses and lambdas\<close>

text\<open>
  A \<open>(\<close> begins a cast, a lambda, a record pattern or a parenthesized expression, and the stream
  tells which by looking ahead: \<open>(a) - b\<close> is a subtraction, \<open>(String) -x\<close> is not a cast (the
  specification excludes a sign after a cast to a reference type), \<open>(int) -x\<close> is.
\<close>

ML\<open>
val _ = roundtrip_expr ["(int) x"]
val _ = roundtrip_expr ["(String) o"]
val _ = roundtrip_expr ["(List<String>) o"]
val _ = roundtrip_expr ["(Map.Entry<K, V>) o"]
val _ = roundtrip_expr ["(int[]) o"]
val _ = roundtrip_expr ["(A & B) x"]
val _ = roundtrip_expr ["(Runnable & Serializable) () -> {}"]
val _ = roundtrip_expr ["(int) -x"]
val _ = roundtrip_expr ["(int) (a + b)"]
val _ = roundtrip_expr ["(a) + b"]
val _ = roundtrip_expr ["(a) - b"]
val _ = roundtrip_expr ["(a)"]
val _ = roundtrip_expr ["((a) + b) * c"]
val _ = roundtrip_expr ["(T) (U) x"]
val _ = roundtrip_expr ["(String) s.trim()"]
val _ = roundtrip_expr ["(char) (c + 1)"]
val _ = roundtrip_expr ["x -> x + 1"]
val _ = roundtrip_expr ["(a, b) -> a + b"]
val _ = roundtrip_expr ["(int a, int b) -> a * b"]
val _ = roundtrip_expr ["(final String s) -> s"]
val _ = roundtrip_expr ["(var a, var b) -> a"]
val _ = roundtrip_expr ["() -> 0"]
val _ = roundtrip_expr ["_ -> 0"]
val _ = roundtrip_expr ["(_, y) -> y"]
val _ = roundtrip_expr ["x -> y -> x + y"]
val _ = roundtrip_expr ["f(x -> x, (a, b) -> a)"]
val _ = roundtrip_expr ["c ? x -> 1 : y -> 2"]
val _ = roundtrip_expr ["(Map<String, Integer> m) -> m.size()"]
val _ = accepts_expr ["() -> {", "    return 1;", "}"]
val _ = accepts_expr ["(String... xs) -> xs.length"]

(* the shapes *)
val _ = check "(a) - b is a subtraction"
  (case expr_of "(a) - b" of Java_Ast.EBinary (Java_Ast.Sub, Java_Ast.EParen _, _,
    _) => true | _ => false)
val _ = check "(String) -x is a subtraction"
  (case expr_of "(String) - x" of Java_Ast.EBinary (Java_Ast.Sub, Java_Ast.EParen _, _,
    _) => true | _ => false)
val _ = check "(int) -x is a cast"
  (case expr_of "(int) -x" of Java_Ast.ECast ([Java_Ast.TPrim (_, "int", _)], _,
    _) => true | _ => false)
val _ = check "(a) b is a cast"
  (case expr_of "(a) b" of Java_Ast.ECast _ => true | _ => false)
val _ = check "(a)(b) is a cast"
  (case expr_of "(a)(b)" of Java_Ast.ECast _ => true | _ => false)
val _ = check "a lambda body extends as far as it can"
  (case expr_of "x -> a + b" of Java_Ast.ELambda (_, _, Java_Ast.LBExpr (Java_Ast.EBinary _),
    _) => true
                              | _ => false)
val _ = check "a cast binds tighter than +"
  (case expr_of "(int) a + b" of Java_Ast.EBinary (Java_Ast.Add, Java_Ast.ECast _, _, _) => true
                               | _ => false)
val _ = check "a cast of a lambda"
  (case expr_of "(Runnable) () -> {}" of Java_Ast.ECast (_, Java_Ast.ELambda _,
    _) => true | _ => false)

val _ = kinds_are "(a) - b" "LPAREN IDENT RPAREN MINUS IDENT"
val _ = kinds_are "(a) b" "CASTLP IDENT RPAREN IDENT"
val _ = kinds_are "(a, b) -> c" "LAMLP IDENT COMMA IDENT RPAREN ARROW IDENT"
val _ = kinds_are "x -> y" "LAMID ARROW IDENT"
\<close>

subsection\<open>Type arguments and comparisons\<close>

text\<open>
  A \<open><\<close> after a name is a comparison unless a balanced list of type arguments follows that is
  itself followed by what a type may be followed by in that place. In an argument list the
  arguments of a call are expressions, so \<open>f(a < b, c > d)\<close> is two comparisons, as in javac.
\<close>

ML\<open>
val _ = roundtrip_expr ["a < b"]
val _ = roundtrip_expr ["a < b && c > d"]
val _ = roundtrip_expr ["i < n >> 1"]
val _ = roundtrip_expr ["f(a < b, c > d)"]
val _ = roundtrip_expr ["x.compare(a < b, c > d)"]
val _ = roundtrip_expr ["a < b ? c : d"]
val _ = roundtrip_expr ["List<String>::new"]
val _ = roundtrip_expr ["Map.Entry<K, V>::getKey"]
val _ = roundtrip_expr ["int[]::new"]
val _ = roundtrip_expr ["String[]::new"]
val _ = roundtrip_expr ["String::valueOf"]
val _ = roundtrip_expr ["this::foo"]
val _ = roundtrip_expr ["super::bar"]
val _ = roundtrip_expr ["Foo.super::baz"]
val _ = roundtrip_expr ["a.b::c"]
val _ = roundtrip_expr ["Foo::<T>bar"]
val _ = roundtrip_expr ["Collections.<String>emptyList()"]
val _ = roundtrip_expr ["this.<T>foo(x)"]
val _ = roundtrip_expr ["new Foo<>()"]
val _ = roundtrip_expr ["new Foo<Bar>(1)"]
val _ = roundtrip_expr ["new Foo<Bar<Baz>>(1)"]
val _ = roundtrip_expr ["new Outer<A>.Inner<B>()"]
val _ = roundtrip_expr ["outer.new Inner()"]
val _ = roundtrip_expr ["new int[3][]"]
val _ = roundtrip_expr ["new int[] {1, 2, 3}"]
val _ = roundtrip_expr ["new int[][] {{1}, {2, 3},}"]
val _ = roundtrip_expr ["new String[n][m]"]
val _ = roundtrip_expr ["new List<?>[3]"]

val _ = check "f(a < b, c > d) is a call with two comparisons"
  (case expr_of "f(a < b, c > d)" of
     Java_Ast.ECall (NONE, _, _, [Java_Ast.EBinary (Java_Ast.Lt, _, _, _),
                                  Java_Ast.EBinary (Java_Ast.Gt, _, _, _)], _) => true
   | _ => false)
val _ = check "i < n >> 1 is a comparison with a shift"
  (case expr_of "i < n >> 1" of Java_Ast.EBinary (Java_Ast.Lt, _, Java_Ast.EBinary (Java_Ast.Shr, _,
    _, _), _) => true
                              | _ => false)

val _ = kinds_are "a < b" "IDENT LT IDENT"
val _ = kinds_are "List<String>::new" "IDENT TLT IDENT TGT COLCOL NEW"
val _ = kinds_are "new A<B<C>>()" "NEW IDENT TLT IDENT TLT IDENT TGT TGT LPAREN RPAREN"
val _ = kinds_are "new A<B<C<D>>>()"
  "NEW IDENT TLT IDENT TLT IDENT TLT IDENT TGT TGT TGT LPAREN RPAREN"
val _ = kinds_are "f(a < b, c > d)" "IDENT LPAREN IDENT LT IDENT COMMA IDENT GT IDENT RPAREN"
\<close>

subsection\<open>Patterns, switch and the contextual keywords\<close>

ML\<open>
val _ = roundtrip_expr ["o instanceof String"]
val _ = roundtrip_expr ["o instanceof String s"]
val _ = roundtrip_expr ["o instanceof final String s"]
val _ = roundtrip_expr ["o instanceof List<?> l && l.isEmpty()"]
val _ = roundtrip_expr ["o instanceof Point(int x, int y)"]
val _ = roundtrip_expr ["o instanceof Box(Point(var x, _), String s)"]
val _ = roundtrip_expr ["o instanceof Box<String>(var s)"]
val _ = roundtrip_expr ["o instanceof Pair<?, ?>(var a, var b) && a != null"]
val _ = roundtrip_expr ["x instanceof A ? foo((B) y) : bar(z)"]
val _ = roundtrip_expr ["(x instanceof A ? 1 : 2) + 3"]

val _ = check "instanceof with a record pattern"
  (case expr_of "o instanceof Point(int x, int y)" of
     Java_Ast.EInstanceof (_, Java_Ast.PRecord (_, [Java_Ast.PType _, Java_Ast.PType _], _),
       _) => true
   | _ => false)

val _ = kinds_are "o instanceof Point(int x, int y)"
  "IDENT INSTANCEOF IDENT RECLP INT IDENT COMMA INT IDENT RPAREN"
val _ = kinds_are "x instanceof A ? f(y) : g(z)"
  "IDENT INSTANCEOF IDENT QUESTION IDENT LPAREN IDENT RPAREN COLON IDENT LPAREN IDENT RPAREN"

(* switch, old and new style, with patterns, guards and yield *)
val _ = accepts_expr ["switch (x) {", "    case 1, 2 -> \"a\";", "    case 3 -> {",
  "        yield \"b\";",
                      "    }", "    default -> \"c\";", "}"]
val _ = accepts_expr ["switch (o) {", "    case null -> 0;",
  "    case String s when s.length() > 3 -> 1;",
                      "    case Point(int x, int y) -> x + y;", "    case Integer i -> i;",
                      "    case Color c when (c == RED) -> 2;", "    default -> throw new X();",
                        "}"]
val _ = accepts_expr ["switch (o) {", "    case null, default -> 0;", "}"]
val _ = accepts_expr ["switch (x) {", "    case 1:", "    case 2:", "        yield 3;",
  "    default:",
                      "        yield 4;", "}"]
val _ = accepts_stmts ["switch (x) {", "    case A:", "        foo();", "        break;",
  "    case B: {", "        bar();", "    }",
                       "    default:", "}"]
val _ = accepts_stmts ["switch (day) {", "    case MONDAY, FRIDAY -> foo();",
  "    case TUESDAY -> { bar(); }",
                       "    default -> throw new Error();", "}"]
val _ = kinds_are_stmts "switch (o) { case Foo f when f.x > 0 -> 1; default -> 2; }"
  ("SWITCH LPAREN IDENT RPAREN LBRACE CASE IDENT IDENT WHEN IDENT PERIOD IDENT GT INT_LIT ARROW "
   ^ "INT_LIT SEMI DEFAULT ARROW INT_LIT SEMI RBRACE")
val _ = kinds_are_stmts "yield 1;" "YIELD INT_LIT SEMI"
val _ = kinds_are_stmts "{ yield = 1; yield(2); }"
  "LBRACE IDENT ASSIGN INT_LIT SEMI YIELD LPAREN INT_LIT RPAREN SEMI RBRACE"
\<close>

subsection\<open>Statements\<close>

ML\<open>
val _ = roundtrip_stmts ["int x = 1, y[] = {2};"]
val _ = roundtrip_stmts ["final int[][] g = new int[3][];"]
val _ = roundtrip_stmts ["List<String> xs = new ArrayList<>();"]
val _ = roundtrip_stmts ["Map<String, List<Integer>> m;"]
val _ = roundtrip_stmts ["Map.Entry<K, V>[] es;"]
val _ = roundtrip_stmts ["var x = 1;"]
val _ = roundtrip_stmts ["@Deprecated final var y = foo();"]
val _ = roundtrip_stmts ["a.b.C d;"]
val _ = roundtrip_stmts ["x = y;"]
val _ = roundtrip_stmts ["foo(a, b);"]
val _ = roundtrip_stmts ["i++;"]
val _ = roundtrip_stmts ["--i;"]
val _ = roundtrip_stmts ["new Foo();"]
val _ = roundtrip_stmts ["a.b().c = 1;"]
val _ = roundtrip_stmts ["lbl: x = 1;"]
val _ = roundtrip_stmts [";"]
val _ = roundtrip_stmts ["return;"]
val _ = roundtrip_stmts ["return x + 1;"]
val _ = roundtrip_stmts ["throw new Error();"]
val _ = roundtrip_stmts ["assert a : \"b\";"]
val _ = roundtrip_stmts ["break outer;"]
val _ = roundtrip_stmts ["continue;"]
val _ = roundtrip_stmts ["if (a)", "    b();", "else", "    c();"]
val _ = roundtrip_stmts ["if (a) {", "    b();", "} else if (c) {", "    d();", "} else {",
  "    e();", "}"]
val _ = roundtrip_stmts ["while (a)", "    b();"]
val _ = roundtrip_stmts ["do {", "    a();", "} while (b);"]
val _ = roundtrip_stmts ["for (int i = 0, j = 1; i < n; i++, j--) {", "    f(i);", "}"]
val _ = accepts_stmts ["for (;;) {}"]
val _ = roundtrip_stmts ["for (i = 0; i < n;)", "    f();"]
val _ = roundtrip_stmts ["for (String s : xs) {", "    f(s);", "}"]
val _ = roundtrip_stmts ["for (final var e : m.entrySet()) {", "    f(e);", "}"]
val _ = roundtrip_stmts ["for (Map.Entry<K, V> e : m.entrySet()) {", "    f(e);", "}"]
val _ = roundtrip_stmts ["synchronized (this) {", "    f();", "}"]
val _ = roundtrip_stmts ["try {", "    f();", "} catch (IOException | RuntimeException e) {",
  "    g(e);", "} finally {", "    h();", "}"]
val _ = roundtrip_stmts ["try (var r = open(); InputStream in = r.in();) {", "    f(in);", "}"]
val _ = accepts_stmts ["try (this.r; other) {}"]
val _ = accepts_stmts ["class Local {", "    int x;", "}"]
val _ = accepts_stmts ["record P(int x, int y) {}"]
val _ = accepts_stmts ["enum E { A, B }"]
val _ = accepts_stmts ["interface I { void m(); }"]
val _ = accepts_stmts ["final class L extends Base implements I {}"]
val _ = accepts_stmts ["this(1, 2);"]
val _ = accepts_stmts ["super();"]
val _ = accepts_stmts ["outer.super(x);"]
val _ = accepts_stmts ["<T>this(x);"]
val _ = accepts_stmts ["int x = 1;", "foo(x);", "super(x);"]
val _ = accepts_stmts ["o = switch (x) { case 1 -> 2; default -> 3; };"]

val _ = kinds_are_stmts "List<String> xs;" "IDENT TLT IDENT TGT IDENT SEMI"
val _ = kinds_are_stmts "var x = 1;" "VAR IDENT ASSIGN INT_LIT SEMI"
val _ = kinds_are_stmts "var = 1;" "IDENT ASSIGN INT_LIT SEMI"
val _ = kinds_are_stmts "int[] a;" "INT EMPTYBRK IDENT SEMI"
val _ = kinds_are_stmts "a[0] = 1;" "IDENT LBRACK INT_LIT RBRACK ASSIGN INT_LIT SEMI"
val _ = kinds_are_stmts "record R(int x) {}" "RECORD IDENT LPAREN INT IDENT RPAREN LBRACE RBRACE"
val _ = kinds_are_stmts "record = 1;" "IDENT ASSIGN INT_LIT SEMI"
\<close>

subsection\<open>Declarations\<close>

ML\<open>
val _ = roundtrip_decls ["int x;"]
val _ = roundtrip_decls ["private static final long serialVersionUID = 1L;"]
val _ = accepts_decls ["public void run() {}"]
val _ = accepts_decls ["abstract int f(int a, String... rest) throws IOException, X;"]
val _ = accepts_decls
  ["<T extends Comparable<? super T>> T max(Collection<? extends T> c) { return null; }"]
val _ = accepts_decls ["public <K, V extends List<K>> Map<K, V> m() { return null; }"]
val _ = accepts_decls ["Foo(int x) { this.x = x; }"]
val _ = accepts_decls ["<T> Foo(T x) {}"]
val _ = accepts_decls ["void m(Foo this) {}"]
val _ = accepts_decls ["int f()[] { return null; }"]
val _ = accepts_decls ["static { init(); }"]
val _ = accepts_decls ["{ init(); }"]
val _ = accepts_decls [";"]
val _ = accepts_decls ["@Override public String toString() { return \"x\"; }"]
val _ = accepts_decls ["@SuppressWarnings({\"a\", \"b\"}) @A(x = 1, y = @B) int f;"]
val _ = accepts_decls
  ["class A<T extends Number & Comparable<T>> extends B<T> implements C, D<T> {}"]
val _ = accepts_decls ["sealed interface S permits A, B {}"]
val _ = accepts_decls ["non-sealed class C extends P {}"]
val _ = accepts_decls ["sealed abstract class S permits X, Y {}"]
val _ = accepts_decls ["record Point(int x, int y) {", "    Point {",
  "        if (x < 0) throw new X();", "    }", "}"]
val _ = accepts_decls ["record Box<T>(T value) implements Wrapper<T> {}"]
val _ = accepts_decls ["record V(int... xs) {}"]
val _ = accepts_decls ["enum Color { RED, GREEN(1) { void f() {} }, BLUE; int x; }"]
val _ = accepts_decls ["enum E { A, B, }"]
val _ = accepts_decls ["enum E implements I { A; }"]
val _ = accepts_decls ["enum E { ; int x; }"]
val _ = accepts_decls ["interface I extends J, K {", "    int C = 1;", "    void m();",
  "    default void d() {}",
                       "    static void s() {}", "    private void p() {}", "}"]
val _ = accepts_decls ["@interface A { int value() default 1; String[] names() default {\"a\"}; }"]
val _ = accepts_decls ["@interface B { Class<?> c(); A a() default @A; }"]
val _ = accepts_decls
  ["class Outer { class Inner {} static class Nested<T> {} interface I {} enum E { X } }"]
val _ = accepts_decls ["Object o = new Object() { int x; void f() {} };"]
val _ = accepts_decls ["Runnable r = () -> { run(); };"]
val _ = accepts_decls ["int[] a = {1, 2,}, b[] = {{1}};"]
val _ = accepts_decls ["List<String>[] ls;"]
val _ = accepts_decls ["java.util.Map.Entry<String, Integer> e;"]
val _ = accepts_decls ["Outer<A>.Inner<B> x;"]
val _ = accepts_decls ["void f(Map<String, List<Integer>> m, int[]... xs) {}"]
val _ = accepts_decls ["void g(@Nullable String s, final int n) {}"]

val _ = kinds_are_decls "<T> void f(T x) {}"
  "TLT IDENT TGT VOID IDENT LPAREN IDENT IDENT RPAREN LBRACE RBRACE"
val _ = kinds_are_decls "class A<T> {}" "CLASS IDENT TLT IDENT TGT LBRACE RBRACE"
val _ = kinds_are_decls "class A implements B<C>, D<E<F>> {}"
  "CLASS IDENT IMPLEMENTS IDENT TLT IDENT TGT COMMA IDENT TLT IDENT TLT IDENT TGT TGT LBRACE RBRACE"
val _ = kinds_are_decls "sealed interface S permits A, B {}"
  "SEALED INTERFACE IDENT PERMITS IDENT COMMA IDENT LBRACE RBRACE"
val _ = kinds_are_decls "non-sealed class C {}" "NONSEALED CLASS IDENT LBRACE RBRACE"
val _ = kinds_are_decls "@Override <T> void f() {}"
  "AT IDENT TLT IDENT TGT VOID IDENT LPAREN RPAREN LBRACE RBRACE"
val _ = kinds_are_decls "@A(x) long y;" "AT IDENT LPAREN IDENT RPAREN LONG IDENT SEMI"
\<close>

subsection\<open>Compilation units\<close>

ML\<open>
val _ = roundtrip ["package a.b;", "", "import java.util.List;",
  "import static java.lang.Math.max;",
                   "import java.io.*;", "import static java.util.Map.*;",
                     "import module java.base;", "",
                   "class A {", "    int x;", "}", ""]
val _ = accepts ["@Ann package p;", "class A {}"]
val _ = accepts ["class A {}", "class B {}", "interface I {}"]
val _ = accepts ["import java.util.*;", "void main() {", "    System.out.println(\"hi\");", "}"]
val _ = accepts ["import java.util.*;", "String greeting = \"hi\";",
  "void main() { println(greeting); }",
                 "class Helper {}"]
val _ = accepts ["module m.n {", "    requires transitive java.base;", "    requires static x.y;",
                 "    exports a.b to c.d, e.f;", "    opens a.c;", "    uses a.b.S;",
                 "    provides a.b.S with a.c.I, a.c.J;", "}"]
val _ = accepts ["@Deprecated open module m {}"]
val _ = accepts ["module module { requires open; requires transitive; exports to; }"]
val _ = accepts
  ["class A { void module() {} int open; int to; int with; int record; int var; int when; }"]
val _ = accepts ["class A { void f() { int yield = 1; yield++; } }"]
val _ = accepts
  ["class A { void f() { var var = 1; var record = 2; var sealed = 3; var permits = 4; } }"]
val _ = accepts [""]
val _ = rejects ["package a;", "package b;"]
val _ = rejects ["class A {}", "import x.Y;"]
val _ = rejects ["module m {}", "class A {}"]
val _ = rejects ["module m {}", "module n {}"]
\<close>

subsection\<open>Rejected input\<close>

ML\<open>
val _ = rejects ["class {}"]
val _ = rejects ["class A { int x = ; }"]
val _ = rejects ["class A { void f( {} }"]
val _ = rejects ["class A { int; }"]
val _ = rejects_expr ["a +"]
val _ = rejects_expr ["("]
val _ = rejects_expr ["x = (int);"]
val _ = rejects_expr ["f(,)"]
val _ = rejects_expr ["1 = 2"]
val _ = rejects_expr ["a++ ++"]
val _ = rejects_expr ["new int[]"]
val _ = rejects_expr ["new Foo"]
val _ = rejects_stmts ["x = ;"]
val _ = rejects_stmts ["if (a) int x = 1;"]
val _ = rejects_stmts ["int x = 1"]
val _ = rejects_stmts ["for (int i = 0; i < n) {}"]
val _ = rejects_stmts ["switch (x) { case 1 -> 2; case 3: 4; }"]
val _ = rejects_stmts ["else x();"]
val _ = rejects_stmts ["foo(;"]
val _ = rejects_decls ["int f() ="]
val _ = rejects_type ["int["]
val _ = rejects_decls ["void f() { break }"]
\<close>

subsection\<open>The platform\<close>

text\<open>
  The real test: if the environment variable \<^verbatim>\<open>JAVA_SRC\<close> names a directory with Java sources
  (for instance the \<^verbatim>\<open>src.zip\<close> of a JDK, which is part of Isabelle's own JDK, unpacked:
  \<^verbatim>\<open>unzip $ISABELLE_JDK_HOME/lib/src.zip -d /tmp/jdksrc\<close>), every \<^verbatim>\<open>.java\<close> file below it is
  read as a compilation unit and printed back; the printed text must have the very tokens of the
  source and must read again to the same text. The sources of OpenJDK 25 are 15\,371 files, and
  all of them pass. Without the variable the test does nothing.
\<close>

ML\<open>
local
  fun java_files p =
    if File.is_dir p
    then maps (fn n => java_files (Path.append p (Path.basic n))) (sort_strings (File.read_dir p))
    else if String.isSuffix ".java" (Path.implode p) then [p] else []

  val root = getenv "JAVA_SRC"
  val files = if root = "" orelse not (File.is_dir (Path.explode root)) then []
              else java_files (Path.explode root)

  fun check_file path =
    let
      val name = Path.implode path
      val text = File.read path
      fun toks t = String.concat (Java_Parse.lex_texts @{context} (Input.string t))
      fun parse t =
        Java_Parse.parse_quiet Java_Parse.Entry_Unit @{context}
          (Input.source true t (Position.file name, Position.none))
    in
      (case Exn.capture parse text of
         Exn.Exn (Java_Parse.Rejected msg) => SOME (name ^ ": rejected: " ^ msg)
       | Exn.Exn e => SOME (name ^ ": " ^ Runtime.exn_message e)
       | Exn.Res NONE => SOME (name ^ ": no result")
       | Exn.Res (SOME r) =>
           let val p1 = Java_Pp.pp_root r
           in
             (case Exn.capture parse p1 of
                Exn.Res (SOME r2) =>
                  if Java_Pp.pp_root r2 <> p1 then SOME (name ^ ": not idempotent")
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
      (writeln ("Java_Tests: " ^ string_of_int corpus_size ^ " Java source file(s) read, "
                ^ string_of_int (corpus_size - length corpus_failures)
                ^ " parsed and printed back, "
                ^ string_of_int (length corpus_failures) ^ " failure(s)");
       List.app fail corpus_failures)
end
\<close>

ML\<open>val _ = report_failures ()\<close>

end
