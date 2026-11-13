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

theory Java_Cmd_Tests
  imports Java Java_Tests
begin

section\<open>Command-level Tests\<close>

ML\<open>
fun check name b = if b then writeln ("OK: " ^ name)
  else error ("FAILED: " ^ name)
\<close>

subsection\<open>Accepting commands\<close>

java_ident\<open>foo_bar\<close>

java_expr\<open>(a + b) * c\<close>

java_type\<open>Map<String, List<int[]>>\<close>

java\<open>
package main;

import java.util.List;

public class Main {
    static int inc(int n) {
        return n + 1;
    }

    public static void main(String[] args) {
        System.out.println(inc(41));
    }
}
\<close>

text\<open>Class body declarations without a class around them, a block statement list as it stands
  between the braces of a method, and a compact source file.\<close>

java_decl\<open>
int twice(int n) { return 2 * n; }
int limit = twice(21);
\<close>

java_stmt\<open>
int x = 0;
if (x < 10) {
    x++;
}
\<close>

java\<open>
import java.util.*;

String greeting = "hi";

void main() {
    System.out.println(greeting);
}
\<close>

java_reject\<open>
class A {
    void f( {
}
\<close>

java_decl_reject\<open>x = 1;\<close>

java_stmt_reject\<open>x = ;\<close>

java_expr_reject\<open>a +\<close>

java_type_reject\<open>int[\<close>

java_ident_reject\<open>a b\<close>

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
    val root = the (Java_Parse.parse_quiet entry (Proof_Context.init_global thy) source)
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

(* the counts below are those of a program alone; the platform has its own tests (see the end) *)
val fresh = Config.put_global AnaEval.java_src "none" (JEnv.reset_jenv @{theory})

(* the number of entity markups: declarations plus resolved uses *)
fun entities_in entry text = count "entity" (reports_in entry fresh text)
fun ent_with entry name text n =
  let val got = entities_in entry text
  in if got = n then writeln ("OK: " ^ name)
     else fail ("FAILED: " ^ name ^ ": expected " ^ Int.toString n ^ ", got " ^ Int.toString got)
  end
val ent = ent_with Java_Parse.Entry_Decls
val ents = ent_with Java_Parse.Entry_Stmts
val entu = ent_with Java_Parse.Entry_Unit

val _ = ent "a field" "int f;" 1
val _ = ent "a parameter" "void f(int x) { }" 2
val _ = ent "a parameter and its use" "int f(int x) { return x; }" 3
val _ = check "an undeclared name is not marked"
  (entities_in Java_Parse.Entry_Decls "void f() { y(); h.x(); }" = 1
   andalso count "bad" (reports_in Java_Parse.Entry_Decls fresh "void f() { y(); }") = 0)
(* members are visible throughout their class, whatever the order *)
val _ = ent "forward reference to a method" "void a() { b(); } void b() {}" 3
val _ = ent "forward reference to a field" "int g() { return v; } int v;" 3
val _ = ent "a field used in a method" "class A { int x; void f() { x = 1; } }" 4
val _ = ent "a type used in its own class" "class A { A next; A() {} }" 4
(* overloading: a call is linked only if the arity leaves one candidate *)
val _ = ent "two methods of the same arity"
  "void m(int a) {} void m(String s) {} void t() { m(1); }" 5
val _ = ent "arities that tell the methods apart"
  "void m(int a) {} void m(int a, int b) {} void t() { m(1); }" 7
val _ = ent "a variable-arity method" "void m(int a, int... r) {} void t() { m(1); m(1, 2, 3); }" 6
val _ = ent "a method of an inner class hides the methods of the outer one"
  "class A { void f() {} class B { void f(int x) {} void g() { f(); } } }" 6
(* locals *)
val _ = ent "local variable" "void f() { int x = 1; x = x + 1; }" 4
val _ = ent "a variable is in scope in its own initializer" "void f() { int x = x; }" 3
val _ = ent "block scope" "void f() { { int x = 1; } x = 2; }" 2
val _ = ent "a for variable" "void f() { for (int i = 0; i < 3; i++) { g(i); } i = 1; }" 5
val _ = ent "an enhanced for variable" "void f(int[] a) { for (int x : a) { use(x); } }" 5
val _ = ent "a catch parameter" "void f() { try { } catch (Exception e) { g(e); } }" 3
val _ = ent "lambdas"
  "void f() { Runnable r = () -> {}; Function<Integer, Integer> g = x -> x + 1; }" 5
val _ = ent "a resource" "void f() { try (var r = open(); var s = r) { s.x(); } }" 5
val _ = ent "a local class" "void f() { class L { } L l = null; }" 4
val _ = ent "an anonymous class" "Object o = new Object() { int y; int z() { return y; } };" 4
val _ = ent "a labelled loop" "void f() { l: for (;;) { break l; } }" 3
val _ = ent "a qualified name uses its first element" "void f(int a) { a.b.c(); }" 3
(* pattern variables follow the flow *)
val _ = ent "instanceof and &&"
  "boolean f(Object o) { return o instanceof String s && s.isEmpty(); }" 5
val _ = ent "negation, return, and the rest of the block"
  "void f(Object o) { if (!(o instanceof String s)) return; use(s); }" 5
val _ = ent "a pattern variable of an if ends with the statement"
  "void f(Object o) { if (o instanceof String s) { use(s); } use(s); }" 5
val _ = ent "a pattern variable is not in scope in the else branch"
  "void f(Object o) { if (o instanceof String s) { } else { use(s); } }" 4
val _ = ent "the unnamed pattern declares nothing"
  "void f(Object o) { if (o instanceof String _) { } }" 3
val _ = ent "a conditional expression"
  "int f(Object o) { return o instanceof String s ? s.length() : 0; }" 5
val _ = ent "a record pattern"
  "int f(Object o) { return o instanceof Point(int x, int y) ? x + y : 0; }" 7
val _ = ent "switch patterns and guards"
  ("int f(Object o) { return switch (o) { case String s when s.isEmpty() -> 1; "
   ^ "case Integer i -> i; default -> 0; }; }") 7
val _ = ent "old-style switch: locals stay for the next group"
  "void f(int k) { switch (k) { case 1: int x = 1; use(x); break; case 2: x = 2; } }" 6
(* type parameters *)
val _ = ent "a type parameter of a class" "class B<T> { T t; }" 4
val _ = ent "a type parameter of a method" "<T> T id(T x) { return x; }" 6
(* classes *)
val _ = ent "an enum" "enum E { A, B; E next() { return A; } }" 6
val _ = ent "an enum constant with a body" "enum E { A { void f() {} } }" 3
val _ = ent "a record sees its components"
  "record P(int x, int y) { int sum() { return x + y; } }" 6
val _ = ent "a constructor" "class A { A(int x) { this.y = x; } int y; }" 6
val _ = ent "an interface" "interface I { int C = 1; default int f() { return C; } }" 4
(* imports *)
(* selections and calls are resolved with types, when that is certain *)
val _ = ent "a field of a parameter" "class A { int x; void f(A a) { a.x = 1; } }" 7
val _ = ent "a method of a parameter" "class A { void m() {} void t(A a) { a.m(); } }" 7
val _ = ent "the types of the arguments select the overload"
  "class A { void m(int a) {} void m(String s) {} void t() { m(1); } }" 7
val _ = ent "the most specific overload"
  ("class P {} class Q extends P {} "
   ^ "class U { void m(P p) {} void m(Q q) {} void t(Q q) { m(q); } }") 15
val _ = ent "a static field through its class" "class A { static int C; int f() { return A.C; } }" 5
val _ = ent "an enum constant through its enum"
  "enum E { X, Y } class U { E e = E.X; }" 8
val _ = ent "an inherited method"
  "class B { void m() {} } class C extends B { void t() { m(); } }" 6
val _ = ent "an inherited field" "class B { int v; } class C extends B { int t() { return v; } }" 6
val _ = ent "a field of the class itself, whatever the superclass"
  "class C extends Unknown { int v; int t() { return this.v; } }" 4
val _ = ent "a member that no known class has is not linked"
  "class C extends Unknown { int t(C c) { return c.w; } }" 5
val _ = ent "an inherited member is not linked if another supertype is unknown"
  "class B { int v; } class C extends B implements Unk { int t(C c) { return c.v; } }" 8
val _ = ent "type arguments are substituted"
  ("class Box<T> { T v; T get() { return v; } } "
   ^ "class U { int f(Box<U> b) { return b.get().f(null); } }") 15
val _ = ent "the length of an array is not a field" "int f(int[] a) { return a.length; }" 3
val _ = ent "the type of a var" "class A { int x; void f() { var a = new A(); a.x = 1; } }" 7
val _ = ent "the variable of an enhanced for"
  "class A { int x; void f(A[] as) { for (A a : as) { a.x = 1; } } }" 10
val _ = ent "the type of a pattern variable"
  "class A { int x; boolean f(Object o) { return o instanceof A a && a.x > 0; } }" 9
val _ = ent "a cast" "class A { int x; int f(Object o) { return ((A) o).x; } }" 7
val _ = ent "a chain of calls"
  "class A { A self() { return this; } int x; int f() { return self().self().x; } }" 8
val _ = ent "an anonymous class inherits"
  "class B { int v; } class U { Object o = new B() { int w() { return v; } }; }" 7
val _ = ent "the type argument of a generic method is inferred"
  "class A { <T> T id(T x) { return x; } int v; int f(A a) { return id(a).v; } }" 14

val _ = entu "an imported type" "import java.util.List; class A { List l; }" 4
val _ = entu "a static import"
  "import static java.lang.Math.max; class A { int f() { return max(1, 2); } }" 4
val _ = entu "an on-demand import declares nothing" "import java.util.*; class A { List l; }" 2
val _ = entu "a compact source file" "void main() { greet(); } void greet() {}" 3
\<close>

subsection\<open>The platform\<close>

text\<open>
  The classes of the platform are read from the sources of a JDK. The first part of the tests uses a
  small tree written to a temporary directory (so they do not depend on a JDK), the second the JDK
  of Isabelle if there is one. A member of a platform class is linked to its declaration, a private
  one is not seen, and a name that is not in the tree changes nothing.\<close>

ML\<open>
fun write_tree dir files =
  List.app (fn (name, text) =>
              let val path = Path.append dir (Path.explode name)
              in (Isabelle_System.make_directory (Path.dir path); File.write path text) end) files

val fake_tree =
  [("java/lang/Object.java",
    "package java.lang; public class Object { public String toString() { return null; } "
    ^ "public boolean equals(Object o) { return false; } private int secret; }"),
   ("java/lang/String.java",
    "package java.lang; public final class String { public int length() { return 0; } "
    ^ "int hidden() { return 0; } }"),
   ("java/lang/Enum.java",
    "package java.lang; public abstract class Enum<E extends Enum<E>> "
    ^ "{ public final int ordinal() { return 0; } }"),
   ("java/util/Collection.java",
    "package java.util; public interface Collection<E> { int size(); }"),
   ("java/util/List.java",
    "package java.util; public interface List<E> extends Collection<E> { E get(int i); }"),
   ("java/util/Map.java",
    "package java.util; public interface Map<K,V> { Entry<K,V> firstEntry(); "
    ^ "interface Entry<K,V> { K getKey(); V getValue(); } }"),
   ("java/util/Objects.java",
    "package java.util; public final class Objects "
    ^ "{ public static boolean isNull(Object o) { return o == null; } }")]

fun ent_in thy entry name text n =
  let val got = count "entity" (reports_in entry thy text)
  in if got = n then writeln ("OK: " ^ name)
     else fail ("FAILED: " ^ name ^ ": expected " ^ Int.toString n ^ ", got " ^ Int.toString got)
  end

fun platform_tests thy =
  let
    val dec = ent_in thy Java_Parse.Entry_Decls
    val unit = ent_in thy Java_Parse.Entry_Unit
  in
    dec "a method of a platform class" "int f(String s) { return s.length(); }" 5;
    dec "a member that is not public is not seen"
      "int f(String s) { return s.hidden() + s.secret; }" 5;
    unit "a method of a supertype"
      "import java.util.List; class A { int f(List<String> l) { return l.size(); } }" 8;
    unit "the type arguments are substituted"
      ("import java.util.List; class A { String f(List<A> l) { return l.get(0).toString(); } }")
      10;
    dec "every class has the methods of Object" "class A { String f() { return toString(); } }" 4;
    dec "an enum has the methods of Enum" "enum E { X; int f() { return ordinal(); } }" 4;
    unit "a static method through its class"
      "import java.util.Objects; class A { boolean f(A a) { return Objects.isNull(a); } }" 8;
    unit "an on-demand import"
      "import java.util.*; class A { int f(List<A> l) { return l.size(); } }" 7;
    unit "a member class"
      ("import java.util.Map; class A { Object f(Map<A,A> m) "
       ^ "{ return m.firstEntry().getKey(); } }") 11;
    dec "a qualified type" "int f(java.util.List<String> l) { return l.size(); }" 5;
    dec "a qualified name in an expression"
      "boolean f(Object o) { return java.util.Objects.isNull(o); }" 5;
    unit "a class that is not in the tree" "import foo.Bar; class A { int f(Bar b) { return b.x; } }" 6
  end

val _ = Isabelle_System.with_tmp_dir "java_tree" (fn dir =>
  let val _ = write_tree dir fake_tree
  in platform_tests (Config.put_global AnaEval.java_src (File.platform_path dir) fresh) end)

val _ =
  if AnaEval.platform_source @{theory} = "" then writeln "no JDK sources: the JDK tests are skipped"
  else
    let
      val thy = Config.put_global AnaEval.java_src "" fresh
      val dec = ent_in thy Java_Parse.Entry_Decls
      val unit = ent_in thy Java_Parse.Entry_Unit
    in
      dec "the JDK: a method of String" "int f(String s) { return s.length(); }" 5;
      dec "the JDK: System.out.println" "void f() { System.out.println(\"x\"); }" 4;
      unit "the JDK: a list of strings"
        "import java.util.*; class A { int f(List<String> l) { return l.get(0).length(); } }" 8;
      dec "the JDK: a qualified generic type"
        "int f(java.util.Map<String,Integer> m) { return m.get(\"a\").intValue(); }" 7
    end
\<close>

subsection\<open>Antiquotations and navigation\<close>

text\<open>
  A comment attaches to the node starting at the next token; with no navigation string the
  handler sees that node (here the whole statement).\<close>

java\<open>
class A {
    int f(int x, int y) {
        //@ probe_ast
        //@ highlight
        x = x + y;
        return x;
    }
}
\<close>

ML\<open>
val _ = check "probe_ast sees the commented statement"
  (Java_Pp.pp_root (!JAVA_AST) = "x = x + y;")
\<close>

text\<open>
  Navigation: \<open>[u]\<close> and \<open>[uu]\<close> re-target to enclosing nodes, \<open>[d]\<close>/\<open>[rd]\<close> to the first child,
  \<open>[rrd]\<close> to the second (as in C11, the first \<open>r\<close> only starts the cursor at 1).\<close>

java\<open>
class A {
    int f(int x, int y) {
        //@ probe_ast[uu]
        //@ highlight[u]
        x = x + y;
        return x;
    }
}
\<close>

ML\<open>
val _ = check "[uu] reaches the enclosing method"
  (String.isPrefix "int f(int x, int y) {" (Java_Pp.pp_root (!JAVA_AST)))
\<close>

java\<open>
class A {
    int f(int x, int y) {
        //@ probe_ast[d]
        x = x + y;
        return x;
    }
}
\<close>

ML\<open>
val _ = check "[d] reaches the first child" (Java_Pp.pp_root (!JAVA_AST) = "x = x + y")
\<close>

java\<open>
class A {
    int f(int x, int y) {
        //@ probe_ast[drrd]
        x = x + y;
        return x;
    }
}
\<close>

ML\<open>
val _ = check "[drrd] reaches the second child of the first child"
  (Java_Pp.pp_root (!JAVA_AST) = "x + y")
\<close>

text\<open>In a statement list: the comment before a statement is attached to it.\<close>

java_stmt\<open>
int x = 0;
//@ probe_ast
x++;
\<close>

ML\<open>
val _ = check "an antiquotation in a statement list" (Java_Pp.pp_root (!JAVA_AST) = "x++;")
\<close>

text\<open>
  An \<open>@\<close> in running comment text, in Javadoc for instance, is not an antiquotation (it would
  fail with an unregistered tag), whereas a tag with a cartouche body is one anywhere in a comment,
  also in a block comment:\<close>

java_decl\<open>
/**
 * Docs. Mail me at someone@example.org, or see @param x and @return.
 * @param x the argument
 */
int g(int x) { return x; }
\<close>

ML\<open>
val ORDER = Unsynchronized.ref ([] : int list)
val record = let fun probe (_, _, l) (_ : string * Position.T) thy = (ORDER := l :: !ORDER; thy)
             in JEnv.store_antiq ("record", JEnv.lift_theory_antiq probe) end
\<close>
setup\<open>record\<close>

text\<open>Evaluation order is by \<open>level\<close>, not by position:\<close>

java_stmt\<open>
//@ record(1)
int a = 1;
/* an ordinary comment @record(1) \<open>\<close> */
//@ record(0)
int b = 2;
/*@ record(1) */
int c = 3;
\<close>

ML\<open>
val _ = check "levels order the evaluation" (rev (!ORDER) = [0, 1, 1, 1])
\<close>

text\<open>The real Isabelle machinery: a \<open>definition\<close> in a comment, then a \<open>lemma\<close> proved about it,
  then a \<open>term\<close> mentioning it.\<close>

java_decl\<open>
// A constant of the Java program, mirrored in HOL:
//@ definition \<open>java_limit :: nat where "java_limit = 100"\<close>
//@ lemma(1) \<open>java_fact: "java_limit * 2 = 200" by (simp add: java_limit_def)\<close>
//@ term(2) \<open>java_limit + 1\<close>
static final int LIMIT = 100;
\<close>

thm java_limit_def java_fact

subsection\<open>\<open>java_file\<close> on external sources\<close>

java_file \<open>examples/Hello.java\<close>

ML\<open>
val thy_h = @{theory}
val key_h =
  (case JEnv.get (Context.Theory thy_h) of JEnv.mk {units, ...} =>
   JEnv.ast_store_key thy_h (units - 1))
val path_h = Path.append (Resources.master_directory thy_h) (Path.explode "examples/Hello.java")
val _ = check "Hello: stored as a compilation unit"
  (case JEnv.get_ast key_h thy_h of
     SOME (Java_Ast.Source (Java_Ast.Unit (SOME (_, pkg), imports, Java_Ast.Types decls, _))) =>
       map Java_Ast.ident_name pkg = ["demo"] andalso length imports = 1 andalso length decls = 1
   | _ => false)
val _ = check "Hello: the source text stored is the file's own"
  (JEnv.get_source key_h thy_h = SOME (File.read path_h))
\<close>

java_file \<open>examples/Stack.java\<close>

java_file \<open>examples/Shapes.java\<close>

java_file \<open>examples/Flow.java\<close>

java_file \<open>examples/Compact.java\<close>

java_file \<open>examples/module-info.java\<close>

ML\<open>
val thy_f = @{theory}
val names_f = (case JEnv.get (Context.Theory thy_f) of JEnv.mk {names, ...} => names)
val _ = check "the types of the compilation units stay"
  (Symtab.defined names_f "type:Hello" andalso Symtab.defined names_f "type:Stack"
   andalso Symtab.defined names_f "type:Shapes" andalso Symtab.defined names_f "type:Flow")
val _ = check "a compact file leaves its fields behind" (Symtab.defined names_f "greeting")
val _ = check "a module declaration leaves nothing"
  (not (Symtab.defined names_f "type:demo"))
\<close>

subsection\<open>Export\<close>

java\<open>
class Exported {
    int x = 1;
    int f() { return x + 1; }
}
\<close>

ML\<open>
val thy_x = @{theory}
val key_x = (case JEnv.get (Context.Theory thy_x) of JEnv.mk {units, ...} =>
               JEnv.ast_store_key thy_x (units - 1))
\<close>
java_export "Java_Cmd_Tests_x" exports "Java_Cmd_Tests#21"
java_export [verbatim] "Java_Cmd_Tests_v" exports "Java_Cmd_Tests#21"

text\<open>
  \<open>java_export\<close> writes the stored sections to a \<^verbatim>\<open>.java\<close> file next to the theory, printed back by
  the pretty-printer or, with \<open>[verbatim]\<close>, as originally written.\<close>

ML\<open>
val exported =
  File.read (Path.append (Resources.master_directory thy_x) (Path.explode "Java_Cmd_Tests_x.java"))
val exported_v =
  File.read (Path.append (Resources.master_directory thy_x) (Path.explode "Java_Cmd_Tests_v.java"))
val _ = check "the exported text is the pretty-printed unit"
  (exported =
     "class Exported {\n    int x = 1;\n    int f() {\n        return x + 1;\n    }\n}\n\n")
val _ = check "the verbatim export is the text as written"
  (String.isSubstring "int f() { return x + 1; }" exported_v)
val _ = check "the pretty-printed text of the section"
  (case JEnv.get_ast key_x thy_x of
     SOME r => Java_Pp.pp_root r =
       "class Exported {\n    int x = 1;\n    int f() {\n        return x + 1;\n    }\n}\n"
   | NONE => false)
val _ = check "the verbatim text of the section"
  (case JEnv.get_source key_x thy_x of
     SOME t => String.isSubstring "int f() { return x + 1; }" t
   | NONE => false)
\<close>

subsection\<open>The semantic-backend hook\<close>

ML\<open>
val BACKEND_SEEN = Unsynchronized.ref ([] : string list)
\<close>

setup_backend\<open>fn root => fn thy => (BACKEND_SEEN := Java_Pp.pp_root root :: !BACKEND_SEEN; thy)\<close>

java\<open>
class Seen { }
\<close>

ML\<open>
val _ = check "the backend saw the unit" (exists (String.isPrefix "class Seen") (!BACKEND_SEEN))
\<close>

setup_backend\<open>K I\<close>

subsection\<open>Resetting the environment\<close>

ML\<open>
val names_before = (case JEnv.get (Context.Theory @{theory}) of JEnv.mk {names,
  ...} => Symtab.size names)
\<close>

reset_jenv

ML\<open>
val names_after = (case JEnv.get (Context.Theory @{theory}) of JEnv.mk {names,
  ...} => Symtab.size names)
val _ = check "reset_jenv forgets the declared names" (names_after = 0 andalso names_before > 0)
\<close>

ML\<open>val _ = report_failures ()\<close>

end
