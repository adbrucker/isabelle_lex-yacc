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

theory Go_Cmd_Tests
  imports Go Go_Tests
begin

section\<open>Command-level Tests\<close>

ML\<open>
fun check name b = if b then writeln ("OK: " ^ name)
  else error ("FAILED: " ^ name)
\<close>

subsection\<open>Accepting commands\<close>

go_ident\<open>foo_bar\<close>

go_expr\<open>(a + b) * c\<close>

go_type\<open>map[string][]int\<close>

go\<open>
package main

import "fmt"

func inc(n int) int {
	return n + 1
}

func main() {
	fmt.Println(inc(41))
}
\<close>

text\<open>Top-level declarations without a package clause, and a statement list as it stands between
  the braces of a function.\<close>

go_decl\<open>
func twice(n int) int { return 2 * n }
var limit = twice(21)
\<close>

go_stmt\<open>
x := 0
if x < 10 {
	x++
}
\<close>

go_reject\<open>
package main
func f( {
\<close>

go_decl_reject\<open>x := 1\<close>

go_stmt_reject\<open>x := \<close>

go_expr_reject\<open>a +\<close>

go_type_reject\<open>[]\<close>

go_ident_reject\<open>a b\<close>

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
    val root = the (Go_Parse.parse_quiet entry (Proof_Context.init_global thy) source)
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

val fresh = GEnv.reset_genv @{theory}

(* the number of entity markups: declarations plus resolved uses *)
fun entities_in entry text = count "entity" (reports_in entry fresh text)
fun ent_with entry name text n =
  let val got = entities_in entry text
  in if got = n then writeln ("OK: " ^ name)
     else fail ("FAILED: " ^ name ^ ": expected " ^ Int.toString n ^ ", got " ^ Int.toString got)
  end
val ent = ent_with Go_Parse.Entry_Decls
val ents = ent_with Go_Parse.Entry_Stmts

val _ = ent "a declaration" "func f() {}" 1
val _ = ent "a parameter and its use" "func f(x int) int { return x }" 3
val _ = check "an undeclared name is not marked"
  (entities_in Go_Parse.Entry_Decls "func f() { y() }" = 1
   andalso count "bad" (reports_in Go_Parse.Entry_Decls fresh "func f() { y() }") = 0)
(* package-level names are visible throughout the package, local ones only after their
   declaration *)
val _ = ent "forward reference to a function" "func a() { b() }\nfunc b() {}" 3
val _ = ent "forward reference to a type and a variable"
  "var v T\ntype T int\nfunc f() { _ = v }" 5
val _ = ents "no forward reference to a local variable" "x := y\ny := 1" 2
val _ = ents "a variable does not see itself" "x := x" 1
(* short variable declarations declare the new names only *)
val _ = ents "redeclaration in :=" "a, b := 1, 2\nb, c := 3, 4" 4
val _ = ents "the blank identifier declares nothing" "_, b := 1, 2" 1
(* scopes *)
val _ = ents "a block shadows" "x := 1\n{\n\tx := 2\n\t_ = x\n}" 3
val _ = ents "a block closes" "{\n\tx := 1\n\t_ = x\n}\n_ = x" 2
val _ = ents "the scope of an if header" "if x := f(); x > 0 {\n\t_ = x\n}\n_ = x" 3
val _ = ents "the variables of a range clause" "for i, v := range xs {\n\t_ = i\n\t_ = v\n}" 4
val _ = ents "the ranged-over expression is outside the scope" "for x := range x {\n}" 1
val _ = ents "a for clause" "for i := 0; i < n; i++ {\n\t_ = i\n}" 4
val _ = ents "a function literal" "f := func(a int) int {\n\treturn a + g\n}" 3
val _ = ents "the variable of a type switch is declared once"
  "switch v := x.(type) {\ncase int:\n\t_ = v\ncase string:\n\t_ = v\n}" 3
val _ = ents "a case clause is a scope"
  "switch x {\ncase 1:\n\ty := 1\n\t_ = y\ncase 2:\n\t_ = y\n}" 2
val _ = ents "a select clause" "select {\ncase v := <-ch:\n\t_ = v\n}" 2
val _ = ents "labels have a name space of their own" "L := 1\nL:\nfor {\n\tbreak L\n}\n_ = L" 4
(* declarations in a function *)
val _ = ents "var and const" "var a, b int = 1, 2\nconst c = a\n_ = b + c" 6
val _ = ents "a local type sees itself" "type L struct{ next *L }" 3
(* types *)
val _ = ent "the fields of a struct are declared" "type T struct{ a, b int }" 3
val _ = ent "a type sees itself" "type L struct {\n\tnext *L\n}" 3
val _ = ent "the methods of an interface are declared" "type I interface {\n\tM() int\n}" 2
(* the key "a" is now the field of T: the declaration of T, of its field and of f, the declaration
   of the variable a, the key (a use of the field) and the value (a use of the variable) *)
val _ = ent "the keys of a composite literal are field names"
  "type T struct{ a int }\nfunc f() {\n\ta := 1\n\t_ = T{a: a}\n}" 7
val _ = ent "constants" "const (\n\tA = iota\n\tB\n\tC\n)" 3
(* selections *)
val _ = ent "a field is selected" "type T struct{ a int }\nfunc f(t T) int { return t.a }" 7
val _ = ent "a method is selected" "type T struct{}\nfunc (t T) M() {}\nfunc f(t T) { t.M() }" 9
val _ = ent "a method with a pointer receiver is selected"
  "type T struct{}\nfunc (t *T) M() {}\nfunc f(t *T) { t.M() }" 9
val _ = ent "a method with a pointer receiver is selected on a value"
  "type T struct{}\nfunc (t *T) M() {}\nfunc f(t T) { t.M() }" 9
val _ = ent "a method declared further down is selected"
  "type T struct{}\nfunc f(t T) { t.M() }\nfunc (t T) M() {}" 9
val _ = ent "a pointer is dereferenced and an embedded field promoted"
  "type B struct{ x int }\ntype D struct{ B }\nfunc f(d *D) int { return d.x }" 9
val _ = ent "the same name at the same depth is ambiguous"
  "type A struct{ x int }\ntype B struct{ x int }\ntype C struct{ A; B }\n\
  \func f(c C) int { return c.x }" 11
val _ = ent "a field of an unknown type is not resolved" "func f(p Q) { _ = p.a }" 3
val _ = ent "a method of an interface is selected" "type I interface{ M() }\nfunc f(i I) { i.M() }" 7
val _ = ent "the type of a short variable declaration is that of the value"
  "type T struct{ a int }\nfunc f() int {\n\tt := T{}\n\treturn t.a\n}" 7
val _ = ent "the type of a call is its result" 
  "type T struct{ n int }\nfunc mk() T { return T{} }\nfunc f() int { return mk().n }" 8
val _ = ent "a range variable has the element type"
  "type T struct{ a int }\nfunc f(xs []T) {\n\tfor _, x := range xs {\n\t\t_ = x.a\n\t}\n}" 9
val _ = ent "a field of an instantiated type is selected"
  "type P[T any] struct{ v T }\nfunc f(p P[int]) int { return p.v }" 9
val _ = ent "the variable of a type switch has the type of its clause"
  "type T struct{ a int }\nfunc f(x any) {\n\tswitch v := x.(type) {\n\tcase T:\n\t\t_ = v.a\n\t}\n}" 9
val _ = ent "the keys of an elided element are fields" "type T struct{ a int }\nvar xs = []T{{a: 1}}" 5
val _ = ent "the key of a map literal is a variable" "var k = 1\nvar m = map[int]int{k: 2}" 3
val _ = ent "a variable's type is inferred from a later declaration"
  "var a = b.n\nvar b = T{}\ntype T struct{ n int }" 7
(* imports *)
val _ = ent "an import is a declaration and fmt is a use"
  "import \"fmt\"\nfunc f() { fmt.Println() }" 3
val _ = ent "an alias" "import m \"math\"\nfunc f() { _ = m.Pi }" 3
val _ = ent "a path with a version suffix" "import \"example.org/x/v2\"\nfunc f() { x.Run() }" 3
(* generics *)
val _ = ent "type parameters scope over the function"
  "func Map[T, U any](xs []T, f func(T) U) []U {\n\tvar r []U\n\treturn r\n}" 12
val _ = ent "the receiver declares the type parameters of a method"
  "func (l *List[T]) Push(x T) {\n\t_ = l\n}" 6
val _ = ent "a type parameter can be used by the next one"
  "func Keys[M ~map[K]V, K comparable, V any](m M) []K { return nil }" 9
val _ = ent "generic types" "type Pair[K comparable, V any] struct {\n\tk K\n\tv V\n}" 7
\<close>

text\<open>The top-level names of a source file stay in the environment for the commands that follow;
  the names local to a function do not.\<close>

go\<open>
package lib

import "strings"

const Limit = 100

func Twice(n int) int {
	return 2 * n
}

var Upper = strings.ToUpper
\<close>

ML\<open>
val thy_lib = @{theory}
val names_lib = (case GEnv.get (Context.Theory thy_lib) of GEnv.mk {names, ...} => names)
val _ = check "the top-level names of a unit stay"
  (Symtab.defined names_lib "Limit" andalso Symtab.defined names_lib "Twice"
   andalso Symtab.defined names_lib "Upper" andalso Symtab.defined names_lib "strings")
val _ = check "local names do not leak" (not (Symtab.defined names_lib "n"))
val _ = check "... (in the theory after the declaring unit)"
  (count "entity" (reports_in Go_Parse.Entry_Stmts thy_lib "x := Twice(Limit)\n_ = x") = 4)
\<close>

subsection\<open>Antiquotations and navigation\<close>

text\<open>
  A comment attaches to the node starting at the next token; with no navigation string the
  handler sees that node (here the whole statement).\<close>

go\<open>
package p

func f(x, y int) int {
	//@ probe_ast
	//@ highlight
	x = x + y
	return x
}
\<close>

ML\<open>
val _ = check "probe_ast sees the commented statement"
  (Go_Pp.pp_root (!GO_AST) = "x = x + y")
\<close>

text\<open>
  Navigation: \<open>[u]\<close> and \<open>[uu]\<close> re-target to enclosing nodes, \<open>[d]\<close>/\<open>[rd]\<close> to the first child,
  \<open>[rrd]\<close> to the second (as in C11, the first \<open>r\<close> only starts the cursor at 1).\<close>

go\<open>
package p

func f(x, y int) int {
	//@ probe_ast[uu]
	//@ highlight[u]
	x = x + y
	return x
}
\<close>

ML\<open>
val _ = check "[uu] reaches the enclosing function"
  (String.isPrefix "func f(x, y int) int {" (Go_Pp.pp_root (!GO_AST)))
\<close>

go\<open>
package p

func f(x, y int) int {
	//@ probe_ast[d]
	//@ highlight[d]
	x = x + y
	return x
}
\<close>

ML\<open>
val _ = check "[d] reaches the first child" (Go_Pp.pp_root (!GO_AST) = "x")
\<close>

go\<open>
package p

func f(x, y int) int {
	//@ probe_ast[rrd]
	//@ highlight[rrd]
	x = x + y
	return x
}
\<close>

ML\<open>
val _ = check "[rrd] reaches the second child" (Go_Pp.pp_root (!GO_AST) = "x + y")
\<close>

text\<open>In a statement list: the comment before a statement is attached to it.\<close>

go_stmt\<open>
x := 0
//@ probe_ast
x++
\<close>

ML\<open>
val _ = check "an antiquotation in a statement list" (Go_Pp.pp_root (!GO_AST) = "x++")
\<close>

text\<open>
  An \<open>@\<close> in running comment text is not an antiquotation (it would fail with an unregistered
  tag), whereas a tag with a cartouche body is one anywhere in a comment, also in a block
  comment:\<close>

go_decl\<open>
// Docs. Mail me at someone@example.org, or see @param.
func g(x int) int { return x }
\<close>

ML\<open>
val ORDER = Unsynchronized.ref ([] : int list)
val record = let fun probe (_, _, l) (_ : string * Position.T) thy = (ORDER := l :: !ORDER; thy)
             in GEnv.store_antiq ("record", GEnv.lift_theory_antiq probe) end
\<close>
setup\<open>record\<close>

text\<open>Evaluation order is by \<open>level\<close>, not by position:\<close>

go_stmt\<open>
//@ record(1)
a := 1
/* an ordinary comment @record(1) \<open>\<close> */
//@ record(0)
b := 2
/*@ record(1) */
c := 3
\<close>

ML\<open>
val _ = check "levels order the evaluation" (rev (!ORDER) = [0, 1, 1, 1])
\<close>

text\<open>The real Isabelle machinery: a \<open>definition\<close> in a comment, then a \<open>lemma\<close> proved about it,
  then a \<open>term\<close> mentioning it.\<close>

go_decl\<open>
// A constant of the Go program, mirrored in HOL:
//@ definition \<open>go_limit :: nat where "go_limit = 100"\<close>
//@ lemma(1) \<open>go_fact: "go_limit * 2 = 200" by (simp add: go_limit_def)\<close>
//@ term(2) \<open>go_limit + 1\<close>
const Limit2 = 100
\<close>

thm go_limit_def go_fact

subsection\<open>\<open>go_file\<close> on external sources\<close>

go_file \<open>examples/hello.go\<close>

ML\<open>
val thy_h = @{theory}
val key_h =
  (case GEnv.get (Context.Theory thy_h) of GEnv.mk {units, ...} =>
   GEnv.ast_store_key thy_h (units - 1))
val path_h = Path.append (Resources.master_directory thy_h) (Path.explode "examples/hello.go")
val _ = check "hello: stored as a source file"
  (case GEnv.get_ast key_h thy_h of
     SOME (Go_Ast.Source (Go_Ast.File (pkg, decls, _))) =>
       Go_Ast.ident_name pkg = "main" andalso length decls = 4
   | _ => false)
val _ = check "hello: the source text stored is the file's own"
  (GEnv.get_source key_h thy_h = SOME (File.read path_h))
\<close>

go_file \<open>examples/stack.go\<close>

go_file \<open>examples/shapes.go\<close>

go_file \<open>examples/worker.go\<close>

go_file \<open>examples/flow.go\<close>

ML\<open>
val thy_f = @{theory}
val names_f = (case GEnv.get (Context.Theory thy_f) of GEnv.mk {names, ...} => names)
val _ = check "the examples: their names are visible afterwards"
  (Symtab.defined names_f "Stack" andalso Symtab.defined names_f "Shape"
   andalso Symtab.defined names_f "Pool" andalso Symtab.defined names_f "Weekday"
   andalso Symtab.defined names_f "fmt" andalso Symtab.defined names_f "context")
val flow_key =
  (case GEnv.get (Context.Theory thy_f) of GEnv.mk {units, ...} =>
   GEnv.ast_store_key thy_f (units - 1))
val _ = check "flow: the stored AST pretty-prints to a parsable program (idempotent)"
  (case GEnv.get_ast flow_key thy_f of
     SOME root =>
       let val text = Go_Pp.pp_root root
           val again = Go_Parse.parse_quiet Go_Parse.Entry_File @{context} (Input.string text)
       in (case again of SOME r => Go_Pp.pp_root r = text | NONE => false) end
   | NONE => false)
val _ = check "flow: the labelled loop survives"
  (String.isSubstring "continue outer"
     (the_default "" (Option.map Go_Pp.pp_root (GEnv.get_ast flow_key thy_f))))
\<close>

subsection\<open>Export\<close>

go\<open>
package p

func one() int { return 1 }
\<close>

ML\<open>
val export_key =
  (case GEnv.get (Context.Theory @{theory}) of GEnv.mk {units, ...} =>
   GEnv.ast_store_key @{theory} (units - 1))
val _ = export_key
\<close>

go_export "Go_Cmd_Tests_x" exports "Go_Cmd_Tests#20"

ML\<open>
val exported =
  File.read (Path.append (Resources.master_directory @{theory}) (Path.explode "Go_Cmd_Tests_x.go"))
val _ = check "exported text is the pretty-printed unit"
  (exported = "package p\n\nfunc one() int {\n\treturn 1\n}\n")
\<close>

subsection\<open>The semantic-backend hook\<close>

text\<open>
  \<open>setup_backend\<close> installs the function run on the parsed root and the freshly stored theory at
  the end of every \<open>go\<close>/\<open>go_decl\<close>/\<open>go_stmt\<close>/\<open>go_file\<close>; by default it is \<open>K I\<close>. A backend
  recording the kind of root it receives is installed, exercised and removed again. The fragment
  commands must not trigger it.\<close>

ML\<open>
val BACKEND_LOG = Unsynchronized.ref ([] : string list)
\<close>

setup_backend\<open>fn root => fn thy =>
  (BACKEND_LOG := (case root of
                     Go_Ast.Source (Go_Ast.File (_, ds, _)) => "Source " ^ Int.toString (length ds)
                   | Go_Ast.Stmts _ => "Stmts"
                   | Go_Ast.Decls _ => "Decls"
                   | Go_Ast.Expr _ => "Expr" | Go_Ast.Id _ => "Id"
                   | Go_Ast.Stmt _ => "Stmt" | Go_Ast.Decl _ => "Decl")
                  :: !BACKEND_LOG;
   thy)\<close>

go\<open>package a; func f() {}; func g() {}\<close>
go_stmt\<open>c := 3\<close>
go_decl\<open>var d = 4\<close>
go_expr\<open>1 + 2\<close>

ML\<open>
val _ = check "the backend ran on units and lists, not on fragments"
  (rev (!BACKEND_LOG) = ["Source 2", "Stmts", "Decls"])
\<close>

setup_backend\<open>K I\<close>

go_decl\<open>var e = 5\<close>

ML\<open>
val _ = check "the default backend (K I) does nothing" (length (!BACKEND_LOG) = 3)
\<close>

subsection\<open>Resetting the environment\<close>

text\<open>\<open>reset_genv\<close> restores the snapshot nominated by \<open>set_genv_default\<close> - at the end of
  \<^verbatim>\<open>Go.thy\<close>, an environment with nothing declared.\<close>

reset_genv

ML\<open>
val _ = check "reset_genv empties the environment"
  (case GEnv.get (Context.Theory @{theory}) of GEnv.mk {names, ...} => Symtab.is_empty names)
val _ = report_failures ()
\<close>

end
