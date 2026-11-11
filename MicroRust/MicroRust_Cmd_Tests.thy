(***********************************************************************************
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
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 ***********************************************************************************)

theory MicroRust_Cmd_Tests
  imports MicroRust MicroRust_Tests
begin

section\<open>Command-level Tests\<close>

ML\<open>
fun check name b = if b then writeln ("OK: " ^ name) else error ("FAILED: " ^ name)
\<close>

subsection\<open>Accepting commands\<close>

microrust_ident\<open>foo_bar\<close>

microrust_expr\<open>(a + b) * c\<close>

microrust_type\<open>Vec<Vec<u8>>\<close>

microrust\<open>
fn inc(n: u32) -> u32 {
    n + 1
}
\<close>

text\<open>A uRust function body is a statement sequence with a final expression, as written between
  \<open>FunctionBody \<lbrakk>\<close> and \<open>\<rbrakk>\<close> in AutoCorrode; the HOL escapes are opaque.\<close>

microrust_body\<open>
let mut x = \<llangle>0 :: nat\<rrangle>;
if *x < 10 {
    x += 1;
};
*x
\<close>

microrust_reject\<open>
fn = 1
\<close>

microrust_expr_reject\<open>a +\<close>

microrust_type_reject\<open>Vec<\<close>

microrust_ident_reject\<open>a b\<close>

microrust_body_reject\<open>let = 1;\<close>

subsection\<open>Binding\<close>

text\<open>
  The binding pass reports through \<^ML>\<open>Position.report\<close>; a position without a document id is never
  reported, so the tests parse a source carrying a dummy id and capture the protocol messages.
  Every declaration and every resolved use is one entity markup; a name that resolves nowhere
  produces nothing (and, unlike C11 and occam 2, no error markup either).
\<close>

ML\<open>
fun reports_in thy text =
  let
    val pos = Position.id "4711"
    val source = Input.source false text (pos, pos)
    val collected = Unsynchronized.ref ([] : string list)
    val root = the (MicroRust_Parse.parse_quiet MicroRust_Parse.Entry_Crate
                                                (Proof_Context.init_global thy) source)
    val _ = Unsynchronized.setmp Private_Output.report_fn
              (fn outs => collected := String.concat outs :: !collected)
              (fn () => AnaEval.analyse_and_eval root thy) ()
  in String.concat (!collected) end

fun count sub s =
  let fun go i n = case Substring.position sub (Substring.extract (s, i, NONE)) of
                        (_, rest) => if Substring.isEmpty rest then n
                                     else go (size s - Substring.size rest + size sub) (n + 1)
  in go 0 0 end

(* the number of entity markups: declarations plus resolved uses *)
fun entities text = count "entity" (reports_in (REnv.reset_renv @{theory}) text)
fun ent name text n =
  let val got = entities text
  in if got = n then writeln ("OK: " ^ name)
     else fail ("FAILED: " ^ name ^ ": expected " ^ Int.toString n ^ ", got " ^ Int.toString got)
  end

val _ = ent "a declaration" "fn f() {}" 1
val _ = ent "a parameter and its use" "fn f(x: u32) -> u32 { x }" 3
val _ = check "an undeclared name is not marked"
              (entities "fn f() { y }" = 1
               andalso count "bad" (reports_in (REnv.reset_renv @{theory}) "fn f() { y }") = 0)
(* the items of a module are visible throughout it, a block's lets only after their statement *)
val _ = ent "forward reference to a function" "fn a() { b(); }\nfn b() {}" 3
val _ = ent "no forward reference to a local let" "fn f() { let a = b; let b = 1; a }" 4
val _ = ent "local functions are mutually visible" "fn f() { fn g() { h() } fn h() {} g() }" 5
(* scopes are closed again *)
val _ = ent "a parameter is not visible outside" "fn f(x: u32) -> u32 { x }\nfn g() { x }" 4
(* the two name spaces *)
val _ = ent "a unit struct is a type and a value" "struct A;\nfn f() -> A { A }" 4
(* imports *)
val _ = ent "an import is a declaration" "use a::b::{c, d as e};\nfn f() { e() }" 4
(* patterns, closures, loops *)
val _ = ent "pattern variables scope over an arm" "fn f(o: u32) -> u32 { match o { Some(v) => v, _ => 0 } }" 5
val _ = ent "a closure parameter" "fn f() { let g = |a: u32| a + 1; g }" 5
val _ = ent "a loop variable scopes over the body" "fn f(xs: Vec<u32>) { for i in xs { i; } }" 5
val _ = ent "if let binds in the then-branch only" "fn f(o: u32) { if let Some(x) = o { x } else { x } }" 5
(* generic parameters *)
val _ = ent "generic parameters and bounds" "fn f<T: Copy>(x: T) -> T { x }" 6
(* struct expressions and fields *)
val _ = ent "a struct, a field, a shorthand initializer"
            "struct P { a: u32 }\nfn f(a: u32) -> P { P { a } }" 7
(* the names of a source file stay for the following unit *)
\<close>

microrust\<open>
mod lib {
    pub fn twice(n: u32) -> u32 {
        n * 2
    }
}
const LIMIT: u32 = 100;
\<close>

microrust\<open>
fn y() -> u32 {
    lib::twice(LIMIT)
}
\<close>

ML\<open>
val thy_lib = @{theory}
val (terms_lib, types_lib) = (case REnv.get (Context.Theory thy_lib) of
                                REnv.mk {terms, types, ...} => (terms, types))
val _ = check "the top-level names of a unit stay in the environment"
              (Symtab.defined types_lib "lib" andalso Symtab.defined terms_lib "LIMIT"
               andalso Symtab.defined terms_lib "y")
val _ = check "local names do not leak" (not (Symtab.defined terms_lib "n"))
val _ = check "... (in the theory after the declaring unit)"
              (count "entity" (reports_in thy_lib "fn z() -> u32 { LIMIT }") = 2)
\<close>

subsection\<open>Antiquotations and navigation\<close>

text\<open>A comment attaches to the node starting at the next token; with no navigation string the
  handler sees that node (here the whole expression statement).\<close>

microrust\<open>
fn f(x: u32) -> u32 {
    //@ probe_ast
    //@ highlight
    x + 1
}
\<close>

ML\<open>
val _ = check "probe_ast sees the commented expression"
  (MicroRust_Pp.pp_root (!RUST_AST) = "x + 1")
\<close>

text\<open>Navigation: \<open>[u]\<close> and \<open>[uu]\<close> re-target to enclosing nodes, \<open>[d]\<close>/\<open>[rd]\<close> to the first child,
  \<open>[rrd]\<close> to the second (as in C11, the first \<open>r\<close> only starts the cursor at 1).\<close>

microrust\<open>
fn f(x: u32, y: u32) -> u32 {
    //@ probe_ast[uu]
    //@ highlight[u]
    let a = x + y;
    a
}
\<close>

ML\<open>
val _ = check "[uu] reaches the enclosing function"
  (String.isPrefix "fn f(x: u32, y: u32) -> u32 {" (MicroRust_Pp.pp_root (!RUST_AST)))
\<close>

microrust\<open>
fn f(x: u32, y: u32) -> u32 {
    //@ probe_ast[d]
    //@ highlight[d]
    x + y
}
\<close>

ML\<open>
val _ = check "[d] reaches the first child" (MicroRust_Pp.pp_root (!RUST_AST) = "x")
\<close>

microrust\<open>
fn f(x: u32, y: u32) -> u32 {
    //@ probe_ast[rrd]
    //@ highlight[rrd]
    x + y
}
\<close>

ML\<open>
val _ = check "[rrd] reaches the second child" (MicroRust_Pp.pp_root (!RUST_AST) = "y")
\<close>

text\<open>In a uRust body: the comment before a statement is attached to it.\<close>

microrust_body\<open>
let mut x = 0;
//@ probe_ast
x += 1;
*x
\<close>

ML\<open>
val _ = check "an antiquotation in a function body" (MicroRust_Pp.pp_root (!RUST_AST) = "x += 1")
\<close>

text\<open>An \<open>@\<close> in running comment text is not an antiquotation (it would fail with an unregistered tag),
  whereas a tag with a cartouche body is one anywhere in a comment:\<close>

microrust\<open>
/// Docs. Mail me at someone@example.org, or see @param.
fn f(x: u32) -> u32 {
    x
}
\<close>

ML\<open>
val ORDER = Unsynchronized.ref ([] : int list)
val record = let fun probe (_, _, l) (_ : string * Position.T) thy = (ORDER := l :: !ORDER; thy)
             in REnv.store_antiq ("record", REnv.lift_theory_antiq probe) end
\<close>
setup\<open>record\<close>

text\<open>Evaluation order is by \<open>level\<close>, not by position:\<close>

microrust\<open>
fn g() {
    //@ record(1)
    let a = 1;
    /* an ordinary comment @record(1) \<open>\<close> */
    //@ record(0)
    let b = 2;
}
\<close>

ML\<open>
val _ = check "levels order the evaluation" (rev (!ORDER) = [0, 1, 1] orelse rev (!ORDER) = [0, 1])
\<close>

text\<open>The real Isabelle machinery: a \<open>definition\<close> in a comment, then a \<open>lemma\<close> proved about it,
  then a \<open>term\<close> mentioning it.\<close>

microrust\<open>
// A constant of the Rust program, mirrored in HOL:
//@ definition \<open>rust_limit :: nat where "rust_limit = 100"\<close>
//@ lemma(1) \<open>rust_fact: "rust_limit * 2 = 200" by (simp add: rust_limit_def)\<close>
//@ term(2) \<open>rust_limit + 1\<close>
const LIMIT: u32 = 100;
\<close>

thm rust_limit_def rust_fact

subsection\<open>\<open>microrust_file\<close> on external sources\<close>

microrust_file \<open>examples/shapes.rs\<close>

ML\<open>
val thy_s = @{theory}
val key_s = (case REnv.get (Context.Theory thy_s) of REnv.mk {units, ...} => REnv.ast_store_key thy_s (units - 1))
val path_s = Path.append (Resources.master_directory thy_s) (Path.explode "examples/shapes.rs")
val _ = check "shapes: stored as a source file"
  (case REnv.get_ast key_s thy_s of SOME (MicroRust_Ast.Crate items) => length items = 7 | _ => false)
val _ = check "shapes: the source text stored is the file's own" (REnv.get_source key_s thy_s = SOME (File.read path_s))
\<close>

microrust_file \<open>examples/counter.rs\<close>

ML\<open>
val thy_c = @{theory}
val (terms_c, types_c) = (case REnv.get (Context.Theory thy_c) of REnv.mk {terms, types, ...} => (terms, types))
val _ = check "shapes: its names are visible afterwards"
  (Symtab.defined types_c "Shape" andalso Symtab.defined types_c "Area" andalso Symtab.defined terms_c "total"
   andalso Symtab.defined terms_c "LIMIT")
val counter_text = File.read (Path.append (Resources.master_directory thy_c) (Path.explode "examples/counter.rs"))
val _ = check "counter: the stored AST pretty-prints to a parsable program (idempotent)"
  (let val key = REnv.ast_store_key thy_c ((case REnv.get (Context.Theory thy_c) of REnv.mk {units, ...} => units) - 1)
   in (case REnv.get_ast key thy_c of
         SOME root =>
           let val text = MicroRust_Pp.pp_root root
               val again = MicroRust_Parse.parse_quiet MicroRust_Parse.Entry_Crate @{context} (Input.string text)
           in (case again of SOME r => MicroRust_Pp.pp_root r = text | NONE => false) end
       | NONE => false) end)
val _ = check "counter: the fuel attribute survives"
  (String.isSubstring "#[fuel(100)]" (the_default "" (Option.map MicroRust_Pp.pp_root
      (REnv.get_ast (REnv.ast_store_key thy_c ((case REnv.get (Context.Theory thy_c) of REnv.mk {units, ...} => units) - 1)) thy_c))))
\<close>

subsection\<open>Export\<close>

microrust\<open>
fn one() -> u32 { 1 }
\<close>

microrust_export "MicroRust_Cmd_Tests_x" exports "MicroRust_Cmd_Tests#17"

ML\<open>
val exported = File.read (Path.append (Resources.master_directory @{theory}) (Path.explode "MicroRust_Cmd_Tests_x.rs"))
val _ = check "exported text is the pretty-printed unit" (exported = "fn one() -> u32 {\n    1\n}\n")
\<close>

subsection\<open>The semantic-backend hook\<close>

text\<open>\<open>setup_backend\<close> installs the function run on the parsed root and the freshly stored theory at
  the end of every \<open>microrust\<close>/\<open>microrust_body\<close>/\<open>microrust_file\<close>; by default it is \<open>K I\<close>. A backend recording
  the kind of root it receives is installed, exercised and removed again. The fragment commands must
  not trigger it.\<close>

ML\<open>
val BACKEND_LOG = Unsynchronized.ref ([] : string list)
\<close>

setup_backend\<open>fn root => fn thy =>
  (BACKEND_LOG := (case root of
                     MicroRust_Ast.Crate items => "Crate " ^ Int.toString (length items)
                   | MicroRust_Ast.Body _ => "Body"
                   | MicroRust_Ast.Expr _ => "Expr" | MicroRust_Ast.Type _ => "Type" | MicroRust_Ast.Id _ => "Id"
                   | MicroRust_Ast.Stmt _ => "Stmt" | MicroRust_Ast.Pat _ => "Pat" | MicroRust_Ast.Item _ => "Item")
                  :: !BACKEND_LOG;
   thy)\<close>

microrust\<open>fn a() {} fn b() {}\<close>
microrust_body\<open>let c = 3; c\<close>
microrust_expr\<open>1 + 2\<close>

ML\<open>
val _ = check "the backend ran on units and bodies, not on fragments" (rev (!BACKEND_LOG) = ["Crate 2", "Body"])
\<close>

setup_backend\<open>K I\<close>

microrust\<open>fn d() {}\<close>

ML\<open>
val _ = check "the default backend (K I) does nothing" (length (!BACKEND_LOG) = 2)
val _ = report_failures ()
\<close>

end
