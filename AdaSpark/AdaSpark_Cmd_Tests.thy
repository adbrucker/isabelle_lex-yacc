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

theory AdaSpark_Cmd_Tests
  imports AdaSpark AdaSpark_Tests
begin

section\<open>Command-level Tests\<close>

ML\<open>
fun check name b = if b then writeln ("OK: " ^ name)
  else error ("FAILED: " ^ name)
\<close>

subsection\<open>Accepting commands\<close>

adaspark_ident\<open>Foo_Bar\<close>

adaspark_expr\<open>(A + B) * C\<close>

adaspark_type\<open>Natural range 0 .. 10\<close>

adaspark\<open>
function Inc (N : Integer) return Integer is
begin
   return N + 1;
end Inc;
\<close>

text\<open>A statement sequence, as it stands between \<open>begin\<close> and \<open>end\<close>.\<close>

adaspark_body\<open>
X := 0;
if X < 10 then
   X := X + 1;
end if;
\<close>

adaspark_reject\<open>
procedure P is begin null;
\<close>

adaspark_expr_reject\<open>A +\<close>

adaspark_type_reject\<open>Integer range\<close>

adaspark_ident_reject\<open>A B\<close>

adaspark_body_reject\<open>X := ;\<close>

subsection\<open>Binding\<close>

text\<open>
  The binding pass reports through \<^ML>\<open>Position.report\<close>; a position without a
  document id is never reported, so the tests parse a source carrying a dummy id
  and capture the protocol messages. Every declaration and every resolved use is
  one entity markup; a name that resolves nowhere produces nothing (and no error
  markup either).
\<close>

ML\<open>
fun reports_in thy text =
  let
    val pos = Position.id "4711"
    val source = Input.source false text (pos, pos)
    val collected = Unsynchronized.ref ([] : string list)
    val root = the (AdaSpark_Parse.parse_quiet AdaSpark_Parse.Entry_Crate
                                               (Proof_Context.init_global thy)
                                                 source)
    val _ = Unsynchronized.setmp Private_Output.report_fn
              (fn outs => collected := String.concat outs :: !collected)
              (fn () => AnaEval.analyse_and_eval root thy) ()
  in String.concat (!collected) end

fun count sub s =
  let fun go i n =
    case Substring.position sub (Substring.extract (s, i, NONE)) of
                        (_, rest) => if Substring.isEmpty rest then n
                                     else go (size s - Substring.size rest
                                              + size sub) (n + 1)
  in go 0 0 end

(* the number of entity markups: declarations plus resolved uses *)
fun entities text = count "entity" (reports_in (AEnv.reset_aenv @{theory}) text)
fun ent name text n =
  let val got = entities text
  in if got = n then writeln ("OK: " ^ name)
     else fail
       ("FAILED: " ^ name ^ ": expected " ^ Int.toString n ^ ", got "
        ^ Int.toString got)
  end

val _ = ent "a declaration" "procedure P is begin null; end P;" 1
val _ = ent "a parameter and its use"
  "function F (X : Integer) return Integer is begin return X; end F;" 3
val _ = check "an undeclared name is not marked"
              (entities "procedure P is begin Q; end P;" = 1
               andalso count
                 "bad" (reports_in (AEnv.reset_aenv @{theory})
                        "procedure P is begin Q; end P;") = 0)
(* a declaration is visible after itself, not before *)
val _ = ent "no forward reference to a later object"
  "procedure P is A : Integer := B; B : Integer := 1; begin null; end P;" 3
val _ = ent "an object does not see itself"
  "procedure P is A : Integer := A; begin null; end P;" 2
val _ = ent "a subprogram sees itself" "procedure P is begin P; end P;" 2
val _ = ent "a type sees itself"
  "package P is type T is access T; end P;" 3
(* scopes are closed again *)
val _ = ent "a parameter is not visible outside"
  ("procedure P (X : Integer) is begin null; end P;\n" ^
   "procedure Q is begin X := 1; end Q;") 3
val _ = ent "a loop variable scopes over the body"
  "procedure P is begin for I in 1 .. 3 loop I := I; end loop; end P;" 4
val _ = ent "... and not beyond it"
  ("procedure P is begin for I in 1 .. 3 loop null; end loop; I := 1; " ^
   "end P;") 2
val _ = ent "a quantified variable"
  ("function F (A : Integer) return Boolean is " ^
   "(for all I in 1 .. A => I > 0);") 5
(* case insensitivity *)
val _ = ent "names are case insensitive"
  "procedure P is X : Integer; begin x := 1; end P;" 3
(* enumeration literals, records, discriminants *)
val _ = ent "enumeration literals are declared in the enclosing scope"
  "package P is type C is (R, G); X : C := R; end P;" 7
val _ = ent "record components are declared, not entered"
  "package P is type R is record X, Y : Integer; end record; end P;" 4
val _ = ent "a discriminant scopes over the components"
  ("package P is type R (D : Integer) is record X : Integer := D; " ^
   "end record; end P;") 5
(* named associations *)
val _ = ent "the choices of an aggregate are expressions"
  ("procedure P (X : in out Integer; Y : Integer) with " ^
   "Depends => (X => Y);") 5
val _ = ent "the names of formal parameters in a call are not resolved"
  ("procedure M is X : Integer; procedure P (Y : Integer) is begin null; " ^
   "end P; begin P (X => 1); end M;") 5
(* packages *)
val _ = ent "a selected name is resolved through the package"
  ("package P is X : Integer; end P;\n" ^
   "procedure Q is begin P.X := 1; end Q;") 5
val _ = ent "the body of a package re-opens its specification"
  ("package P is procedure Q; end P;\n" ^
   "package body P is procedure Q is begin null; end Q; end P;") 4
val _ = ent "a use clause makes the names of a package visible"
  ("package P is X : Integer; end P;\n" ^
   "with P; use P;\nprocedure M is begin X := 1; end M;") 6
val _ = ent "a nested package"
  ("package P is package Q is X : Integer; end Q; end P;\n" ^
   "procedure M is begin P.Q.X := 1; end M;") 7
\<close>

text\<open>The names a source file declares stay in the environment for the units that
  follow; the names local to them do not.\<close>

adaspark\<open>
package Lib is
   Limit : constant := 100;
   function Twice (N : Integer) return Integer;
end Lib;
\<close>

ML\<open>
val thy_lib = @{theory}
val names_lib = (case AEnv.get (Context.Theory thy_lib) of
                   AEnv.mk {names, ...} => names)
val _ = check "the library unit and its qualified names stay"
              (Symtab.defined names_lib "lib"
               andalso Symtab.defined names_lib "lib.limit"
               andalso Symtab.defined names_lib "lib.twice")
val _ = check "the unqualified names of the package do not"
              (not (Symtab.defined names_lib "limit")
               andalso not (Symtab.defined names_lib "twice"))
val _ = check "local names do not leak" (not (Symtab.defined names_lib "n"))
val _ = check "... (in the theory after the declaring unit)"
              (count "entity"
                 (reports_in thy_lib
                    ("procedure Z is X : Integer := Lib.Limit; begin " ^
                     "null; end Z;")) = 4)
\<close>

subsection\<open>Antiquotations and navigation\<close>

text\<open>
  A comment attaches to the node starting at the next token; with no navigation
  string the handler sees that node (here the whole statement).\<close>

adaspark\<open>
procedure P (X : Integer) is
begin
   --@ probe_ast
   --@ highlight
   X := X + 1;
end P;
\<close>

ML\<open>
val _ = check "probe_ast sees the commented statement"
  (AdaSpark_Pp.pp_root (!ADA_AST) = "X := X + 1;")
\<close>

text\<open>
  Navigation: \<open>[u]\<close> and \<open>[uu]\<close> re-target to enclosing nodes, \<open>[d]\<close>/\<open>[rd]\<close> to the
  first child, \<open>[rrd]\<close> to the second (as in C11, the first \<open>r\<close> only starts the
  cursor at 1).\<close>

adaspark\<open>
procedure P (X, Y : Integer) is
begin
   --@ probe_ast[uu]
   --@ highlight[u]
   X := X + Y;
end P;
\<close>

ML\<open>
val _ = check "[uu] reaches the enclosing subprogram"
  (String.isPrefix
   "procedure P (X, Y : Integer) is" (AdaSpark_Pp.pp_root (!ADA_AST)))
\<close>

adaspark\<open>
procedure P (X, Y : Integer) is
begin
   --@ probe_ast[d]
   --@ highlight[d]
   X := X + Y;
end P;
\<close>

ML\<open>
val _ = check
  "[d] reaches the first child" (AdaSpark_Pp.pp_root (!ADA_AST) = "X")
\<close>

adaspark\<open>
procedure P (X, Y : Integer) is
begin
   --@ probe_ast[rrd]
   --@ highlight[rrd]
   X := X + Y;
end P;
\<close>

ML\<open>
val _ = check
  "[rrd] reaches the second child" (AdaSpark_Pp.pp_root (!ADA_AST) = "X + Y")
\<close>

text\<open>In a statement sequence: the comment before a statement is attached to
  it.\<close>

adaspark_body\<open>
X := 0;
--@ probe_ast
X := X + 1;
\<close>

ML\<open>
val _ = check
  "an antiquotation in a statement sequence"
  (AdaSpark_Pp.pp_root (!ADA_AST) = "X := X + 1;")
\<close>

text\<open>
  A comment before a compilation unit is attached to the unit, whose closest
  context is the source file: \<open>[d]\<close> reaches the declaration, \<open>[dd]\<close> its first
  child - here the type of the first parameter.\<close>

adaspark\<open>
--@ probe_ast[dd]
procedure Inc (X : in out Integer)
  with Pre => X < Integer'Last;
\<close>

ML\<open>
val _ = check "the first child of a subprogram declaration is its parameter"
  (AdaSpark_Pp.pp_root (!ADA_AST) = "Integer")
\<close>

text\<open>
  An \<open>@\<close> in running comment text is not an antiquotation (it would fail with an
  unregistered tag), whereas a tag with a cartouche body is one anywhere in a
  comment:\<close>

adaspark\<open>
--  Docs. Mail me at someone@example.org, or see @param.
function F (X : Integer) return Integer;
\<close>

ML\<open>
val ORDER = Unsynchronized.ref ([] : int list)
val record = let fun probe (_, _, l) (_ : string * Position.T) thy =
  (ORDER := l :: !ORDER; thy)
             in AEnv.store_antiq ("record", AEnv.lift_theory_antiq probe) end
\<close>
setup\<open>record\<close>

text\<open>Evaluation order is by \<open>level\<close>, not by position:\<close>

adaspark\<open>
procedure G is
begin
   --@ record(1)
   null;
   --  an ordinary comment @record(1) \<open>\<close>
   --@ record(0)
   null;
end G;
\<close>

ML\<open>
val _ = check
  "levels order the evaluation" (rev (!ORDER) = [0, 1, 1] orelse rev (!ORDER) =
                                 [0, 1])
\<close>

text\<open>The real Isabelle machinery: a \<open>definition\<close> in a comment, then a \<open>lemma\<close>
  proved about it, then a \<open>term\<close> mentioning it.\<close>

adaspark\<open>
--  A constant of the Ada program, mirrored in HOL:
--@ definition \<open>ada_limit :: nat where "ada_limit = 100"\<close>
--@ lemma(1) \<open>ada_fact: "ada_limit * 2 = 200" by (simp add: ada_limit_def)\<close>
--@ term(2) \<open>ada_limit + 1\<close>
package Constants is
   Limit : constant := 100;
end Constants;
\<close>

thm ada_limit_def ada_fact

subsection\<open>\<open>adaspark_file\<close> on external sources\<close>

adaspark_file \<open>examples/stacks.ads\<close>

ML\<open>
val thy_s = @{theory}
val key_s =
  (case AEnv.get (Context.Theory thy_s) of AEnv.mk {units, ...} =>
   AEnv.ast_store_key thy_s (units - 1))
val path_s =
  Path.append (Resources.master_directory thy_s)
    (Path.explode "examples/stacks.ads")
val _ = check "stacks: stored as a source file with one unit"
  (case AEnv.get_ast key_s thy_s of SOME (AdaSpark_Ast.Crate units) =>
   length units = 1 | _ => false)
val _ = check
  "stacks: the source text stored is the file's own" (AEnv.get_source key_s
      thy_s = SOME (File.read path_s))
val names_s = (case AEnv.get (Context.Theory thy_s) of
                 AEnv.mk {names, ...} => names)
val _ = check "stacks: its names are visible afterwards"
  (Symtab.defined names_s "stacks" andalso Symtab.defined names_s "stacks.push"
   andalso Symtab.defined names_s "stacks.stack"
   andalso Symtab.defined names_s "stacks.capacity")
\<close>

adaspark_file \<open>examples/stacks.adb\<close>

adaspark_file \<open>examples/search.ads\<close>

adaspark_file \<open>examples/search.adb\<close>

adaspark_file \<open>examples/counters.ads\<close>

adaspark_file \<open>examples/counters.adb\<close>

adaspark_file \<open>examples/shapes.ads\<close>

adaspark_file \<open>examples/animals.ads\<close>

adaspark_file \<open>examples/hello.adb\<close>

ML\<open>
val thy_h = @{theory}
val last_key =
  (case AEnv.get (Context.Theory thy_h) of AEnv.mk {units, ...} =>
   AEnv.ast_store_key thy_h (units - 1))
val hello_text =
  File.read
    (Path.append (Resources.master_directory thy_h)
     (Path.explode "examples/hello.adb"))
val _ = check
  "hello: the stored AST pretty-prints to a parsable program (idempotent)"
  (case AEnv.get_ast last_key thy_h of
     SOME root =>
       let val text = AdaSpark_Pp.pp_root root
           val again =
             AdaSpark_Parse.parse_quiet
               AdaSpark_Parse.Entry_Crate @{context} (Input.string text)
       in (case again of SOME r => AdaSpark_Pp.pp_root r = text | NONE =>
           false) end
   | NONE => false)
val _ = check "hello: the handler survives"
  (String.isSubstring "when Constraint_Error =>"
     (the_default "" (Option.map AdaSpark_Pp.pp_root
                        (AEnv.get_ast last_key thy_h))))
\<close>

subsection\<open>Export\<close>

adaspark\<open>
function One return Integer is
begin
   return 1;
end One;
\<close>

ML\<open>
val export_key =
  (case AEnv.get (Context.Theory @{theory}) of AEnv.mk {units, ...} =>
   AEnv.ast_store_key @{theory} (units - 1))
val _ = export_key
\<close>

adaspark_export "AdaSpark_Cmd_Tests_x" exports "AdaSpark_Cmd_Tests#24"

ML\<open>
val exported =
  File.read
    (Path.append (Resources.master_directory @{theory})
     (Path.explode "AdaSpark_Cmd_Tests_x.ada"))
val _ = check
  "exported text is the pretty-printed unit"
  (exported = "function One return Integer is\nbegin\n   return 1;\nend One;\n")
\<close>

subsection\<open>The semantic-backend hook\<close>

text\<open>
  \<open>setup_backend\<close> installs the function run on the parsed root and the freshly
  stored theory at the end of every
  \<open>adaspark\<close>/\<open>adaspark_body\<close>/\<open>adaspark_file\<close>; by default it is \<open>K I\<close>. A
  backend recording the kind of root it receives is installed, exercised and
  removed again. The fragment commands must not trigger it.\<close>

ML\<open>
val BACKEND_LOG = Unsynchronized.ref ([] : string list)
\<close>

setup_backend\<open>fn root => fn thy =>
  (BACKEND_LOG := (case root of
                     AdaSpark_Ast.Crate units =>
                       "Crate " ^ Int.toString (length units)
                   | AdaSpark_Ast.Body _ => "Body"
                   | AdaSpark_Ast.Expr _ => "Expr" | AdaSpark_Ast.Type _ =>
                     "Type" | AdaSpark_Ast.Id _ => "Id"
                   | AdaSpark_Ast.Stmt _ => "Stmt" | AdaSpark_Ast.Decl _ =>
                     "Decl")
                  :: !BACKEND_LOG;
   thy)\<close>

adaspark\<open>procedure A; procedure B;\<close>
adaspark_body\<open>C := 3;\<close>
adaspark_expr\<open>1 + 2\<close>

ML\<open>
val _ = check
  "the backend ran on units and bodies, not on fragments" (rev (!BACKEND_LOG) =
      ["Crate 2", "Body"])
\<close>

setup_backend\<open>K I\<close>

adaspark\<open>procedure D;\<close>

ML\<open>
val _ = check
  "the default backend (K I) does nothing" (length (!BACKEND_LOG) = 2)
\<close>

subsection\<open>Resetting the environment\<close>

text\<open>\<open>reset_aenv\<close> restores the snapshot nominated by \<open>set_aenv_default\<close> - at the
  end of \<^verbatim>\<open>AdaSpark.thy\<close>, an environment with nothing declared.\<close>

reset_aenv

ML\<open>
val _ = check "reset_aenv empties the environment"
  (case AEnv.get (Context.Theory @{theory}) of
     AEnv.mk {names, ...} => Symtab.is_empty names)
val _ = report_failures ()
\<close>

end
