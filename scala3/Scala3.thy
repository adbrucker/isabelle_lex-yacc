(***********************************************************************************
 * Copyright (c) University of Paris-Saclay
 *
 * All rights reserved.
 *
 * Authors: Burkhart Wolff, Claude Sonnet 5.5
 *
 * This is a LLM-generated replication of the Isabelle/C version 2 design
 * to the programming language Scala 3. It provides an efficient parser for Scala 3,
 * deeply integrated into the Isabelle/PIDE document model, allowing external
 * files as well as in-theory code-snippets which are transparent to the underlying
 * theory. It provides an API for the generated AST’s, and an API to hook up
 * semantic backends that compile these AST’s to theory extensions in Isabelle/HOL.
 * Members of the family come with a Scala 3-specific antiquotation mechanism
 * allowing programmable links to the semantic backends as necessary for
 * support of program-annotations with HOL formulas.
 *
 * This session is part of the Isabelle Programming Language Toolkit (Isabelle/PLTk).
 * The generation has been done with Claude Sonnet 5.5; while the replicants come
 * with a detailed (generated) test-suite for Scala 3, I expect that human users might find
 * errors or inconsistencies; experience reports and comments are therefore welcomed.
 * The concrete and abstract syntax, being generated from Isabelle/LexYacc specifications,
 * should be easy to modify and adapt.
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

theory Scala3
  imports "Scala3_Parser" "Scala3_AnaEval"
  keywords "scala3" "scala3_ident" "scala3_expr" "scala3_type" :: thy_decl
  and      "scala3_file" :: thy_load
  and      "scala3_reject" "scala3_ident_reject" "scala3_expr_reject" "scala3_type_reject" :: diag
  and      "set_senv_default" "reset_senv" :: thy_decl
  and      "setup_backend" :: thy_decl
  and      "scala3_export" :: thy_decl
  and      "exports" "verbatim"
begin

text\<open>
  This theory is the Scala 3 analogue of the C11 and occam2 core theories (\<^verbatim>\<open>C11/C11.thy\<close>,
  \<^verbatim>\<open>occam2/Occam2.thy\<close>): an ml-lex/ml-yacc lexer/parser pair for the language of the
  \<^emph>\<open>Scala 3 Syntax Summary\<close>, producing a real abstract syntax tree (\<^verbatim>\<open>scala3_ast.ML\<close>), plus the
  Isar commands that run it: \<open>scala3\<close> (a compilation unit), \<open>scala3_expr\<close>, \<open>scala3_type\<close>,
  \<open>scala3_ident\<close>, \<open>scala3_file\<close>, their \<open>_reject\<close> counterparts for negative tests, and
  \<open>scala3_export\<close>. The concepts are those of the C11 project, carried over one for one:

  \<^item> \<^bold>\<open>Comments and antiquotations.\<close> Scala has \<^verbatim>\<open>//\<close> line comments and nested \<^verbatim>\<open>/* */\<close>
    comments. A comment may contain \<^verbatim>\<open>@tag[navi](level) \<open>...\<close>\<close> antiquotations (the cartouche may
    span lines); the comment is attached to the AST node of the next real token. A \<^emph>\<open>bodyless\<close>
    tag is recognised only directly after the opener (\<^verbatim>\<open>//@ highlight\<close>, \<^verbatim>\<open>/*@ highlight */\<close>), so as
    not to take the Scaladoc tags (\<^verbatim>\<open>@param\<close>, \<^verbatim>\<open>@return\<close>) for antiquotations. Plain comments are
    kept as \<open>Raw_txt\<close>.
  \<^item> \<^bold>\<open>Binding.\<close> Every declaration site and every use of a name that resolves is reported
    with Isabelle's entity markup: hover and click-through from a use to its declaration, with the
    usual Scala scoping and two name spaces (terms and types). A name that resolves nowhere is not
    marked, as in Scala it routinely comes from a library, an import wildcard or a parent class.
    See \<^verbatim>\<open>Scala3_AnaEval.thy\<close>.
  \<^item> \<^bold>\<open>Navigation.\<close> \<^verbatim>\<open>@tag[u|U|r|d...]\<close> re-targets an antiquotation from the node a comment is
    attached to to a parent, sibling or child, with the same four-letter language and rules as C11.
  \<^item> \<^bold>\<open>Antiquotations\<close> are dispatched in ascending \<open>level\<close> order after the whole unit has been
    analysed, and see the \<^emph>\<open>resolved\<close> node; the standard ones (\<open>probe_senv\<close>, \<open>probe_ast\<close>, \<open>highlight\<close>,
    \<open>term\<close>, \<open>ML\<close>, \<open>text\<close>, \<open>definition\<close>, \<open>lemma\<close>) are registered in \<^verbatim>\<open>Scala3_AnaEval.thy\<close>.
  \<^item> \<^bold>\<open>The semantic-backend hook.\<close> At the very end of \<open>scala3\<close>/\<open>scala3_file\<close>, after the antiquotation
    actions have run and the AST is stored, a function of type
    \<open>pos Scala3_Ast.root -> theory -> theory\<close> kept in the theory's context is applied; it is \<open>K I\<close> by
    default, and \<open>setup_backend \<open>f\<close>\<close> installs another one.

  What is specific to Scala, and so handled differently from the other front-ends, is the
  \<^emph>\<open>layout\<close> (newlines are statement separators when the tokens around them allow it) and the
  \<^emph>\<open>operators\<close> (precedence by first character, associativity by last), both explained in
  \<^verbatim>\<open>Scala3_Parser.thy\<close>. Optional braces (significant indentation) and the quote/splice macro
  syntax are not covered; the grammar parses all 380 Scala sources of Isabelle itself (see
  \<^verbatim>\<open>Scala3_Tests.thy\<close>, which runs them, and \<^verbatim>\<open>README.md\<close>).
\<close>

subsection\<open>Defining the Isar-toplevel Commands\<close>

text\<open>
  As in C11 each accepting command stores the parsed AST under a fresh per-theory key
  (\<open>"Theory#N"\<close>, reported as \<open>[stored as ...]\<close>) in \<^ML_structure>\<open>SEnv.Ast_Store\<close>. The parser
  has one grammar entry point per command (\<open>Entry_Unit\<close>, \<open>Entry_Expr\<close>, \<open>Entry_Type\<close>, \<open>Entry_Id\<close>), so
  no result shape needs gating afterwards; a \<open>_reject\<close> command succeeds exactly when the
  fragment is \<^emph>\<open>not\<close> accepted by the corresponding entry point, silently, without
  leaving error markup. Only \<open>scala3\<close> and \<open>scala3_file\<close> (whole program units) chain their
  antiquotation actions into the stored theory; \<open>scala3_expr\<close> and \<open>scala3_ident\<close> are
  syntax checks on a fragment and run the analysis only for its hyperlinking.
\<close>
ML\<open>
local open SEnv in

fun string_of_root (Scala3_Ast.Id id) =
      "Id " ^ Scala3_Ast.ident_name id ^ " " ^ Position.here (Scala3_Ast.pos_of_ident id)
  | string_of_root (Scala3_Ast.Expr e) =
      "Expr " ^ Position.here (Scala3_Ast.pos_of_expr e)
  | string_of_root (Scala3_Ast.Type t) =
      "Type " ^ Position.here (Scala3_Ast.pos_of_type t)
  | string_of_root (Scala3_Ast.Stat s) =
      "Stat " ^ Position.here (Scala3_Ast.pos_of_stat s)
  | string_of_root (Scala3_Ast.Pat p) =
      "Pat " ^ Position.here (Scala3_Ast.pos_of_pat p)
  | string_of_root (Scala3_Ast.Unit ss) =
      "Unit (" ^ Int.toString (length ss) ^ " top-level statement(s))"

(* The antiquotation actions are folded together as a plain
   "Context.generic -> Context.generic" function in ascending "level" order
   (a stable sort, so equal levels keep their textual order) - see the note on
   "full_eval_and_store" in C11.thy for why they are never lifted one by one. *)
(* The last step is the semantic-backend hook (SEnv.get_backend, "setup_backend"
   below): a function from the parsed root and the theory the root has just been
   stored into to a theory, "K I" unless a backend has been installed. It runs
   after the root is stored and reported, and only for "scala3"/"scala3_file", the
   commands whose input is a genuine program unit. *)
fun full_eval_and_store root text thy =
    let
      val (thy', antiq_evals) = AnaEval.analyse_and_eval root thy
      val sorted_evals = sort (fn ((l1, _), (l2, _)) => Int.compare (l1, l2)) antiq_evals
      val context_for_store = fold (fn (_, f) => f) sorted_evals (Context.Theory thy')
      val thy_for_store = Context.theory_of context_for_store
      val (key, thy'') = store_root root text thy_for_store
      val _ = writeln (string_of_root root ^ "  [stored as " ^ key ^ "]")
    in get_backend thy'' root thy'' end

(* A fragment (identifier, expression): analysed for its hyperlinks only. *)
fun fragment_and_store entry cmd_name source thy =
    let
      val ctxt = Proof_Context.init_global thy
    in
      case Scala3_Parse.parse_loud entry ctxt source of
        NONE => error (cmd_name ^ ": no result")
      | SOME root =>
          let
            val _ = AnaEval.analyse_and_eval root thy
            val (key, thy'') = store_root root (Input.text_of source) thy
            val _ = writeln (string_of_root root ^ "  [stored as " ^ key ^ "]")
          in thy'' end
    end

fun run_scala3 source thy =
    let val ctxt = Proof_Context.init_global thy
    in
      case Scala3_Parse.parse_loud Scala3_Parse.Entry_Unit ctxt source of
        NONE => error "scala3: no result"
      | SOME root => full_eval_and_store root (Input.text_of source) thy
    end

val _ = Outer_Syntax.command @{command_keyword "scala3"}
        "Syntax check a Scala 3 program unit and store its AST"
        (Parse.input Parse.cartouche >> (fn source => Toplevel.theory (run_scala3 source)))

val _ = Outer_Syntax.command @{command_keyword "scala3_ident"}
        "Syntax check a bare Scala 3 name and store its AST"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory (fragment_and_store Scala3_Parse.Entry_Id "scala3_ident" source)))

val _ = Outer_Syntax.command @{command_keyword "scala3_type"}
        "Syntax check a Scala 3 type and store its AST"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory (fragment_and_store Scala3_Parse.Entry_Type "scala3_type" source)))

val _ = Outer_Syntax.command @{command_keyword "scala3_expr"}
        "Syntax check a Scala 3 expression and store its AST"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory (fragment_and_store Scala3_Parse.Entry_Expr "scala3_expr" source)))

(* "thy_load", not "diag", for the reason given at "c11_file" in C11.thy:
   only a thy_load command gets the file dependency registered. *)
fun run_scala3_file get_file thy =
    let
      val file = get_file thy
      val source = Token.file_source file
      val ctxt = Proof_Context.init_global thy
    in
      case Scala3_Parse.parse_loud Scala3_Parse.Entry_Unit ctxt source of
        NONE => error "scala3_file: no result"
      | SOME root => full_eval_and_store root (Input.text_of source) thy
    end

val _ = Outer_Syntax.command @{command_keyword "scala3_file"}
        "Read and syntax-check an external Scala 3 source file, and store its AST"
        (Resources.parse_file >> (fn get_file => Toplevel.theory (run_scala3_file get_file)))

fun report_senv_size label thy =
    let val mk {terms, types, ...} = get (Context.Theory thy)
        fun count t = Int.toString (Symtab.fold (K (fn n => n + 1)) t 0)
    in writeln (label ^ ": " ^ count terms ^ " term(s), " ^ count types ^ " type(s)") end

val _ = Outer_Syntax.command @{command_keyword "set_senv_default"}
        "Nominate the current senv as the snapshot a later reset_senv restores"
        (Scan.succeed (Toplevel.theory (fn thy =>
          let val thy' = set_senv_default thy in report_senv_size "set_senv_default" thy'; thy' end)))

val _ = Outer_Syntax.command @{command_keyword "reset_senv"}
        "Reset senv to the snapshot set_senv_default last nominated (or empty_senv, if none yet)"
        (Scan.succeed (Toplevel.theory (fn thy =>
          let val thy' = reset_senv thy in report_senv_size "reset_senv" thy'; thy' end)))

(* "setup_backend \<open>f\<close>" installs the semantic backend that "full_eval_and_store" runs at
   the end of every "scala3"/"scala3_file": "f" is an ML expression of type
   "Position.T Scala3_Ast.root -> theory -> theory", evaluated exactly like the
   argument of Isabelle's own "setup" command (Isar_Cmd.setup). The default is
   "K I"; "setup_backend \<open>K I\<close>" restores it. The function lives in the theory's
   context and is inherited by later theories. *)
fun setup_backend source =
  ML_Context.expression (Input.pos_of source)
    (ML_Lex.read "Theory.setup (SEnv.set_backend (" @ ML_Lex.read_source source @ ML_Lex.read "))")
  |> Context.theory_map

val _ = Outer_Syntax.command @{command_keyword "setup_backend"}
        "Install the semantic backend run at the end of every scala3/scala3_file"
        (Parse.ML_source >> (Toplevel.theory o setup_backend))

(* "scala3_export name exports key ..." writes the stored sections, printed
   back with "Scala3_Pp.pp_root" (or, with "[verbatim]", as originally
   written), to "name.scala" in the theory's master directory. Same contract as
   "c11_export_c" (see C11.thy). *)
fun run_scala3_export (verbatim, path, keys) thy =
    let
      val out_path = Path.append (Resources.master_directory thy) (Path.explode (path ^ ".scala"))
      fun unknown key = error ("no stored scala3 section named " ^ quote key ^
                               " (expected one of the \"[stored as ...]\" keys the scala3 commands report)")
      fun text_of key =
        if verbatim
        then (case get_source key thy of SOME text => text | NONE => unknown key)
        else (case get_ast key thy of SOME root => Scala3_Pp.pp_root root | NONE => unknown key)
      val _ = File.write out_path (space_implode "\n\n" (map text_of keys) ^ "\n")
      val _ = writeln ("Exported " ^ Int.toString (length keys) ^ " section(s) to " ^
                        Path.print out_path)
    in thy end

val export_args =
  Scan.optional (Parse.$$$ "[" |-- Parse.$$$ "verbatim" --| Parse.$$$ "]" >> K true) false --
    Parse.path -- (Parse.$$$ "exports" |-- Parse.!!! (Scan.repeat1 Parse.string))
  >> (fn ((verbatim, path), keys) => (verbatim, path, keys))

val _ = Outer_Syntax.command @{command_keyword "scala3_export"}
        "Export the given stored scala3 section(s) as Scala 3 source text into a .scala file"
        (export_args >> (fn args => Toplevel.theory (run_scala3_export args)))

(* The _reject commands store nothing, so they are "diag"; Isabelle evaluates a diag command
   asynchronously, in parallel with the commands after it (Pure/PIDE/command.ML,
   "Toplevel.diag") - harmless here, as every parse has its own state. Correct rejection
   means a parse failure under the silent, locally-raising error callback (see
   "Scala3_Parse.parse_quiet"). *)
fun run_reject entry kind_name source thy =
    let
      val ctxt = Proof_Context.init_global thy
      val rejected =
        (case Scala3_Parse.parse_quiet entry ctxt source of
           SOME _ => false
         | NONE => true)
          handle Scala3_Parse.Rejected _ => true
      val _ =
        if rejected
        then writeln ("OK: malformed input was correctly rejected as an " ^ kind_name ^ ".")
        else error   ("Malformed-input test FAILED: the parser unexpectedly accepted this as an " ^
                       kind_name ^ ".")
    in thy end

val _ = Outer_Syntax.command @{command_keyword "scala3_reject"}
        "Check that a Scala 3 fragment is correctly rejected as a compilation unit"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory (run_reject Scala3_Parse.Entry_Unit "Scala 3 compilation unit" source)))

val _ = Outer_Syntax.command @{command_keyword "scala3_ident_reject"}
        "Check that a fragment is correctly rejected as a Scala 3 name"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory (run_reject Scala3_Parse.Entry_Id "Scala 3 name" source)))

val _ = Outer_Syntax.command @{command_keyword "scala3_type_reject"}
        "Check that a fragment is correctly rejected as a Scala 3 type"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory (run_reject Scala3_Parse.Entry_Type "Scala 3 type" source)))

val _ = Outer_Syntax.command @{command_keyword "scala3_expr_reject"}
        "Check that a fragment is correctly rejected as a Scala 3 expression"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory (run_reject Scala3_Parse.Entry_Expr "Scala 3 expression" source)))

end (* local open *)
\<close>

text\<open>The environment as it stands now - the standard antiquotation handlers of
  \<^verbatim>\<open>Scala3_AnaEval.thy\<close> registered, nothing declared - is what \<open>reset_senv\<close> restores
  unless a later theory nominates another snapshot.\<close>
set_senv_default

end
