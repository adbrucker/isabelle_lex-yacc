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

theory AdaSpark
  imports "AdaSpark_Parser" "AdaSpark_AnaEval"
  keywords "adaspark" "adaspark_body" "adaspark_ident"
           "adaspark_expr" "adaspark_type" :: thy_decl
  and      "adaspark_file" :: thy_load
  and      "adaspark_reject" "adaspark_body_reject" "adaspark_ident_reject"
           "adaspark_expr_reject" "adaspark_type_reject" :: diag
  and      "set_aenv_default" "reset_aenv" :: thy_decl
  and      "setup_backend" :: thy_decl
  and      "adaspark_export" :: thy_decl
  and      "exports" "verbatim"
begin

text\<open>
  This theory is the AdaSpark analogue of the C11, occam2, Scala 3 and
  AdaSpark core theories (\<^verbatim>\<open>C11/C11.thy\<close>, \<^verbatim>\<open>occam2/Occam2.thy\<close>,
  \<^verbatim>\<open>scala3/Scala3.thy\<close>, \<^verbatim>\<open>AdaSpark/AdaSpark.thy\<close>): an ml-lex/ml-yacc
  lexer/parser pair for Ada 2012 and its SPARK 2014 subset - see
  \<^verbatim>\<open>AdaSpark_Parser.thy\<close> for what is covered - producing a real abstract
  syntax tree (\<^verbatim>\<open>adaspark_ast.ML\<close>), plus the Isar commands that run it:
  \<open>adaspark\<close> (a source file: a sequence of compilation units),
  \<open>adaspark_body\<close> (a sequence of statements), \<open>adaspark_expr\<close>,
  \<open>adaspark_type\<close> (a subtype indication), \<open>adaspark_ident\<close>, \<open>adaspark_file\<close>,
  their \<open>_reject\<close> counterparts for negative tests, and \<open>adaspark_export\<close>. The
  concepts are those of the C11 project, carried over one for one:

     \<^item> \<^bold>\<open>Comments and antiquotations.\<close> Ada has \<^verbatim>\<open>--\<close> line comments only. A comment
       may contain \<^verbatim>\<open>@tag[navi](level) \<open>...\<close>\<close> antiquotations (the cartouche may
       span lines); the comment is attached to the AST node of the next real
       token. A \<^emph>\<open>bodyless\<close> tag is recognised only directly after the opener
       (\<^verbatim>\<open>--@ highlight\<close>), so as not to take an \<^verbatim>\<open>@\<close> in running comment text for
       an antiquotation. Plain comments are kept as \<open>Raw_txt\<close>; the annotations
       of the older SPARK language (\<^verbatim>\<open>--# pre ...\<close>) are plain comments.
     \<^item> \<^bold>\<open>Binding.\<close> Every declaration site and every use of a name that resolves is
       reported with Isabelle's entity markup: hover and click-through from a
       use to its declaration, with Ada's one case-insensitive name space,
       its sequential visibility and its packages. A name that resolves
       nowhere is not marked, as in Ada it routinely comes from a \<open>with\<close>ed
       unit or a predefined package. See \<^verbatim>\<open>AdaSpark_AnaEval.thy\<close>.
     \<^item> \<^bold>\<open>Navigation.\<close> \<^verbatim>\<open>@tag[u|U|r|d...]\<close> re-targets an antiquotation from the node
       a comment is attached to to a parent, sibling or child, with the same
       four-letter language and rules as C11.
     \<^item> \<^bold>\<open>Antiquotations\<close> are dispatched in ascending \<open>level\<close> order after the whole
       unit has been analysed, and see the \<^emph>\<open>resolved\<close> node; the standard ones
       (\<open>probe_aenv\<close>, \<open>probe_ast\<close>, \<open>highlight\<close>, \<open>term\<close>, \<open>ML\<close>, \<open>text\<close>,
       \<open>definition\<close>, \<open>lemma\<close>) are registered in \<^verbatim>\<open>AdaSpark_AnaEval.thy\<close>.
     \<^item> \<^bold>\<open>The semantic-backend hook.\<close> At the very end of
       \<open>adaspark\<close>/\<open>adaspark_file\<close>/\<open>adaspark_body\<close>, after the antiquotation
       actions have run and the AST is stored, a function of type \<open>pos
       AdaSpark_Ast.root -> theory -> theory\<close> kept in the theory's context is
       applied; it is \<open>K I\<close> by default, and \<open>setup_backend \<open>f\<close>\<close> installs another
       one. This is where a translation of SPARK contracts to proof obligations
       (or to anything else) plugs in.

  What is specific to AdaSpark is the syntax itself: no layout and no stream
  between lexer and parser, but a case-insensitive language in which a name is
  an expression, contracts are \<^emph>\<open>aspects\<close> (\<open>with Pre => ..., Post => ...\<close>), and
  the apostrophe is both the attribute tick and the delimiter of a character
  literal - all explained in \<^verbatim>\<open>AdaSpark_Parser.thy\<close>. The grammar reads the Ada
  sources of Isabelle's own SPARK examples (see \<^verbatim>\<open>AdaSpark_Tests.thy\<close>, which runs
  them, and \<^verbatim>\<open>README.md\<close>).
\<close>

subsection\<open>Defining the Isar-toplevel Commands\<close>

text\<open>
  As in C11 each accepting command stores the parsed AST under a fresh
  per-theory key (\<open>"Theory#N"\<close>, reported as \<open>[stored as ...]\<close>) in
  \<^ML_structure>\<open>AEnv.Ast_Store\<close>. The parser has one grammar entry point per command
  (\<open>Entry_Crate\<close>, \<open>Entry_Body\<close>, \<open>Entry_Expr\<close>, \<open>Entry_Type\<close>, \<open>Entry_Id\<close>), so no
  result shape needs gating afterwards; a \<open>_reject\<close> command succeeds exactly
  when the fragment is \<^emph>\<open>not\<close> accepted by the corresponding entry point,
  silently, without leaving error markup. Only \<open>adaspark\<close> and \<open>adaspark_file\<close>
  (whole program units) chain their antiquotation actions into the stored
  theory; \<open>adaspark_expr\<close> and \<open>adaspark_ident\<close> are syntax checks on a fragment
  and run the analysis only for its hyperlinking.
\<close>
ML\<open>
local open AEnv in

fun string_of_root (AdaSpark_Ast.Id id) =
      "Id " ^ AdaSpark_Ast.ident_name id ^ " "
        ^ Position.here (AdaSpark_Ast.pos_of_ident id)
  | string_of_root (AdaSpark_Ast.Expr e) =
      "Expr " ^ Position.here (AdaSpark_Ast.pos_of_expr e)
  | string_of_root (AdaSpark_Ast.Type t) =
      "Type " ^ Position.here (AdaSpark_Ast.pos_of_sub t)
  | string_of_root (AdaSpark_Ast.Stmt s) =
      "Stmt " ^ Position.here (AdaSpark_Ast.pos_of_stmt s)
  | string_of_root (AdaSpark_Ast.Decl d) =
      "Decl " ^ Position.here (AdaSpark_Ast.pos_of_decl d)
  | string_of_root (AdaSpark_Ast.Body ss) =
      "Body (" ^ Int.toString (length ss) ^ " statement(s))"
  | string_of_root (AdaSpark_Ast.Crate units) =
      "Crate (" ^ Int.toString (length units) ^ " unit(s))"

(* The antiquotation actions are folded together as a plain
   "Context.generic -> Context.generic" function in ascending "level" order
   (a stable sort, so equal levels keep their textual order) - see the note on
   "full_eval_and_store" in C11.thy for why they are never lifted one by one. *)
(* The last step is the semantic-backend hook (AEnv.get_backend, "setup_backend"
   below): a function from the parsed root and the theory the root has just been
   stored into to a theory, "K I" unless a backend has been installed. It runs
   after the root is stored and reported, and only for
   "adaspark"/"adaspark_file", the commands whose input is a genuine program
   unit. *)
fun full_eval_and_store root text thy =
    let
      val (thy', antiq_evals) = AnaEval.analyse_and_eval root thy
      val sorted_evals =
        sort (fn ((l1, _), (l2, _)) => Int.compare (l1, l2)) antiq_evals
      val context_for_store =
        fold (fn (_, f) => f) sorted_evals (Context.Theory thy')
      val thy_for_store = Context.theory_of context_for_store
      val (key, thy'') = store_root root text thy_for_store
      val _ = writeln (string_of_root root ^ "  [stored as " ^ key ^ "]")
    in get_backend thy'' root thy'' end

(* A fragment (identifier, expression): analysed for its hyperlinks only. *)
fun fragment_and_store entry cmd_name source thy =
    let
      val ctxt = Proof_Context.init_global thy
    in
      case AdaSpark_Parse.parse_loud entry ctxt source of
        NONE => error (cmd_name ^ ": no result")
      | SOME root =>
          let
            val _ = AnaEval.analyse_and_eval root thy
            val (key, thy'') = store_root root (Input.text_of source) thy
            val _ = writeln (string_of_root root ^ "  [stored as " ^ key ^ "]")
          in thy'' end
    end

fun full_eval_body source thy =
    let val ctxt = Proof_Context.init_global thy
    in
      case AdaSpark_Parse.parse_loud AdaSpark_Parse.Entry_Body ctxt source of
        NONE => error "adaspark_body: no result"
      | SOME root => full_eval_and_store root (Input.text_of source) thy
    end

fun run_adaspark source thy =
    let val ctxt = Proof_Context.init_global thy
    in
      case AdaSpark_Parse.parse_loud AdaSpark_Parse.Entry_Crate ctxt source of
        NONE => error "adaspark: no result"
      | SOME root => full_eval_and_store root (Input.text_of source) thy
    end

val _ = Outer_Syntax.command @{command_keyword "adaspark"}
        "Syntax check a AdaSpark program unit and store its AST"
        (Parse.input
         Parse.cartouche >> (fn source =>
                             Toplevel.theory (run_adaspark source)))

val _ = Outer_Syntax.command @{command_keyword "adaspark_ident"}
        "Syntax check a bare AdaSpark name and store its AST"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory
             (fragment_and_store AdaSpark_Parse.Entry_Id
              "adaspark_ident" source)))

val _ = Outer_Syntax.command @{command_keyword "adaspark_type"}
        "Syntax check a AdaSpark type and store its AST"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory
             (fragment_and_store AdaSpark_Parse.Entry_Type
              "adaspark_type" source)))

val _ = Outer_Syntax.command @{command_keyword "adaspark_body"}
        ("Syntax check a statement sequence (" ^
         "expression) and store its AST")
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory (full_eval_body source)))

val _ = Outer_Syntax.command @{command_keyword "adaspark_expr"}
        "Syntax check a AdaSpark expression and store its AST"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory
             (fragment_and_store AdaSpark_Parse.Entry_Expr
              "adaspark_expr" source)))

(* "thy_load", not "diag", for the reason given at "c11_file" in C11.thy:
   only a thy_load command gets the file dependency registered. *)
fun run_adaspark_file get_file thy =
    let
      val file = get_file thy
      val source = Token.file_source file
      val ctxt = Proof_Context.init_global thy
    in
      case AdaSpark_Parse.parse_loud AdaSpark_Parse.Entry_Crate ctxt source of
        NONE => error "adaspark_file: no result"
      | SOME root => full_eval_and_store root (Input.text_of source) thy
    end

val _ = Outer_Syntax.command @{command_keyword "adaspark_file"}
        ("Read and syntax-check an external AdaSpark source file, and " ^
         "store its AST")
        (Resources.parse_file >> (fn get_file =>
                                  Toplevel.theory
                                    (run_adaspark_file get_file)))

fun report_aenv_size label thy =
    let val mk {names, ...} = get (Context.Theory thy)
    in writeln
      (label ^ ": " ^ Int.toString (Symtab.fold (K (fn n => n + 1)) names 0)
       ^ " name(s)") end

val _ = Outer_Syntax.command @{command_keyword "set_aenv_default"}
        "Nominate the current aenv as the snapshot a later reset_aenv restores"
        (Scan.succeed (Toplevel.theory (fn thy =>
          let val thy' = set_aenv_default thy
            in report_aenv_size "set_aenv_default" thy'; thy' end)))

val _ = Outer_Syntax.command @{command_keyword "reset_aenv"}
        ("Reset aenv to the snapshot set_aenv_default last nominated (or " ^
         "empty_aenv, if none yet)")
        (Scan.succeed (Toplevel.theory (fn thy =>
          let val thy' = reset_aenv thy
            in report_aenv_size "reset_aenv" thy'; thy' end)))

(* "setup_backend \<open>f\<close>" installs the semantic backend that "full_eval_and_store"
   runs at the end of every "adaspark"/"adaspark_file": "f" is an ML
   expression of type "Position.T AdaSpark_Ast.root -> theory -> theory",
   evaluated exactly like the argument of Isabelle's own "setup" command
   (Isar_Cmd.setup). The default is "K I"; "setup_backend \<open>K I\<close>" restores it.
   The function lives in the theory's context and is inherited by later
   theories. *)
fun setup_backend source =
  ML_Context.expression (Input.pos_of source)
    (ML_Lex.read "Theory.setup (AEnv.set_backend (" @ ML_Lex.read_source source
     @ ML_Lex.read "))")
  |> Context.theory_map

val _ = Outer_Syntax.command @{command_keyword "setup_backend"}
        ("Install the semantic backend run at the end of every " ^
         "adaspark/adaspark_file")
        (Parse.ML_source >> (Toplevel.theory o setup_backend))

(* "adaspark_export name exports key ..." writes the stored sections, printed
   back with "AdaSpark_Pp.pp_root" (or, with "[verbatim]", as originally
   written), to "name.ada" in the theory's master directory. Same contract as
   "c11_export_c" (see C11.thy). *)
fun run_adaspark_export (verbatim, path, keys) thy =
    let
      val out_path =
        Path.append (Resources.master_directory thy)
          (Path.explode (path ^ ".ada"))
      fun unknown key =
        error ("no stored adaspark section named " ^ quote key ^
               " (expected one of the \"[stored as ...]\" keys the " ^
               "adaspark commands report)")
      fun text_of key =
        if verbatim
        then (case get_source key thy of SOME text => text | NONE =>
              unknown key)
        else (case get_ast key thy of SOME root =>
              AdaSpark_Pp.pp_root root | NONE => unknown key)
      val _ = File.write out_path
        (space_implode "\n\n" (map text_of keys) ^ "\n")
      val _ = writeln
        ("Exported " ^ Int.toString (length keys) ^ " section(s) to " ^
                        Path.print out_path)
    in thy end

val export_args =
  Scan.optional
    (Parse.$$$ "[" |-- Parse.$$$ "verbatim" --| Parse.$$$ "]" >> K true)
      false --
    Parse.path -- (Parse.$$$ "exports" |-- Parse.!!! (Scan.repeat1
        Parse.string))
  >> (fn ((verbatim, path), keys) => (verbatim, path, keys))

val _ = Outer_Syntax.command @{command_keyword "adaspark_export"}
        ("Export the given stored adaspark section(s) as AdaSpark source " ^
         "text into an .ada file")
        (export_args >> (fn args =>
                         Toplevel.theory (run_adaspark_export args)))

(* The _reject commands store nothing, so they are "diag"; Isabelle evaluates a
   diag command asynchronously, in parallel with the commands after it
   (Pure/PIDE/command.ML, "Toplevel.diag") - harmless here, as every parse has
   its own state. Correct rejection means a parse failure under the silent,
   locally-raising error callback (see "AdaSpark_Parse.parse_quiet"). *)
fun run_reject entry kind_name source thy =
    let
      val ctxt = Proof_Context.init_global thy
      val rejected =
        (case AdaSpark_Parse.parse_quiet entry ctxt source of
           SOME _ => false
         | NONE => true)
          handle AdaSpark_Parse.Rejected _ => true
      val _ =
        if rejected
        then writeln
          ("OK: malformed input was correctly rejected as an " ^ kind_name
           ^ ".")
        else error ("Malformed-input test FAILED: the parser unexpectedly " ^
                    "accepted this as an " ^ kind_name ^ ".")
    in thy end

val _ = Outer_Syntax.command @{command_keyword "adaspark_reject"}
        "Check that a AdaSpark fragment is correctly rejected as a source file"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory
             (run_reject AdaSpark_Parse.Entry_Crate
              "AdaSpark source file" source)))

val _ = Outer_Syntax.command @{command_keyword "adaspark_body_reject"}
        "Check that a fragment is correctly rejected as a statement sequence"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory
             (run_reject AdaSpark_Parse.Entry_Body
              "statement sequence" source)))

val _ = Outer_Syntax.command @{command_keyword "adaspark_ident_reject"}
        "Check that a fragment is correctly rejected as a AdaSpark name"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory
             (run_reject AdaSpark_Parse.Entry_Id "AdaSpark name" source)))

val _ = Outer_Syntax.command @{command_keyword "adaspark_type_reject"}
        "Check that a fragment is correctly rejected as a AdaSpark type"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory
             (run_reject AdaSpark_Parse.Entry_Type "AdaSpark type" source)))

val _ = Outer_Syntax.command @{command_keyword "adaspark_expr_reject"}
        "Check that a fragment is correctly rejected as a AdaSpark expression"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory
             (run_reject AdaSpark_Parse.Entry_Expr
              "AdaSpark expression" source)))

end (* local open *)
\<close>

text\<open>The environment as it stands now - the standard antiquotation handlers of
  \<^verbatim>\<open>AdaSpark_AnaEval.thy\<close> registered, nothing declared - is what \<open>reset_aenv\<close>
  restores unless a later theory nominates another snapshot.\<close>
set_aenv_default

end
