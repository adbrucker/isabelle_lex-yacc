(******************************************************************************
 * Copyright (c) University of Paris-Saclay
 *
 * All rights reserved.
 *
 * Authors: Burkhart Wolff, Claude Sonnet 5.5
 *
 * This is an LLM-generated replication of the Isabelle/C version 2 design to the
 * programming language Rust (MicroRust). It provides an efficient parser for
 * MicroRust, deeply integrated into the Isabelle/PIDE document model, allowing
 * external files as well as in-theory code-snippets which are transparent to
 * the underlying theory. It provides an API for the generated AST’s, and an API
 * to hook up semantic backends that compile these AST’s to theory extensions in
 * Isabelle/HOL. Members of the family come with a MicroRust-specific
 * antiquotation mechanism allowing programmable links to the semantic backends
 * as necessary for support of program-annotations with HOL formulas.
 *
 * This session is part of the Isabelle Programming Language Toolkit
 * (Isabelle/PLTk). The generation has been done with Claude Sonnet 5.5; while
 * the replicants come with a detailed (generated) test-suite for MicroRust, I
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

theory MicroRust
  imports "MicroRust_Parser" "MicroRust_AnaEval"
  keywords "microrust" "microrust_body" "microrust_ident" 
           "microrust_expr" "microrust_type" :: thy_decl
  and      "microrust_file" :: thy_load
  and      "microrust_reject" "microrust_body_reject" "microrust_ident_reject"
           "microrust_expr_reject" "microrust_type_reject" :: diag
  and      "set_renv_default" "reset_renv" :: thy_decl
  and      "setup_backend" :: thy_decl
  and      "microrust_export" :: thy_decl
  and      "exports" "verbatim"
begin

text\<open>
  This theory is the MicroRust analogue of the C11, occam2 and Scala 3 core
  theories (\<^verbatim>\<open>C11/C11.thy\<close>, \<^verbatim>\<open>occam2/Occam2.thy\<close>, \<^verbatim>\<open>scala3/Scala3.thy\<close>): an
  ml-lex/ml-yacc lexer/parser pair for MicroRust - the Rust-like language
  \<^emph>\<open>uRust\<close> of the AutoCorrode verification framework, with a layer of Rust items;
  see \<^verbatim>\<open>MicroRust_Parser.thy\<close> for what is covered and why there is no official
  grammar to follow - producing a real abstract syntax tree
  (\<^verbatim>\<open>microrust_ast.ML\<close>), plus the Isar commands that run it: \<open>microrust\<close> (a
  source file: a sequence of items), \<open>microrust_body\<close> (a uRust function body:
  statements and a final expression, without braces, as written between
  \<open>FunctionBody \<lbrakk>\<close> and \<open>\<rbrakk>\<close>), \<open>microrust_expr\<close>, \<open>microrust_type\<close>,
  \<open>microrust_ident\<close>, \<open>microrust_file\<close>, their \<open>_reject\<close> counterparts for negative
  tests, and \<open>microrust_export\<close>. The concepts are those of the C11 project,
  carried over one for one:

     \<^item> \<^bold>\<open>Comments and antiquotations.\<close> Rust has \<^verbatim>\<open>//\<close> line comments and nested
       \<^verbatim>\<open>/* */\<close> comments (and uRust bodies contain Isabelle's \<open>\<comment>\<open>...\<close>\<close>, which are
       comments too). A comment may contain \<^verbatim>\<open>@tag[navi](level) \<open>...\<close>\<close>
       antiquotations (the cartouche may span lines); the comment is attached to
       the AST node of the next real token. A \<^emph>\<open>bodyless\<close> tag is recognised only
       directly after the opener (\<^verbatim>\<open>//@ highlight\<close>, \<^verbatim>\<open>/*@ highlight */\<close>), so as
       not to take an \<^verbatim>\<open>@\<close> in running comment text for an antiquotation. Plain
       comments are kept as \<open>Raw_txt\<close>.
     \<^item> \<^bold>\<open>Binding.\<close> Every declaration site and every use of a name that resolves is
       reported with Isabelle's entity markup: hover and click-through from a
       use to its declaration, with Rust's scoping and its two name spaces
       (values and types). A name that resolves nowhere is not marked, as in
       Rust it routinely comes from the prelude, a glob import or the standard
       library. See \<^verbatim>\<open>MicroRust_AnaEval.thy\<close>.
     \<^item> \<^bold>\<open>Navigation.\<close> \<^verbatim>\<open>@tag[u|U|r|d...]\<close> re-targets an antiquotation from the node
       a comment is attached to to a parent, sibling or child, with the same
       four-letter language and rules as C11.
     \<^item> \<^bold>\<open>Antiquotations\<close> are dispatched in ascending \<open>level\<close> order after the whole
       unit has been analysed, and see the \<^emph>\<open>resolved\<close> node; the standard ones
       (\<open>probe_renv\<close>, \<open>probe_ast\<close>, \<open>highlight\<close>, \<open>term\<close>, \<open>ML\<close>, \<open>text\<close>,
       \<open>definition\<close>, \<open>lemma\<close>) are registered in \<^verbatim>\<open>MicroRust_AnaEval.thy\<close>.
     \<^item> \<^bold>\<open>The semantic-backend hook.\<close> At the very end of
       \<open>microrust\<close>/\<open>microrust_file\<close>/\<open>microrust_body\<close>, after the antiquotation
       actions have run and the AST is stored, a function of type \<open>pos
       MicroRust_Ast.root -> theory -> theory\<close> kept in the theory's context is
       applied; it is \<open>K I\<close> by default, and \<open>setup_backend \<open>f\<close>\<close> installs another
       one. This is where a translation to AutoCorrode's shallow embedding (or
       to anything else) plugs in.

  What is specific to MicroRust is the syntax itself - braces and semicolons, no
  layout - and the three places where the stream between lexer and parser helps
  the LALR grammar (struct expressions against blocks, \<open>>>\<close> against generics,
  block-like statements), all explained in \<^verbatim>\<open>MicroRust_Parser.thy\<close>. The grammar
  reads all uRust bodies of the AutoCorrode sources (see \<^verbatim>\<open>MicroRust_Tests.thy\<close>,
  which runs them, and \<^verbatim>\<open>README.md\<close>).
\<close>

subsection\<open>Defining the Isar-toplevel Commands\<close>

text\<open>
  As in C11 each accepting command stores the parsed AST under a fresh
  per-theory key (\<open>"Theory#N"\<close>, reported as \<open>[stored as ...]\<close>) in
  \<^ML_structure>\<open>REnv.Ast_Store\<close>. The parser has one grammar entry point per command
  (\<open>Entry_Crate\<close>, \<open>Entry_Body\<close>, \<open>Entry_Expr\<close>, \<open>Entry_Type\<close>, \<open>Entry_Id\<close>), so no
  result shape needs gating afterwards; a \<open>_reject\<close> command succeeds exactly
  when the fragment is \<^emph>\<open>not\<close> accepted by the corresponding entry point,
  silently, without leaving error markup. Only \<open>microrust\<close> and \<open>microrust_file\<close>
  (whole program units) chain their antiquotation actions into the stored
  theory; \<open>microrust_expr\<close> and \<open>microrust_ident\<close> are syntax checks on a fragment
  and run the analysis only for its hyperlinking.
\<close>
ML\<open>
local open REnv in

fun string_of_root (MicroRust_Ast.Id id) =
      "Id " ^ MicroRust_Ast.ident_name id ^ " "
        ^ Position.here (MicroRust_Ast.pos_of_ident id)
  | string_of_root (MicroRust_Ast.Expr e) =
      "Expr " ^ Position.here (MicroRust_Ast.pos_of_expr e)
  | string_of_root (MicroRust_Ast.Type t) =
      "Type " ^ Position.here (MicroRust_Ast.pos_of_type t)
  | string_of_root (MicroRust_Ast.Pat p) =
      "Pat " ^ Position.here (MicroRust_Ast.pos_of_pat p)
  | string_of_root (MicroRust_Ast.Stmt s) =
      "Stmt " ^ Position.here (MicroRust_Ast.pos_of_stmt s)
  | string_of_root (MicroRust_Ast.Item it) =
      "Item " ^ Position.here (MicroRust_Ast.pos_of_item it)
  | string_of_root (MicroRust_Ast.Body (MicroRust_Ast.Block (ss, tail, _))) =
      "Body (" ^ Int.toString (length ss) ^ " statement(s)" 
               ^ (if is_some tail then " and a final expression" else "") ^ ")"
  | string_of_root (MicroRust_Ast.Crate items) =
      "Crate (" ^ Int.toString (length items) ^ " item(s))"

(* The antiquotation actions are folded together as a plain
   "Context.generic -> Context.generic" function in ascending "level" order
   (a stable sort, so equal levels keep their textual order) - see the note on
   "full_eval_and_store" in C11.thy for why they are never lifted one by one. *)
(* The last step is the semantic-backend hook (REnv.get_backend, "setup_backend"
   below): a function from the parsed root and the theory the root has just been
   stored into to a theory, "K I" unless a backend has been installed. It runs
   after the root is stored and reported, and only for
   "microrust"/"microrust_file", the commands whose input is a genuine program
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
      case MicroRust_Parse.parse_loud entry ctxt source of
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
      case MicroRust_Parse.parse_loud MicroRust_Parse.Entry_Body ctxt source of
        NONE => error "microrust_body: no result"
      | SOME root => full_eval_and_store root (Input.text_of source) thy
    end

fun run_microrust source thy =
    let val ctxt = Proof_Context.init_global thy
    in
      case MicroRust_Parse.parse_loud MicroRust_Parse.Entry_Crate ctxt source of
        NONE => error "microrust: no result"
      | SOME root => full_eval_and_store root (Input.text_of source) thy
    end

val _ = Outer_Syntax.command @{command_keyword "microrust"}
        "Syntax check a MicroRust program unit and store its AST"
        (Parse.input
         Parse.cartouche >> (fn source =>
                             Toplevel.theory (run_microrust source)))

val _ = Outer_Syntax.command @{command_keyword "microrust_ident"}
        "Syntax check a bare MicroRust name and store its AST"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory
             (fragment_and_store MicroRust_Parse.Entry_Id
              "microrust_ident" source)))

val _ = Outer_Syntax.command @{command_keyword "microrust_type"}
        "Syntax check a MicroRust type and store its AST"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory
             (fragment_and_store MicroRust_Parse.Entry_Type
              "microrust_type" source)))

val _ = Outer_Syntax.command @{command_keyword "microrust_body"}
        ("Syntax check a uRust function body (statements and a final " ^
         "expression) and store its AST")
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory (full_eval_body source)))

val _ = Outer_Syntax.command @{command_keyword "microrust_expr"}
        "Syntax check a MicroRust expression and store its AST"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory
             (fragment_and_store MicroRust_Parse.Entry_Expr
              "microrust_expr" source)))

(* "thy_load", not "diag", for the reason given at "c11_file" in C11.thy:
   only a thy_load command gets the file dependency registered. *)
fun run_microrust_file get_file thy =
    let
      val file = get_file thy
      val source = Token.file_source file
      val ctxt = Proof_Context.init_global thy
    in
      case MicroRust_Parse.parse_loud MicroRust_Parse.Entry_Crate ctxt source of
        NONE => error "microrust_file: no result"
      | SOME root => full_eval_and_store root (Input.text_of source) thy
    end

val _ = Outer_Syntax.command @{command_keyword "microrust_file"}
        ("Read and syntax-check an external MicroRust source file, and " ^
         "store its AST")
        (Resources.parse_file >> (fn get_file =>
                                  Toplevel.theory
                                    (run_microrust_file get_file)))

fun report_renv_size label thy =
    let val mk {terms, types, ...} = get (Context.Theory thy)
        fun count t = Int.toString (Symtab.fold (K (fn n => n + 1)) t 0)
    in writeln
      (label ^ ": " ^ count terms ^ " term(s), " ^ count types ^ " type(s)") end

val _ = Outer_Syntax.command @{command_keyword "set_renv_default"}
        "Nominate the current renv as the snapshot a later reset_renv restores"
        (Scan.succeed (Toplevel.theory (fn thy =>
          let val thy' = set_renv_default thy
            in report_renv_size "set_renv_default" thy'; thy' end)))

val _ = Outer_Syntax.command @{command_keyword "reset_renv"}
        ("Reset renv to the snapshot set_renv_default last nominated (or " ^
         "empty_renv, if none yet)")
        (Scan.succeed (Toplevel.theory (fn thy =>
          let val thy' = reset_renv thy
            in report_renv_size "reset_renv" thy'; thy' end)))

(* "setup_backend \<open>f\<close>" installs the semantic backend that "full_eval_and_store"
   runs at the end of every "microrust"/"microrust_file": "f" is an ML
   expression of type "Position.T MicroRust_Ast.root -> theory -> theory",
   evaluated exactly like the argument of Isabelle's own "setup" command
   (Isar_Cmd.setup). The default is "K I"; "setup_backend \<open>K I\<close>" restores it.
   The function lives in the theory's context and is inherited by later
   theories. *)
fun setup_backend source =
  ML_Context.expression (Input.pos_of source)
    (ML_Lex.read "Theory.setup (REnv.set_backend (" @ ML_Lex.read_source source
     @ ML_Lex.read "))")
  |> Context.theory_map

val _ = Outer_Syntax.command @{command_keyword "setup_backend"}
        ("Install the semantic backend run at the end of every " ^
         "microrust/microrust_file")
        (Parse.ML_source >> (Toplevel.theory o setup_backend))

(* "microrust_export name exports key ..." writes the stored sections, printed
   back with "MicroRust_Pp.pp_root" (or, with "[verbatim]", as originally
   written), to "name.rs" in the theory's master directory. Same contract as
   "c11_export_c" (see C11.thy). *)
fun run_microrust_export (verbatim, path, keys) thy =
    let
      val out_path =
        Path.append (Resources.master_directory thy)
          (Path.explode (path ^ ".rs"))
      fun unknown key =
        error ("no stored microrust section named " ^ quote key ^
               " (expected one of the \"[stored as ...]\" keys the " ^
               "microrust commands report)")
      fun text_of key =
        if verbatim
        then (case get_source key thy of SOME text => text | NONE =>
              unknown key)
        else (case get_ast key thy of SOME root =>
              MicroRust_Pp.pp_root root | NONE => unknown key)
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

val _ = Outer_Syntax.command @{command_keyword "microrust_export"}
        ("Export the given stored microrust section(s) as MicroRust source " ^
         "text into a .rs file")
        (export_args >> (fn args =>
                         Toplevel.theory (run_microrust_export args)))

(* The _reject commands store nothing, so they are "diag"; Isabelle evaluates a
   diag command asynchronously, in parallel with the commands after it
   (Pure/PIDE/command.ML, "Toplevel.diag") - harmless here, as every parse has
   its own state. Correct rejection means a parse failure under the silent,
   locally-raising error callback (see "MicroRust_Parse.parse_quiet"). *)
fun run_reject entry kind_name source thy =
    let
      val ctxt = Proof_Context.init_global thy
      val rejected =
        (case MicroRust_Parse.parse_quiet entry ctxt source of
           SOME _ => false
         | NONE => true)
          handle MicroRust_Parse.Rejected _ => true
      val _ =
        if rejected
        then writeln
          ("OK: malformed input was correctly rejected as an " ^ kind_name
           ^ ".")
        else error ("Malformed-input test FAILED: the parser unexpectedly " ^
                    "accepted this as an " ^ kind_name ^ ".")
    in thy end

val _ = Outer_Syntax.command @{command_keyword "microrust_reject"}
        "Check that a MicroRust fragment is correctly rejected as a source file"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory
             (run_reject MicroRust_Parse.Entry_Crate
              "MicroRust source file" source)))

val _ = Outer_Syntax.command @{command_keyword "microrust_body_reject"}
        "Check that a fragment is correctly rejected as a uRust function body"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory
             (run_reject MicroRust_Parse.Entry_Body
              "uRust function body" source)))

val _ = Outer_Syntax.command @{command_keyword "microrust_ident_reject"}
        "Check that a fragment is correctly rejected as a MicroRust name"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory
             (run_reject MicroRust_Parse.Entry_Id "MicroRust name" source)))

val _ = Outer_Syntax.command @{command_keyword "microrust_type_reject"}
        "Check that a fragment is correctly rejected as a MicroRust type"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory
             (run_reject MicroRust_Parse.Entry_Type "MicroRust type" source)))

val _ = Outer_Syntax.command @{command_keyword "microrust_expr_reject"}
        "Check that a fragment is correctly rejected as a MicroRust expression"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory
             (run_reject MicroRust_Parse.Entry_Expr
              "MicroRust expression" source)))

end (* local open *)
\<close>

text\<open>The environment as it stands now - the standard antiquotation handlers of
  \<^verbatim>\<open>MicroRust_AnaEval.thy\<close> registered, nothing declared - is what \<open>reset_renv\<close>
  restores unless a later theory nominates another snapshot.\<close>
set_renv_default

end
