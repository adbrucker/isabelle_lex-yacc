(***********************************************************************************
 * Copyright (c) University of Paris-Saclay
 *
 * All rights reserved.
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

theory Occam2
  imports "Occam2_Parser" "Occam2_AnaEval"
  keywords "occam2" "occam2_ident" "occam2_expr" :: thy_decl
  and      "occam2_file" :: thy_load
  and      "occam2_reject" "occam2_ident_reject" "occam2_expr_reject" :: diag
  and      "set_oenv_default" "reset_oenv" :: thy_decl
  and      "setup_backend" :: thy_decl
  and      "occam2_export" :: thy_decl
  and      "exports" "verbatim"
begin

text\<open>
  This theory is the occam 2 analogue of the C11 core theory (\<^verbatim>\<open>C11/C11.thy\<close>) of
  Isabelle/C Version 2.0: an ml-lex/ml-yacc lexer/parser pair for the language of the
  INMOS \<^emph>\<open>occam 2 Reference Manual\<close> (Prentice Hall, 1988; appendix G is the
  grammar followed here), producing a real abstract syntax tree (\<^verbatim>\<open>occam2_ast.ML\<close>),
  plus the Isar commands that run it: \<open>occam2\<close> (a program unit), \<open>occam2_expr\<close>,
  \<open>occam2_ident\<close>, \<open>occam2_file\<close>, their \<open>_reject\<close> counterparts for negative tests, and
  \<open>occam2_export\<close>. The remaining concepts are those of the C11 project, carried over
  one for one:

  \<^item> \<^bold>\<open>Comments and antiquotations.\<close> occam has only \<^verbatim>\<open>--\<close> line comments. A comment
    may contain \<^verbatim>\<open>@tag[navi](level) \<open>...\<close>\<close> antiquotations (the cartouche may span lines);
    the comment is attached to the AST node of the next real token. Plain comments
    are kept as \<open>Raw_txt\<close>.
  \<^item> \<^bold>\<open>Binding.\<close> Every declaration site and every use of a name is reported with
    Isabelle's entity markup: hover and click-through from a use to its declaration,
    with the usual occam scoping (a specification scopes over the process it prefixes;
    no recursion; replicator indices scope over their body). Undeclared names are
    underlined, not rejected. See \<^verbatim>\<open>Occam2_AnaEval.thy\<close>.
  \<^item> \<^bold>\<open>Navigation.\<close> \<^verbatim>\<open>@tag[u|U|r|d...]\<close> re-targets an antiquotation from the node a
    comment is attached to to a parent, sibling or child, with the same four-letter
    language and rules as C11.
  \<^item> \<^bold>\<open>Antiquotations\<close> are dispatched in ascending \<open>level\<close> order after the whole unit
    has been analysed, and see the \<^emph>\<open>resolved\<close> node; the standard ones (\<open>probe_oenv\<close>,
    \<open>probe_ast\<close>, \<open>highlight\<close>, \<open>term\<close>, \<open>ML\<close>, \<open>text\<close>, \<open>definition\<close>, \<open>lemma\<close>) are
    registered in \<^verbatim>\<open>Occam2_AnaEval.thy\<close>.
  \<^item> \<^bold>\<open>The semantic-backend hook.\<close> At the very end of \<open>occam2\<close>/\<open>occam2_file\<close>, after the
    antiquotation actions have run and the AST is stored, a function of type
    \<open>pos Occam2_Ast.root -> theory -> theory\<close> kept in the theory's context is applied; it is
    \<open>K I\<close> by default, and \<open>setup_backend \<open>f\<close>\<close> installs another one.

  What is specific to occam, and so handled differently from C11, is \<^emph>\<open>layout\<close>. The
  language has no braces: a construct's body is its lines indented two spaces deeper
  (the manual's only layout rule), and the manual writes this as "the process is
  indented by two spaces". The lexer therefore records, per token, the indentation of
  the line it starts, and a small stream transformer between lexer and parser
  (\<open>Occam2_Parse.layout_stream\<close>, in \<^verbatim>\<open>Occam2_Parser.thy\<close>) turns indentation changes into
  explicit NEWLINE / INDENT / OUTDENT tokens with the classical indentation stack. A
  line that follows an operator, a comma, a semicolon, an assignment or one of
  \<open>IS\<close>, \<open>FROM\<close>, \<open>FOR\<close> is a continuation line and gets no layout tokens. The grammar
  proper (ml-yacc) is thus context free.

  \<^bold>\<open>Known deviations from the manual\<close> (all deliberate, none affects accepting the
  programs the manual's own examples show):
  \<^item> Indentation is checked leniently: an indent by \<^emph>\<open>more\<close> than two columns is accepted
    (only consistency of dedents is enforced), and tabs count as one column.
  \<^item> The first token of a fragment fixes the base indentation, so a cartouche may be
    indented as a whole.
  \<^item> The grammar has four benign ml-yacc conflicts (one reduce/reduce, three
    shift/reduce), each resolved in the intended way: a declaration \<open>INT x, y:\<close> wins over
    a type conversion \<open>INT x\<close> followed by a comma; \<open>[e]\<close> is read as an array type rather than a
    one-element table; \<open>INT::[]BYTE\<close> is a counted-array protocol rather than \<open>INT\<close> followed
    by something else; and \<open>;\<close> continues a sequential protocol rather than ending it.
  \<^item> Compiler directives (\<open>#USE\<close>, \<open>#INCLUDE\<close>, \<open>#OPTION\<close>, ...), which are not part of
    the language proper in the manual, are not recognised; consequently there is no
    analogue of C11's \<open>c11_predef\<close>. A library-style unit of specifications (parsed by
    \<open>occam2\<close> as a \<open>Specs\<close> root) instead leaves its names in the environment for later
    units to use.
  \<^item> A comment placed directly before a \<^emph>\<open>name\<close> that is not the first token of its
    line is attached to the name, not to the enclosing construct.
\<close>

subsection\<open>Defining the Isar-toplevel Commands\<close>

text\<open>
  As in C11 each accepting command stores the parsed AST under a fresh per-theory key
  (\<open>"Theory#N"\<close>, reported as \<open>[stored as ...]\<close>) in \<^ML_structure>\<open>OEnv.Ast_Store\<close>. The parser
  has one grammar entry point per command (\<open>Entry_Unit\<close>, \<open>Entry_Expr\<close>, \<open>Entry_Id\<close>), so
  no result shape needs gating afterwards; a \<open>_reject\<close> command succeeds exactly when the
  fragment is \<^emph>\<open>not\<close> accepted by the corresponding entry point, silently, without
  leaving error markup. Only \<open>occam2\<close> and \<open>occam2_file\<close> (whole program units) chain their
  antiquotation actions into the stored theory; \<open>occam2_expr\<close> and \<open>occam2_ident\<close> are
  syntax checks on a fragment and run the analysis only for its hyperlinking.
\<close>
ML\<open>
local open OEnv in

fun string_of_root (Occam2_Ast.Id id) =
      "Id " ^ Occam2_Ast.ident_name id ^ " " ^ Position.here (Occam2_Ast.pos_of_ident id)
  | string_of_root (Occam2_Ast.Expr e) =
      "Expr " ^ Position.here (Occam2_Ast.pos_of_expr e)
  | string_of_root (Occam2_Ast.Proc p) =
      "Proc " ^ Position.here (Occam2_Ast.pos_of_process p)
  | string_of_root (Occam2_Ast.Spec s) =
      "Spec " ^ Position.here (Occam2_Ast.pos_of_spec s)
  | string_of_root (Occam2_Ast.Specs ss) =
      "Specs (" ^ Int.toString (length ss) ^ " specification(s))"

(* The antiquotation actions are folded together as a plain
   "Context.generic -> Context.generic" function in ascending "level" order
   (a stable sort, so equal levels keep their textual order) - see the note on
   "full_eval_and_store" in C11.thy for why they are never lifted one by one. *)
(* The last step is the semantic-backend hook (OEnv.get_backend, "setup_backend"
   below): a function from the parsed root and the theory the root has just been
   stored into to a theory, "K I" unless a backend has been installed. It runs
   after the root is stored and reported, and only for "occam2"/"occam2_file", the
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
      case Occam2_Parse.parse_loud entry ctxt source of
        NONE => error (cmd_name ^ ": no result")
      | SOME root =>
          let
            val _ = AnaEval.analyse_and_eval root thy
            val (key, thy'') = store_root root (Input.text_of source) thy
            val _ = writeln (string_of_root root ^ "  [stored as " ^ key ^ "]")
          in thy'' end
    end

fun run_occam2 source thy =
    let val ctxt = Proof_Context.init_global thy
    in
      case Occam2_Parse.parse_loud Occam2_Parse.Entry_Unit ctxt source of
        NONE => error "occam2: no result"
      | SOME root => full_eval_and_store root (Input.text_of source) thy
    end

val _ = Outer_Syntax.command @{command_keyword "occam2"}
        "Syntax check an occam 2 program unit and store its AST"
        (Parse.input Parse.cartouche >> (fn source => Toplevel.theory (run_occam2 source)))

val _ = Outer_Syntax.command @{command_keyword "occam2_ident"}
        "Syntax check a bare occam 2 name and store its AST"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory (fragment_and_store Occam2_Parse.Entry_Id "occam2_ident" source)))

val _ = Outer_Syntax.command @{command_keyword "occam2_expr"}
        "Syntax check an occam 2 expression and store its AST"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory (fragment_and_store Occam2_Parse.Entry_Expr "occam2_expr" source)))

(* "thy_load", not "diag", for the reason given at "c11_file" in C11.thy:
   only a thy_load command gets the file dependency registered. *)
fun run_occam2_file get_file thy =
    let
      val file = get_file thy
      val source = Token.file_source file
      val ctxt = Proof_Context.init_global thy
    in
      case Occam2_Parse.parse_loud Occam2_Parse.Entry_Unit ctxt source of
        NONE => error "occam2_file: no result"
      | SOME root => full_eval_and_store root (Input.text_of source) thy
    end

val _ = Outer_Syntax.command @{command_keyword "occam2_file"}
        "Read and syntax-check an external occam 2 source file, and store its AST"
        (Resources.parse_file >> (fn get_file => Toplevel.theory (run_occam2_file get_file)))

fun report_oenv_size label thy =
    let val mk {idents, ...} = get (Context.Theory thy)
    in writeln (label ^ ": " ^ Int.toString (Symtab.fold (K (fn n => n + 1)) idents 0) ^
                " ident(s)") end

val _ = Outer_Syntax.command @{command_keyword "set_oenv_default"}
        "Nominate the current oenv as the snapshot a later reset_oenv restores"
        (Scan.succeed (Toplevel.theory (fn thy =>
          let val thy' = set_oenv_default thy in report_oenv_size "set_oenv_default" thy'; thy' end)))

val _ = Outer_Syntax.command @{command_keyword "reset_oenv"}
        "Reset oenv to the snapshot set_oenv_default last nominated (or empty_oenv, if none yet)"
        (Scan.succeed (Toplevel.theory (fn thy =>
          let val thy' = reset_oenv thy in report_oenv_size "reset_oenv" thy'; thy' end)))

(* "setup_backend \<open>f\<close>" installs the semantic backend that "full_eval_and_store" runs at
   the end of every "occam2"/"occam2_file": "f" is an ML expression of type
   "Position.T Occam2_Ast.root -> theory -> theory", evaluated exactly like the
   argument of Isabelle's own "setup" command (Isar_Cmd.setup). The default is
   "K I"; "setup_backend \<open>K I\<close>" restores it. The function lives in the theory's
   context and is inherited by later theories. *)
fun setup_backend source =
  ML_Context.expression (Input.pos_of source)
    (ML_Lex.read "Theory.setup (OEnv.set_backend (" @ ML_Lex.read_source source @ ML_Lex.read "))")
  |> Context.theory_map

val _ = Outer_Syntax.command @{command_keyword "setup_backend"}
        "Install the semantic backend run at the end of every occam2/occam2_file"
        (Parse.ML_source >> (Toplevel.theory o setup_backend))

(* "occam2_export name exports key ..." writes the stored sections, printed
   back with "Occam2_Ast.pp_root" (or, with "[verbatim]", as originally
   written), to "name.occ" in the theory's master directory. Same contract as
   "c11_export_c" (see C11.thy). *)
fun run_occam2_export (verbatim, path, keys) thy =
    let
      val out_path = Path.append (Resources.master_directory thy) (Path.explode (path ^ ".occ"))
      fun unknown key = error ("no stored occam2 section named " ^ quote key ^
                               " (expected one of the \"[stored as ...]\" keys the occam2 commands report)")
      fun text_of key =
        if verbatim
        then (case get_source key thy of SOME text => text | NONE => unknown key)
        else (case get_ast key thy of SOME root => Occam2_Ast.pp_root root | NONE => unknown key)
      val _ = File.write out_path (space_implode "\n\n" (map text_of keys) ^ "\n")
      val _ = writeln ("Exported " ^ Int.toString (length keys) ^ " section(s) to " ^
                        Path.print out_path)
    in thy end

val export_args =
  Scan.optional (Parse.$$$ "[" |-- Parse.$$$ "verbatim" --| Parse.$$$ "]" >> K true) false --
    Parse.path -- (Parse.$$$ "exports" |-- Parse.!!! (Scan.repeat1 Parse.string))
  >> (fn ((verbatim, path), keys) => (verbatim, path, keys))

val _ = Outer_Syntax.command @{command_keyword "occam2_export"}
        "Export the given stored occam2 section(s) as occam 2 source text into a .occ file"
        (export_args >> (fn args => Toplevel.theory (run_occam2_export args)))

(* The _reject commands store nothing, so they are "diag"; Isabelle evaluates a diag command
   asynchronously, in parallel with the commands after it (Pure/PIDE/command.ML,
   "Toplevel.diag") - harmless here, as every parse has its own state. Correct rejection
   means a parse failure under the silent, locally-raising error callback (see
   "Occam2_Parse.parse_quiet"). *)
fun run_reject entry kind_name source thy =
    let
      val ctxt = Proof_Context.init_global thy
      val rejected =
        (case Occam2_Parse.parse_quiet entry ctxt source of
           SOME _ => false
         | NONE => true)
          handle Occam2_Parse.Rejected _ => true
      val _ =
        if rejected
        then writeln ("OK: malformed input was correctly rejected as an " ^ kind_name ^ ".")
        else error   ("Malformed-input test FAILED: the parser unexpectedly accepted this as an " ^
                       kind_name ^ ".")
    in thy end

val _ = Outer_Syntax.command @{command_keyword "occam2_reject"}
        "Check that an occam 2 fragment is correctly rejected as a program unit"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory (run_reject Occam2_Parse.Entry_Unit "occam 2 program unit" source)))

val _ = Outer_Syntax.command @{command_keyword "occam2_ident_reject"}
        "Check that a fragment is correctly rejected as an occam 2 name"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory (run_reject Occam2_Parse.Entry_Id "occam 2 name" source)))

val _ = Outer_Syntax.command @{command_keyword "occam2_expr_reject"}
        "Check that a fragment is correctly rejected as an occam 2 expression"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory (run_reject Occam2_Parse.Entry_Expr "occam 2 expression" source)))

end (* local open *)
\<close>

text\<open>The environment as it stands now - the standard antiquotation handlers of
  \<^verbatim>\<open>Occam2_AnaEval.thy\<close> registered, nothing declared - is what \<open>reset_oenv\<close> restores
  unless a later theory nominates another snapshot.\<close>
set_oenv_default

end
