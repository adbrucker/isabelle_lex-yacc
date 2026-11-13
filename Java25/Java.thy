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

theory Java
  imports "Java_Parser" "Java_AnaEval"
  keywords "java" "java_decl" "java_stmt" "java_ident" "java_expr" "java_type" :: thy_decl
  and      "java_file" :: thy_load
  and      "java_reject" "java_decl_reject" "java_stmt_reject" "java_ident_reject"
           "java_expr_reject" "java_type_reject" :: diag
  and      "set_jenv_default" "reset_jenv" :: thy_decl
  and      "setup_backend" :: thy_decl
  and      "java_export" :: thy_decl
  and      "exports" "verbatim"
begin

text\<open>
  This theory is the Java analogue of the C11, occam2, Scala 3, MicroRust, AdaSpark and Go core
  theories (\<^verbatim>\<open>C11/C11.thy\<close>, \<^verbatim>\<open>occam2/Occam2.thy\<close>, \<^verbatim>\<open>scala3/Scala3.thy\<close>,
  \<^verbatim>\<open>MicroRust/MicroRust.thy\<close>, \<^verbatim>\<open>AdaSpark/AdaSpark.thy\<close>, \<^verbatim>\<open>Golang1.27/Go.thy\<close>): an ml-lex/ml-yacc
  lexer/parser pair for Java - see \<^verbatim>\<open>Java_Parser.thy\<close> for what is covered; the grammar follows
  the Java Language Specification, Java SE 25 Edition,
  \<^url>\<open>https://docs.oracle.com/javase/specs/jls/se25/html/\<close> - producing a real abstract syntax tree
  (\<^verbatim>\<open>java_ast.ML\<close>), plus the Isar commands that run it: \<open>java\<close> (a compilation unit, ordinary,
  modular or compact), \<open>java_decl\<close> (class body declarations, without a class around them),
  \<open>java_stmt\<close> (block statements), \<open>java_expr\<close>, \<open>java_type\<close>, \<open>java_ident\<close>, \<open>java_file\<close> (an
  external \<^verbatim>\<open>.java\<close> file), their \<open>_reject\<close> counterparts for negative tests, and
  \<open>java_export\<close>. The concepts are those of the C11 project, carried over one for one:

     \<^item> \<^bold>\<open>Comments and antiquotations.\<close> Java has \<^verbatim>\<open>//\<close> line comments and \<^verbatim>\<open>/* */\<close> block comments
       (which do not nest; the documentation comments \<^verbatim>\<open>/** */\<close> are block comments). A comment
       may contain \<^verbatim>\<open>@tag[navi](level) \<open>...\<close>\<close> antiquotations (the cartouche may span lines);
       the comment is attached to the AST node of the next real token. A \<^emph>\<open>bodyless\<close> tag is
       recognised only directly after the opener (\<^verbatim>\<open>//@ highlight\<close>, \<^verbatim>\<open>/*@ highlight */\<close>), so
       as not to take an \<^verbatim>\<open>@\<close> of Javadoc (\<^verbatim>\<open>@param\<close>, \<^verbatim>\<open>@return\<close>) for an antiquotation. Plain
       comments are kept as \<open>Raw_txt\<close>.
     \<^item> \<^bold>\<open>Binding.\<close> Every declaration site and every use of a name that resolves is reported
       with Isabelle's entity markup: hover and click-through from a use to its declaration,
       with Java's several name spaces, its block scoping, the scope of the members of a class,
       the flow scoping of pattern variables, imports and generics, and with the types of
       expressions to link selections and overloaded calls. A name that resolves
       nowhere is not marked, as in Java it routinely comes from an inherited member, an
       on-demand import or the platform. See \<^verbatim>\<open>Java_AnaEval.thy\<close>.
     \<^item> \<^bold>\<open>Navigation.\<close> \<^verbatim>\<open>@tag[u|U|r|d...]\<close> re-targets an antiquotation from the node a comment is
       attached to to a parent, sibling or child, with the same four-letter language and rules
       as C11.
     \<^item> \<^bold>\<open>Antiquotations\<close> are dispatched in ascending \<open>level\<close> order after the whole unit has been
       analysed, and see the \<^emph>\<open>resolved\<close> node; the standard ones (\<open>probe_jenv\<close>, \<open>probe_ast\<close>,
       \<open>highlight\<close>, \<open>term\<close>, \<open>ML\<close>, \<open>text\<close>, \<open>definition\<close>, \<open>lemma\<close>) are registered in
       \<^verbatim>\<open>Java_AnaEval.thy\<close>.
     \<^item> \<^bold>\<open>The semantic-backend hook.\<close> At the very end of \<open>java\<close>/\<open>java_decl\<close>/\<open>java_stmt\<close>/\<open>java_file\<close>,
       after the antiquotation actions have run and the AST is stored, a function of type \<open>pos
       Java_Ast.root -> theory -> theory\<close> kept in the theory's context is applied; it is \<open>K I\<close>
       by default, and \<open>setup_backend \<open>f\<close>\<close> installs another one. This is where a translation
       of Java programs to HOL (or to anything else) plugs in.

  What is specific to Java is a grammar that an LALR(1) parser cannot read over the plain tokens:
  type arguments against comparisons, lambdas and casts against parenthesized expressions,
  the contextual keywords. These are resolved in a stream between lexer and parser, explained in
  \<^verbatim>\<open>Java_Parser.thy\<close>. The grammar reads the whole platform of Java 25 (see \<^verbatim>\<open>Java_Tests.thy\<close>,
  which runs it if the source archive of a JDK is available, and \<^verbatim>\<open>README.md\<close>).
\<close>

subsection\<open>Defining the Isar-toplevel Commands\<close>

text\<open>
  As in C11 each accepting command stores the parsed AST under a fresh
  per-theory key (\<open>"Theory#N"\<close>, reported as \<open>[stored as ...]\<close>) in
  \<^ML_structure>\<open>JEnv.Ast_Store\<close>. The parser has one grammar entry point per command
  (\<open>Entry_Unit\<close>, \<open>Entry_Decls\<close>, \<open>Entry_Stmts\<close>, \<open>Entry_Expr\<close>, \<open>Entry_Type\<close>, \<open>Entry_Id\<close>), so no
  result shape needs gating afterwards; a \<open>_reject\<close> command succeeds exactly
  when the fragment is \<^emph>\<open>not\<close> accepted by the corresponding entry point,
  silently, without leaving error markup. Only \<open>java\<close> and \<open>java_file\<close>
  (whole program units) chain their antiquotation actions into the stored
  theory; \<open>java_expr\<close> and \<open>java_ident\<close> are syntax checks on a fragment
  and run the analysis only for its hyperlinking.
\<close>
ML\<open>
local open JEnv in

fun string_of_root (Java_Ast.Id id) =
      "Id " ^ Java_Ast.ident_name id ^ " " ^ Position.here (Java_Ast.pos_of_ident id)
  | string_of_root (Java_Ast.Expr e) = "Expr " ^ Position.here (Java_Ast.pos_of_expr e)
  | string_of_root (Java_Ast.Type t) = "Type " ^ Position.here (Java_Ast.pos_of_type t)
  | string_of_root (Java_Ast.Stmt s) = "Stmt " ^ Position.here (Java_Ast.pos_of_stmt s)
  | string_of_root (Java_Ast.Decl d) = "Decl " ^ Position.here (Java_Ast.pos_of_decl d)
  | string_of_root (Java_Ast.Stmts ss) = "Stmts (" ^ Int.toString (length ss) ^ " statement(s))"
  | string_of_root (Java_Ast.Decls ds) = "Decls (" ^ Int.toString (length ds) ^ " declaration(s))"
  | string_of_root (Java_Ast.Source (Java_Ast.Unit (_, imports, body, _))) =
      "Source (" ^ Int.toString (length imports) ^ " import(s), "
      ^ (case body of
           Java_Ast.Types ds => Int.toString (length ds) ^ " declaration(s)"
         | Java_Ast.Module (_, _, name, _, _) =>
             "module " ^ space_implode "." (map Java_Ast.ident_name name)) ^ ")"

(* The antiquotation actions are folded together as a plain
   "Context.generic -> Context.generic" function in ascending "level" order
   (a stable sort, so equal levels keep their textual order) - see the note on
   "full_eval_and_store" in C11.thy for why they are never lifted one by one. *)
(* The last step is the semantic-backend hook (JEnv.get_backend, "setup_backend"
   below): a function from the parsed root and the theory the root has just been
   stored into to a theory, "K I" unless a backend has been installed. It runs
   after the root is stored and reported, and only for
   "java"/"java_file", the commands whose input is a genuine program
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
      case Java_Parse.parse_loud entry ctxt source of
        NONE => error (cmd_name ^ ": no result")
      | SOME root =>
          let
            val _ = AnaEval.analyse_and_eval root thy
            val (key, thy'') = store_root root (Input.text_of source) thy
            val _ = writeln (string_of_root root ^ "  [stored as " ^ key ^ "]")
          in thy'' end
    end

fun full_eval_entry entry cmd_name source thy =
    let val ctxt = Proof_Context.init_global thy
    in
      case Java_Parse.parse_loud entry ctxt source of
        NONE => error (cmd_name ^ ": no result")
      | SOME root => full_eval_and_store root (Input.text_of source) thy
    end

fun run_java source thy =
    let val ctxt = Proof_Context.init_global thy
    in
      case Java_Parse.parse_loud Java_Parse.Entry_Unit ctxt source of
        NONE => error "java: no result"
      | SOME root => full_eval_and_store root (Input.text_of source) thy
    end

val _ = Outer_Syntax.command @{command_keyword "java"}
        "Syntax check a Java compilation unit and store its AST"
        (Parse.input
         Parse.cartouche >> (fn source =>
                             Toplevel.theory (run_java source)))

val _ = Outer_Syntax.command @{command_keyword "java_ident"}
        "Syntax check a bare Java name and store its AST"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory
             (fragment_and_store Java_Parse.Entry_Id
              "java_ident" source)))

val _ = Outer_Syntax.command @{command_keyword "java_type"}
        "Syntax check a Java type and store its AST"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory
             (fragment_and_store Java_Parse.Entry_Type
              "java_type" source)))

val _ = Outer_Syntax.command @{command_keyword "java_stmt"}
        "Syntax check a Java block statements and store its AST"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory (full_eval_entry Java_Parse.Entry_Stmts "java_stmt" source)))

val _ = Outer_Syntax.command @{command_keyword "java_decl"}
        "Syntax check Java member declarations (without a class around them) and store their AST"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory (full_eval_entry Java_Parse.Entry_Decls "java_decl" source)))

val _ = Outer_Syntax.command @{command_keyword "java_expr"}
        "Syntax check a Java expression and store its AST"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory
             (fragment_and_store Java_Parse.Entry_Expr
              "java_expr" source)))

(* "thy_load", not "diag", for the reason given at "c11_file" in C11.thy:
   only a thy_load command gets the file dependency registered. *)
fun run_java_file get_file thy =
    let
      val file = get_file thy
      val source = Token.file_source file
      val ctxt = Proof_Context.init_global thy
    in
      case Java_Parse.parse_loud Java_Parse.Entry_Unit ctxt source of
        NONE => error "java_file: no result"
      | SOME root => full_eval_and_store root (Input.text_of source) thy
    end

val _ = Outer_Syntax.command @{command_keyword "java_file"}
        ("Read and syntax-check an external Java compilation unit, and " ^
         "store its AST")
        (Resources.parse_file >> (fn get_file =>
                                  Toplevel.theory
                                    (run_java_file get_file)))

fun report_jenv_size label thy =
    let val mk {names, ...} = get (Context.Theory thy)
    in writeln
      (label ^ ": " ^ Int.toString (Symtab.fold (K (fn n => n + 1)) names 0)
       ^ " name(s)") end

val _ = Outer_Syntax.command @{command_keyword "set_jenv_default"}
        "Nominate the current jenv as the snapshot a later reset_jenv restores"
        (Scan.succeed (Toplevel.theory (fn thy =>
          let val thy' = set_jenv_default thy
            in report_jenv_size "set_jenv_default" thy'; thy' end)))

val _ = Outer_Syntax.command @{command_keyword "reset_jenv"}
        ("Reset jenv to the snapshot set_jenv_default last nominated (or " ^
         "empty_jenv, if none yet)")
        (Scan.succeed (Toplevel.theory (fn thy =>
          let val thy' = reset_jenv thy
            in report_jenv_size "reset_jenv" thy'; thy' end)))

(* "setup_backend \<open>f\<close>" installs the semantic backend that "full_eval_and_store"
   runs at the end of every "java"/"java_decl"/"java_stmt"/"java_file": "f" is an ML
   expression of type "Position.T Java_Ast.root -> theory -> theory",
   evaluated exactly like the argument of Isabelle's own "setup" command
   (Isar_Cmd.setup). The default is "K I"; "setup_backend \<open>K I\<close>" restores it.
   The function lives in the theory's context and is inherited by later
   theories. *)
fun setup_backend source =
  ML_Context.expression (Input.pos_of source)
    (ML_Lex.read "Theory.setup (JEnv.set_backend (" @ ML_Lex.read_source source
     @ ML_Lex.read "))")
  |> Context.theory_map

val _ = Outer_Syntax.command @{command_keyword "setup_backend"}
        ("Install the semantic backend run at the end of every " ^
         "go/java_decl/java_stmt/java_file")
        (Parse.ML_source >> (Toplevel.theory o setup_backend))

(* "java_export name exports key ..." writes the stored sections, printed
   back with "Java_Pp.pp_root" (or, with "[verbatim]", as originally
   written), to "name.java" in the theory's master directory. Same contract as
   "c11_export_c" (see C11.thy). *)
fun run_java_export (verbatim, path, keys) thy =
    let
      val out_path =
        Path.append (Resources.master_directory thy)
          (Path.explode (path ^ ".java"))
      fun unknown key =
        error ("no stored java section named " ^ quote key ^
               " (expected one of the \"[stored as ...]\" keys the " ^
               "go commands report)")
      fun text_of key =
        if verbatim
        then (case get_source key thy of SOME text => text | NONE =>
              unknown key)
        else (case get_ast key thy of SOME root =>
              Java_Pp.pp_root root | NONE => unknown key)
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

val _ = Outer_Syntax.command @{command_keyword "java_export"}
        ("Export the given stored java section(s) as Java source " ^
         "text into a .go file")
        (export_args >> (fn args =>
                         Toplevel.theory (run_java_export args)))

(* The _reject commands store nothing, so they are "diag"; Isabelle evaluates a
   diag command asynchronously, in parallel with the commands after it
   (Pure/PIDE/command.ML, "Toplevel.diag") - harmless here, as every parse has
   its own state. Correct rejection means a parse failure under the silent,
   locally-raising error callback (see "Java_Parse.parse_quiet"). *)
fun run_reject entry kind_name source thy =
    let
      val ctxt = Proof_Context.init_global thy
      val rejected =
        (case Java_Parse.parse_quiet entry ctxt source of
           SOME _ => false
         | NONE => true)
          handle Java_Parse.Rejected _ => true
      val _ =
        if rejected
        then writeln
          ("OK: malformed input was correctly rejected as an " ^ kind_name
           ^ ".")
        else error ("Malformed-input test FAILED: the parser unexpectedly " ^
                    "accepted this as an " ^ kind_name ^ ".")
    in thy end

val _ = Outer_Syntax.command @{command_keyword "java_reject"}
        "Check that a Java fragment is correctly rejected as a source file"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory
             (run_reject Java_Parse.Entry_Unit
              "Java compilation unit" source)))

val _ = Outer_Syntax.command @{command_keyword "java_stmt_reject"}
        "Check that a fragment is correctly rejected as a statement list"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory
             (run_reject Java_Parse.Entry_Stmts "statement list" source)))

val _ = Outer_Syntax.command @{command_keyword "java_decl_reject"}
        "Check that a fragment is correctly rejected as top-level declarations"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory
             (run_reject Java_Parse.Entry_Decls "declaration list" source)))

val _ = Outer_Syntax.command @{command_keyword "java_ident_reject"}
        "Check that a fragment is correctly rejected as a Java name"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory
             (run_reject Java_Parse.Entry_Id "Java name" source)))

val _ = Outer_Syntax.command @{command_keyword "java_type_reject"}
        "Check that a fragment is correctly rejected as a Java type"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory
             (run_reject Java_Parse.Entry_Type "Java type" source)))

val _ = Outer_Syntax.command @{command_keyword "java_expr_reject"}
        "Check that a fragment is correctly rejected as a Java expression"
        (Parse.input Parse.cartouche >> (fn source =>
           Toplevel.theory
             (run_reject Java_Parse.Entry_Expr
              "Java expression" source)))

end (* local open *)
\<close>

text\<open>The environment as it stands now - the standard antiquotation handlers of
  \<^verbatim>\<open>Java_AnaEval.thy\<close> registered, nothing declared - is what \<open>reset_jenv\<close>
  restores unless a later theory nominates another snapshot.\<close>
set_jenv_default

end
