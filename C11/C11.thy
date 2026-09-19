(***********************************************************************************
 * Copyright (c) University of Paris-Saclay 2026
 *
 * Author : Burkhart Wolff
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

theory C11
  imports  "C11_Parser" "AnaEval" 
  keywords "c11" "c11_ident" "c11_expr" "c11_statement" "c11_predef" :: thy_decl
  and      "c11_file" :: thy_load
  and      "c11_reject" "c11_ident_reject" "c11_expr_reject" "c11_statement_reject" :: diag
begin

text\<open>
  This theory implements the ANSI C11 grammar as a ml-lex/ml-yacc lexer/parser pair,
  ported from the reference grammar published at 
  \<^verbatim>\<open>https://www.quut.com/c/ANSI-C-grammar-y.html\<close> (Yacc) and
  \<^verbatim>\<open>https://www.quut.com/c/ANSI-C-grammar-l-2011.html\<close> (Lex), based on the 2011 ISO C
  standard. Semantic actions build a real abstract syntax tree, defined in
  \<^verbatim>\<open>c_ast.ML\<close> (a hand-pruned port of the Isabelle_C AFP entry's own C11 AST) and
  instantiated here with \<^verbatim>\<open>Position.T\<close> as the position/annotation type: every
  \<^verbatim>\<open>cXxx\<close> constructor's own trailing field is a \<^verbatim>\<open>Position.T nodeInfo\<close>, which carries
  not just a position but also, where present, the source comments and \<open>@tag \<open>...\<close>\<close>
  antiquotations attached to that node (see \<^verbatim>\<open>C11_Comments\<close>, below, and the
  \<^verbatim>\<open>merge_nodeInfo\<close>/\<^verbatim>\<open>nodeInfo_of_CXxx\<close> family in \<^verbatim>\<open>c_ast.ML\<close> itself). The grammar's
  own start symbol accepts a bare identifier, a standalone expression, a standalone
  statement, or a whole translation unit, wrapping whichever one actually matched into
  \<^verbatim>\<open>c_ast_root\<close>'s \<open>Id\<close>/\<open>Expr\<close>/\<open>Stmt\<close>/\<open>Units\<close> case respectively - a bare identifier
  resolves to \<open>Id\<close>, not to the (also grammatically valid) one-token \<open>Expr\<close> reading, since
  \<open>start_rule\<close> lists the \<open>IDENTIFIER\<close> alternative first and ml-yacc's reduce/reduce
  conflict resolution favours the earlier-declared rule. A handful of deliberate,
  documented simplifications keep this a tractable single pass rather than a full
  semantic C front-end: array-declarator type-qualifier lists are dropped (\<^verbatim>\<open>cArraySize\<close>
  has no room for them); a parenthesized declarator that itself has a pointer prefix
  \<^emph>\<open>and\<close> further suffixes attached outside the parens does not get fully correct
  suffix-binding precedence (the classic C "declarator inversion" problem, needing a
  genuine closure-based rewrite to solve properly); \<open>_Imaginary\<close> maps onto the same
  \<open>CComplexType0\<close> as \<open>_Complex\<close>, since \<^verbatim>\<open>c_ast.ML\<close>'s \<open>cTypeSpecifier\<close> - inherited from
  language-c - has no separate case for it; and a small fragment of the C preprocessor is
  recognized directly and kept as genuine AST nodes rather than being silently discarded -
  see the dedicated paragraph on \<open>preproc_directive\<close> below for exactly which forms and
  how \<^verbatim>\<open>c_ast.ML\<close>'s \<open>cPreprocDirective\<close>/\<open>CPPExt0\<close> represent them. Constant-literal
  parsing (integer bases/suffixes, character/string escapes) is similarly modest rather
  than exhaustive; see the comments on \<open>parse_c_integer\<close>/\<open>parse_c_char\<close>/\<open>unescape_c\<close>
  below. Following the reference grammar's own note, identifiers are never lexed as
  \<open>TYPEDEF_NAME\<close> or
  \<open>ENUMERATION_CONSTANT\<close> (which would require a symbol table); these tokens remain
  part of the grammar, but are only ever produced were a symbol table to be added later.
  The grammar has two known shift/reduce conflicts (the dangling \<open>ELSE\<close> and the
  \<open>ATOMIC\<close>/\<open>type_name\<close> ambiguity), both correctly resolved by ml-yacc's default
  shift preference, exactly as documented for the reference grammar.

  As a departure from the reference grammar (which assumes translation phases 1..5,
  including preprocessing, have already run), this theory additionally recognizes a
  small fragment of the C preprocessor directly (ISO C11 6.10, Annex A.3), kept as
  genuine \<open>preproc_directive\<close> syntax tree nodes usable wherever an external
  declaration may appear, rather than being silently discarded like a comment:

  \<^item> \<open>#include <file>\<close> and \<open>#include "file"\<close>. The lexer switches into a dedicated
    \<open>INCLUDE\<close> start state right after \<open>#include\<close> so that the header name's \<open>< >\<close>
    delimiters are not confused with the relational/shift operators.
  \<^item> \<open>#define name = expr\<close> and \<open>#define name(arg1, \<dots>, argn) = expr\<close>, a simplified
    object-like/function-like macro definition (using \<open>=\<close> rather than the C standard's
    juxtaposed replacement-list, and a syntactic constant expression as the body rather
    than an arbitrary preprocessing-token sequence).
  \<^item> \<open>#ifdef name \<dots> #endif\<close>, \<open>#ifndef name \<dots> #endif\<close>, and their \<open>#else\<close> variants,
    bracketing a (possibly empty) sequence of external declarations. Since \<open>#else\<close>
    would otherwise clash with the \<open>ELSE\<close> keyword of \<open>if\<dots>else\<close>, it is lexed as the
    separate token \<open>PP_ELSE\<close>.

  This fragment is purely syntactic, not a real preprocessor: \<open>#define\<close> does not
  perform macro expansion, and \<open>#ifdef\<close>/\<open>#ifndef\<close> do not consult a macro-definition
  table to decide which branch is live: \<^emph>\<open>both\<close> branches must simply be
  syntactically well-formed.
\<close>

section\<open>Relation to Isabelle/C (AFP)\<close>

text\<open>
  This theory is a small-scale, from-scratch re-design to the
  \<^emph>\<open>Isabelle_C\<close> AFP entry (Tuong and Wolff, \<^url>\<open>https://www.isa-afp.org/entries/Isabelle_C.html\<close>),
  which provides a full C11/C18 front-end for Isabelle built around its \<^emph>\<open>own\<close>
  hand-written, PIDE-integrated incremental lexer/parser (\<^verbatim>\<open>C_Lex\<close>, \<^verbatim>\<open>C_Parser\<close>,
  \<^verbatim>\<open>C_Grammar_Rule\<close>, \<open>\<dots>\<close>). This theory deliberately does \<^emph>\<open>not\<close> depend on Isabelle_C
  or its machinery; the point is to see how far the same \<^emph>\<open>user-facing shape\<close> can be
  reproduced on top of the generic, off-the-shelf \<^verbatim>\<open>ml_lex_yacc\<close> command of this
  \<^verbatim>\<open>Isabelle_Lex-Yacc\<close> framework instead - i.e. plain ml-lex/ml-yacc, not a bespoke
  parser combinator. Three aspects of Isabelle_C's interface are mirrored here, each
  necessarily only a syntactic sliver of the original:

  \<^enum> \<^bold>\<open>Inline and file-based entry points.\<close> Isabelle_C's \<^verbatim>\<open>C \<open>...\<close>\<close> command (inline
    source) and \<^verbatim>\<open>C_file \<open>path\<close>\<close> command (external \<open>.c\<close> file, read relative to the
    theory's master directory) correspond here to \<open>c11 \<open>...\<close>\<close> and \<open>c11_file \<open>path\<close>\<close>
    below - the latter built directly on \<^verbatim>\<open>Resources.parse_file\<close> /
    \<^verbatim>\<open>Token.file_source\<close>, the same Isabelle/Pure machinery used by the built-in
    \<^verbatim>\<open>ML_file\<close>/\<^verbatim>\<open>SML_file\<close> commands, so that file positions and build-dependency
    tracking come for free.
  \<^enum> \<^bold>\<open>Antiquotation-carrying comments.\<close> Isabelle_C lets \<open>/*@ \<dots> */\<close> and \<open>//@ \<dots>\<close>
    comments carry Isar-level \<^emph>\<open>annotation commands\<close> (\<open>ensures\<close>, \<open>invariant\<close>, a
    user-registered \<open>setup \<open>...\<close>\<close>, \<open>\<dots>\<close>), spliced into the surrounding C syntax tree
    and executed as the file is processed. Here, the lexer instead \<^emph>\<open>lexically\<close>
    recognizes the shape \<open>@tag(level) \<open>...\<close>\<close> - an \<open>@\<close>-prefixed tag, an optional
    parenthesized integer \<open>level\<close> (\<open>0\<close> when omitted, e.g. plain \<open>@tag \<open>...\<close>\<close>),
    optionally followed by whitespace, and a body - either a properly-nested Isabelle
    cartouche \<open>\<open>\<dots>\<close>\<close> or, as an equivalent alternative notation, a double-quoted
    string \<open>"\<dots>"\<close> - reporting both as PIDE markup (\<^ML>\<open>Markup.antiquote\<close> /
    \<^ML>\<open>Markup.cartouche\<close> for the cartouche spelling, \<^ML>\<open>Markup.antiquote\<close> alone
    for the tag+string spelling since it is matched as a single token) instead of
    discarding them as opaque comment text. Nothing is \<^emph>\<open>executed\<close>: this recognizer
    has no notion of an annotation command language, only of where one \<^emph>\<open>could\<close> be
    hooked in later. Since a cartouche can nest, recognizing it needs more than one
    regular-expression rule and a small amount of \<^verbatim>\<open>lex_user_declarations\<close> state (a
    depth counter); see the \<open>ANTIQ\<close> lexer state below for how that turns into a
    well-defined \<^emph>\<open>non-expert-mode\<close> ml-lex specification - no \<open>[expert]\<close> switch
    turned out to be necessary after all. A double-quoted body, by contrast, cannot
    nest, so \<open>@tag(level) "..."\<close> is matched by a single, longer regular-expression
    alternative competing with the plain \<open>@tag(level)\<close> one for the same input -
    ml-lex's usual longest-match rule then picks the string-body alternative whenever
    a quote genuinely follows the tag (with only horizontal whitespace in between,
    never across other text or a newline), and falls back to the plain, bodyless tag
    match otherwise; this is what keeps an unrelated \<open>"\<close> elsewhere in a comment (an
    apostrophe-free quotation, say) from ever being mistaken for an antiquotation
    body - unlike the cartouche form, which (see below) is recognized whenever it
    occurs in a comment, tag or no tag. Comments and antiquotations are, beyond that
    markup, now also genuinely
    \<^emph>\<open>registered\<close>: \<^verbatim>\<open>C11_Comments\<close> (defined just above the lexer/parser definition,
    \<^verbatim>\<open>SML_import\<close>ed into the lex/yacc sandbox the same way \<^verbatim>\<open>YaccLib.thy\<close> already
    does for \<^verbatim>\<open>Position\<close>/\<open>Markup\<close>) accumulates raw text and antiquotation fragments as
    the lexer scans them and attaches each batch to whichever real token follows, so
    the grammar can fold them into that token's \<^verbatim>\<open>nodeInfo\<close> once it decides which AST
    node owns them - see the fuller rationale on \<^verbatim>\<open>C11_Comments\<close> itself for why
    attachment happens at the token's own lex time rather than at the point some later
    LALR(1) reduction gets around to it. Recognizing a genuine nested cartouche this way
    surfaced a latent, previously invisible bug in \<open>OPENCART\<close>/\<open>CLOSECART\<close> themselves.
    Isabelle's cartouche-open and cartouche-close symbols are each spelled, in the raw
    source text ml-lex's generated scanner actually reads character by character, as a
    literal backslash followed by an angle-bracketed name - seven and eight raw
    characters respectively, not one special codepoint. As a plain ml-lex regular
    expression this needs \<^emph>\<open>three\<close> backslashes, not one: one escaped pair to match
    that leading literal backslash, and a second escaped pair for the angle bracket right
    after it, since a bare, unescaped angle bracket is ml-lex's own syntax for a start-state
    prefix (as in the \<open><INITIAL>\<close> seen throughout the rules below) rather than a literal
    character - the letters of the symbol's name and its closing angle bracket need no
    escaping of their own. With only one backslash, as the original definitions had it, the
    pattern silently compiled to matching the six-character angle-bracketed name alone,
    missing its leading backslash - invisible before now because the antiquotation content
    it should have captured was simply discarded either way.
  \<^enum> \<^bold>\<open>The lexer test suite.\<close> Isabelle_C's own lexer/parser stress tests live in
    \<^verbatim>\<open>C11-FrontEnd/examples/C0.thy\<close> (obfuscated/adversarial C, comment nesting,
    preprocessor directives, and a battery of real-world \<open>.c\<close> files borrowed from the
    \<^verbatim>\<open>parser_menhir\<close> C11 conformance suite) and \<^verbatim>\<open>C11-FrontEnd/examples/C1.thy\<close> (AST
    access and the annotation-command examples referenced above). The test sections
    in \<^verbatim>\<open>C11_Tests.thy\<close> adapt what is in scope for a bare recognizer without a symbol table
    or macro expansion from both files - comment nesting, the \<open>@tag \<open>...\<close>\<close> examples,
    and (where the underlying \<open>.c\<close> files are locally available) \<open>c11_file\<close> on a
    handful of \<^verbatim>\<open>parser_menhir\<close> tests - while using \<open>c11_reject\<close> to document,
    rather than silently skip, the constructs that fall outside this fragment's scope
    (real \<open>#define\<close>/\<open>#if\<close>/\<open>#elif\<close>, backslash-newline splicing, \<open>_Pragma\<close>).
\<close>

subsection\<open>Defining the Isar-toplevel Commands\<close>

text\<open>
  Four accepting commands share the one grammar (\<open>C11.parse_source\<close>, whose
  \<open>start_rule\<close> can produce any of \<open>Id\<close>/\<open>Expr\<close>/\<open>Stmt\<close>/\<open>Units\<close>), each simply
  \<^emph>\<open>gating\<close> on the shape it wants rather than having its own grammar entry point:
  \<open>c11\<close>/\<open>c11_file\<close> are reserved for a whole translation unit (\<open>Units\<close>) and error
  if the input parses as anything else, while \<open>c11_ident\<close>/\<open>c11_expr\<close>/\<open>c11_statement\<close>
  each similarly require \<open>Id\<close>/\<open>Expr\<close>/\<open>Stmt\<close>. Every successful parse is stored into
  \<^verbatim>\<open>CEnv\<close>'s AST store (\<^verbatim>\<open>CEnv.Ast_Store\<close>, in its own \<^verbatim>\<open>CEnv.thy\<close>, imported
  here transitively via \<^verbatim>\<open>AnaEval.thy\<close>) under a fresh, per-theory \<open>store_root\<close>
  key - \<^verbatim>\<open>open CEnv\<close> below makes \<open>store_root\<close>/\<open>get_ast\<close>/\<open>\<dots>\<close> usable unqualified
  throughout the rest of this theory. \<open>AnaEval.analyse_and_eval\<close> also runs on
  every successful parse, \<open>c11\<close> included, but only \<open>c11\<close>'s own antiquotation
  actions are actually chained onto the stored theory (\<open>run_c11_kind\<close>'s
  \<open>full_eval\<close> flag): \<open>c11_ident\<close>/\<open>c11_expr\<close>/\<open>c11_statement\<close> are syntax-checks
  on a single fragment, not a compilation unit, so \<open>analyse_and_eval\<close> is run
  there purely for its \<^emph>\<open>side effect\<close> - the declaration/use hyperlinking
  reported via \<^ML>\<open>Position.report\<close> during the walk - and its returned theory
  and antiquotation actions are deliberately discarded rather than persisted.
  Each accepting command has a \<open>_reject\<close>
  counterpart (\<open>c11_reject\<close> - pre-existing, kept general-purpose across
  all four shapes - and the three new \<open>c11_ident_reject\<close>/\<open>c11_expr_reject\<close>/
  \<open>c11_statement_reject\<close>) that documents a fragment as correctly \<^emph>\<open>not\<close> that
  shape: either a genuine parse failure, or a successful parse of the \<^emph>\<open>wrong\<close>
  shape - both count as "rejected" for that command's purposes, since the command's
  contract is "this fragment is a valid \<open>X\<close>", not merely "this fragment parses
  somehow". Reject variants never touch the AST store.
\<close>
ML\<open>
local open CEnv in

(* A shallow, top-level-only summary of the parsed result - not a full AST
   pretty-printer - just enough to confirm, from "c11" and friends, that a
   real AST (positions and comment counts included) came out the other end,
   not only that parsing succeeded. *)
fun string_of_root (C_Ast.Id (C_Ast.Ident (s, _, ndI))) =
      "Id " ^ s ^ " " ^ Position.here (C_Ast.pos_of_NodeInfo ndI)
  | string_of_root (C_Ast.Expr e) =
      "Expr " ^ Position.here (C_Ast.pos_of_CExpr e)
  | string_of_root (C_Ast.Stmt s) =
      "Stmt " ^ Position.here (C_Ast.pos_of_CStat s)
  | string_of_root (C_Ast.Units us) =
      "Units (" ^ Int.toString (length us) ^ " top-level declaration(s))"

fun classify (C_Ast.Id _) = "identifier"
  | classify (C_Ast.Expr _) = "expression"
  | classify (C_Ast.Stmt _) = "statement"
  | classify (C_Ast.Units _) = "translation unit"

val is_units = fn C_Ast.Units _ => true | _ => false
val is_id    = fn C_Ast.Id _ => true | _ => false
val is_expr  = fn C_Ast.Expr _ => true | _ => false
val is_stmt  = fn C_Ast.Stmt _ => true | _ => false

fun require_kind check kind_name cmd_name root =
  if check root then root
  else error (cmd_name ^ " is reserved for a " ^ kind_name ^
              "; this input parses instead as a " ^ classify root ^ ".")

(* Shared by every accepting command: parse, gate on the expected shape,
   store under a fresh CEnv.Ast_Store key, and report both. "C11_Comments.reset"
   clears any comments left pending/attached from a previous parse - "claim"
   is now non-destructive (see its own comment in C11_Parser.thy), and
   nothing else ever drains "attached", so without this it would simply grow
   for the rest of the session; position uniqueness means stale entries can
   never be *wrongly* matched by a later parse, only wastefully retained.

   "full_eval" distinguishes "c11" (a whole translation unit, i.e. genuinely a
   compilation unit) from "c11_ident"/"c11_expr"/"c11_statement" (a syntax
   check on a single fragment): "analyse_and_eval" always runs - it is what
   produces the declaration/use hyperlinking reported via "Position.report"
   during the walk, wanted for all four - but only under "full_eval" are its
   returned antiquotation actions actually sorted by "level", chained, and
   used as the theory the parsed AST is stored under; otherwise that returned
   theory (and the antiquotation actions) are simply discarded and the
   original "thy" is used for storing instead, exactly as if
   "analyse_and_eval" had not been called at all except for its side effect. *)
(* Shared by every command that treats its parsed root under "full_eval =
   true" semantics (a genuine whole translation unit, currently "c11" and
   "c11_file"): runs "analyse_and_eval", chains its collected antiquotation
   actions in ascending "level" order - each against the theory the previous
   one produced ("level" is the author's own explicit ordering knob, see
   "@tag(level) ..." in C11_Parser.thy, so equal levels keep their relative,
   i.e. textual, order, which "sort" already guarantees being stable) -
   against the theory "analyse_and_eval" itself returns, then stores the
   root and reports both. Factored out rather than duplicated so "c11" and
   "c11_file" cannot again silently drift apart the way they already once
   did (see "run_c11_file"'s own note). *)
fun full_eval_and_store root thy =
    let
      val (thy', antiq_evals) = AnaEval.analyse_and_eval root thy
      val sorted_evals = sort (fn ((l1, _), (l2, _)) => Int.compare (l1, l2)) antiq_evals
      val thy_for_store = fold (fn (_, f) => f) sorted_evals thy'
      val (key, thy'') = store_root root thy_for_store
      val _ = writeln (string_of_root root ^ "  [stored as " ^ key ^ "]")
    in thy'' end

fun run_c11_kind check kind_name cmd_name full_eval source thy =
    let
      val _ = C11_Comments.reset ()
      val ctxt = Proof_Context.init_global thy
      val res = C11.parse_source ctxt source
    in
      case res of
        NONE => error (cmd_name ^ ": no result")
      | SOME root =>
          let
            val root = require_kind check kind_name cmd_name root
          in
            if full_eval then full_eval_and_store root thy
            else
              let
                val _ = AnaEval.analyse_and_eval root thy
                val (key, thy'') = store_root root thy
                val _ = writeln (string_of_root root ^ "  [stored as " ^ key ^ "]")
              in thy'' end
          end
    end

fun run_c11 source = run_c11_kind is_units "translation unit" "c11" true source

val _ = Outer_Syntax.command @{command_keyword "c11"}
        "Syntax check a C11 translation unit and store its AST"
        (Parse.input Parse.cartouche >> (fn source => Toplevel.theory (run_c11 source)))

fun run_c11_ident source = run_c11_kind is_id "identifier" "c11_ident" false source

val _ = Outer_Syntax.command @{command_keyword "c11_ident"}
        "Syntax check a bare C11 identifier and store its AST"
        (Parse.input Parse.cartouche >> (fn source => Toplevel.theory (run_c11_ident source)))

fun run_c11_expr source = run_c11_kind is_expr "expression" "c11_expr" false source

val _ = Outer_Syntax.command @{command_keyword "c11_expr"}
        "Syntax check a C11 expression and store its AST"
        (Parse.input Parse.cartouche >> (fn source => Toplevel.theory (run_c11_expr source)))

fun run_c11_statement source = run_c11_kind is_stmt "statement" "c11_statement" false source

val _ = Outer_Syntax.command @{command_keyword "c11_statement"}
        "Syntax check a C11 statement and store its AST"
        (Parse.input Parse.cartouche >> (fn source => Toplevel.theory (run_c11_statement source)))

(* Isabelle_C's counterpart is "C_file \<open>path\<close>". Resources.parse_file/
   Token.file_source/Resources.provide_file are the same Isabelle/Pure
   building blocks the built-in ML_file/SML_file commands use (see
   Pure/ML/ml_file.ML): the path is resolved relative to this theory's
   master directory, the resulting Input.source carries correct file
   positions (so parse errors point at the actual file/line/column, not
   at the command invocation), and the file is registered as a dependency
   so `isabelle build` re-checks this theory when it changes. Note the
   keyword kind below: "c11_file" is declared "thy_load" (a specialised
   "thy_decl"), not "diag" - Resources.parse_file's file-dependency
   resolution is only actually wired up by Isabelle's command-span scanner
   for thy_load-kind commands (matching how ML_file/SML_file/external_file
   are themselves declared in Pure.thy); under "diag" the file is never
   read, silently. "c11"/"c11_ident"/"c11_expr"/"c11_statement" are "thy_decl"
   for a related but different reason: each mutates CEnv's data (persistent
   theory-level state, via store_root below), and "diag" - Isabelle's kind for
   read-only, disposable diagnostic commands - does not reliably thread such
   mutations into the following command's starting theory the way "thy_decl"
   does. Only the "_reject" variants, which store nothing, stay "diag". Like
   "c11", "c11_file" is reserved for a whole translation unit - and, exactly
   like "c11", should run under "full_eval = true" semantics: an external
   file is just as much a genuine compilation unit as an inline "c11 \<open>...\<close>"
   one, so it needs the same declaration/use hyperlinking and antiquotation
   handling. This was originally missed here - "run_c11_file" called neither
   "analyse_and_eval" nor "full_eval_and_store" at all, so a file read via
   "c11_file" got no hyperlinking whatsoever, unlike every other accepting
   command - now fixed by routing through the same "full_eval_and_store"
   helper "run_c11_kind" itself uses. *)
fun run_c11_file get_file thy =
    let
      val _ = C11_Comments.reset ()
      val file = get_file thy
      val source = Token.file_source file
      val ctxt = Proof_Context.init_global thy
      val res = C11.parse_source ctxt source
    in
      case res of
        NONE => error "c11_file: no result"
      | SOME root =>
          let
            val root = require_kind is_units "translation unit" "c11_file" root
            val thy' = full_eval_and_store root thy
          in Resources.provide_file file thy' end
    end

val _ = Outer_Syntax.command @{command_keyword "c11_file"}
        "Read and syntax-check an external C11 source file, and store its AST"
        (Resources.parse_file >> (fn get_file => Toplevel.theory (run_c11_file get_file)))

(* "c11_predef [header] \<open>decl_list\<close>" gives a real, "#include"-independent
   \<^emph>\<open>basic\<close> functionality (the user's own word - see the design discussion
   this responds to): a way to tell this fragment about the usual global
   variables/macro-definitions/function prototypes a real "#include <header>"
   would bring into scope, so that later uses of e.g. "printf"/"malloc"/
   "errno" are no longer "genuinely undeclared" (\<^ML>\<open>Markup.bad ()\<close>) but
   resolve into "cenv" exactly like any other predeclared name. "header" is a
   plain label (a "name" token, so a dotted form like "stdio.h" parses
   directly as a "long_ident" - no quoting needed), echoed in the reported
   confirmation message; it plays no functional role and is not connected to
   "#include" in any way - "#include" stays purely syntactic (see above), and
   declaring "stdio.h"'s contents this way does not require ever having
   written "#include <stdio.h>", nor does it restrict which uses of the
   declared names are accepted. "decl_list" is parsed and walked exactly like
   an ordinary "c11" translation unit (reusing "full_eval_and_store", so
   struct/union/enum tags and enum constants register too, and any
   antiquotation present would be dispatched the same way) - with one added
   restriction: a function \<^emph>\<open>definition\<close> (a real body, not just a prototype)
   is rejected outright, since "c11_predef" is for declaring an interface,
   never an implementation, matching "no implementations" in the design
   discussion.

   A real limitation, not yet addressed: this fragment's lexer never
   produces a "TYPEDEF_NAME" token (see the note on this in
   \<^verbatim>\<open>C11_Parser.thy\<close> - "these tokens remain part of the grammar, but are
   only ever produced were a symbol table to be added later"), so a
   "typedef"'d type name is not recognized as a type at all, anywhere, by
   this fragment today - independently of "c11_predef". Most of "stdio.h"
   (the non-"FILE"-taking functions), all of "stdlib.h", "errno.h", and
   "assert.h" are declarable without needing any such name; "setjmp.h"'s
   "jmp_buf" and "stdarg.h"'s "va_list" are themselves always "typedef"'d
   types in a real C library, so \<^emph>\<open>every\<close> declaration in those two headers
   needs exactly the mechanism this fragment does not have - a
   standards-faithful "c11_predef [setjmp.h] \<open>...\<close>"/"c11_predef [stdarg.h]
   \<open>...\<close>" cannot be written at all until real "typedef" support (lexer
   feedback registering a "typedef"'d name so a later use of it is lexed as
   "TYPEDEF_NAME") is added - a separate, materially larger piece of work,
   deliberately out of scope here. *)
fun reject_predef_implementations header (C_Ast.Units us) =
      List.app (fn C_Ast.CTranslUnit (eds, _) =>
                    List.app (fn C_Ast.CFDefExt (C_Ast.CFunDef (_, _, _, _, ni)) =>
                                  error ("c11_predef " ^ quote header ^
                                         ": function definitions are not allowed here, only " ^
                                         "prototypes (no \"{ ... }\" body)" ^
                                         Position.here (C_Ast.pos_of_NodeInfo ni))
                                | _ => ())
                      eds)
        us
  | reject_predef_implementations _ _ = () (* unreachable: "root" is already known to be "Units" *)

fun run_c11_predef header source thy =
    let
      val _ = C11_Comments.reset ()
      val ctxt = Proof_Context.init_global thy
      val res = C11.parse_source ctxt source
    in
      case res of
        NONE => error ("c11_predef " ^ quote header ^ ": no result")
      | SOME root =>
          let
            val root = require_kind is_units "translation unit" ("c11_predef " ^ quote header) root
            val _ = reject_predef_implementations header root
          in full_eval_and_store root thy end
    end

val _ = Outer_Syntax.command @{command_keyword "c11_predef"}
        "Declare a fragment of predefined C11 global variables/macros/function prototypes"
        (Parse.$$$ "[" |-- Parse.name --| Parse.$$$ "]" -- Parse.input Parse.cartouche
          >> (fn (header, source) => Toplevel.theory (run_c11_predef header source)))

(* C11.parse_source (generated by the `linker` template in YaccLib.thy)
   always delegates to Isabelle_lex_yacc.parse_source, which hard-codes
   Isabelle_lex_yacc.print_error as the parser's error callback - it is not
   a parameter we can override from here. print_error unconditionally
   reports the error span via Position.report ... Markup.error *before*
   raising, so that PIDE markup appears regardless of whether the caller
   later catches the resulting exception; on top of that, since this
   framework bridges two ML environments via SML_import/SML_export,
   `error`'s `ERROR` exception raised from the generated parser's
   execution context is not reliably `handle ERROR _ => ...`-catchable
   from plain Isabelle/ML (exception matching is by constructor identity,
   not by name).

   Rather than patch YaccLib.thy (out of scope here), every reject command
   below re-implements parse_source's control flow directly against the
   public C11Lex/C11Parser/C11LrVals structures and the exposed
   Isabelle_lex_yacc.set/get_pos, substituting a private, silent error
   callback that raises a *locally declared* exception - so it is caught
   by construction, with no cross-environment identity mismatch possible,
   and no spurious error markup is left on rejected (expected-to-fail)
   input. *)
exception Rejected of string
fun quiet_error (s: string, _: Position.T, _: Position.T) = raise Rejected s

fun parse_source_quiet ctxt source =
    let
      val _ = C11_Comments.reset ()
      val _ = Isabelle_lex_yacc.set source ctxt
      val (input_text, _) = Input.source_content source
      fun invoke lexstream = C11.C11Parser.parse (0, lexstream, quiet_error, ())
      val parsed = Unsynchronized.ref false
      fun input_string _ = if !parsed then "" else (parsed := true; input_text)
      val lexer = C11.C11Parser.makeLexer input_string
      val eof_pos = Isabelle_lex_yacc.get_pos (String.size input_text + 1)
      val dummyEOF = C11.C11LrVals.Tokens.EOF (eof_pos, eof_pos)
      fun loop lexer =
        let
          val (res, lexer) = invoke lexer
          val (nextToken, lexer) = C11.C11Parser.Stream.get lexer
        in
          if C11.C11Parser.sameToken (nextToken, dummyEOF) then ((), res)
          else loop lexer
        end
    in
      #2 (loop lexer)
    end

(* Shared by every reject command: a fragment is correctly rejected either
   by a genuine parse failure, or by parsing successfully as the *wrong*
   shape ("check" then returns false on the SOME branch). Never touches
   the AST store - a rejected fragment has nothing to store. *)
fun run_c11_kind_reject check kind_name source thy =
    let
      val ctxt = Proof_Context.init_global thy
      val rejected =
        (case parse_source_quiet ctxt source of
           SOME root => not (check root)
         | NONE => true)
          handle Rejected _ => true
      val _ =
        if rejected
        then writeln ("OK: malformed input was correctly rejected as a " ^ kind_name ^ ".")
        else error   ("Malformed-input test FAILED: the parser unexpectedly accepted this as a " ^
                       kind_name ^ ".")
    in thy end

fun run_c11_reject source = run_c11_kind_reject is_units "translation unit" source

val _ = Outer_Syntax.command @{command_keyword "c11_reject"}
        "Check that a C11 fragment is correctly rejected (error-recovery / malformed-input tests)"
        (Parse.input Parse.cartouche >> (fn source => Toplevel.theory (run_c11_reject source)))

fun run_c11_ident_reject source = run_c11_kind_reject is_id "identifier" source

val _ = Outer_Syntax.command @{command_keyword "c11_ident_reject"}
        "Check that a fragment is correctly rejected as a C11 identifier"
        (Parse.input Parse.cartouche >> (fn source => Toplevel.theory (run_c11_ident_reject source)))

fun run_c11_expr_reject source = run_c11_kind_reject is_expr "expression" source

val _ = Outer_Syntax.command @{command_keyword "c11_expr_reject"}
        "Check that a fragment is correctly rejected as a C11 expression"
        (Parse.input Parse.cartouche >> (fn source => Toplevel.theory (run_c11_expr_reject source)))

fun run_c11_statement_reject source = run_c11_kind_reject is_stmt "statement" source

val _ = Outer_Syntax.command @{command_keyword "c11_statement_reject"}
        "Check that a fragment is correctly rejected as a C11 statement"
        (Parse.input Parse.cartouche >> (fn source => Toplevel.theory (run_c11_statement_reject source)))

end (* local open *)
\<close>

end
