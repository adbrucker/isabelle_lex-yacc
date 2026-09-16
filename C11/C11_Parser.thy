(***********************************************************************************
 * Copyright (c) University of Exeter, UK
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

theory C11_Parser
  imports "../LexYacc"
begin

text\<open>
  This theory formalizes the ANSI C11 grammar as a ml-lex/ml-yacc lexer/parser pair,
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
  \<^verbatim>\<open>root\<close>'s \<open>Id\<close>/\<open>Expr\<close>/\<open>Stmt\<close>/\<open>Units\<close> case respectively - a bare identifier
  resolves to \<open>Id\<close>, not to the (also grammatically valid) one-token \<open>Expr\<close> reading, since
  \<open>start_rule\<close> lists the \<open>IDENTIFIER\<close> alternative first and ml-yacc's reduce/reduce
  conflict resolution favours the earlier-declared rule. A handful of deliberate,
  documented simplifications keep this a tractable single pass rather than a full
  semantic C front-end: array-declarator type-qualifier lists are dropped (\<^verbatim>\<open>cArraySize\<close>
  has no room for them); a parenthesized declarator that itself has a pointer prefix
  \<^emph>\<open>and\<close> further suffixes attached outside the parens does not get fully correct
  suffix-binding precedence (the classic C "declarator inversion" problem, needing a
  genuine closure-based rewrite to solve properly); \<open>_Imaginary\<close> maps onto the same
  \<open>CComplexType\<close> as \<open>_Complex\<close>, since \<^verbatim>\<open>c_ast.ML\<close>'s \<open>cTypeSpecifier\<close> - inherited from
  language-c - has no separate case for it; and a small fragment of the C preprocessor is
  recognized directly and kept as genuine AST nodes rather than being silently discarded -
  see the dedicated paragraph on \<open>preproc_directive\<close> below for exactly which forms and
  how \<^verbatim>\<open>c_ast.ML\<close>'s \<open>cPreprocDirective\<close>/\<open>CPPExt\<close> represent them. Constant-literal
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
  This theory is a small-scale, from-scratch counterpart to the
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
    further below adapt what is in scope for a bare recognizer without a symbol table
    or macro expansion from both files - comment nesting, the \<open>@tag \<open>...\<close>\<close> examples,
    and (where the underlying \<open>.c\<close> files are locally available) \<open>c11_file\<close> on a
    handful of \<^verbatim>\<open>parser_menhir\<close> tests - while using \<open>c11_reject\<close> to document,
    rather than silently skip, the constructs that fall outside this fragment's scope
    (real \<open>#define\<close>/\<open>#if\<close>/\<open>#elif\<close>, backslash-newline splicing, \<open>_Pragma\<close>).
\<close>

section\<open>The Lex/Yacc Definition\<close>

ML_file\<open>c_ast.ML\<close>

text\<open>
  Comment/antiquotation bookkeeping, kept outside \<open>lex_user_declarations\<close>/
  \<open>yacc_user_declarations\<close> deliberately: the two become two \<^emph>\<open>separate\<close>
  generated SML structures (\<^verbatim>\<open>C11Lex\<close> vs. \<^verbatim>\<open>C11LrVals\<close>, linked together only
  afterwards, per \<open>YaccLib.thy\<close>'s \<open>linker\<close>), so a ref declared inside one is
  not visible from the other - yet comments are discovered by the \<^emph>\<open>lexer\<close>
  while the \<^emph>\<open>grammar\<close> is what knows which AST node should own them. A
  plain top-level structure, \<open>SML_import\<close>ed into the lex/yacc sandbox the
  same way \<open>YaccLib.thy\<close> already does for \<open>Position\<close>/\<open>Markup\<close> (and exactly
  how \<open>Datalog.thy\<close> exposes its own \<open>Datalog_AST\<close>), is visible from both.

  Comments are attached to the \<^emph>\<open>token\<close> whose start position they
  immediately precede, not to whatever the parser happens to be reducing
  when it gets around to them: an LALR(1) parser's lookahead means a rule's
  action can run after later tokens have already been shifted, by which
  point a naive "whatever is currently pending" read would silently
  attach a comment to the wrong node. Recording \<open>(start position,
  comments)\<close> pairs in an association list keyed on the token's own
  \<open>Position.T\<close> (an \<open>eqtype\<close>) as each token is produced, and looking the
  entry back up by that same position when the grammar later builds a
  \<^verbatim>\<open>nodeInfo\<close> from it, keeps the attachment correct regardless of
  lookahead.
\<close>

(* <Bu>: this prototypical, Claude-generated code is quite state-heavy and surely not re-entrant. *) 

text\<open>
  \<open>pending\<close>/\<open>attached\<close> live in one \<^verbatim>\<open>Synchronized.var\<close>, not plain
  \<^verbatim>\<open>Unsynchronized.ref\<close>s. Two things were tried and ruled out empirically
  before landing here, both worth recording since either looks reasonable on
  paper: a plain \<^verbatim>\<open>Unsynchronized.ref\<close> is not atomic across concurrent
  writers, so it is never really safe as *global* state. The seemingly obvious
  fix, \<^verbatim>\<open>Thread_Data.var\<close> (what \<open>Isabelle_lex_yacc.global_state\<close> in
  \<^verbatim>\<open>YaccLib.thy\<close> uses for its own per-command state), turned out to be
  actively *wrong* here: a targeted test confirmed a push and an immediately
  following read of \<open>pending\<close> agree with each other (so the sandbox is not
  somehow talking to a different copy of this structure), yet the very next
  token's \<open>attach_pending\<close> already sees it as empty - meaning the generated
  lexer's own token production does not reliably stay on one OS thread between
  one token and the next, so \<^verbatim>\<open>Thread_Data.var\<close>'s per-thread isolation
  silently drops state that must survive from one token to the next \<^emph>\<open>within
  a single parse\<close>. \<^verbatim>\<open>Synchronized.var\<close> is the mechanism that is actually
  correct for that: one global cell, atomic reads and writes, visible
  regardless of which thread happens to run a given token. It does not, on its
  own, stop two genuinely concurrent \<open>c11\<close>-family commands from interleaving
  their comments - a real, still-open limitation \<^emph>\<open>if\<close> \<open>isabelle build\<close> ever
  schedules two such commands' lexing truly concurrently, rather than
  serializing them via their shared, sequential \<open>thy_decl\<close> theory-state
  dependency (see \<open>run_c11_kind\<close>, below, and its own note on why the four
  accepting commands are \<open>thy_decl\<close> rather than \<open>diag\<close>) - but it is no longer
  wrong even *within one single parse*, which is what mattered here.
\<close>
ML\<open>
structure C11_Comments = struct
  type state = {pending: Position.T C_Ast.comment list,
                attached: (Position.T * Position.T C_Ast.comment list) list}
  val state : state Synchronized.var =
    Synchronized.var "C11_Comments.state" {pending = [], attached = []}

  fun push c =
    Synchronized.change state (fn {pending, attached} =>
      {pending = pending @ [c], attached = attached})

  (* A fragment made up entirely of whitespace (a blank line between two
     pieces of real text, indentation, ...) carries no information worth
     keeping and is dropped rather than pushed - this also stops a comment
     consisting of nothing but blank lines from producing a spurious
     "attached" entry of all-whitespace Raw_txt. *)
  fun push_raw (text, pos) =
    if List.all Char.isSpace (String.explode text) then ()
    else push (C_Ast.Raw_txt [(text, pos)])

  fun push_antiquotation tag level cartouche = push (C_Ast.Antiquotation (tag, level, cartouche))

  (* Called once per real token, at its start position: claims whatever
     comments/antiquotations have accumulated since the previous token. *)
  fun attach_pending (p : Position.T) =
    Synchronized.change state (fn {pending, attached} =>
      case pending of
        [] => {pending = pending, attached = attached}
      | cs => {pending = [], attached = (p, cs) :: attached})

  (* Looks up whatever comments were attached at exactly this position -
     "p" must be the *token's own* position, exactly as it was originally
     passed to "attach_pending" (an un-merged, single-point position), never
     a since-computed range: "Position.range_position (p, q)" builds a
     genuinely different Position.T value from "p" alone (a different
     end_offset), so looking *that* up would never find anything a real
     token was ever attached under.

     Deliberately non-destructive (no entry ever removed on a successful
     lookup): more than one grammar action can legitimately want the exact
     same leftmost position, and LALR's bottom-up reduction order fixes
     which one runs first, not which one "should" own the comment. The
     clearest case is "expression_statement: expression SEMI", whose own
     nodeInfo and its wrapped expression's nodeInfo both start at the
     expression's own leftmost token: with a destructive claim, the *inner*
     expression reduces first and silently takes the comment, leaving the
     *outer* statement's own nodeInfo - almost always the one actually
     inspected - with none, even though the comment was captured correctly
     somewhere. Every node genuinely starting at "p" now sees the same
     comments; a caller wanting only one copy (e.g. after combining several
     nodes into one, where duplication would otherwise compound) already has
     "merge_nodeInfo" in c_ast.ML to de-duplicate explicitly. *)
  fun claim (p : Position.T) : Position.T C_Ast.comment list =
    case AList.lookup (op =) (#attached (Synchronized.value state)) p of
      NONE => []
    | SOME cs => cs

  (* Builds the nodeInfo a grammar action actually reports for a node:
     "claimed_at" is always the node's own leftmost token's un-merged
     position (see "claim" above), while "report_pos" is the position/span
     actually stored in the resulting nodeInfo - typically the same position
     for a single-token node, but often a wider merged range for a
     multi-token one. Keeping the two separate is exactly what makes claiming
     correct regardless of how wide the node's own reported span is. *)
  fun mk_nodeInfo (claimed_at : Position.T) (report_pos : Position.T) : Position.T C_Ast.nodeInfo =
    case claim claimed_at of
      [] => C_Ast.OnlyPos report_pos
    | cs => C_Ast.NodeInfo (cs, report_pos)

  fun reset () = Synchronized.change state (fn _ => {pending = [], attached = []})
end
\<close>
SML_import \<open>structure C_Ast = struct open C_Ast end\<close>
SML_import \<open>structure C11_Comments = struct open C11_Comments end\<close>

ml_lex_yacc [verbose] "C11" where
lex_user_declarations\<open>
(* State kept for lexically recognizing "@tag \<open>...\<close>" antiquotations inside
   comments (see the ANTIQ state below): the nesting depth of the cartouche
   currently being skipped, and which comment state (block "/* */" or line
   "//") to return to once it closes. Plain "ref", not Isabelle_lex_yacc's
   own machinery, so it needs no qualification here. *)
val antiq_depth = ref 0
val antiq_from_block = ref true

(* Position handling for keyword tokens, following Pascal.thy's convention:
   report the token's full span under the given markup (Markup.keyword1 for
   C keywords, Markup.keyword2 for preprocessor directives) - carrying the
   literal spelling itself, not a fixed type name, as Pascal.thy does - so
   it is coloured and hoverable in the IDE, but hand the parser a single,
   zero-width position for the token, exactly as Pascal.thy's keyword case
   calls "v(p, p)" rather than "tok"'s "cons(p, p')". Unlike ordinary tokens
   (identifiers, numerals, operators, ...), where "tok"'s full start/end span
   is used unchanged, collapsing keyword positions this way avoids the
   position ranges of adjacent keyword and identifier tokens overlapping in
   the PIDE markup tree, where such overlaps are silently dropped - which
   otherwise suppressed keyword coloring intermittently. *)
fun kw_tok markup (yypos, yytext, cons) =
    let
      val p = get_pos yypos
      val _ = report_token (yypos, String.size yytext, markup, yytext, "")
    in cons (p, p) end

(* Every real token claims whatever comments/antiquotations have piled up
   since the previous one (see C11_Comments, above), before the underlying
   "tok"/"tok_val"/"kw_tok" of YaccLib.thy computes and reports its own
   position - claiming at the token's own start ("get_pos yypos"), which is
   exactly the position the grammar will later see as this token's "left". *)
fun c11_tok (yypos, yytext, markup, typ, sort, cons) =
    (C11_Comments.attach_pending (get_pos yypos);
     tok (yypos, yytext, markup, typ, sort, cons))

fun c11_tok_val (yypos, yytext, markup, typ, sort, cons, value) =
    (C11_Comments.attach_pending (get_pos yypos);
     tok_val (yypos, yytext, markup, typ, sort, cons, value))

fun c11_kw_tok markup (yypos, yytext, cons) =
    (C11_Comments.attach_pending (get_pos yypos);
     kw_tok markup (yypos, yytext, cons))

(* Accumulate one fragment of raw comment text, tagged with its own span -
   mirrors "report_token"'s own start/end computation, since comment
   fragments never go through "tok"/"tok_val" themselves (they produce no
   token at all). *)
fun push_raw_fragment (yypos, yytext) =
    C11_Comments.push_raw (yytext, Position.range_position (get_pos yypos, get_pos (yypos + String.size yytext)))

(* Antiquotation state: the tag most recently seen ("@tag", or "@tag(N)"
   with an explicit level - see "parse_tag_and_level" below), and the text
   of the cartouche body currently being scanned (accumulated fragment by
   fragment across possibly-nested "\<open>...\<close>", the same way the surrounding
   comment text itself is never assembled into one string up front - see
   the ANTIQ lexer rules below), together with that body's start position.
   The quoted-string body alternative ("@tag(N) \"...\"") needs none of
   this: since a quoted body cannot nest, it is matched, extracted, and
   pushed in one shot by a single lex rule/handler - see
   "antiq_tag_and_string_seen" below - without ever touching this state. *)
val antiq_tag : (string * int * Position.T) ref = ref ("", 0, Position.none)
val antiq_buf : string list ref = ref []
val antiq_start : Position.T ref = ref Position.none

(* Splits the text matched after the leading "@" into the tag name and its
   optional parenthesized level ("foo" -> ("foo", 0), "foo(3)"/"foo (3)" ->
   ("foo", 3)) - shared by the cartouche-body path ("antiq_tag_seen") and
   the quoted-string-body path ("antiq_tag_and_string_seen"), so both
   notations parse "@tag(N)" identically. *)
fun parse_tag_and_level text =
    let
      val trim = Substring.string o Substring.dropr Char.isSpace o Substring.full
      val stripped =
        Substring.string (Substring.dropl (fn c => c = #"@" orelse Char.isSpace c) (Substring.full text))
    in
      case String.fields (fn c => c = #"(") stripped of
        [name] => (trim name, 0)
      | [name, rest] =>
          (trim name,
           valOf (Int.fromString (String.substring (rest, 0, String.size rest - 1))))
      | _ => (trim stripped, 0)
    end

fun antiq_tag_seen (yypos, yytext) =
    let val (name, level) = parse_tag_and_level yytext
    in antiq_tag := (name, level, get_pos yypos) end

fun antiq_body_start yypos = antiq_start := get_pos yypos

fun antiq_body_push text = antiq_buf := text :: !antiq_buf

fun antiq_body_finish yypos =
    let
      val body_text = String.concat (rev (!antiq_buf))
      val body_pos = Position.range_position (!antiq_start, get_pos yypos)
      val (tag_text, level, tag_pos) = !antiq_tag
    in
      antiq_buf := [];
      C11_Comments.push_antiquotation {tag = (tag_text, tag_pos)} {level = level} {cartouche = (body_text, body_pos)}
    end

(* The quoted-string alternative to a cartouche body: unlike "\<open>...\<close>",
   a double-quoted string cannot nest, so the whole "@tag(N) \"...\""
   (tag, optional level, and body) is recognized and matched by a single
   lex rule (see the "ANTIQ" macro-free rule below reusing "ES", the
   existing C-string escape-sequence class, purely so an escaped quote
   "\"" inside the body does not end the match early) rather than needing
   a dedicated lexer sub-state the way the cartouche body does. Since the
   rule requires the quote to follow the tag/level with only horizontal
   whitespace between (no other character, no newline), it only ever
   matches a quote that is genuinely a body opener right after a tag -
   an unrelated quote elsewhere in the comment is untouched, falling
   through to ordinary raw-comment-text scanning as always. The body text
   is kept exactly as written between the quotes (no escape decoding),
   matching how the cartouche body is likewise stored raw. *)
fun antiq_tag_and_string_seen (yypos, yytext) =
    let
      fun find_quote i = if String.sub (yytext, i) = #"\"" then i else find_quote (i + 1)
      val qpos = find_quote 0
      val (name, level) = parse_tag_and_level (String.substring (yytext, 0, qpos))
      val body_len = String.size yytext - qpos - 2
      val body_text = String.substring (yytext, qpos + 1, body_len)
      val body_start = yypos + qpos + 1
      val body_pos = Position.range_position (get_pos body_start, get_pos (body_start + body_len))
    in
      C11_Comments.push_antiquotation {tag = (name, get_pos yypos)} {level = level} {cartouche = (body_text, body_pos)}
    end
\<close>
lex_definitions\<open>
O=[0-7];
D=[0-9];
NZ=[1-9];
L=[A-Za-z_];
A=[A-Za-z_0-9];
H=[a-fA-F0-9];
HP=(0[xX]);
E=([eE][+-]?{D}+);
P=([pP][+-]?{D}+);
FS=(f|F|l|L);
IS=(((u|U)(l|L|ll|LL)?)|((l|L|ll|LL)(u|U)?));
CP=(u|U|L);
SP=(u8|u|U|L);
ES=(\\(['"?\\abfnrtv]|{O}{1,3}|x{H}+));
WS=[\ \t\r\n\011\012];
HWS=[\ \t\011\012];
OPENCART=\\\<open>;
CLOSECART=\\\<close>;
%s COMMENT INCLUDE LCOMMENT ANTIQ;
\<close>
lex_rules\<open>
<INITIAL>"/*"                            => (YYBEGIN COMMENT; lex());
<INITIAL>"//"                            => (antiq_from_block := false; YYBEGIN LCOMMENT; lex());

<INITIAL>"#"{HWS}*"include"               => (YYBEGIN INCLUDE; c11_kw_tok Markup.keyword2 (yypos, yytext, Tokens.INCLUDE));
<INCLUDE>{HWS}+                          => (lex());
<INCLUDE>"<"[^>\n]*">"                   => (YYBEGIN INITIAL; c11_tok_val (yypos, yytext, Markup.string, "HEADER_NAME", "", Tokens.HEADER_NAME, yytext));
<INCLUDE>["][^"\n]*["]                   => (YYBEGIN INITIAL; c11_tok_val (yypos, yytext, Markup.string, "HEADER_NAME", "", Tokens.HEADER_NAME, yytext));
<INCLUDE>\n                              => (YYBEGIN INITIAL; lex());
<INCLUDE>.                               => (YYBEGIN INITIAL; lex());

<INITIAL>"#"{HWS}*"define"               => (c11_kw_tok Markup.keyword2 (yypos, yytext, Tokens.DEFINE));
<INITIAL>"#"{HWS}*"ifndef"               => (c11_kw_tok Markup.keyword2 (yypos, yytext, Tokens.IFNDEF));
<INITIAL>"#"{HWS}*"ifdef"                => (c11_kw_tok Markup.keyword2 (yypos, yytext, Tokens.IFDEF));
<INITIAL>"#"{HWS}*"else"                 => (c11_kw_tok Markup.keyword2 (yypos, yytext, Tokens.PP_ELSE));
<INITIAL>"#"{HWS}*"endif"                => (c11_kw_tok Markup.keyword2 (yypos, yytext, Tokens.ENDIF));

<INITIAL>"auto"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.AUTO));
<INITIAL>"break"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.BREAK));
<INITIAL>"case"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.CASE));
<INITIAL>"char"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.CHAR));
<INITIAL>"const"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.CONST));
<INITIAL>"continue"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.CONTINUE));
<INITIAL>"default"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.DEFAULT));
<INITIAL>"do"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.DO));
<INITIAL>"double"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.DOUBLE));
<INITIAL>"else"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.ELSE));
<INITIAL>"enum"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.ENUM));
<INITIAL>"extern"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.EXTERN));
<INITIAL>"float"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.FLOAT));
<INITIAL>"for"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.FOR));
<INITIAL>"goto"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.GOTO));
<INITIAL>"if"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.IF));
<INITIAL>"inline"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.INLINE));
<INITIAL>"int"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.INT));
<INITIAL>"long"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.LONG));
<INITIAL>"register"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.REGISTER));
<INITIAL>"restrict"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.RESTRICT));
<INITIAL>"return"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.RETURN));
<INITIAL>"short"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.SHORT));
<INITIAL>"signed"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.SIGNED));
<INITIAL>"sizeof"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.SIZEOF));
<INITIAL>"static"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.STATIC));
<INITIAL>"struct"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.STRUCT));
<INITIAL>"switch"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.SWITCH));
<INITIAL>"typedef"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.TYPEDEF));
<INITIAL>"union"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.UNION));
<INITIAL>"unsigned"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.UNSIGNED));
<INITIAL>"void"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.VOID));
<INITIAL>"volatile"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.VOLATILE));
<INITIAL>"while"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.WHILE));
<INITIAL>"_Alignas"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.ALIGNAS));
<INITIAL>"_Alignof"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.ALIGNOF));
<INITIAL>"_Atomic"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.ATOMIC));
<INITIAL>"_Bool"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.BOOL));
<INITIAL>"_Complex"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.COMPLEX));
<INITIAL>"_Generic"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.GENERIC));
<INITIAL>"_Imaginary"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.IMAGINARY));
<INITIAL>"_Noreturn"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.NORETURN));
<INITIAL>"_Static_assert"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.STATIC_ASSERT));
<INITIAL>"_Thread_local"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.THREAD_LOCAL));
<INITIAL>"__func__"	=> (c11_kw_tok Markup.keyword1 (yypos, yytext, Tokens.FUNC_NAME));

<INITIAL>{L}{A}*	=> (c11_tok_val (yypos, yytext, Markup.free, "IDENTIFIER", "", Tokens.IDENTIFIER, yytext));

<INITIAL>{HP}{H}+{IS}?	=> (c11_tok_val (yypos, yytext, Markup.numeral, "I_CONSTANT", "", Tokens.I_CONSTANT, yytext));
<INITIAL>{NZ}{D}*{IS}?	=> (c11_tok_val (yypos, yytext, Markup.numeral, "I_CONSTANT", "", Tokens.I_CONSTANT, yytext));
<INITIAL>"0"{O}*{IS}?	=> (c11_tok_val (yypos, yytext, Markup.numeral, "I_CONSTANT", "", Tokens.I_CONSTANT, yytext));
<INITIAL>{CP}?'([^'\\\n]|{ES})+'	=> (c11_tok_val (yypos, yytext, Markup.numeral, "I_CONSTANT", "", Tokens.I_CONSTANT, yytext));

<INITIAL>{D}+{E}{FS}?	=> (c11_tok_val (yypos, yytext, Markup.numeral, "F_CONSTANT", "", Tokens.F_CONSTANT, yytext));
<INITIAL>{D}*"."{D}+{E}?{FS}?	=> (c11_tok_val (yypos, yytext, Markup.numeral, "F_CONSTANT", "", Tokens.F_CONSTANT, yytext));
<INITIAL>{D}+"."{E}?{FS}?	=> (c11_tok_val (yypos, yytext, Markup.numeral, "F_CONSTANT", "", Tokens.F_CONSTANT, yytext));
<INITIAL>{HP}{H}+{P}{FS}?	=> (c11_tok_val (yypos, yytext, Markup.numeral, "F_CONSTANT", "", Tokens.F_CONSTANT, yytext));
<INITIAL>{HP}{H}*"."{H}+{P}{FS}?	=> (c11_tok_val (yypos, yytext, Markup.numeral, "F_CONSTANT", "", Tokens.F_CONSTANT, yytext));
<INITIAL>{HP}{H}+"."{P}{FS}?	=> (c11_tok_val (yypos, yytext, Markup.numeral, "F_CONSTANT", "", Tokens.F_CONSTANT, yytext));

<INITIAL>({SP}?["]([^"\\\n]|{ES})*["]{WS}*)+	=> (c11_tok_val (yypos, yytext, Markup.string, "STRING_LITERAL", "", Tokens.STRING_LITERAL, yytext));

<INITIAL>"..."	=> (c11_tok (yypos, yytext, Markup.operator, "ELLIPSIS", "", Tokens.ELLIPSIS));
<INITIAL>">>="	=> (c11_tok (yypos, yytext, Markup.operator, "RIGHT_ASSIGN", "", Tokens.RIGHT_ASSIGN));
<INITIAL>"<<="	=> (c11_tok (yypos, yytext, Markup.operator, "LEFT_ASSIGN", "", Tokens.LEFT_ASSIGN));
<INITIAL>"+="	=> (c11_tok (yypos, yytext, Markup.operator, "ADD_ASSIGN", "", Tokens.ADD_ASSIGN));
<INITIAL>"-="	=> (c11_tok (yypos, yytext, Markup.operator, "SUB_ASSIGN", "", Tokens.SUB_ASSIGN));
<INITIAL>"*="	=> (c11_tok (yypos, yytext, Markup.operator, "MUL_ASSIGN", "", Tokens.MUL_ASSIGN));
<INITIAL>"/="	=> (c11_tok (yypos, yytext, Markup.operator, "DIV_ASSIGN", "", Tokens.DIV_ASSIGN));
<INITIAL>"%="	=> (c11_tok (yypos, yytext, Markup.operator, "MOD_ASSIGN", "", Tokens.MOD_ASSIGN));
<INITIAL>"&="	=> (c11_tok (yypos, yytext, Markup.operator, "AND_ASSIGN", "", Tokens.AND_ASSIGN));
<INITIAL>"^="	=> (c11_tok (yypos, yytext, Markup.operator, "XOR_ASSIGN", "", Tokens.XOR_ASSIGN));
<INITIAL>"|="	=> (c11_tok (yypos, yytext, Markup.operator, "OR_ASSIGN", "", Tokens.OR_ASSIGN));
<INITIAL>">>"	=> (c11_tok (yypos, yytext, Markup.operator, "RIGHT_OP", "", Tokens.RIGHT_OP));
<INITIAL>"<<"	=> (c11_tok (yypos, yytext, Markup.operator, "LEFT_OP", "", Tokens.LEFT_OP));
<INITIAL>"++"	=> (c11_tok (yypos, yytext, Markup.operator, "INC_OP", "", Tokens.INC_OP));
<INITIAL>"--"	=> (c11_tok (yypos, yytext, Markup.operator, "DEC_OP", "", Tokens.DEC_OP));
<INITIAL>"->"	=> (c11_tok (yypos, yytext, Markup.operator, "PTR_OP", "", Tokens.PTR_OP));
<INITIAL>"&&"	=> (c11_tok (yypos, yytext, Markup.operator, "AND_OP", "", Tokens.AND_OP));
<INITIAL>"||"	=> (c11_tok (yypos, yytext, Markup.operator, "OR_OP", "", Tokens.OR_OP));
<INITIAL>"<="	=> (c11_tok (yypos, yytext, Markup.operator, "LE_OP", "", Tokens.LE_OP));
<INITIAL>">="	=> (c11_tok (yypos, yytext, Markup.operator, "GE_OP", "", Tokens.GE_OP));
<INITIAL>"=="	=> (c11_tok (yypos, yytext, Markup.operator, "EQ_OP", "", Tokens.EQ_OP));
<INITIAL>"!="	=> (c11_tok (yypos, yytext, Markup.operator, "NE_OP", "", Tokens.NE_OP));

<INITIAL>";"	=> (c11_tok (yypos, yytext, Markup.operator, "SEMI", "", Tokens.SEMI));
<INITIAL>("{"|"<%")	=> (c11_tok (yypos, yytext, Markup.operator, "LBRACE", "", Tokens.LBRACE));
<INITIAL>("}"|"%>")	=> (c11_tok (yypos, yytext, Markup.operator, "RBRACE", "", Tokens.RBRACE));
<INITIAL>","	=> (c11_tok (yypos, yytext, Markup.operator, "COMMA", "", Tokens.COMMA));
<INITIAL>":"	=> (c11_tok (yypos, yytext, Markup.operator, "COLON", "", Tokens.COLON));
<INITIAL>"="	=> (c11_tok (yypos, yytext, Markup.operator, "ASSIGN", "", Tokens.ASSIGN));
<INITIAL>"("	=> (c11_tok (yypos, yytext, Markup.operator, "LPAREN", "", Tokens.LPAREN));
<INITIAL>")"	=> (c11_tok (yypos, yytext, Markup.operator, "RPAREN", "", Tokens.RPAREN));
<INITIAL>("["|"<:")	=> (c11_tok (yypos, yytext, Markup.operator, "LBRACKET", "", Tokens.LBRACKET));
<INITIAL>("]"|":>")	=> (c11_tok (yypos, yytext, Markup.operator, "RBRACKET", "", Tokens.RBRACKET));
<INITIAL>"."	=> (c11_tok (yypos, yytext, Markup.operator, "DOT", "", Tokens.DOT));
<INITIAL>"&"	=> (c11_tok (yypos, yytext, Markup.operator, "AMP", "", Tokens.AMP));
<INITIAL>"!"	=> (c11_tok (yypos, yytext, Markup.operator, "BANG", "", Tokens.BANG));
<INITIAL>"~"	=> (c11_tok (yypos, yytext, Markup.operator, "TILDE", "", Tokens.TILDE));
<INITIAL>"-"	=> (c11_tok (yypos, yytext, Markup.operator, "MINUS", "", Tokens.MINUS));
<INITIAL>"+"	=> (c11_tok (yypos, yytext, Markup.operator, "PLUS", "", Tokens.PLUS));
<INITIAL>"*"	=> (c11_tok (yypos, yytext, Markup.operator, "STAR", "", Tokens.STAR));
<INITIAL>"/"	=> (c11_tok (yypos, yytext, Markup.operator, "SLASH", "", Tokens.SLASH));
<INITIAL>"%"	=> (c11_tok (yypos, yytext, Markup.operator, "PERCENT", "", Tokens.PERCENT));
<INITIAL>"<"	=> (c11_tok (yypos, yytext, Markup.operator, "LT", "", Tokens.LT));
<INITIAL>">"	=> (c11_tok (yypos, yytext, Markup.operator, "GT", "", Tokens.GT));
<INITIAL>"^"	=> (c11_tok (yypos, yytext, Markup.operator, "CARET", "", Tokens.CARET));
<INITIAL>"|"	=> (c11_tok (yypos, yytext, Markup.operator, "PIPE", "", Tokens.PIPE));
<INITIAL>"?"	=> (c11_tok (yypos, yytext, Markup.operator, "QUESTION", "", Tokens.QUESTION));

<INITIAL>{WS}+                             => (lex());
<INITIAL>.                                  => (lex());

<COMMENT>[^*@\\\n]+                        => (push_raw_fragment (yypos, yytext); lex());
<COMMENT>\n+                                => (push_raw_fragment (yypos, yytext); lex());
<COMMENT>"*"+[^*/@\\\n]*                   => (push_raw_fragment (yypos, yytext); lex());
<COMMENT>"*"+"/"                            => (YYBEGIN INITIAL; lex());

<COMMENT>"@"{HWS}*{L}{A}*({HWS}*"("{D}+")")?{HWS}*["]([^"\\\n]|{ES})*["]
                                            => (report_token (yypos, String.size yytext, Markup.antiquote, "C antiquotation tag+body", "");
                                                antiq_tag_and_string_seen (yypos, yytext); lex());
<COMMENT>"@"{HWS}*{L}{A}*({HWS}*"("{D}+")")?
                                            => (report_token (yypos, String.size yytext, Markup.antiquote, "C antiquotation tag", "");
                                                antiq_tag_seen (yypos, yytext); lex());
<COMMENT>"@"                               => (push_raw_fragment (yypos, yytext); lex());
<COMMENT>"\\"                              => (push_raw_fragment (yypos, yytext); lex());
<COMMENT>{OPENCART}                        => (report_token (yypos, String.size yytext, Markup.cartouche, "C antiquotation body", "");
                                                antiq_depth := 1; antiq_from_block := true;
                                                antiq_body_start (yypos + String.size yytext); YYBEGIN ANTIQ; lex());

<LCOMMENT>[^@\\\n]+                        => (push_raw_fragment (yypos, yytext); lex());
<LCOMMENT>"@"{HWS}*{L}{A}*({HWS}*"("{D}+")")?{HWS}*["]([^"\\\n]|{ES})*["]
                                            => (report_token (yypos, String.size yytext, Markup.antiquote, "C antiquotation tag+body", "");
                                                antiq_tag_and_string_seen (yypos, yytext); lex());
<LCOMMENT>"@"{HWS}*{L}{A}*({HWS}*"("{D}+")")?
                                            => (report_token (yypos, String.size yytext, Markup.antiquote, "C antiquotation tag", "");
                                                antiq_tag_seen (yypos, yytext); lex());
<LCOMMENT>"@"                              => (push_raw_fragment (yypos, yytext); lex());
<LCOMMENT>"\\"                             => (push_raw_fragment (yypos, yytext); lex());
<LCOMMENT>{OPENCART}                       => (report_token (yypos, String.size yytext, Markup.cartouche, "C antiquotation body", "");
                                                antiq_depth := 1; antiq_from_block := false;
                                                antiq_body_start (yypos + String.size yytext); YYBEGIN ANTIQ; lex());
<LCOMMENT>\n                               => (YYBEGIN INITIAL; lex());

<ANTIQ>[^\\\n]+                            => (antiq_body_push yytext; lex());
<ANTIQ>\n+                                  => (antiq_body_push yytext; lex());
<ANTIQ>"\\"                                => (antiq_body_push yytext; lex());
<ANTIQ>{OPENCART}                          => (antiq_depth := !antiq_depth + 1; antiq_body_push yytext; lex());
<ANTIQ>{CLOSECART}                         => (antiq_depth := !antiq_depth - 1;
                                                if !antiq_depth = 0
                                                then (antiq_body_finish yypos;
                                                      (if !antiq_from_block then YYBEGIN COMMENT else YYBEGIN LCOMMENT); lex())
                                                else (antiq_body_push yytext; lex()));
\<close>
and yacc_user_declarations\<open>
open C_Ast

(* --- Literal parsing helpers -------------------------------------------
   Deliberately modest, not a full C11 constant-literal decoder: covers the
   common cases (decimal/hex/octal integers, the usual u/l/ll suffixes,
   float literals kept verbatim since CFloat already wants the raw text,
   and the ordinary backslash escapes in char/string literals). Anything
   past that (unusual escape forms, exotic suffix combinations) falls back
   to a safe default rather than raising, since this is a syntax-directed
   translation, not a validator. *)

fun strip_int_suffix s =
  Substring.string (Substring.dropr
    (fn c => c = #"u" orelse c = #"U" orelse c = #"l" orelse c = #"L") (Substring.full s))

fun opt_int NONE = 0
  | opt_int (SOME n) = n

fun parse_c_int_repr (core : string) : int * cIntRepr =
  if String.isPrefix "0x" core orelse String.isPrefix "0X" core
  then (opt_int (StringCvt.scanString (Int.scan StringCvt.HEX) core), HexRepr)
  else if core <> "" andalso String.sub (core, 0) = #"0" andalso size core > 1
  then (opt_int (StringCvt.scanString (Int.scan StringCvt.OCT) core), OctalRepr)
  else (opt_int (Int.fromString core), DecRepr)

(* Bit-encoding of cIntFlag into "cIntFlag flags" (= "Flags of int"): no
   encoder survived c_ast.ML's own pruning of the generic HOL flag-set
   machinery, so this is a fresh, self-contained convention (bit 0
   unsigned, bit 1 long, bit 2 long long, bit 3 imaginary) - nothing
   downstream currently decodes these bits, so any consistent convention
   is equally valid. *)
fun parse_c_int_flags (s : string) : cIntFlag flags =
  let
    val u = String.isSubstring "u" s orelse String.isSubstring "U" s
    val ll = String.isSubstring "ll" s orelse String.isSubstring "LL" s
    val l = (String.isSubstring "l" s orelse String.isSubstring "L" s) andalso not ll
  in
    Flags ((if u then 1 else 0) + (if l then 2 else 0) + (if ll then 4 else 0))
  end

fun parse_c_integer (text : string) : cInteger =
  let
    val core = strip_int_suffix text
    val (n, repr) = parse_c_int_repr core
  in CInteger (n, repr, parse_c_int_flags text) end

fun unescape_c (s : string) : string =
  let
    fun go [] acc = rev acc
      | go (#"\\" :: #"n" :: cs) acc = go cs (#"\n" :: acc)
      | go (#"\\" :: #"t" :: cs) acc = go cs (#"\t" :: acc)
      | go (#"\\" :: #"r" :: cs) acc = go cs (#"\r" :: acc)
      | go (#"\\" :: #"0" :: cs) acc = go cs (#"\000" :: acc)
      | go (#"\\" :: #"\\" :: cs) acc = go cs (#"\\" :: acc)
      | go (#"\\" :: #"'" :: cs) acc = go cs (#"'" :: acc)
      | go (#"\\" :: #"\"" :: cs) acc = go cs (#"\"" :: acc)
      | go (#"\\" :: c :: cs) acc = go cs (c :: acc)
      | go (c :: cs) acc = go cs (c :: acc)
  in String.implode (go (String.explode s) []) end

(* Strips an optional wide-prefix (u/U/L) and the surrounding quotes. *)
fun strip_quotes quote (s : string) =
  let
    val s = Substring.full s
    val s = Substring.dropl (fn c => c <> quote) s (* drop any prefix letters *)
    val s = Substring.slice (s, 1, SOME (Substring.size s - 2))
  in Substring.string s end

fun parse_c_char (text : string) : cChar =
  let
    val is_wide = String.size text > 0 andalso String.sub (text, 0) <> #"'"
    val inner = unescape_c (strip_quotes #"'" text)
  in
    case String.explode inner of
      [c] => CChar (c, is_wide)
    | cs => CChars (cs, is_wide)
  end

fun const_of_i_constant (text, ndI) =
  if String.isSubstring "'" text
  then CCharConst (parse_c_char text, ndI)
  else CIntConst (parse_c_integer text, ndI)

fun parse_c_string (text : string) : cString =
  let val is_wide = String.size text > 0 andalso String.sub (text, 0) <> #"\""
  in CString (unescape_c (strip_quotes #"\"" text), is_wide) end

fun strLit_to_constant (CStrLit (s, ndI)) = CStrConst (s, ndI)

(* --- Declarator assembly -------------------------------------------------
   direct_declarator's value is (base identifier option, derived-declarator
   suffix list collected so far); each array/function suffix rule appends
   its own "cDerivedDeclarator" to that list. A "(declarator)" base splices
   in the inner declarator's own derived-declarator list directly. Known,
   deliberate simplification: a parenthesized declarator that itself has a
   pointer prefix AND further suffixes attached outside the parens (e.g. a
   pointer-to-array-of-10-ints declarator written with the star inside the
   parens and the array bound outside) does not get fully correct
   suffix-binding precedence -
   the rare case a from-scratch C declarator grammar is famous for - since
   getting that exactly right needs a genuine closure-based "declarator
   inversion" (as in language-c's own Parser.y), out of scope for this
   pass. Every other shape (plain identifiers, pointers, simple arrays,
   simple function declarators, ordinary nesting) is unaffected. *)

fun mk_declarator (ident_opt, derived, str_lit_opt, attrs, ndI) =
  CDeclr (ident_opt, derived, str_lit_opt, attrs, ndI)

(* type_name / parameter_declaration / struct member: wrap a
   specifier-qualifier list plus an optional declarator/abstract-declarator
   into the "cDeclaration" shape everywhere else in c_ast.ML already
   expects for this ("val cSizeofType : ... -> 'a cExpression" etc. all
   take a plain "'a cDeclaration"). *)
fun mk_type_decl (specs, declr_opt, ndI) =
  CDecl (specs, [((declr_opt, NONE), NONE)], ndI)

fun ident_of_declr (CDeclr (io, _, _, _, _)) = io

exception Parse_gap of string

fun ndi p = C11_Comments.mk_nodeInfo p p
fun ndi2 (p1, p2) = C11_Comments.mk_nodeInfo p1 (Position.range_position (p1, p2))
\<close>
yacc_definitions\<open>
%eop EOF
%pure
%noshift EOF

%term
        IDENTIFIER of string | I_CONSTANT of string | F_CONSTANT of string | STRING_LITERAL of string | FUNC_NAME | SIZEOF |
        INCLUDE | HEADER_NAME of string | DEFINE | IFDEF | IFNDEF | PP_ELSE | ENDIF |
        PTR_OP | INC_OP | DEC_OP | LEFT_OP | RIGHT_OP | LE_OP | GE_OP | EQ_OP | NE_OP |
        AND_OP | OR_OP | MUL_ASSIGN | DIV_ASSIGN | MOD_ASSIGN | ADD_ASSIGN |
        SUB_ASSIGN | LEFT_ASSIGN | RIGHT_ASSIGN | AND_ASSIGN |
        XOR_ASSIGN | OR_ASSIGN |
        TYPEDEF_NAME | ENUMERATION_CONSTANT |
        TYPEDEF | EXTERN | STATIC | AUTO | REGISTER | INLINE |
        CONST | RESTRICT | VOLATILE |
        BOOL | CHAR | SHORT | INT | LONG | SIGNED | UNSIGNED | FLOAT | DOUBLE | VOID |
        COMPLEX | IMAGINARY |
        STRUCT | UNION | ENUM | ELLIPSIS |
        CASE | DEFAULT | IF | ELSE | SWITCH | WHILE | DO | FOR | GOTO | CONTINUE | BREAK | RETURN |
        ALIGNAS | ALIGNOF | ATOMIC | GENERIC | NORETURN | STATIC_ASSERT | THREAD_LOCAL |
        LPAREN | RPAREN | LBRACKET | RBRACKET | LBRACE | RBRACE |
        COMMA | DOT | COLON | SEMI | ASSIGN |
        STAR | AMP | PLUS | MINUS | TILDE | BANG |
        LT | GT | CARET | PIPE | QUESTION | PERCENT | SLASH |
        EOF

%nonterm
        primary_expression of Position.T cExpression | constant of Position.T cConstant |
        enumeration_constant of Position.T ident | string of Position.T cStringLiteral |
        generic_selection of Position.T cExpression |
        generic_assoc_list of (Position.T cDeclaration option * Position.T cExpression) list |
        generic_association of Position.T cDeclaration option * Position.T cExpression |
        postfix_expression of Position.T cExpression |
        argument_expression_list of Position.T cExpression list |
        unary_expression of Position.T cExpression | unary_operator of cUnaryOp |
        cast_expression of Position.T cExpression |
        multiplicative_expression of Position.T cExpression | additive_expression of Position.T cExpression |
        shift_expression of Position.T cExpression | relational_expression of Position.T cExpression |
        equality_expression of Position.T cExpression | and_expression of Position.T cExpression |
        exclusive_or_expression of Position.T cExpression | inclusive_or_expression of Position.T cExpression |
        logical_and_expression of Position.T cExpression | logical_or_expression of Position.T cExpression |
        conditional_expression of Position.T cExpression | assignment_expression of Position.T cExpression |
        assignment_operator of cAssignOp | expression of Position.T cExpression |
        constant_expression of Position.T cExpression | declaration of Position.T cDeclaration |
        declaration_specifiers of Position.T cDeclarationSpecifier list |
        init_declarator_list of ((Position.T cDeclarator option * Position.T cInitializer option) * Position.T cExpression option) list |
        init_declarator of (Position.T cDeclarator option * Position.T cInitializer option) * Position.T cExpression option |
        storage_class_specifier of Position.T cStorageSpecifier |
        type_specifier of Position.T cTypeSpecifier | struct_or_union_specifier of Position.T cTypeSpecifier |
        struct_or_union of cStructTag | struct_declaration_list of Position.T cDeclaration list |
        struct_declaration of Position.T cDeclaration |
        specifier_qualifier_list of Position.T cDeclarationSpecifier list |
        struct_declarator_list of ((Position.T cDeclarator option * Position.T cInitializer option) * Position.T cExpression option) list |
        struct_declarator of (Position.T cDeclarator option * Position.T cInitializer option) * Position.T cExpression option |
        enum_specifier of Position.T cTypeSpecifier |
        enumerator_list of (Position.T ident * Position.T cExpression option) list |
        enumerator of Position.T ident * Position.T cExpression option |
        atomic_type_specifier of Position.T cTypeSpecifier |
        type_qualifier of Position.T cTypeQualifier | function_specifier of Position.T cFunctionSpecifier |
        alignment_specifier of Position.T cAlignmentSpecifier | declarator of Position.T cDeclarator |
        direct_declarator of Position.T ident option * Position.T cDerivedDeclarator list |
        pointer of Position.T cDerivedDeclarator list |
        type_qualifier_list of Position.T cTypeQualifier list |
        parameter_type_list of Position.T cDeclaration list * bool |
        parameter_list of Position.T cDeclaration list | parameter_declaration of Position.T cDeclaration |
        identifier_list of Position.T ident list | type_name of Position.T cDeclaration |
        abstract_declarator of Position.T cDeclarator |
        direct_abstract_declarator of Position.T cDerivedDeclarator list |
        initializer of Position.T cInitializer |
        initializer_list of (Position.T cPartDesignator list * Position.T cInitializer) list |
        designation of Position.T cPartDesignator list | designator_list of Position.T cPartDesignator list |
        designator of Position.T cPartDesignator | static_assert_declaration of Position.T cDeclaration |
        statement of Position.T cStatement | labeled_statement of Position.T cStatement |
        compound_statement of Position.T cStatement | block_item_list of Position.T cCompoundBlockItem list |
        block_item of Position.T cCompoundBlockItem | expression_statement of Position.T cStatement |
        selection_statement of Position.T cStatement | iteration_statement of Position.T cStatement |
        jump_statement of Position.T cStatement | translation_unit of Position.T cExternalDeclaration list |
        external_declaration of Position.T cExternalDeclaration option |
        function_definition of Position.T cFunctionDef |
        declaration_list of Position.T cDeclaration list | preproc_directive of Position.T cPreprocDirective |
        external_declaration_list of Position.T cExternalDeclaration list |
        start_rule of Position.T root option
\<close>
yacc_rules\<open>
start_rule: 
        IDENTIFIER    (SOME (Id (Ident (IDENTIFIER, 0, ndi IDENTIFIERleft))))
|       expression    (SOME (Expr expression))
|       statement     (SOME (Stmt statement))
|       translation_unit    
                      (SOME (Units [CTranslUnit (translation_unit, 
                                                  ndi2 (translation_unitleft, 
                                                        translation_unitright))]))

primary_expression: 
        IDENTIFIER    (CVar (Ident (IDENTIFIER, 0, ndi IDENTIFIERleft), ndi IDENTIFIERleft))
|       constant      (CConst constant)
|       string        (CConst (strLit_to_constant string))
|       LPAREN expression RPAREN    (expression)
|       generic_selection           (generic_selection)

constant: 
        I_CONSTANT           (const_of_i_constant (I_CONSTANT, ndi I_CONSTANTleft))
|       F_CONSTANT           (CFloatConst (CFloat F_CONSTANT, ndi F_CONSTANTleft))
|       ENUMERATION_CONSTANT    (CIntConst (CInteger (0, DecRepr, Flags 0), 
                                             ndi ENUMERATION_CONSTANTleft))

enumeration_constant: IDENTIFIER     (Ident (IDENTIFIER, 0, ndi IDENTIFIERleft))

string: STRING_LITERAL    (CStrLit (parse_c_string STRING_LITERAL, ndi STRING_LITERALleft))
|       FUNC_NAME         (CStrLit (CString ("__func__", false), ndi FUNC_NAMEleft))

generic_selection: 
        GENERIC LPAREN assignment_expression COMMA generic_assoc_list RPAREN    
                          (CGenericSelection (assignment_expression, generic_assoc_list, 
                                               ndi2 (GENERICleft, RPARENright)))

generic_assoc_list: generic_association                ([generic_association])
|       generic_assoc_list COMMA generic_association   (generic_assoc_list @ [generic_association])

generic_association: 
        type_name COLON assignment_expression    (SOME type_name, assignment_expression)
|       DEFAULT COLON assignment_expression      (NONE, assignment_expression)

postfix_expression: 
        primary_expression    (primary_expression)
|       postfix_expression LBRACKET expression RBRACKET    
                              (CIndex (postfix_expression, expression, 
                                        ndi2 (postfix_expressionleft, RBRACKETright)))
|       postfix_expression LPAREN RPAREN    
                              (CCall (postfix_expression, [], 
                                        ndi2 (postfix_expressionleft, RPARENright)))
|       postfix_expression LPAREN argument_expression_list RPAREN    
                              (CCall (postfix_expression, argument_expression_list, 
                                       ndi2 (postfix_expressionleft, RPARENright)))
|       postfix_expression DOT IDENTIFIER    
                              (CMember (postfix_expression, Ident (IDENTIFIER, 0, 
                                                                     ndi IDENTIFIERleft), 
                                         false, 
                                         ndi2 (postfix_expressionleft, IDENTIFIERright)))
|       postfix_expression PTR_OP IDENTIFIER    
                              (CMember (postfix_expression, 
                                         Ident (IDENTIFIER, 0, ndi IDENTIFIERleft), true, 
                                         ndi2 (postfix_expressionleft, IDENTIFIERright)))
|       postfix_expression INC_OP    
                              (CUnary (CPostIncOp, postfix_expression, 
                                        ndi2 (postfix_expressionleft, INC_OPright)))
|       postfix_expression DEC_OP    
                              (CUnary (CPostDecOp, postfix_expression, 
                                        ndi2 (postfix_expressionleft, DEC_OPright)))
|       LPAREN type_name RPAREN LBRACE initializer_list RBRACE    
                              (CCompoundLit (type_name, initializer_list, 
                                              ndi2 (LPARENleft, RBRACEright)))
|       LPAREN type_name RPAREN LBRACE initializer_list COMMA RBRACE    
                              (CCompoundLit (type_name, initializer_list, 
                                              ndi2 (LPARENleft, RBRACEright)))

argument_expression_list: 
        assignment_expression    ([assignment_expression])
|       argument_expression_list COMMA assignment_expression    
                              (argument_expression_list @ [assignment_expression])

unary_expression: 
        postfix_expression         (postfix_expression)
|       INC_OP unary_expression    (CUnary (CPreIncOp, unary_expression, 
                                             ndi2 (INC_OPleft, unary_expressionright)))
|       DEC_OP unary_expression    (CUnary (CPreDecOp, unary_expression, 
                                             ndi2 (DEC_OPleft, unary_expressionright)))
|       unary_operator cast_expression    
                                   (CUnary (unary_operator, cast_expression, 
                                             ndi2 (unary_operatorleft, cast_expressionright)))
|       SIZEOF unary_expression    (CSizeofExpr (unary_expression, 
                                                  ndi2 (SIZEOFleft, unary_expressionright)))
|       SIZEOF LPAREN type_name RPAREN    
                                   (CSizeofType (type_name, 
                                                  ndi2 (SIZEOFleft, RPARENright)))
|       ALIGNOF LPAREN type_name RPAREN    
                                   (CAlignofType (type_name, ndi2 (ALIGNOFleft, RPARENright)))

unary_operator: 
        AMP     (CAdrOp)
|       STAR    (CIndOp)
|       PLUS    (CPlusOp)
|       MINUS   (CMinOp)
|       TILDE   (CCompOp)
|       BANG    (CNegOp)

cast_expression: 
        unary_expression    (unary_expression)
|       LPAREN type_name RPAREN cast_expression    
                            (CCast (type_name, cast_expression, 
                                     ndi2 (LPARENleft, cast_expressionright)))

multiplicative_expression: 
        cast_expression    (cast_expression)
|       multiplicative_expression STAR cast_expression    
                           (CBinary (CMulOp, multiplicative_expression, cast_expression, 
                                      ndi2 (multiplicative_expressionleft, cast_expressionright)))
|       multiplicative_expression SLASH cast_expression    
                           (CBinary (CDivOp, multiplicative_expression, cast_expression, 
                                      ndi2 (multiplicative_expressionleft, cast_expressionright)))
|       multiplicative_expression PERCENT cast_expression    
                           (CBinary (CRmdOp, multiplicative_expression, cast_expression, 
                                      ndi2 (multiplicative_expressionleft, cast_expressionright)))

additive_expression: 
        multiplicative_expression    
                           (multiplicative_expression)
|       additive_expression PLUS multiplicative_expression    
                           (CBinary (CAddOp, additive_expression, multiplicative_expression, 
                                      ndi2 (additive_expressionleft, multiplicative_expressionright)))
|       additive_expression MINUS multiplicative_expression    
                           (CBinary (CSubOp, additive_expression, multiplicative_expression, 
                                      ndi2 (additive_expressionleft, 
                                            multiplicative_expressionright)))

shift_expression: 
        additive_expression(additive_expression)
|       shift_expression LEFT_OP additive_expression    
                           (CBinary (CShlOp, shift_expression, additive_expression, 
                                      ndi2 (shift_expressionleft, additive_expressionright)))
|       shift_expression RIGHT_OP additive_expression    
                           (CBinary (CShrOp, shift_expression, additive_expression, 
                                      ndi2 (shift_expressionleft, additive_expressionright)))

relational_expression: 
        shift_expression(shift_expression)
|       relational_expression LT shift_expression    
                        (CBinary (CLeOp, relational_expression, shift_expression, 
                                   ndi2 (relational_expressionleft, shift_expressionright)))
|       relational_expression GT shift_expression    
                        (CBinary (CGrOp, relational_expression, shift_expression, 
                                   ndi2 (relational_expressionleft, shift_expressionright)))
|       relational_expression LE_OP shift_expression    
                        (CBinary (CLeqOp, relational_expression, shift_expression, 
                                   ndi2 (relational_expressionleft, shift_expressionright)))
|       relational_expression GE_OP shift_expression    
                        (CBinary (CGeqOp, relational_expression, shift_expression, 
                                   ndi2 (relational_expressionleft, shift_expressionright)))

equality_expression: 
        relational_expression    
                        (relational_expression)
|       equality_expression EQ_OP relational_expression    
                        (CBinary (CEqOp, equality_expression, relational_expression, 
                                   ndi2 (equality_expressionleft, relational_expressionright)))
|       equality_expression NE_OP relational_expression    
                        (CBinary (CNeqOp, equality_expression, relational_expression, 
                                   ndi2 (equality_expressionleft, relational_expressionright)))

and_expression: 
        equality_expression    
                        (equality_expression)
|       and_expression AMP equality_expression    
                        (CBinary (CAndOp, and_expression, equality_expression, 
                                   ndi2 (and_expressionleft, equality_expressionright)))

exclusive_or_expression: 
        and_expression  (and_expression)
|       exclusive_or_expression CARET and_expression    
                        (CBinary (CXorOp, exclusive_or_expression, and_expression, 
                                   ndi2 (exclusive_or_expressionleft, and_expressionright)))

inclusive_or_expression: 
        exclusive_or_expression    
                        (exclusive_or_expression)
|       inclusive_or_expression PIPE exclusive_or_expression    
                        (CBinary (COrOp, inclusive_or_expression, exclusive_or_expression, 
                                   ndi2 (inclusive_or_expressionleft, exclusive_or_expressionright)))

logical_and_expression: 
        inclusive_or_expression    
                        (inclusive_or_expression)
|       logical_and_expression AND_OP inclusive_or_expression    
                        (CBinary (CLndOp, logical_and_expression, inclusive_or_expression, 
                                   ndi2 (logical_and_expressionleft, inclusive_or_expressionright)))

logical_or_expression: 
        logical_and_expression    
                        (logical_and_expression)
|       logical_or_expression OR_OP logical_and_expression    
                        (CBinary (CLorOp, logical_or_expression, logical_and_expression, 
                                   ndi2 (logical_or_expressionleft, logical_and_expressionright)))

conditional_expression: 
        logical_or_expression    
                        (logical_or_expression)
|       logical_or_expression QUESTION expression COLON conditional_expression    
                        (CCond (logical_or_expression, SOME expression, conditional_expression, 
                                 ndi2 (logical_or_expressionleft, conditional_expressionright)))

assignment_expression: 
        conditional_expression    
                        (conditional_expression)
|       unary_expression assignment_operator assignment_expression    
                        (CAssign (assignment_operator, unary_expression, assignment_expression, 
                                   ndi2 (unary_expressionleft, assignment_expressionright)))

assignment_operator: 
        ASSIGN        (CAssignOp)
|       MUL_ASSIGN    (CMulAssOp)
|       DIV_ASSIGN    (CDivAssOp)
|       MOD_ASSIGN    (CRmdAssOp)
|       ADD_ASSIGN    (CAddAssOp)
|       SUB_ASSIGN    (CSubAssOp)
|       LEFT_ASSIGN   (CShlAssOp)
|       RIGHT_ASSIGN  (CShrAssOp)
|       AND_ASSIGN    (CAndAssOp)
|       XOR_ASSIGN    (CXorAssOp)
|       OR_ASSIGN     (COrAssOp)

expression: 
        assignment_expression    
                      (assignment_expression)
|       expression COMMA assignment_expression    
                      (CComma ((case expression of CComma (l,_) => l | e => [e]) 
                                @ [assignment_expression], 
                                ndi2 (expressionleft, assignment_expressionright)))

constant_expression: 
        conditional_expression    (conditional_expression)

declaration: 
        declaration_specifiers SEMI    
                      (CDecl (declaration_specifiers, [], ndi2 (declaration_specifiersleft, SEMIright)))
|       declaration_specifiers init_declarator_list SEMI    
                      (CDecl (declaration_specifiers, init_declarator_list, 
                               ndi2 (declaration_specifiersleft, SEMIright)))
|       static_assert_declaration    
                      (static_assert_declaration)

declaration_specifiers: 
        storage_class_specifier declaration_specifiers    
                      (CStorageSpec storage_class_specifier :: declaration_specifiers)
|       storage_class_specifier    
                      ([CStorageSpec storage_class_specifier])
|       type_specifier declaration_specifiers    
                      (CTypeSpec type_specifier :: declaration_specifiers)
|       type_specifier([CTypeSpec type_specifier])
|       type_qualifier declaration_specifiers    
                      (CTypeQual type_qualifier :: declaration_specifiers)
|       type_qualifier([CTypeQual type_qualifier])
|       function_specifier declaration_specifiers    
                      (CFunSpec function_specifier :: declaration_specifiers)
|       function_specifier    
                      ([CFunSpec function_specifier])
|       alignment_specifier declaration_specifiers    
                      (CAlignSpec alignment_specifier :: declaration_specifiers)
|       alignment_specifier    
                      ([CAlignSpec alignment_specifier])

init_declarator_list: 
        init_declarator    
                      ([init_declarator])
|       init_declarator_list COMMA init_declarator    
                      (init_declarator_list @ [init_declarator])

init_declarator: 
        declarator ASSIGN initializer    
                      ((SOME declarator, SOME initializer), NONE)
|       declarator    ((SOME declarator, NONE), NONE)

storage_class_specifier: 
        TYPEDEF       (CTypedef (ndi TYPEDEFleft))
|       EXTERN        (CExtern (ndi EXTERNleft))
|       STATIC        (CStatic (ndi STATICleft))
|       THREAD_LOCAL  (CThread (ndi THREAD_LOCALleft))
|       AUTO          (CAuto (ndi AUTOleft))
|       REGISTER      (CRegister (ndi REGISTERleft))

type_specifier: 
        VOID          (CVoidType (ndi VOIDleft))
|       CHAR          (CCharType (ndi CHARleft))
|       SHORT         (CShortType (ndi SHORTleft))
|       INT           (CIntType (ndi INTleft))
|       LONG          (CLongType (ndi LONGleft))
|       FLOAT         (CFloatType (ndi FLOATleft))
|       DOUBLE        (CDoubleType (ndi DOUBLEleft))
|       SIGNED        (CSignedType (ndi SIGNEDleft))
|       UNSIGNED      (CUnsigType (ndi UNSIGNEDleft))
|       BOOL          (CBoolType (ndi BOOLleft))
|       COMPLEX       (CComplexType (ndi COMPLEXleft))
|       IMAGINARY     (CComplexType (ndi IMAGINARYleft))
|       atomic_type_specifier    
                      (atomic_type_specifier)
|       struct_or_union_specifier    
                      (struct_or_union_specifier)
|       enum_specifier(enum_specifier)
|       TYPEDEF_NAME  (CTypeDef (Ident ("", 0, ndi TYPEDEF_NAMEleft), ndi TYPEDEF_NAMEleft))

struct_or_union_specifier: 
        struct_or_union LBRACE struct_declaration_list RBRACE    
                      (CSUType (CStruct (struct_or_union, NONE, SOME struct_declaration_list, [], 
                                           ndi2 (struct_or_unionleft, RBRACEright)), 
                                 ndi2 (struct_or_unionleft, RBRACEright)))
|       struct_or_union IDENTIFIER LBRACE struct_declaration_list RBRACE    
                      (CSUType (CStruct (struct_or_union, SOME (Ident (IDENTIFIER, 0, ndi IDENTIFIERleft)), 
                                 SOME struct_declaration_list, [], ndi2 (struct_or_unionleft, RBRACEright)), 
                                 ndi2 (struct_or_unionleft, RBRACEright)))
|       struct_or_union IDENTIFIER    
                      (CSUType (CStruct (struct_or_union, 
                                           SOME (Ident (IDENTIFIER, 0, ndi IDENTIFIERleft)),NONE,[], 
                                                 ndi2 (struct_or_unionleft, IDENTIFIERright)), 
                                 ndi2 (struct_or_unionleft, IDENTIFIERright)))

struct_or_union: 
        STRUCT        (CStructTag)
|       UNION         (CUnionTag)

struct_declaration_list: 
        struct_declaration    
                      ([struct_declaration])
|       struct_declaration_list struct_declaration    
                      (struct_declaration_list @ [struct_declaration])

struct_declaration: 
        specifier_qualifier_list SEMI    
                      (CDecl (specifier_qualifier_list, [], 
                               ndi2 (specifier_qualifier_listleft, SEMIright)))
|       specifier_qualifier_list struct_declarator_list SEMI    
                      (CDecl (specifier_qualifier_list, struct_declarator_list, 
                               ndi2 (specifier_qualifier_listleft, SEMIright)))
|       static_assert_declaration    
                      (static_assert_declaration)

specifier_qualifier_list: 
        type_specifier specifier_qualifier_list    
                      (CTypeSpec type_specifier :: specifier_qualifier_list)
|       type_specifier([CTypeSpec type_specifier])
|       type_qualifier specifier_qualifier_list    
                      (CTypeQual type_qualifier :: specifier_qualifier_list)
|       type_qualifier([CTypeQual type_qualifier])

struct_declarator_list: 
        struct_declarator    
                      ([struct_declarator])
|       struct_declarator_list COMMA struct_declarator    
                      (struct_declarator_list @ [struct_declarator])

struct_declarator: 
        COLON constant_expression    
                      ((NONE, NONE), SOME constant_expression)
|       declarator COLON constant_expression    
                      ((SOME declarator, NONE), SOME constant_expression)
|       declarator    ((SOME declarator, NONE), NONE)

enum_specifier: 
        ENUM LBRACE enumerator_list RBRACE    
                      (CEnumType (CEnum (NONE, SOME enumerator_list, [], 
                                      ndi2 (ENUMleft, RBRACEright)), ndi2 (ENUMleft, RBRACEright)))
|       ENUM LBRACE enumerator_list COMMA RBRACE    
                      (CEnumType (CEnum (NONE, SOME enumerator_list, [], 
                                           ndi2 (ENUMleft, RBRACEright)), 
                                   ndi2 (ENUMleft, RBRACEright)))
|       ENUM IDENTIFIER LBRACE enumerator_list RBRACE    
                      (CEnumType (CEnum (SOME (Ident (IDENTIFIER, 0, ndi IDENTIFIERleft)), 
                                           SOME enumerator_list, [], ndi2 (ENUMleft, RBRACEright)), 
                                   ndi2 (ENUMleft, RBRACEright)))
|       ENUM IDENTIFIER LBRACE enumerator_list COMMA RBRACE    
                      (CEnumType (CEnum (SOME (Ident (IDENTIFIER, 0, ndi IDENTIFIERleft)), 
                                                 SOME enumerator_list, [], 
                                           ndi2 (ENUMleft, RBRACEright)), 
                                   ndi2 (ENUMleft, RBRACEright)))
|       ENUM IDENTIFIER
                      (CEnumType (CEnum (SOME (Ident (IDENTIFIER, 0, ndi IDENTIFIERleft)), 
                                           NONE, [], ndi2 (ENUMleft, IDENTIFIERright)), 
                                   ndi2 (ENUMleft, IDENTIFIERright)))

enumerator_list: 
        enumerator    ([enumerator])
|       enumerator_list COMMA enumerator    
                      (enumerator_list @ [enumerator])

enumerator: 
        enumeration_constant ASSIGN constant_expression    
                      (enumeration_constant, SOME constant_expression)
|       enumeration_constant    
                      (enumeration_constant, NONE)

atomic_type_specifier: 
        ATOMIC LPAREN type_name RPAREN    
                      (CAtomicType (type_name, ndi2 (ATOMICleft, RPARENright)))

type_qualifier: 
        CONST         (CConstQual (ndi CONSTleft))
|       RESTRICT      (CRestrQual (ndi RESTRICTleft))
|       VOLATILE      (CVolatQual (ndi VOLATILEleft))
|       ATOMIC        (CAtomicQual (ndi ATOMICleft))

function_specifier: 
        INLINE        (CInlineQual (ndi INLINEleft))
|       NORETURN      (CNoreturnQual (ndi NORETURNleft))

alignment_specifier: 
        ALIGNAS LPAREN type_name RPAREN    
                      (CAlignAsType (type_name, ndi2 (ALIGNASleft, RPARENright)))
|       ALIGNAS LPAREN constant_expression RPAREN    
                      (CAlignAsExpr (constant_expression, ndi2 (ALIGNASleft, RPARENright)))

declarator: 
        pointer direct_declarator    
                      (let val (io, derived) = direct_declarator 
                       in mk_declarator (io, pointer @ derived, NONE, [], 
                                         ndi2 (pointerleft, direct_declaratorright)) 
                       end)
|       direct_declarator    
                      (let val (io, derived) = direct_declarator 
                       in mk_declarator (io, derived, NONE, [], 
                                         ndi2 (direct_declaratorleft, direct_declaratorright)) 
                       end)

direct_declarator: 
        IDENTIFIER    (SOME (Ident (IDENTIFIER, 0, ndi IDENTIFIERleft)), [])
|       LPAREN declarator RPAREN    
                      (let val CDeclr (io, derived, _, _, _) = declarator in (io, derived) end)
|       direct_declarator LBRACKET RBRACKET    
                      (let val (io, d) = direct_declarator 
                       in (io, d @ [CArrDeclr ([], CNoArrSize false, 
                                                ndi2 (direct_declaratorleft, RBRACKETright))]) 
                       end)
|       direct_declarator LBRACKET STAR RBRACKET    
                      (let val (io, d) = direct_declarator 
                       in (io, d @ [CArrDeclr ([], CNoArrSize false, 
                                                ndi2 (direct_declaratorleft, RBRACKETright))]) 
                       end)
|       direct_declarator LBRACKET STATIC type_qualifier_list assignment_expression RBRACKET    
                      (let val (io, d) = direct_declarator 
                       in (io, d @ [CArrDeclr (type_qualifier_list, 
                                                CArrSize (true, assignment_expression), 
                                                ndi2 (direct_declaratorleft, RBRACKETright))]) 
                       end)
|       direct_declarator LBRACKET STATIC assignment_expression RBRACKET    
                      (let val (io, d) = direct_declarator 
                       in (io, d @ [CArrDeclr ([], CArrSize (true, assignment_expression), 
                                                ndi2 (direct_declaratorleft, RBRACKETright))]) 
                       end)
|       direct_declarator LBRACKET type_qualifier_list STAR RBRACKET    
                      (let val (io, d) = direct_declarator 
                       in (io, d @ [CArrDeclr (type_qualifier_list, CNoArrSize false, 
                                                ndi2 (direct_declaratorleft, RBRACKETright))]) 
                       end)
|       direct_declarator LBRACKET type_qualifier_list STATIC assignment_expression RBRACKET    
                      (let val (io, d) = direct_declarator 
                       in (io, d @ [CArrDeclr (type_qualifier_list, CArrSize (true, assignment_expression), 
                                                ndi2 (direct_declaratorleft, RBRACKETright))]) 
                       end)
|       direct_declarator LBRACKET type_qualifier_list assignment_expression RBRACKET    
                      (let val (io, d) = direct_declarator 
                       in (io, d @ [CArrDeclr (type_qualifier_list, CArrSize (false, assignment_expression), 
                                                ndi2 (direct_declaratorleft, RBRACKETright))]) 
                       end)
|       direct_declarator LBRACKET type_qualifier_list RBRACKET    
                      (let val (io, d) = direct_declarator 
                       in (io, d @ [CArrDeclr (type_qualifier_list, CNoArrSize false, 
                                                ndi2 (direct_declaratorleft, RBRACKETright))]) 
                       end)
|       direct_declarator LBRACKET assignment_expression RBRACKET    
                      (let val (io, d) = direct_declarator 
                       in (io, d @ [CArrDeclr ([], CArrSize (false, assignment_expression), 
                                                ndi2 (direct_declaratorleft, RBRACKETright))]) 
                       end)
|       direct_declarator LPAREN parameter_type_list RPAREN    
                      (let val (io, d) = direct_declarator 
                           val (params, ellipsis) = parameter_type_list 
                       in (io, d @ [CFunDeclr (Right (params, ellipsis), [], 
                                                ndi2 (direct_declaratorleft, RPARENright))]) 
                       end)
|       direct_declarator LPAREN RPAREN    
                      (let val (io, d) = direct_declarator 
                       in (io, d @ [CFunDeclr (Right ([], false), [], 
                                                       ndi2 (direct_declaratorleft, RPARENright))]) 
                       end)
|       direct_declarator LPAREN identifier_list RPAREN    
                      (let val (io, d) = direct_declarator 
                       in (io, d @ [CFunDeclr (Left identifier_list, [], 
                                                ndi2 (direct_declaratorleft, RPARENright))]) 
                       end)

pointer:STAR type_qualifier_list pointer    
                     (CPtrDeclr (type_qualifier_list, 
                                  ndi2 (STARleft, type_qualifier_listright)) :: pointer)
|       STAR type_qualifier_list    
                     ([CPtrDeclr (type_qualifier_list, ndi2 (STARleft, type_qualifier_listright))])
|       STAR pointer (CPtrDeclr ([], ndi STARleft) :: pointer)
|       STAR         ([CPtrDeclr ([], ndi STARleft)])

type_qualifier_list: 
        type_qualifier
                     ([type_qualifier])
|       type_qualifier_list type_qualifier    
                     (type_qualifier_list @ [type_qualifier])

parameter_type_list: 
        parameter_list COMMA ELLIPSIS    
                     (parameter_list, true)
|       parameter_list(parameter_list, false)

parameter_list: 
        parameter_declaration    
                     ([parameter_declaration])
|       parameter_list COMMA parameter_declaration    
                     (parameter_list @ [parameter_declaration])

parameter_declaration: 
        declaration_specifiers declarator    
                     (mk_type_decl (declaration_specifiers, SOME declarator, 
                                    ndi2 (declaration_specifiersleft, declaratorright)))
|       declaration_specifiers abstract_declarator    
                     (mk_type_decl (declaration_specifiers, SOME abstract_declarator, 
                                    ndi2 (declaration_specifiersleft, abstract_declaratorright)))
|       declaration_specifiers    
                     (mk_type_decl (declaration_specifiers, NONE, ndi declaration_specifiersleft))

identifier_list: 
        IDENTIFIER    ([Ident (IDENTIFIER, 0, ndi IDENTIFIERleft)])
|       identifier_list COMMA IDENTIFIER    
                      (identifier_list @ [Ident (IDENTIFIER, 0, ndi IDENTIFIERleft)])

type_name: specifier_qualifier_list abstract_declarator    
                      (mk_type_decl (specifier_qualifier_list, SOME abstract_declarator, 
                                     ndi2 (specifier_qualifier_listleft, abstract_declaratorright)))
|       specifier_qualifier_list    
                      (mk_type_decl (specifier_qualifier_list, NONE, ndi specifier_qualifier_listleft))

abstract_declarator: 
        pointer direct_abstract_declarator    
                      (mk_declarator (NONE, pointer @ direct_abstract_declarator, NONE, [], 
                                      ndi2 (pointerleft, direct_abstract_declaratorright)))
|       pointer       (mk_declarator (NONE, pointer, NONE, [], ndi pointerleft))
|       direct_abstract_declarator    
                      (mk_declarator (NONE, direct_abstract_declarator, NONE, [], 
                                      ndi2 (direct_abstract_declaratorleft, 
                                            direct_abstract_declaratorright)))

direct_abstract_declarator: 
        LPAREN abstract_declarator RPAREN    
                      (let val CDeclr (_, d, _, _, _) = abstract_declarator in d end)
|       LBRACKET RBRACKET    
                      ([CArrDeclr ([], CNoArrSize false, ndi2 (LBRACKETleft, RBRACKETright))])
|       LBRACKET STAR RBRACKET    
                      ([CArrDeclr ([], CNoArrSize false, ndi2 (LBRACKETleft, RBRACKETright))])
|       LBRACKET STATIC type_qualifier_list assignment_expression RBRACKET    
                      ([CArrDeclr (type_qualifier_list, CArrSize (true, assignment_expression), 
                                    ndi2 (LBRACKETleft, RBRACKETright))])
|       LBRACKET STATIC assignment_expression RBRACKET    
                      ([CArrDeclr ([], CArrSize (true, assignment_expression), 
                                    ndi2 (LBRACKETleft, RBRACKETright))])
|       LBRACKET type_qualifier_list STATIC assignment_expression RBRACKET    
                      ([CArrDeclr (type_qualifier_list, CArrSize (true, assignment_expression), 
                                    ndi2 (LBRACKETleft, RBRACKETright))])
|       LBRACKET type_qualifier_list assignment_expression RBRACKET    
                      ([CArrDeclr (type_qualifier_list, CArrSize (false, assignment_expression), 
                                    ndi2 (LBRACKETleft, RBRACKETright))])
|       LBRACKET type_qualifier_list RBRACKET    
                      ([CArrDeclr (type_qualifier_list, CNoArrSize false, 
                                    ndi2 (LBRACKETleft, RBRACKETright))])
|       LBRACKET assignment_expression RBRACKET    
                      ([CArrDeclr ([], CArrSize (false, assignment_expression), 
                                    ndi2 (LBRACKETleft, RBRACKETright))])
|       direct_abstract_declarator LBRACKET RBRACKET    
                      (direct_abstract_declarator 
                       @ [CArrDeclr ([], CNoArrSize false, 
                                      ndi2 (direct_abstract_declaratorleft, RBRACKETright))])
|       direct_abstract_declarator LBRACKET STAR RBRACKET    
                      (direct_abstract_declarator 
                       @ [CArrDeclr ([], CNoArrSize false, 
                                      ndi2 (direct_abstract_declaratorleft, RBRACKETright))])
|       direct_abstract_declarator LBRACKET STATIC type_qualifier_list assignment_expression RBRACKET    
                      (direct_abstract_declarator 
                       @ [CArrDeclr (type_qualifier_list, CArrSize (true, assignment_expression), 
                                      ndi2 (direct_abstract_declaratorleft, RBRACKETright))])
|       direct_abstract_declarator LBRACKET STATIC assignment_expression RBRACKET    
                      (direct_abstract_declarator 
                       @ [CArrDeclr ([], CArrSize (true, assignment_expression), 
                                      ndi2 (direct_abstract_declaratorleft, RBRACKETright))])
|       direct_abstract_declarator LBRACKET type_qualifier_list assignment_expression RBRACKET    
                      (direct_abstract_declarator 
                       @ [CArrDeclr (type_qualifier_list, CArrSize (false, assignment_expression), 
                                      ndi2 (direct_abstract_declaratorleft, RBRACKETright))])
|       direct_abstract_declarator LBRACKET type_qualifier_list STATIC assignment_expression RBRACKET    
                      (direct_abstract_declarator 
                       @ [CArrDeclr (type_qualifier_list, CArrSize (true, assignment_expression), 
                                      ndi2 (direct_abstract_declaratorleft, RBRACKETright))])
|       direct_abstract_declarator LBRACKET type_qualifier_list RBRACKET    
                      (direct_abstract_declarator 
                       @ [CArrDeclr (type_qualifier_list, CNoArrSize false, 
                                      ndi2 (direct_abstract_declaratorleft, RBRACKETright))])
|       direct_abstract_declarator LBRACKET assignment_expression RBRACKET    
                      (direct_abstract_declarator 
                       @ [CArrDeclr ([], CArrSize (false, assignment_expression), 
                                      ndi2 (direct_abstract_declaratorleft, RBRACKETright))])
|       LPAREN RPAREN ([CFunDeclr (Right ([], false), [], ndi2 (LPARENleft, RPARENright))])
|       LPAREN parameter_type_list RPAREN    
                      (let val (params, ell) = parameter_type_list 
                       in [CFunDeclr (Right (params, ell),[], ndi2 (LPARENleft, RPARENright))] end)
|       direct_abstract_declarator LPAREN RPAREN    
                      (direct_abstract_declarator 
                       @ [CFunDeclr (Right ([], false), [], 
                                      ndi2 (direct_abstract_declaratorleft, RPARENright))])
|       direct_abstract_declarator LPAREN parameter_type_list RPAREN    
                      (let val (params, ell) = parameter_type_list 
                       in direct_abstract_declarator 
                          @ [CFunDeclr (Right (params, ell), [], 
                                         ndi2 (direct_abstract_declaratorleft, RPARENright))] 
                       end)

initializer: 
        LBRACE initializer_list RBRACE    
                      (CInitList (initializer_list, ndi2 (LBRACEleft, RBRACEright)))
|       LBRACE initializer_list COMMA RBRACE    
                      (CInitList (initializer_list, ndi2 (LBRACEleft, RBRACEright)))
|       assignment_expression    
                      (CInitExpr (assignment_expression, ndi assignment_expressionleft))

initializer_list: 
        designation initializer    
                      ([(designation, initializer)])
|       initializer   ([([], initializer)])
|       initializer_list COMMA designation initializer    
                      (initializer_list @ [(designation, initializer)])
|       initializer_list COMMA initializer    
                      (initializer_list @ [([], initializer)])

designation: designator_list ASSIGN    (designator_list)

designator_list: 
        designator    ([designator])
|       designator_list designator    
                      (designator_list @ [designator])

designator: 
        LBRACKET constant_expression RBRACKET    
                      (CArrDesig (constant_expression, ndi2 (LBRACKETleft, RBRACKETright)))
|       DOT IDENTIFIER(CMemberDesig (Ident (IDENTIFIER, 0, ndi IDENTIFIERleft), 
                                      ndi2 (DOTleft, IDENTIFIERright)))

static_assert_declaration: 
        STATIC_ASSERT LPAREN constant_expression COMMA STRING_LITERAL RPAREN SEMI    
                      (CStaticAssert (constant_expression, 
                                       CStrLit (parse_c_string STRING_LITERAL, ndi STRING_LITERALleft), 
                                       ndi2 (STATIC_ASSERTleft, SEMIright)))

statement: 
        labeled_statement    
                      (labeled_statement)
|       compound_statement    
                      (compound_statement)
|       expression_statement    
                      (expression_statement)
|       selection_statement    
                      (selection_statement)
|       iteration_statement    
                      (iteration_statement)
|       jump_statement(jump_statement)

labeled_statement: 
        IDENTIFIER COLON statement    
                      (CLabel (Ident (IDENTIFIER, 0, ndi IDENTIFIERleft), statement, [], 
                                ndi2 (IDENTIFIERleft, statementright)))
|       CASE constant_expression COLON statement    
                      (CCase (constant_expression, statement, ndi2 (CASEleft, statementright)))
|       DEFAULT COLON statement    
                      (CDefault (statement, ndi2 (DEFAULTleft, statementright)))

compound_statement: LBRACE RBRACE    
                      (CCompound ([], [], ndi2 (LBRACEleft, RBRACEright)))
|       LBRACE block_item_list RBRACE    
                      (CCompound ([], block_item_list, ndi2 (LBRACEleft, RBRACEright)))

block_item_list: 
        block_item    ([block_item])
|       block_item_list block_item    
                      (block_item_list @ [block_item])

block_item: declaration    
                      (CBlockDecl declaration)
|       statement     (CBlockStmt statement)

expression_statement: 
        SEMI          (CExpr (NONE, ndi SEMIleft))
|       expression SEMI(CExpr (SOME expression, ndi2 (expressionleft, SEMIright)))

selection_statement: 
        IF LPAREN expression RPAREN statement ELSE statement    
           (CIf (expression, statement1, SOME statement2, ndi2 (IFleft, statement2right)))
|       IF LPAREN expression RPAREN statement    
           (CIf (expression, statement, NONE, ndi2 (IFleft, statementright)))
|       SWITCH LPAREN expression RPAREN statement    
           (CSwitch (expression, statement, ndi2 (SWITCHleft, statementright)))

iteration_statement: 
        WHILE LPAREN expression RPAREN statement    
           (CWhile (expression, statement, false, ndi2 (WHILEleft, statementright)))
|       DO statement WHILE LPAREN expression RPAREN SEMI    
           (CWhile (expression, statement, true, ndi2 (DOleft, SEMIright)))
|       FOR LPAREN expression_statement expression_statement RPAREN statement    
           (CFor (Left (case expression_statement1 of CExpr (eo,_) => eo), 
                        (case expression_statement2 of CExpr (eo,_) => eo), NONE, statement, 
                   ndi2 (FORleft, statementright)))
|       FOR LPAREN expression_statement expression_statement expression RPAREN statement    
           (CFor (Left (case expression_statement1 of CExpr (eo,_) => eo), 
                   (case expression_statement2 of CExpr (eo,_) => eo), SOME expression, statement, 
                   ndi2 (FORleft, statementright)))
|       FOR LPAREN declaration expression_statement RPAREN statement    
           (CFor (Right declaration, (case expression_statement of CExpr (eo,_) => eo), 
                   NONE, statement, ndi2 (FORleft, statementright)))
|       FOR LPAREN declaration expression_statement expression RPAREN statement    
           (CFor (Right declaration, (case expression_statement of CExpr (eo,_) => eo), 
                   SOME expression, statement, ndi2 (FORleft, statementright)))

jump_statement: 
        GOTO IDENTIFIER SEMI    
           (CGoto (Ident (IDENTIFIER, 0, ndi IDENTIFIERleft), ndi2 (GOTOleft, SEMIright)))
|       CONTINUE SEMI    
           (CCont (ndi2 (CONTINUEleft, SEMIright)))
|       BREAK SEMI    
           (CBreak (ndi2 (BREAKleft, SEMIright)))
|       RETURN SEMI    
           (CReturn (NONE, ndi2 (RETURNleft, SEMIright)))
|       RETURN expression SEMI    
           (CReturn (SOME expression, ndi2 (RETURNleft, SEMIright)))

translation_unit: 
        external_declaration    
           (case external_declaration of SOME e => [e] | NONE => [])
|       translation_unit external_declaration    
           (translation_unit @ (case external_declaration of SOME e => [e] | NONE => []))

external_declaration: 
        function_definition    
           (SOME (CFDefExt function_definition))
|       declaration    
           (SOME (CDeclExt declaration))
|       preproc_directive
           (SOME (CPPExt preproc_directive))

preproc_directive:
        INCLUDE HEADER_NAME
           (let val system = String.isPrefix "<" HEADER_NAME
                val name = String.substring (HEADER_NAME, 1, String.size HEADER_NAME - 2)
            in CPPInclude (system, name, ndi2 (INCLUDEleft, HEADER_NAMEright)) end)
|       DEFINE IDENTIFIER ASSIGN constant_expression
           (CPPDefine (Ident (IDENTIFIER, 0, ndi IDENTIFIERleft), constant_expression,
                        ndi2 (DEFINEleft, constant_expressionright)))
|       DEFINE IDENTIFIER LPAREN RPAREN ASSIGN constant_expression
           (CPPDefineFun (Ident (IDENTIFIER, 0, ndi IDENTIFIERleft), [], constant_expression,
                           ndi2 (DEFINEleft, constant_expressionright)))
|       DEFINE IDENTIFIER LPAREN identifier_list RPAREN ASSIGN constant_expression
           (CPPDefineFun (Ident (IDENTIFIER, 0, ndi IDENTIFIERleft), identifier_list, constant_expression,
                           ndi2 (DEFINEleft, constant_expressionright)))
|       IFDEF IDENTIFIER external_declaration_list ENDIF
           (CPPIfdef (false, Ident (IDENTIFIER, 0, ndi IDENTIFIERleft), external_declaration_list, [],
                       ndi2 (IFDEFleft, ENDIFright)))
|       IFDEF IDENTIFIER external_declaration_list PP_ELSE external_declaration_list ENDIF
           (CPPIfdef (false, Ident (IDENTIFIER, 0, ndi IDENTIFIERleft),
                       external_declaration_list1, external_declaration_list2,
                       ndi2 (IFDEFleft, ENDIFright)))
|       IFNDEF IDENTIFIER external_declaration_list ENDIF
           (CPPIfdef (true, Ident (IDENTIFIER, 0, ndi IDENTIFIERleft), external_declaration_list, [],
                       ndi2 (IFNDEFleft, ENDIFright)))
|       IFNDEF IDENTIFIER external_declaration_list PP_ELSE external_declaration_list ENDIF
           (CPPIfdef (true, Ident (IDENTIFIER, 0, ndi IDENTIFIERleft),
                       external_declaration_list1, external_declaration_list2,
                       ndi2 (IFNDEFleft, ENDIFright)))

external_declaration_list:    ([])
|       external_declaration_list external_declaration    
            (external_declaration_list @ (case external_declaration of SOME e => [e] | NONE => []))

function_definition: 
        declaration_specifiers declarator declaration_list compound_statement    
           (CFunDef (declaration_specifiers, declarator, declaration_list, compound_statement, 
                      ndi2 (declaration_specifiersleft, compound_statementright)))
|       declaration_specifiers declarator compound_statement    
           (CFunDef (declaration_specifiers, declarator, [], compound_statement, 
                      ndi2 (declaration_specifiersleft, compound_statementright)))

declaration_list: 
        declaration    
           ([declaration])
|       declaration_list declaration    
           (declaration_list @ [declaration])
\<close>


end
