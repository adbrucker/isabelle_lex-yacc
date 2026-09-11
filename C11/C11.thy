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

theory C11
  imports "../LexYacc"
  keywords "c11" "c11_reject" :: diag
  and "c11_file" :: thy_load
begin

text\<open>
  This theory formalizes the ANSI C11 grammar as a ml-lex/ml-yacc lexer/parser pair,
  ported from the reference grammar published at
  \<^verbatim>\<open>https://www.quut.com/c/ANSI-C-grammar-y.html\<close> (Yacc) and
  \<^verbatim>\<open>https://www.quut.com/c/ANSI-C-grammar-l-2011.html\<close> (Lex), based on the 2011 ISO C
  standard. As in the reference grammar, this is a pure recognizer: no abstract syntax
  tree is built, all semantic actions are the trivial \<open>()\<close>. Following the reference
  grammar's own note, identifiers are never lexed as \<open>TYPEDEF_NAME\<close> or
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
    recognizes the shape \<open>@tag \<open>...\<close>\<close> - an \<open>@\<close>-prefixed tag optionally followed
    by whitespace, and, independently, a properly-nested Isabelle cartouche
    \<open>\<open>\<dots>\<close>\<close> - anywhere inside a comment, reporting both as PIDE markup
    (\<^ML>\<open>Markup.antiquote\<close> / \<^ML>\<open>Markup.cartouche\<close>) instead of discarding them as
    opaque comment text. Nothing is \<^emph>\<open>executed\<close>: this recognizer has no notion of
    an annotation command language, only of where one \<^emph>\<open>could\<close> be hooked in later.
    Since a cartouche can nest, recognizing it needs more than one regular-expression
    rule; see the \<open>ANTIQ\<close> lexer state below for how a small amount of \<^verbatim>\<open>lex_user_declarations\<close>
    state (a depth counter) turns this into a well-defined \<^emph>\<open>non-expert-mode\<close>
    ml-lex specification - no \<open>[expert]\<close> switch turned out to be necessary after all.
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
OPENCART=\<open>;
CLOSECART=\<close>;
%s COMMENT INCLUDE LCOMMENT ANTIQ;
\<close>
lex_rules\<open>
<INITIAL>"/*"                            => (YYBEGIN COMMENT; lex());
<INITIAL>"//"                            => (antiq_from_block := false; YYBEGIN LCOMMENT; lex());

<INITIAL>"#"{HWS}*"include"               => (YYBEGIN INCLUDE; kw_tok Markup.keyword2 (yypos, yytext, Tokens.INCLUDE));
<INCLUDE>{HWS}+                          => (lex());
<INCLUDE>"<"[^>\n]*">"                   => (YYBEGIN INITIAL; tok (yypos, yytext, Markup.string, "HEADER_NAME", "", Tokens.HEADER_NAME));
<INCLUDE>["][^"\n]*["]                   => (YYBEGIN INITIAL; tok (yypos, yytext, Markup.string, "HEADER_NAME", "", Tokens.HEADER_NAME));
<INCLUDE>\n                              => (YYBEGIN INITIAL; lex());
<INCLUDE>.                               => (YYBEGIN INITIAL; lex());

<INITIAL>"#"{HWS}*"define"               => (kw_tok Markup.keyword2 (yypos, yytext, Tokens.DEFINE));
<INITIAL>"#"{HWS}*"ifndef"               => (kw_tok Markup.keyword2 (yypos, yytext, Tokens.IFNDEF));
<INITIAL>"#"{HWS}*"ifdef"                => (kw_tok Markup.keyword2 (yypos, yytext, Tokens.IFDEF));
<INITIAL>"#"{HWS}*"else"                 => (kw_tok Markup.keyword2 (yypos, yytext, Tokens.PP_ELSE));
<INITIAL>"#"{HWS}*"endif"                => (kw_tok Markup.keyword2 (yypos, yytext, Tokens.ENDIF));

<INITIAL>"auto"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.AUTO));
<INITIAL>"break"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.BREAK));
<INITIAL>"case"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.CASE));
<INITIAL>"char"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.CHAR));
<INITIAL>"const"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.CONST));
<INITIAL>"continue"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.CONTINUE));
<INITIAL>"default"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.DEFAULT));
<INITIAL>"do"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.DO));
<INITIAL>"double"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.DOUBLE));
<INITIAL>"else"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.ELSE));
<INITIAL>"enum"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.ENUM));
<INITIAL>"extern"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.EXTERN));
<INITIAL>"float"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.FLOAT));
<INITIAL>"for"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.FOR));
<INITIAL>"goto"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.GOTO));
<INITIAL>"if"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.IF));
<INITIAL>"inline"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.INLINE));
<INITIAL>"int"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.INT));
<INITIAL>"long"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.LONG));
<INITIAL>"register"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.REGISTER));
<INITIAL>"restrict"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.RESTRICT));
<INITIAL>"return"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.RETURN));
<INITIAL>"short"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.SHORT));
<INITIAL>"signed"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.SIGNED));
<INITIAL>"sizeof"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.SIZEOF));
<INITIAL>"static"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.STATIC));
<INITIAL>"struct"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.STRUCT));
<INITIAL>"switch"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.SWITCH));
<INITIAL>"typedef"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.TYPEDEF));
<INITIAL>"union"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.UNION));
<INITIAL>"unsigned"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.UNSIGNED));
<INITIAL>"void"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.VOID));
<INITIAL>"volatile"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.VOLATILE));
<INITIAL>"while"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.WHILE));
<INITIAL>"_Alignas"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.ALIGNAS));
<INITIAL>"_Alignof"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.ALIGNOF));
<INITIAL>"_Atomic"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.ATOMIC));
<INITIAL>"_Bool"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.BOOL));
<INITIAL>"_Complex"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.COMPLEX));
<INITIAL>"_Generic"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.GENERIC));
<INITIAL>"_Imaginary"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.IMAGINARY));
<INITIAL>"_Noreturn"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.NORETURN));
<INITIAL>"_Static_assert"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.STATIC_ASSERT));
<INITIAL>"_Thread_local"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.THREAD_LOCAL));
<INITIAL>"__func__"	=> (kw_tok Markup.keyword1 (yypos, yytext, Tokens.FUNC_NAME));

<INITIAL>{L}{A}*	=> (tok (yypos, yytext, Markup.free, "IDENTIFIER", "", Tokens.IDENTIFIER));

<INITIAL>{HP}{H}+{IS}?	=> (tok (yypos, yytext, Markup.numeral, "I_CONSTANT", "", Tokens.I_CONSTANT));
<INITIAL>{NZ}{D}*{IS}?	=> (tok (yypos, yytext, Markup.numeral, "I_CONSTANT", "", Tokens.I_CONSTANT));
<INITIAL>"0"{O}*{IS}?	=> (tok (yypos, yytext, Markup.numeral, "I_CONSTANT", "", Tokens.I_CONSTANT));
<INITIAL>{CP}?'([^'\\\n]|{ES})+'	=> (tok (yypos, yytext, Markup.numeral, "I_CONSTANT", "", Tokens.I_CONSTANT));

<INITIAL>{D}+{E}{FS}?	=> (tok (yypos, yytext, Markup.numeral, "F_CONSTANT", "", Tokens.F_CONSTANT));
<INITIAL>{D}*"."{D}+{E}?{FS}?	=> (tok (yypos, yytext, Markup.numeral, "F_CONSTANT", "", Tokens.F_CONSTANT));
<INITIAL>{D}+"."{E}?{FS}?	=> (tok (yypos, yytext, Markup.numeral, "F_CONSTANT", "", Tokens.F_CONSTANT));
<INITIAL>{HP}{H}+{P}{FS}?	=> (tok (yypos, yytext, Markup.numeral, "F_CONSTANT", "", Tokens.F_CONSTANT));
<INITIAL>{HP}{H}*"."{H}+{P}{FS}?	=> (tok (yypos, yytext, Markup.numeral, "F_CONSTANT", "", Tokens.F_CONSTANT));
<INITIAL>{HP}{H}+"."{P}{FS}?	=> (tok (yypos, yytext, Markup.numeral, "F_CONSTANT", "", Tokens.F_CONSTANT));

<INITIAL>({SP}?["]([^"\\\n]|{ES})*["]{WS}*)+	=> (tok (yypos, yytext, Markup.string, "STRING_LITERAL", "", Tokens.STRING_LITERAL));

<INITIAL>"..."	=> (tok (yypos, yytext, Markup.operator, "ELLIPSIS", "", Tokens.ELLIPSIS));
<INITIAL>">>="	=> (tok (yypos, yytext, Markup.operator, "RIGHT_ASSIGN", "", Tokens.RIGHT_ASSIGN));
<INITIAL>"<<="	=> (tok (yypos, yytext, Markup.operator, "LEFT_ASSIGN", "", Tokens.LEFT_ASSIGN));
<INITIAL>"+="	=> (tok (yypos, yytext, Markup.operator, "ADD_ASSIGN", "", Tokens.ADD_ASSIGN));
<INITIAL>"-="	=> (tok (yypos, yytext, Markup.operator, "SUB_ASSIGN", "", Tokens.SUB_ASSIGN));
<INITIAL>"*="	=> (tok (yypos, yytext, Markup.operator, "MUL_ASSIGN", "", Tokens.MUL_ASSIGN));
<INITIAL>"/="	=> (tok (yypos, yytext, Markup.operator, "DIV_ASSIGN", "", Tokens.DIV_ASSIGN));
<INITIAL>"%="	=> (tok (yypos, yytext, Markup.operator, "MOD_ASSIGN", "", Tokens.MOD_ASSIGN));
<INITIAL>"&="	=> (tok (yypos, yytext, Markup.operator, "AND_ASSIGN", "", Tokens.AND_ASSIGN));
<INITIAL>"^="	=> (tok (yypos, yytext, Markup.operator, "XOR_ASSIGN", "", Tokens.XOR_ASSIGN));
<INITIAL>"|="	=> (tok (yypos, yytext, Markup.operator, "OR_ASSIGN", "", Tokens.OR_ASSIGN));
<INITIAL>">>"	=> (tok (yypos, yytext, Markup.operator, "RIGHT_OP", "", Tokens.RIGHT_OP));
<INITIAL>"<<"	=> (tok (yypos, yytext, Markup.operator, "LEFT_OP", "", Tokens.LEFT_OP));
<INITIAL>"++"	=> (tok (yypos, yytext, Markup.operator, "INC_OP", "", Tokens.INC_OP));
<INITIAL>"--"	=> (tok (yypos, yytext, Markup.operator, "DEC_OP", "", Tokens.DEC_OP));
<INITIAL>"->"	=> (tok (yypos, yytext, Markup.operator, "PTR_OP", "", Tokens.PTR_OP));
<INITIAL>"&&"	=> (tok (yypos, yytext, Markup.operator, "AND_OP", "", Tokens.AND_OP));
<INITIAL>"||"	=> (tok (yypos, yytext, Markup.operator, "OR_OP", "", Tokens.OR_OP));
<INITIAL>"<="	=> (tok (yypos, yytext, Markup.operator, "LE_OP", "", Tokens.LE_OP));
<INITIAL>">="	=> (tok (yypos, yytext, Markup.operator, "GE_OP", "", Tokens.GE_OP));
<INITIAL>"=="	=> (tok (yypos, yytext, Markup.operator, "EQ_OP", "", Tokens.EQ_OP));
<INITIAL>"!="	=> (tok (yypos, yytext, Markup.operator, "NE_OP", "", Tokens.NE_OP));

<INITIAL>";"	=> (tok (yypos, yytext, Markup.operator, "SEMI", "", Tokens.SEMI));
<INITIAL>("{"|"<%")	=> (tok (yypos, yytext, Markup.operator, "LBRACE", "", Tokens.LBRACE));
<INITIAL>("}"|"%>")	=> (tok (yypos, yytext, Markup.operator, "RBRACE", "", Tokens.RBRACE));
<INITIAL>","	=> (tok (yypos, yytext, Markup.operator, "COMMA", "", Tokens.COMMA));
<INITIAL>":"	=> (tok (yypos, yytext, Markup.operator, "COLON", "", Tokens.COLON));
<INITIAL>"="	=> (tok (yypos, yytext, Markup.operator, "ASSIGN", "", Tokens.ASSIGN));
<INITIAL>"("	=> (tok (yypos, yytext, Markup.operator, "LPAREN", "", Tokens.LPAREN));
<INITIAL>")"	=> (tok (yypos, yytext, Markup.operator, "RPAREN", "", Tokens.RPAREN));
<INITIAL>("["|"<:")	=> (tok (yypos, yytext, Markup.operator, "LBRACKET", "", Tokens.LBRACKET));
<INITIAL>("]"|":>")	=> (tok (yypos, yytext, Markup.operator, "RBRACKET", "", Tokens.RBRACKET));
<INITIAL>"."	=> (tok (yypos, yytext, Markup.operator, "DOT", "", Tokens.DOT));
<INITIAL>"&"	=> (tok (yypos, yytext, Markup.operator, "AMP", "", Tokens.AMP));
<INITIAL>"!"	=> (tok (yypos, yytext, Markup.operator, "BANG", "", Tokens.BANG));
<INITIAL>"~"	=> (tok (yypos, yytext, Markup.operator, "TILDE", "", Tokens.TILDE));
<INITIAL>"-"	=> (tok (yypos, yytext, Markup.operator, "MINUS", "", Tokens.MINUS));
<INITIAL>"+"	=> (tok (yypos, yytext, Markup.operator, "PLUS", "", Tokens.PLUS));
<INITIAL>"*"	=> (tok (yypos, yytext, Markup.operator, "STAR", "", Tokens.STAR));
<INITIAL>"/"	=> (tok (yypos, yytext, Markup.operator, "SLASH", "", Tokens.SLASH));
<INITIAL>"%"	=> (tok (yypos, yytext, Markup.operator, "PERCENT", "", Tokens.PERCENT));
<INITIAL>"<"	=> (tok (yypos, yytext, Markup.operator, "LT", "", Tokens.LT));
<INITIAL>">"	=> (tok (yypos, yytext, Markup.operator, "GT", "", Tokens.GT));
<INITIAL>"^"	=> (tok (yypos, yytext, Markup.operator, "CARET", "", Tokens.CARET));
<INITIAL>"|"	=> (tok (yypos, yytext, Markup.operator, "PIPE", "", Tokens.PIPE));
<INITIAL>"?"	=> (tok (yypos, yytext, Markup.operator, "QUESTION", "", Tokens.QUESTION));

<INITIAL>{WS}+                             => (lex());
<INITIAL>.                                  => (lex());

<COMMENT>[^*@\\\n]+                        => (lex());
<COMMENT>\n+                                => (lex());
<COMMENT>"*"+[^*/@\\\n]*                   => (lex());
<COMMENT>"*"+"/"                            => (YYBEGIN INITIAL; lex());

<COMMENT>"@"{HWS}*{L}{A}*                  => (report_token (yypos, String.size yytext, Markup.antiquote, "C antiquotation tag", ""); lex());
<COMMENT>"@"                               => (lex());
<COMMENT>"\\"                              => (lex());
<COMMENT>{OPENCART}                        => (report_token (yypos, String.size yytext, Markup.cartouche, "C antiquotation body", "");
                                                antiq_depth := 1; antiq_from_block := true; YYBEGIN ANTIQ; lex());

<LCOMMENT>[^@\\\n]+                        => (lex());
<LCOMMENT>"@"{HWS}*{L}{A}*                 => (report_token (yypos, String.size yytext, Markup.antiquote, "C antiquotation tag", ""); lex());
<LCOMMENT>"@"                              => (lex());
<LCOMMENT>"\\"                             => (lex());
<LCOMMENT>{OPENCART}                       => (report_token (yypos, String.size yytext, Markup.cartouche, "C antiquotation body", "");
                                                antiq_depth := 1; antiq_from_block := false; YYBEGIN ANTIQ; lex());
<LCOMMENT>\n                               => (YYBEGIN INITIAL; lex());

<ANTIQ>[^\\\n]+                            => (lex());
<ANTIQ>\n+                                  => (lex());
<ANTIQ>"\\"                                => (lex());
<ANTIQ>{OPENCART}                          => (antiq_depth := !antiq_depth + 1; lex());
<ANTIQ>{CLOSECART}                         => (antiq_depth := !antiq_depth - 1;
                                                if !antiq_depth = 0
                                                then ((if !antiq_from_block then YYBEGIN COMMENT else YYBEGIN LCOMMENT); lex())
                                                else lex());
\<close>
and yacc_user_declarations\<open>\<close>
yacc_definitions\<open>
%eop EOF
%pure
%noshift EOF

%term
        IDENTIFIER | I_CONSTANT | F_CONSTANT | STRING_LITERAL | FUNC_NAME | SIZEOF |
        INCLUDE | HEADER_NAME | DEFINE | IFDEF | IFNDEF | PP_ELSE | ENDIF |
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
        primary_expression | constant | enumeration_constant | string |
        generic_selection | generic_assoc_list | generic_association | postfix_expression |
        argument_expression_list | unary_expression | unary_operator | cast_expression |
        multiplicative_expression | additive_expression | shift_expression | relational_expression |
        equality_expression | and_expression | exclusive_or_expression | inclusive_or_expression |
        logical_and_expression | logical_or_expression | conditional_expression | assignment_expression |
        assignment_operator | expression | constant_expression | declaration |
        declaration_specifiers | init_declarator_list | init_declarator | storage_class_specifier |
        type_specifier | struct_or_union_specifier | struct_or_union | struct_declaration_list |
        struct_declaration | specifier_qualifier_list | struct_declarator_list | struct_declarator |
        enum_specifier | enumerator_list | enumerator | atomic_type_specifier |
        type_qualifier | function_specifier | alignment_specifier | declarator |
        direct_declarator | pointer | type_qualifier_list | parameter_type_list |
        parameter_list | parameter_declaration | identifier_list | type_name |
        abstract_declarator | direct_abstract_declarator | initializer | initializer_list |
        designation | designator_list | designator | static_assert_declaration |
        statement | labeled_statement | compound_statement | block_item_list |
        block_item | expression_statement | selection_statement | iteration_statement |
        jump_statement | translation_unit | external_declaration | function_definition |
        declaration_list | preproc_directive | external_declaration_list |
        start_rule of unit option
\<close>
yacc_rules\<open>
start_rule: translation_unit (SOME ())
primary_expression: IDENTIFIER    ()
|       constant    ()
|       string    ()
|       LPAREN expression RPAREN    ()
|       generic_selection    ()

constant: I_CONSTANT    ()
|       F_CONSTANT    ()
|       ENUMERATION_CONSTANT    ()

enumeration_constant: IDENTIFIER    ()

string: STRING_LITERAL    ()
|       FUNC_NAME    ()

generic_selection: GENERIC LPAREN assignment_expression COMMA generic_assoc_list RPAREN    ()

generic_assoc_list: generic_association    ()
|       generic_assoc_list COMMA generic_association    ()

generic_association: type_name COLON assignment_expression    ()
|       DEFAULT COLON assignment_expression    ()

postfix_expression: primary_expression    ()
|       postfix_expression LBRACKET expression RBRACKET    ()
|       postfix_expression LPAREN RPAREN    ()
|       postfix_expression LPAREN argument_expression_list RPAREN    ()
|       postfix_expression DOT IDENTIFIER    ()
|       postfix_expression PTR_OP IDENTIFIER    ()
|       postfix_expression INC_OP    ()
|       postfix_expression DEC_OP    ()
|       LPAREN type_name RPAREN LBRACE initializer_list RBRACE    ()
|       LPAREN type_name RPAREN LBRACE initializer_list COMMA RBRACE    ()

argument_expression_list: assignment_expression    ()
|       argument_expression_list COMMA assignment_expression    ()

unary_expression: postfix_expression    ()
|       INC_OP unary_expression    ()
|       DEC_OP unary_expression    ()
|       unary_operator cast_expression    ()
|       SIZEOF unary_expression    ()
|       SIZEOF LPAREN type_name RPAREN    ()
|       ALIGNOF LPAREN type_name RPAREN    ()

unary_operator: AMP    ()
|       STAR    ()
|       PLUS    ()
|       MINUS    ()
|       TILDE    ()
|       BANG    ()

cast_expression: unary_expression    ()
|       LPAREN type_name RPAREN cast_expression    ()

multiplicative_expression: cast_expression    ()
|       multiplicative_expression STAR cast_expression    ()
|       multiplicative_expression SLASH cast_expression    ()
|       multiplicative_expression PERCENT cast_expression    ()

additive_expression: multiplicative_expression    ()
|       additive_expression PLUS multiplicative_expression    ()
|       additive_expression MINUS multiplicative_expression    ()

shift_expression: additive_expression    ()
|       shift_expression LEFT_OP additive_expression    ()
|       shift_expression RIGHT_OP additive_expression    ()

relational_expression: shift_expression    ()
|       relational_expression LT shift_expression    ()
|       relational_expression GT shift_expression    ()
|       relational_expression LE_OP shift_expression    ()
|       relational_expression GE_OP shift_expression    ()

equality_expression: relational_expression    ()
|       equality_expression EQ_OP relational_expression    ()
|       equality_expression NE_OP relational_expression    ()

and_expression: equality_expression    ()
|       and_expression AMP equality_expression    ()

exclusive_or_expression: and_expression    ()
|       exclusive_or_expression CARET and_expression    ()

inclusive_or_expression: exclusive_or_expression    ()
|       inclusive_or_expression PIPE exclusive_or_expression    ()

logical_and_expression: inclusive_or_expression    ()
|       logical_and_expression AND_OP inclusive_or_expression    ()

logical_or_expression: logical_and_expression    ()
|       logical_or_expression OR_OP logical_and_expression    ()

conditional_expression: logical_or_expression    ()
|       logical_or_expression QUESTION expression COLON conditional_expression    ()

assignment_expression: conditional_expression    ()
|       unary_expression assignment_operator assignment_expression    ()

assignment_operator: ASSIGN    ()
|       MUL_ASSIGN    ()
|       DIV_ASSIGN    ()
|       MOD_ASSIGN    ()
|       ADD_ASSIGN    ()
|       SUB_ASSIGN    ()
|       LEFT_ASSIGN    ()
|       RIGHT_ASSIGN    ()
|       AND_ASSIGN    ()
|       XOR_ASSIGN    ()
|       OR_ASSIGN    ()

expression: assignment_expression    ()
|       expression COMMA assignment_expression    ()

constant_expression: conditional_expression    ()

declaration: declaration_specifiers SEMI    ()
|       declaration_specifiers init_declarator_list SEMI    ()
|       static_assert_declaration    ()

declaration_specifiers: storage_class_specifier declaration_specifiers    ()
|       storage_class_specifier    ()
|       type_specifier declaration_specifiers    ()
|       type_specifier    ()
|       type_qualifier declaration_specifiers    ()
|       type_qualifier    ()
|       function_specifier declaration_specifiers    ()
|       function_specifier    ()
|       alignment_specifier declaration_specifiers    ()
|       alignment_specifier    ()

init_declarator_list: init_declarator    ()
|       init_declarator_list COMMA init_declarator    ()

init_declarator: declarator ASSIGN initializer    ()
|       declarator    ()

storage_class_specifier: TYPEDEF    ()
|       EXTERN    ()
|       STATIC    ()
|       THREAD_LOCAL    ()
|       AUTO    ()
|       REGISTER    ()

type_specifier: VOID    ()
|       CHAR    ()
|       SHORT    ()
|       INT    ()
|       LONG    ()
|       FLOAT    ()
|       DOUBLE    ()
|       SIGNED    ()
|       UNSIGNED    ()
|       BOOL    ()
|       COMPLEX    ()
|       IMAGINARY    ()
|       atomic_type_specifier    ()
|       struct_or_union_specifier    ()
|       enum_specifier    ()
|       TYPEDEF_NAME    ()

struct_or_union_specifier: struct_or_union LBRACE struct_declaration_list RBRACE    ()
|       struct_or_union IDENTIFIER LBRACE struct_declaration_list RBRACE    ()
|       struct_or_union IDENTIFIER    ()

struct_or_union: STRUCT    ()
|       UNION    ()

struct_declaration_list: struct_declaration    ()
|       struct_declaration_list struct_declaration    ()

struct_declaration: specifier_qualifier_list SEMI    ()
|       specifier_qualifier_list struct_declarator_list SEMI    ()
|       static_assert_declaration    ()

specifier_qualifier_list: type_specifier specifier_qualifier_list    ()
|       type_specifier    ()
|       type_qualifier specifier_qualifier_list    ()
|       type_qualifier    ()

struct_declarator_list: struct_declarator    ()
|       struct_declarator_list COMMA struct_declarator    ()

struct_declarator: COLON constant_expression    ()
|       declarator COLON constant_expression    ()
|       declarator    ()

enum_specifier: ENUM LBRACE enumerator_list RBRACE    ()
|       ENUM LBRACE enumerator_list COMMA RBRACE    ()
|       ENUM IDENTIFIER LBRACE enumerator_list RBRACE    ()
|       ENUM IDENTIFIER LBRACE enumerator_list COMMA RBRACE    ()
|       ENUM IDENTIFIER    ()

enumerator_list: enumerator    ()
|       enumerator_list COMMA enumerator    ()

enumerator: enumeration_constant ASSIGN constant_expression    ()
|       enumeration_constant    ()

atomic_type_specifier: ATOMIC LPAREN type_name RPAREN    ()

type_qualifier: CONST    ()
|       RESTRICT    ()
|       VOLATILE    ()
|       ATOMIC    ()

function_specifier: INLINE    ()
|       NORETURN    ()

alignment_specifier: ALIGNAS LPAREN type_name RPAREN    ()
|       ALIGNAS LPAREN constant_expression RPAREN    ()

declarator: pointer direct_declarator    ()
|       direct_declarator    ()

direct_declarator: IDENTIFIER    ()
|       LPAREN declarator RPAREN    ()
|       direct_declarator LBRACKET RBRACKET    ()
|       direct_declarator LBRACKET STAR RBRACKET    ()
|       direct_declarator LBRACKET STATIC type_qualifier_list assignment_expression RBRACKET    ()
|       direct_declarator LBRACKET STATIC assignment_expression RBRACKET    ()
|       direct_declarator LBRACKET type_qualifier_list STAR RBRACKET    ()
|       direct_declarator LBRACKET type_qualifier_list STATIC assignment_expression RBRACKET    ()
|       direct_declarator LBRACKET type_qualifier_list assignment_expression RBRACKET    ()
|       direct_declarator LBRACKET type_qualifier_list RBRACKET    ()
|       direct_declarator LBRACKET assignment_expression RBRACKET    ()
|       direct_declarator LPAREN parameter_type_list RPAREN    ()
|       direct_declarator LPAREN RPAREN    ()
|       direct_declarator LPAREN identifier_list RPAREN    ()

pointer: STAR type_qualifier_list pointer    ()
|       STAR type_qualifier_list    ()
|       STAR pointer    ()
|       STAR    ()

type_qualifier_list: type_qualifier    ()
|       type_qualifier_list type_qualifier    ()

parameter_type_list: parameter_list COMMA ELLIPSIS    ()
|       parameter_list    ()

parameter_list: parameter_declaration    ()
|       parameter_list COMMA parameter_declaration    ()

parameter_declaration: declaration_specifiers declarator    ()
|       declaration_specifiers abstract_declarator    ()
|       declaration_specifiers    ()

identifier_list: IDENTIFIER    ()
|       identifier_list COMMA IDENTIFIER    ()

type_name: specifier_qualifier_list abstract_declarator    ()
|       specifier_qualifier_list    ()

abstract_declarator: pointer direct_abstract_declarator    ()
|       pointer    ()
|       direct_abstract_declarator    ()

direct_abstract_declarator: LPAREN abstract_declarator RPAREN    ()
|       LBRACKET RBRACKET    ()
|       LBRACKET STAR RBRACKET    ()
|       LBRACKET STATIC type_qualifier_list assignment_expression RBRACKET    ()
|       LBRACKET STATIC assignment_expression RBRACKET    ()
|       LBRACKET type_qualifier_list STATIC assignment_expression RBRACKET    ()
|       LBRACKET type_qualifier_list assignment_expression RBRACKET    ()
|       LBRACKET type_qualifier_list RBRACKET    ()
|       LBRACKET assignment_expression RBRACKET    ()
|       direct_abstract_declarator LBRACKET RBRACKET    ()
|       direct_abstract_declarator LBRACKET STAR RBRACKET    ()
|       direct_abstract_declarator LBRACKET STATIC type_qualifier_list assignment_expression RBRACKET    ()
|       direct_abstract_declarator LBRACKET STATIC assignment_expression RBRACKET    ()
|       direct_abstract_declarator LBRACKET type_qualifier_list assignment_expression RBRACKET    ()
|       direct_abstract_declarator LBRACKET type_qualifier_list STATIC assignment_expression RBRACKET    ()
|       direct_abstract_declarator LBRACKET type_qualifier_list RBRACKET    ()
|       direct_abstract_declarator LBRACKET assignment_expression RBRACKET    ()
|       LPAREN RPAREN    ()
|       LPAREN parameter_type_list RPAREN    ()
|       direct_abstract_declarator LPAREN RPAREN    ()
|       direct_abstract_declarator LPAREN parameter_type_list RPAREN    ()

initializer: LBRACE initializer_list RBRACE    ()
|       LBRACE initializer_list COMMA RBRACE    ()
|       assignment_expression    ()

initializer_list: designation initializer    ()
|       initializer    ()
|       initializer_list COMMA designation initializer    ()
|       initializer_list COMMA initializer    ()

designation: designator_list ASSIGN    ()

designator_list: designator    ()
|       designator_list designator    ()

designator: LBRACKET constant_expression RBRACKET    ()
|       DOT IDENTIFIER    ()

static_assert_declaration: STATIC_ASSERT LPAREN constant_expression COMMA STRING_LITERAL RPAREN SEMI    ()

statement: labeled_statement    ()
|       compound_statement    ()
|       expression_statement    ()
|       selection_statement    ()
|       iteration_statement    ()
|       jump_statement    ()

labeled_statement: IDENTIFIER COLON statement    ()
|       CASE constant_expression COLON statement    ()
|       DEFAULT COLON statement    ()

compound_statement: LBRACE RBRACE    ()
|       LBRACE block_item_list RBRACE    ()

block_item_list: block_item    ()
|       block_item_list block_item    ()

block_item: declaration    ()
|       statement    ()

expression_statement: SEMI    ()
|       expression SEMI    ()

selection_statement: IF LPAREN expression RPAREN statement ELSE statement    ()
|       IF LPAREN expression RPAREN statement    ()
|       SWITCH LPAREN expression RPAREN statement    ()

iteration_statement: WHILE LPAREN expression RPAREN statement    ()
|       DO statement WHILE LPAREN expression RPAREN SEMI    ()
|       FOR LPAREN expression_statement expression_statement RPAREN statement    ()
|       FOR LPAREN expression_statement expression_statement expression RPAREN statement    ()
|       FOR LPAREN declaration expression_statement RPAREN statement    ()
|       FOR LPAREN declaration expression_statement expression RPAREN statement    ()

jump_statement: GOTO IDENTIFIER SEMI    ()
|       CONTINUE SEMI    ()
|       BREAK SEMI    ()
|       RETURN SEMI    ()
|       RETURN expression SEMI    ()

translation_unit: external_declaration    ()
|       translation_unit external_declaration    ()

external_declaration: function_definition    ()
|       declaration    ()
|       preproc_directive    ()

preproc_directive: INCLUDE HEADER_NAME    ()
|       DEFINE IDENTIFIER ASSIGN constant_expression    ()
|       DEFINE IDENTIFIER LPAREN RPAREN ASSIGN constant_expression    ()
|       DEFINE IDENTIFIER LPAREN identifier_list RPAREN ASSIGN constant_expression    ()
|       IFDEF IDENTIFIER external_declaration_list ENDIF    ()
|       IFDEF IDENTIFIER external_declaration_list PP_ELSE external_declaration_list ENDIF    ()
|       IFNDEF IDENTIFIER external_declaration_list ENDIF    ()
|       IFNDEF IDENTIFIER external_declaration_list PP_ELSE external_declaration_list ENDIF    ()

external_declaration_list:    ()
|       external_declaration_list external_declaration    ()

function_definition: declaration_specifiers declarator declaration_list compound_statement    ()
|       declaration_specifiers declarator compound_statement    ()

declaration_list: declaration    ()
|       declaration_list declaration    ()
\<close>

subsection\<open>Defining a simple Isar-toplevel command to test the Parser\<close>
ML\<open>
fun run_c11 source thy =
    let
      val ctxt = Proof_Context.init_global thy
      val _ = C11.parse_source ctxt source
    in thy end

val _ = Outer_Syntax.command @{command_keyword "c11"}
        "Syntax check a C11 translation unit"
        (Parse.input Parse.cartouche >> (fn source => Toplevel.theory (run_c11 source)))

(* Isabelle_C's counterpart is "C_file \<open>path\<close>". Resources.parse_file/
   Token.file_source/Resources.provide_file are the same Isabelle/Pure
   building blocks the built-in ML_file/SML_file commands use (see
   Pure/ML/ml_file.ML): the path is resolved relative to this theory's
   master directory, the resulting Input.source carries correct file
   positions (so parse errors point at the actual file/line/column, not
   at the command invocation), and the file is registered as a dependency
   so `isabelle build` re-checks this theory when it changes. Note the
   keyword kind below: "c11_file" is declared "thy_load", not "diag" like
   "c11"/"c11_reject" - Resources.parse_file's file-dependency resolution
   is only actually wired up by Isabelle's command-span scanner for
   thy_load-kind commands (matching how ML_file/SML_file/external_file
   are themselves declared in Pure.thy); under "diag" the file is never
   read, silently. *)
fun run_c11_file get_file thy =
    let
      val file = get_file thy
      val source = Token.file_source file
      val ctxt = Proof_Context.init_global thy
      val _ = C11.parse_source ctxt source
    in Resources.provide_file file thy end

val _ = Outer_Syntax.command @{command_keyword "c11_file"}
        "Read and syntax-check an external C11 source file"
        (Resources.parse_file >> (fn get_file => Toplevel.theory (run_c11_file get_file)))

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

   Rather than patch YaccLib.thy (out of scope here), run_c11_reject below
   re-implements parse_source's control flow directly against the public
   C11Lex/C11Parser/C11LrVals structures and the exposed
   Isabelle_lex_yacc.set/get_pos, substituting a private, silent error
   callback that raises a *locally declared* exception - so it is caught
   by construction, with no cross-environment identity mismatch possible,
   and no spurious error markup is left on rejected (expected-to-fail)
   input. *)
exception Rejected of string
fun quiet_error (s: string, _: Position.T, _: Position.T) = raise Rejected s

fun parse_source_quiet ctxt source =
    let
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

fun run_c11_reject source thy =
    let
      val ctxt = Proof_Context.init_global thy
      val rejected =
        (parse_source_quiet ctxt source; false)
          handle Rejected _ => true
      val _ =
        if rejected
        then writeln "OK: malformed input was correctly rejected by the parser."
        else error "Malformed-input test FAILED: the parser unexpectedly accepted this input."
    in thy end

val _ = Outer_Syntax.command @{command_keyword "c11_reject"}
        "Check that a C11 fragment is correctly rejected (error-recovery / malformed-input tests)"
        (Parse.input Parse.cartouche >> (fn source => Toplevel.theory (run_c11_reject source)))
\<close>

section\<open>Testing the generated C11 Parser with Syntax Highlighting\<close>

subsection\<open>A more Comprehensive Program Text\<close>

c11\<open>
#include <stdio.h>
#include "local_header.h"

#define MAX_SIZE = 100
#define SQUARE(x) = x * x

#ifdef MAX_SIZE
int buffer[MAX_SIZE];
#else
int buffer[10];
#endif

#ifndef NDEBUG
int debug_flag = 1;
#endif

int max(int a, int b) {
  if (a > b)
    return a;
  else
    return b;
}

int main(void) {
  int x = max(3, 42);
  return x;
}
\<close>

subsection\<open>\<open>c11_file\<close> on real-world C11 sources (\<^verbatim>\<open>parser_menhir\<close>)\<close>
text\<open>
  \<^verbatim>\<open>examples/\<close> vendors three files, unmodified, from the \<^verbatim>\<open>parser_menhir\<close>
  C11 conformance test suite (via its copy in the Isabelle_C AFP entry, see
  \<^verbatim>\<open>examples/README.md\<close> for provenance and license), the same files
  Isabelle_C's own \<open>C0.thy\<close> exercises its lexer/parser against. None of them
  use this fragment's unsupported constructs (real \<open>#define\<close>, \<open>#if\<close>/\<open>#elif\<close>,
  backslash-newline), so all three are expected to succeed here too - genuine,
  non-trivial C11 (compound literals, deeply nested declarators, anonymous
  struct/union members, \<open>[*]\<close> parameter arrays, the dangling-\<open>else\<close> case,
  \<open>\<dots>\<close>), not code written for this theory.
\<close>
c11_file \<open>examples/expressions.c\<close>
c11_file \<open>examples/dangling_else.c\<close>
c11_file \<open>examples/declarators.c\<close>


subsection\<open>Tests for Arithmetic, Bitwise, Relational and Logical Operators\<close>
text\<open>
  The following blocks exercise the expression language (\<open>expression\<close> down to
  \<open>primary_expression\<close>) more broadly, roughly one grammar layer at a time.
\<close>

c11\<open>
int test_arith(void) {
  int a = 10, b = 3, c;
  c = a + b - a * b / b % a;
  c = (a << 1) >> 1;
  c = (a & b) | (a ^ b);
  c = ~a & !b;
  c = a < b || a > b;
  c = a <= b && a >= b;
  c = a == b;
  c = a != b;
  return c;
}
\<close>

subsection\<open>Tests on Assignment operators, Increment/decrement, Comma and ternary Operators\<close>
c11\<open>
int test_assign(void) {
  int a = 1, b = 2, r;
  a += 1; a -= 1; a *= 2; a /= 2; a %= 3;
  a <<= 1; a >>= 1; a &= 1; a |= 2; a ^= 1;
  r = a++;
  r = ++a;
  r = b--;
  r = --b;
  r = (a = b);
  r = a > b ? a : b;
  r = (a += 1, b += 1, a + b);
  return r;
}
\<close>

subsection\<open>Pointers, arrays, structs, casts, sizeof/alignof, and generic selection\<close>
c11\<open>
struct point { int x; int y; };

int test_misc(int n, ...) {
  int arr[5] = {1, 2, 3, 4, 5};
  int *p = &arr[0];
  struct point pt = { .x = 1, .y = 2 };
  struct point *pp = &pt;
  int s1 = sizeof(int);
  int s2 = sizeof arr;
  int s3 = _Alignof(int);
  int c1 = (int) 3.14;
  double c2 = (double) n;
  int g = _Generic(n, int: 1, default: 0);
  int cl = (int[]){1, 2, 3}[0];
  return *p + arr[n] + pt.x + pp->y + s1 + s2 + s3 + c1 + g + cl;
}
\<close>

text\<open>
  The following blocks exercise statement-level constructs (\<open>statement\<close> and its
  alternatives): iteration, selection/switch, and jump statements including \<open>goto\<close>.
\<close>

subsection\<open>Iteration statements: while, do-while, and all four for-loop forms\<close>
c11\<open>
int test_loops(void) {
  int i = 0;
  int sum = 0;

  while (i < 10) {
    sum += i;
    i++;
  }

  i = 0;
  do {
    sum += i;
    i++;
  } while (i < 5);

  for (i = 0; i < 10; i++) {
    if (i == 5)
      continue;
    sum += i;
  }

  for (i = 0; i < 10; )
    i++;

  for (int j = 0; j < 10; )
    j++;

  for (int j = 0, k = 10; j < k; j++, k--) {
    sum += j - k;
  }

  return sum;
}
\<close>

subsection\<open>Switch statement, fallthrough, labeled statements, and goto\<close>
c11\<open>
int test_switch_goto(int x) {
  int result = 0;

  switch (x) {
    case 0:
      result = 100;
      break;
    case 1:
    case 2:
      result = 200;
      break;
    default:
      result = -1;
      break;
  }

  int i = 0;
  loop_start:
  if (i < 5) {
    result += i;
    i++;
    goto loop_start;
  }

  switch (x) {
    case 3: {
      int y = x * 2;
      result += y;
    }
    default:
      result += 1;
  }

  return result;
}
\<close>



section\<open>Error-recovery / Malformed-input Tests\<close>

text\<open>Each of the following fragments is syntactically invalid, and \<open>c11_reject\<close>
  (defined above) fails the theory build if the parser unexpectedly \<^emph>\<open>accepts\<close>
  one of them, rather than reporting the expected parse error.\<close>

subsection\<open>Unbalanced braces and parentheses\<close>
c11_reject\<open>
int main(void) { return 0;
\<close>
c11_reject\<open>
int max(int a, int b { return a; }
\<close>
c11_reject\<open>
int main(void) { return 0; } }
\<close>

subsection\<open>Missing Separators and dangling Operators\<close>
c11_reject\<open>
int x = 5 int y = 6;
\<close>
c11_reject\<open>
int x = 1 + ;
\<close>
c11_reject\<open>
int y = ;
\<close>

subsection\<open>Keywords vs. Identifiers\<close>
text\<open>Keywords cannot be used as identifiers.\<close>
c11_reject\<open>
int if = 5;
\<close>

subsection\<open>C11 - Specifics\<close>
text\<open>Unlike pre-C99 Kernighan\<open>&\<close>Ritchie C, C11 has no implicit \<open>int\<close>:
     a function definition needs declaration specifiers.\<close>
c11_reject\<open>
main(void) { return 0; }
\<close>


subsection\<open>The Preprocessor Fragment\<close>
text\<open>The preprocessor fragment: a missing header name, and an unterminated \<open>#ifdef\<close>.\<close>
c11_reject\<open>
#include
int x;
\<close>

c11_reject\<open>
#ifdef DEBUG
int x;
\<close>

section\<open>Antiquotation-carrying Comments (cf. Isabelle_C's \<^verbatim>\<open>C1.thy\<close>)\<close>

text\<open>
  A line comment carrying a tag and a properly-nested cartouche, adapted from
  Isabelle_C's own \<open>#include\<close> example (\<^verbatim>\<open>C11-FrontEnd/examples/C1.thy\<close>). The
  lexer reports \<open>@setup\<close> and the cartouche as PIDE markup; nothing is executed.
\<close>
c11\<open>
int b;
//@ setup \<open>Include.append "tmp" [\<open>b\<close>]\<close>
int a = b;
\<close>

text\<open>A block-comment variant, with a doubly-nested cartouche.\<close>
c11\<open>
/*@ setup \<open>Include.append "tmp" [\<open>b\<close>, \<open>c\<close>]\<close> */
int a = 0;
\<close>

text\<open>
  A Frama-C/ACSL-style annotation comment (Isabelle_C's other supported style):
  bare keywords followed by plain strings, no \<open>@\<close>-tag or cartouche. The lexer
  does not specially recognize \<open>requires\<close>/\<open>ensures\<close> here - it is simply
  comment text - but must not choke on it either.
\<close>
c11\<open>
/*@ requires "n >= 0"
  @ ensures "result >= 0"
 */
int abs(int n) {
  if (n < 0) return -n;
  return n;
}
\<close>

section\<open>Comment Nesting (cf. Isabelle_C's \<^verbatim>\<open>C0.thy\<close>)\<close>

text\<open>
  Adapted from Isabelle_C's own comment-nesting example, which follows
  \<^url>\<open>https://gcc.gnu.org/onlinedocs/cpp/Initial-processing.html\<close>: a \<open>/* */\<close>
  comment does \<^emph>\<open>not\<close> nest, so the first \<open>*/\<close> closes it - the code after is
  live, not still-commented-out. \<open>c11\<close> succeeding on this is itself the test.
\<close>
c11\<open>
/* inside /* inside */ int a = 1;
// inside // inside until end of line
int b = 2;
/* inside
  // inside
inside
*/ int c = 3;
// inside /* inside until end of line
int d = 4;
\<close>

section\<open>What Falls Outside This Fragment (cf. Isabelle_C's \<^verbatim>\<open>C0.thy\<close>)\<close>

text\<open>
  Isabelle_C's directive/macro stress tests use the real C preprocessor's
  \<open>#define\<close> (juxtaposed replacement-list, no \<open>=\<close>) and general \<open>#if\<close>/\<open>#elif\<close>,
  neither of which this simplified fragment implements (this theory's own
  \<open>#define name = expr\<close> and \<open>#ifdef\<close>/\<open>#ifndef\<close> only). \<open>c11_reject\<close> documents
  the boundary instead of silently skipping it.
\<close>
c11_reject\<open>
#define a zz
\<close>
c11_reject\<open>
#ifdef a
#elif
#else
#if
#endif
#endif
\<close>

text\<open>
  Likewise, backslash-newline splicing (ISO C11 translation phase 2, which
  would let a keyword be split across lines by ending each fragment with a
  backslash, e.g. \<open>i\<close> then a line break then \<open>nt\<close> for \<open>int\<close>) is not
  implemented: it would require preprocessing the source text before lexing,
  with its own position-mapping machinery, which is out of scope here. Below,
  the split keyword is lexed as the two identifiers \<open>i\<close> and \<open>nt\<close> rather
  than as \<open>int\<close>, so the fragment is correctly rejected.
\<close>
c11_reject\<open>
i\
nt a = 1;
\<close>

end
