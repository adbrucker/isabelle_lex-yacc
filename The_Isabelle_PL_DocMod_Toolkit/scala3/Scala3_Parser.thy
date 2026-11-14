(******************************************************************************
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

theory Scala3_Parser
  imports "../../Isabelle_Lex-Yacc/LexYacc" "Scala3_Ast"
begin

section\<open>Lexer and Parser for Scala 3\<close>

text\<open>
  This theory formalizes the Scala 3 grammar of the \<^emph>\<open>Scala 3 Syntax Summary\<close>
  (\<^verbatim>\<open>docs.scala-lang.org/scala3/reference/syntax.html\<close>) as an ml-lex/ml-yacc
  lexer/parser pair, built, like \<^verbatim>\<open>C11_Parser.thy\<close> and \<^verbatim>\<open>Occam2_Parser.thy\<close>, with
  this repository's own \<^verbatim>\<open>ml_lex_yacc [state]\<close> command (a re-entrant parser:
  every parse has its own state object).

  \<^bold>\<open>What is covered, and why.\<close> The aim is a front-end that is \<^emph>\<open>useful\<close> for real
  Scala sources, in particular for the Scala sources of Isabelle itself (380
  files, 93\,000 lines in \<^verbatim>\<open>~~/src\<close>), which Isabelle could manage in its own
  document model. A survey of those sources decides the scope:

  \<^item> They are Scala 3 sources written in the \<^emph>\<open>brace\<close> style: no significant
    indentation, no \<open>then\<close>/\<open>do\<close>, no end markers. Blocks are delimited by braces,
    and statements are separated by newlines or semicolons.
  \<^item> The Scala 3 features they use are few: \<open>enum\<close> (27, with \<open>case a, b\<close> and \<open>case
    A(x) extends E\<close>), \<open>extension (x: T) { ... }\<close> (4), \<open>given\<close> (2) and \<open>(using
    ...)\<close> (1). Not used at all: \<open>opaque\<close>, \<open>transparent\<close>, \<open>infix\<close> modifiers,
    \<open>derives\<close>, context functions, type lambdas, match types, macros and quotes,
    end markers, optional braces.
  \<^item> Of the \<^emph>\<open>soft keywords\<close> only \<open>extension\<close> and \<open>using\<close> matter; \<open>end\<close>, on the
    other hand, is an ordinary identifier all over the place (\<open>end: Int\<close>,
    \<open>end.shortcut\<close>), so it must never be treated as a keyword. The grammar below
    accepts \<open>as\<close>, \<open>extension\<close>, \<open>infix\<close>, \<open>inline\<close>, \<open>opaque\<close>, \<open>open\<close>,
    \<open>transparent\<close> and \<open>using\<close> both as identifiers and in their keyword role (the
    lexer emits distinct tokens, the grammar's \<open>name\<close> accepts them all, and the
    LALR(1) lookahead decides); \<open>end\<close> and \<open>derives\<close> are plain identifiers.
    Optional braces (indentation-delimited blocks) are therefore \<^emph>\<open>not\<close> covered;
    they would be added with the same kind of layout stage as for occam 2
    (\<open>Occam2_Parser.thy\<close>), see the Limitations in the manual.

  \<^bold>\<open>Statement separators.\<close> Scala has no statement terminator token in the lexical
  grammar: a newline \<^emph>\<open>is\<close> a separator when the token before it can end a
  statement, the token after it can begin one, and the newline is not inside
  parentheses or brackets (newlines are enabled inside braces, and disabled
  again between \<open>case\<close> and its \<open>=>\<close>). The lexer cannot produce this on its own
  (it depends on the nesting), so, as for occam, it only \<^emph>\<open>records\<close> facts per
  token (\<open>Scala3_Layout\<close>: the number of newlines before the token, its kind) and
  a stream wrapper (\<open>Scala3_Parse.layout_stream\<close>, at the end of this theory)
  inserts a \<open>NEWLINE\<close> token where the rules above say so, keeping a stack of the
  open brackets. Two refinements of Scala 3 are implemented: a line starting
  with an infix operator followed by an operand on the same line continues the
  previous line (a \<^emph>\<open>leading infix operator\<close>), and a single newline before \<open>{\<close> is
  ignored (the Scala 2 rule that lets \<open>f\<close> and \<open>{ ... }\<close> on separate lines form
  an application).

  \<^bold>\<open>Operators.\<close> Scala has no operator declarations: the precedence of an infix
  operator is given by its first character, its associativity by its last (a
  colon makes it right associative). The lexer classifies each operator token
  accordingly (\<open>OPBAR\<close>, \<open>OPCARET\<close>, \<open>OPAMP\<close>, \<open>OPEQ\<close>, \<open>OPLT\<close>, \<open>OPCOLON\<close>, \<open>OPADD\<close>,
  \<open>OPMUL\<close>, \<open>OPOTHER\<close>; the alphanumeric operators are \<open>IDENT\<close>), and the yacc
  grammar declares the nine precedence levels. Simplification: every operator
  ending in a colon (\<open>::\<close>, \<open>+:\<close>, \<open>/:\<close>) is right associative \<^emph>\<open>at the level of
  \<open>::\<close>\<close>, not at its own first-character level.

  \<^bold>\<open>Comments\<close> nest in Scala, and may contain antiquotations, as in C11 and occam
  2: \<open>@tag[navi](level) \<open>body\<close>\<close>. As the Scaladoc tags (\<open>@param\<close>, \<open>@return\<close>, ...)
  look exactly like bodyless antiquotation tags, a \<^emph>\<open>bodyless\<close> tag is recognised
  only directly after the comment opener (\<open>//@ tag\<close>, \<open>/*@ tag */\<close>); a tag \<^emph>\<open>with\<close>
  a cartouche or string body is recognised anywhere in a comment.

  \<^bold>\<open>Strings.\<close> Plain, multi-line (\<open>"""\<close>) and interpolated strings (\<open>s"..."\<close>,
  \<open>f"""..."""\<close>) are single tokens. The embedded expressions \<open>${...}\<close> of an
  interpolated string are skipped over (balanced, nested strings and characters
  included) but not parsed; the token carries the raw text.
\<close>
ML\<open>
(* Everything the lexer and the grammar actions need to remember during one
   parse lives in one state object, created per parse ("init") and handed to
   the lexer (ML-Lex %arg) and the parser (ML-Yacc %arg) by "ml_lex_yacc
   [state]" - nothing is shared between parses.
     base        - the library's own part: source, context, position table
     pending     - comments lexed since the previous real token
     attached    - the comments that have been attached to a token position
     layout      - the layout recorder, see "Scala3_Layout"
     antiq_*     - the antiquotation scanner (see the lexer): nesting depth of
                   the cartouche being skipped, which comment state to return
                   to, the most recent tag, the body text so far and its start
                   position
     comment_depth, bodyless_ok
                 - block comments nest; whether a bodyless antiquotation tag
                   is allowed in the current comment (see the introduction)
     str_*, iexpr_depth
                 - the scanner of multi-line and interpolated strings
     lex_error   - the first lexical error (unterminated comment, string or
                   antiquotation): the lexer cannot raise it itself, as the
                   parse's error callback decides how an error is reported
                   (loudly, or silently for the "_reject" commands), so it is
                   recorded here and reported by "Scala3_Parse.parse" when the
                   parse is over *)
structure Scala3_State = struct
  type comments = Position.T Scala3_Ast.comment list
  type layout = {nl: int, start: int, stop: int, kind: string}
  val layout_init : layout = {nl = 0, start = 0, stop = 0, kind = ""}

  type T = {base : Lex_yacc_state.T,
            pending : comments Unsynchronized.ref,
            attached : (Position.T * comments) list Unsynchronized.ref,
            layout : layout Unsynchronized.ref,
            antiq_depth : int Unsynchronized.ref,
            antiq_from_block : bool Unsynchronized.ref,
            antiq_tag : (string * Scala3_Ast.navi list * int * Position.T)
              Unsynchronized.ref,
            antiq_buf : string list Unsynchronized.ref,
            antiq_start : Position.T Unsynchronized.ref,
            comment_depth : int Unsynchronized.ref,
            bodyless_ok : bool Unsynchronized.ref,
            comment_start : int Unsynchronized.ref,
            str_prefix : string Unsynchronized.ref,
            str_buf : string list Unsynchronized.ref,
            str_start : int Unsynchronized.ref,
            str_ml : bool Unsynchronized.ref,
            iexpr_depth : int Unsynchronized.ref,
            lex_error : (string * Position.T) option Unsynchronized.ref}

  fun init ctxt source : T =
    {base = Lex_yacc_state.init ctxt source,
     pending = Unsynchronized.ref [],
     attached = Unsynchronized.ref [],
     layout = Unsynchronized.ref layout_init,
     antiq_depth = Unsynchronized.ref 0,
     antiq_from_block = Unsynchronized.ref true,
     antiq_tag = Unsynchronized.ref ("", [], 0, Position.none),
     antiq_buf = Unsynchronized.ref [],
     antiq_start = Unsynchronized.ref Position.none,
     comment_depth = Unsynchronized.ref 0,
     bodyless_ok = Unsynchronized.ref false,
     comment_start = Unsynchronized.ref 0,
     str_prefix = Unsynchronized.ref "",
     str_buf = Unsynchronized.ref [],
     str_start = Unsynchronized.ref 0,
     str_ml = Unsynchronized.ref false,
     iexpr_depth = Unsynchronized.ref 0,
     lex_error = Unsynchronized.ref NONE}
end

(* The comments/antiquotations collected while lexing, attached to whichever
   real token follows (as in C11_Comments / Occam2_Comments). *)
structure Scala3_Comments = struct
  fun push (st : Scala3_State.T) c = #pending st := !(#pending st) @ [c]

  fun push_raw st (text, pos) =
    if List.all Char.isSpace (String.explode text) then ()
    else push st (Scala3_Ast.Raw_txt [(text, pos)])

  fun push_antiquotation st tag navi level cartouche =
    push st (Scala3_Ast.Antiquotation (tag, navi, level, cartouche))

  fun attach_pending (st : Scala3_State.T) (p : Position.T) =
    (case !(#pending st) of
       [] => ()
     | cs => (#pending st := []; #attached st := (p, cs) :: !(#attached st)))

  (* Non-destructive on purpose, for the reason given at "C11_Comments.claim".
     *)
  fun claim (st : Scala3_State.T) (p : Position.T) : Position.T
    Scala3_Ast.comment list =
    (case AList.lookup (op =) (!(#attached st)) p of NONE => [] | SOME cs => cs)

  fun mk_nodeInfo st (claimed_at : Position.T)
    (report_pos : Position.T) : Position.T Scala3_Ast.nodeInfo =
    (case claim st claimed_at of
       [] => Scala3_Ast.OnlyPos report_pos
     | cs => Scala3_Ast.NodeInfo (cs, report_pos))
end

(* Layout bookkeeping shared between the lexer actions and the stream wrapper.
   The lexer only ever records facts here; it never emits a layout token
   itself:
     nl     - the number of newlines lexed since the previous real token (also
              those inside comments, as in scalac)
     start/stop - character offsets of the newest real token
     kind   - the newest token's kind: its name in the grammar ("IDENT",
              "LBRACE", ...) *)
structure Scala3_Layout = struct
  fun get (st : Scala3_State.T) = !(#layout st)

  fun newline (st : Scala3_State.T) =
    let val {nl, start, stop, kind} = get st
    in #layout st := {nl = nl + 1, start = start, stop = stop, kind = kind} end

  fun token (st : Scala3_State.T) (start, stop, kind) =
    let val {nl, ...} = get st
    in #layout st := {nl = nl, start = start, stop = stop, kind = kind} end

  fun clear_newlines (st : Scala3_State.T) =
    let val {start, stop, kind, ...} = get st
    in #layout st := {nl = 0, start = start, stop = stop, kind = kind} end
end
\<close>
SML_import \<open>structure Scala3_Ast = struct open Scala3_Ast end\<close>
SML_import \<open>structure Scala3_State = struct open Scala3_State end\<close>
SML_import \<open>structure Scala3_Comments = struct open Scala3_Comments end\<close>
SML_import \<open>structure Scala3_Layout = struct open Scala3_Layout end\<close>

ml_lex_yacc [verbose, state] "Scala3" where

lex_user_declarations\<open>
(* The lexer's and the parser's argument is the per-parse state of
   "Scala3_State" (the lexer rules and the grammar actions call it "st"); "init"
   creates it, "base" is its part the library functions work on. *)
type arg = Scala3_State.T
fun init ctxt source : arg = Scala3_State.init ctxt source
fun base (st : arg) : Lex_yacc_state.T = #base st

fun gp (st : arg) yypos = Lex_yacc_state.get_pos (base st) yypos
fun report (st : arg) x = Lex_yacc_state.report_token (base st) x

fun antiq_depth (st : arg) = #antiq_depth st
fun antiq_from_block (st : arg) = #antiq_from_block st
fun antiq_tag (st : arg) = #antiq_tag st
fun antiq_buf (st : arg) = #antiq_buf st
fun antiq_start (st : arg) = #antiq_start st
fun comment_depth (st : arg) = #comment_depth st
fun bodyless_ok (st : arg) = #bodyless_ok st
fun comment_start (st : arg) = #comment_start st

(* Every real token goes through one of the two constructors below, which,
   before reporting the token's markup, (1) let the comments gathered since the
   previous token attach themselves to this one, and (2) tell the layout
   recorder where this token starts and stops and what kind of token it is (the
   stream wrapper decides from that where a statement separator goes).
   Value-carrying tokens get their true start/end span as position. *)
fun stok st kind markup (yypos, yytext, cons) =
    (Scala3_Comments.attach_pending st (gp st yypos);
     Scala3_Layout.token st (yypos, yypos + String.size yytext, kind);
     tok (base st) (yypos, yytext, markup, kind, "", cons))

fun stok_val st kind markup (yypos, yytext, cons, value) =
    let
      val _ = Scala3_Comments.attach_pending st (gp st yypos)
      val _ = Scala3_Layout.token st (yypos, yypos + String.size yytext, kind)
      val p = gp st yypos
      val p' = gp st (yypos + String.size yytext)
      val _ = report st (yypos, String.size yytext, markup, kind, "")
    in cons (value, p, p') end

(* An identifier-like word: a hard keyword, a soft keyword (a token of its own,
   which the grammar also accepts wherever an identifier is accepted), or an
   identifier. "end" and "derives" are not keywords here (see the introduction
   of Scala3_Parser.thy). *)
fun word_tok st (yypos, yytext) =
    let
      fun kw kind cons = stok st kind Markup.keyword1 (yypos, yytext, cons)
      fun sw kind cons =
        stok_val st kind Markup.free (yypos, yytext, cons, yytext)
    in
      case yytext of
        "" => raise Fail "empty word"
    | "abstract" => kw "ABSTRACT" Tokens.ABSTRACT
    | "case" => kw "CASE" Tokens.CASE
    | "catch" => kw "CATCH" Tokens.CATCH
    | "class" => kw "CLASS" Tokens.CLASS
    | "def" => kw "DEF" Tokens.DEF
    | "do" => kw "DO" Tokens.DO
    | "else" => kw "ELSE" Tokens.ELSE
    | "enum" => kw "ENUM" Tokens.ENUM
    | "export" => kw "EXPORT" Tokens.EXPORT
    | "extends" => kw "EXTENDS" Tokens.EXTENDS
    | "false" => kw "FALSE" Tokens.FALSE
    | "final" => kw "FINAL" Tokens.FINAL
    | "finally" => kw "FINALLY" Tokens.FINALLY
    | "for" => kw "FOR" Tokens.FOR
    | "given" => kw "GIVEN" Tokens.GIVEN
    | "if" => kw "IF" Tokens.IF
    | "implicit" => kw "IMPLICIT" Tokens.IMPLICIT
    | "import" => kw "IMPORT" Tokens.IMPORT
    | "lazy" => kw "LAZY" Tokens.LAZY
    | "match" => kw "MATCH" Tokens.MATCH
    | "new" => kw "NEW" Tokens.NEW
    | "null" => kw "NULL" Tokens.NULL
    | "object" => kw "OBJECT" Tokens.OBJECT
    | "override" => kw "OVERRIDE" Tokens.OVERRIDE
    | "package" => kw "PACKAGE" Tokens.PACKAGE
    | "private" => kw "PRIVATE" Tokens.PRIVATE
    | "protected" => kw "PROTECTED" Tokens.PROTECTED
    | "return" => kw "RETURN" Tokens.RETURN
    | "sealed" => kw "SEALED" Tokens.SEALED
    | "super" => kw "SUPER" Tokens.SUPER
    | "then" => kw "THEN" Tokens.THEN
    | "this" => kw "THIS" Tokens.THIS
    | "throw" => kw "THROW" Tokens.THROW
    | "trait" => kw "TRAIT" Tokens.TRAIT
    | "true" => kw "TRUE" Tokens.TRUE
    | "try" => kw "TRY" Tokens.TRY
    | "type" => kw "TYPE" Tokens.TYPE
    | "val" => kw "VAL" Tokens.VAL
    | "var" => kw "VAR" Tokens.VAR
    | "while" => kw "WHILE" Tokens.WHILE
    | "with" => kw "WITH" Tokens.WITH
    | "yield" => kw "YIELD" Tokens.YIELD
    | "as" => sw "AS" Tokens.AS
    | "extension" => sw "EXTENSION" Tokens.EXTENSION
    | "infix" => sw "INFIX" Tokens.INFIX
    | "inline" => sw "INLINE" Tokens.INLINE
    | "opaque" => sw "OPAQUE" Tokens.OPAQUE
    | "open" => sw "OPEN" Tokens.OPEN
    | "transparent" => sw "TRANSPARENT" Tokens.TRANSPARENT
    | "using" => sw "USING" Tokens.USING
      | _ => stok_val st "IDENT" Markup.free
          (yypos, yytext, Tokens.IDENT, yytext)
    end

(* An operator: a reserved symbol, or classified by its first character
   (precedence) and its last (a colon: right associative), as the language
   definition prescribes. *)
fun op_tok st (yypos, yytext) =
    let
      fun u kind cons = stok st kind Markup.operator (yypos, yytext, cons)
      fun v kind cons =
        stok_val st kind Markup.operator (yypos, yytext, cons, yytext)
      val c0 = String.sub (yytext, 0)
      val last = String.sub (yytext, String.size yytext - 1)
    in
      case yytext of
        ":" => u "COLON" Tokens.COLON
      | "=" => u "EQUALS" Tokens.EQUALS
      | "<-" => u "LARROW" Tokens.LARROW
      | "=>" => u "ARROW" Tokens.ARROW
      | "?=>" => u "CTXARROW" Tokens.CTXARROW
      | "=>>" => u "TYARROW" Tokens.TYARROW
      | "<:" => u "SUBTYPE" Tokens.SUBTYPE
      | ">:" => u "SUPERTYPE" Tokens.SUPERTYPE
      | "#" => u "HASH" Tokens.HASH
      | "@" => u "AT" Tokens.AT
      | "+" => v "PLUS" Tokens.PLUS
      | "-" => v "MINUS" Tokens.MINUS
      | "*" => v "STAR" Tokens.STAR
      | "|" => v "BAR" Tokens.BAR
      | "!" => v "BANG" Tokens.BANG
      | "~" => v "TILDE" Tokens.TILDE
      | "?" => v "QMARK" Tokens.QMARK
      | "???" => v "IDENT" Tokens.IDENT
      | _ =>
          if last = #":" then v "OPCOLON" Tokens.OPCOLON
          else
            (case c0 of
               #"|" => v "OPBAR" Tokens.OPBAR
             | #"^" => v "OPCARET" Tokens.OPCARET
             | #"&" => v "OPAMP" Tokens.OPAMP
             | #"=" => v "OPEQ" Tokens.OPEQ
             | #"!" => v "OPEQ" Tokens.OPEQ
             | #"<" => v "OPLT" Tokens.OPLT
             | #">" => v "OPLT" Tokens.OPLT
             | #":" => v "OPCOLONL" Tokens.OPCOLONL
             | #"+" => v "OPADD" Tokens.OPADD
             | #"-" => v "OPADD" Tokens.OPADD
             | #"*" => v "OPMUL" Tokens.OPMUL
             | #"/" => v "OPMUL" Tokens.OPMUL
             | #"%" => v "OPMUL" Tokens.OPMUL
             | _ => v "OPOTHER" Tokens.OPOTHER)
    end

(* Accumulate one fragment of raw comment text, tagged with its own span. *)
fun push_raw_fragment st (yypos, yytext) =
    Scala3_Comments.push_raw st
      (yytext, Position.range_position
       (gp st yypos, gp st (yypos + String.size yytext)))

fun layout_newline st = Scala3_Layout.newline st

fun char_to_navi #"u" = Scala3_Ast.up
  | char_to_navi #"U" = Scala3_Ast.Up
  | char_to_navi #"r" = Scala3_Ast.right
  | char_to_navi #"d" = Scala3_Ast.down
  | char_to_navi c = raise Fail ("invalid navigation character " ^ String.str c)

(* Splits the text matched after the leading "@" into the tag name, its optional
   bracketed navigation string, and its optional parenthesized level. *)
fun parse_tag_navi_level text =
    let
      val trim =
        Substring.string o Substring.dropr Char.isSpace o Substring.full
      val after_at =
        Substring.dropl (fn c => c = #"@" orelse Char.isSpace c)
          (Substring.full text)
      val (name_ss, rest1) =
        Substring.splitl (fn c => Char.isAlphaNum c orelse c = #"_") after_at
      val rest1' = Substring.dropl Char.isSpace rest1
      val (navi, rest2) =
        if Substring.size rest1' > 0 andalso Substring.sub (rest1', 0) =
          #"[" then
          let
            val (navi_ss, after) =
              Substring.splitl (fn c => c <> #"]") (Substring.triml 1 rest1')
          in (map char_to_navi (String.explode (Substring.string navi_ss)),
              Substring.triml 1 after) end
        else ([], rest1')
      val rest2' = Substring.dropl Char.isSpace rest2
      val level =
        if Substring.size rest2' > 0 andalso Substring.sub (rest2', 0) =
          #"(" then
          let val (lvl_ss, _) =
            Substring.splitl (fn c => c <> #")") (Substring.triml 1 rest2')
          in valOf (Int.fromString (Substring.string lvl_ss)) end
        else 0
    in (trim (Substring.string name_ss), navi, level) end

(* A bodyless tag is a complete antiquotation with the empty body - but only
   where the comment opener allowed it ("//@", "/*@"): elsewhere it is plain
   comment text, such as a Scaladoc tag, and is dropped here. *)
fun antiq_flush_pending_tag st =
    let val (name, navi, level, pos) = !(antiq_tag st) in
      if name = "" then ()
      else
        (antiq_tag st := ("", [], 0, Position.none);
         if !(bodyless_ok st)
         then Scala3_Comments.push_antiquotation
           st {tag = (name, pos)} navi {level = level} {cartouche = ("", pos)}
         else ())
    end

fun antiq_tag_seen st (yypos, yytext) =
    let
      val (name, navi, level) = parse_tag_navi_level yytext
      val _ = if yypos = !(comment_start st) then bodyless_ok st := true else ()
    in antiq_flush_pending_tag st; antiq_tag
      st := (name, navi, level, gp st yypos) end

fun antiq_body_start st yypos = antiq_start st := gp st yypos

fun antiq_body_push st text = antiq_buf st := text :: !(antiq_buf st)

fun antiq_body_finish st yypos =
    let
      val body_text = String.concat (rev (!(antiq_buf st)))
      val body_pos = Position.range_position (!(antiq_start st), gp st yypos)
      val (tag_text, navi, level, tag_pos) = !(antiq_tag st)
    in
      antiq_buf st := [];
      antiq_tag st := ("", [], 0, Position.none);
      Scala3_Comments.push_antiquotation
        st {tag = (tag_text, tag_pos)} navi {level = level} {cartouche =
            (body_text, body_pos)}
    end

(* The quoted-string alternative to a cartouche body: tag, level and body in one
   rule. *)
fun antiq_tag_and_string_seen st (yypos, yytext) =
    let
      fun find_quote i = if String.sub (yytext, i) =
        #"\"" then i else find_quote (i + 1)
      val qpos = find_quote 0
      val (name, navi, level) =
        parse_tag_navi_level (String.substring (yytext, 0, qpos))
      val body_len = String.size yytext - qpos - 2
      val body_text = String.substring (yytext, qpos + 1, body_len)
      val body_start = yypos + qpos + 1
      val body_pos =
        Position.range_position
          (gp st body_start, gp st (body_start + body_len))
    in
      Scala3_Comments.push_antiquotation
        st {tag = (name, gp st yypos)} navi {level = level} {cartouche =
            (body_text, body_pos)}
    end

(* Comments. A block comment nests; whichever way it ends, a pending bodyless
   tag is flushed. *)
fun comment_open st block yypos =
    (bodyless_ok st := false; comment_start st := yypos
     + 2; antiq_from_block st := block;
     if block then comment_depth st := 1 else ())

(* Strings with more than one token's worth of scanning (multi-line,
   interpolated). *)
fun str_open (st : arg) yypos prefix ml =
    (#str_prefix st := prefix; #str_ml st := ml; #str_start
     st := yypos; #str_buf st := [])
fun str_push (st : arg) text = #str_buf st := text :: !(#str_buf st)
fun str_finish (st : arg) (yypos, yytext) =
    let
      val start = !(#str_start st)
      val stop = yypos + String.size yytext
      val body = String.concat (rev (!(#str_buf st)))
      val prefix = !(#str_prefix st)
      val ml = !(#str_ml st)
      val kind = if prefix = "" then "STRING_LIT" else "INTERP_LIT"
      val p = gp st start
      val p' = gp st stop
      val _ = Scala3_Comments.attach_pending st p
      val _ = Scala3_Layout.token st (start, stop, kind)
      val _ = report st (start, stop - start, Markup.string, kind, "")
    in
      if prefix = "" then Tokens.STRING_LIT ((body, ml), p, p')
      else Tokens.INTERP_LIT ((prefix, body, ml), p, p')
    end

(* "s\"" -> "s" and "s\"\"\"" -> "s" *)
fun prefix_of yytext n = String.substring (yytext, 0, String.size yytext - n)

(* The first lexical error is recorded (see "Scala3_State"); the lexer carries
   on, and "Scala3_Parse.parse" reports it when the parse is over. *)
fun lex_fail (st : arg) (msg, pos) =
    (case !(#lex_error st) of NONE =>
     #lex_error st := SOME (msg, pos) | SOME _ => ())

(* Shadows the default "eof" of the "[state]" header: unterminated constructs
   are genuine errors, reported at their own start. *)
fun eof (st : arg) =
    let
      val _ =
        if !(antiq_depth st) > 0
        then (antiq_depth st := 0;
              lex_fail st
                (("Unterminated antiquotation body: no matching closing " ^
                  "cartouche before the end of input"),
                           !(antiq_start st)))
        else if !(comment_depth st) > 0
        then (comment_depth st := 0; lex_fail st
              ("Unterminated comment", gp st 0))
        else antiq_flush_pending_tag st
    in Tokens.EOF (Position.none, Position.none) end
\<close>
lex_definitions\<open>
D=[0-9];
N=[0-9][0-9_]*;
H=[0-9A-Fa-f];
LET=([A-Za-z$_]|[^\000-\127]);
LD=([A-Za-z0-9$_]|[^\000-\127]);
TL=[A-Za-z_];
TA=[A-Za-z_0-9];
OPC=[!#%&*+/:<=>?@\\^|~\-];
OPNS=[!#%&*+:<=>?@\\^|~\-];
OPNSS=[!#%&+:<=>?@\\^|~\-];
EXP=[eE][+\-]?{N};
FT=[fFdD];
HWS=[\ \t];
WS=[\ \t\r\012];
NAVI=[uUrd];
ATAG={HWS}*{TL}{TA}*({HWS}*"["{NAVI}*"]")?({HWS}*"("{D}+")")?;
ES=(\\(["\\abfnrtv]|x{H}{H}));
OPENCART=\\\<open>;
CLOSECART=\\\<close>;
%s COMMENT LCOMMENT ANTIQ MLSTR ISTR IEXPR;
\<close>
lex_rules\<open>
<INITIAL>"//"
        => (comment_open st false yypos;
            YYBEGIN LCOMMENT;
            continue ());
<INITIAL>"/*"
        => (comment_open st true yypos;
            YYBEGIN COMMENT;
            continue ());
<INITIAL>\n                         => (layout_newline st; continue ());
<INITIAL>{WS}+                      => (continue ());

<INITIAL>"_"
        => (stok st "UNDERSCORE" Markup.keyword1
            (yypos, yytext, Tokens.UNDERSCORE));
<INITIAL>"("
        => (stok st "LPAREN" Markup.delimiter (yypos, yytext, Tokens.LPAREN));
<INITIAL>")"
        => (stok st "RPAREN" Markup.delimiter (yypos, yytext, Tokens.RPAREN));
<INITIAL>"["
        => (stok st "LBRACKET" Markup.delimiter
            (yypos, yytext, Tokens.LBRACKET));
<INITIAL>"]"
        => (stok st "RBRACKET" Markup.delimiter
            (yypos, yytext, Tokens.RBRACKET));
<INITIAL>"{"
        => (stok st "LBRACE" Markup.delimiter (yypos, yytext, Tokens.LBRACE));
<INITIAL>"}"
        => (stok st "RBRACE" Markup.delimiter (yypos, yytext, Tokens.RBRACE));
<INITIAL>","
        => (stok st "COMMA" Markup.delimiter (yypos, yytext, Tokens.COMMA));
<INITIAL>"."
        => (stok st "DOT" Markup.delimiter (yypos, yytext, Tokens.DOT));
<INITIAL>";"
        => (stok st "SEMI" Markup.delimiter (yypos, yytext, Tokens.SEMI));

<INITIAL>{LET}{LD}*                 => (word_tok st (yypos, yytext));
<INITIAL>{LET}{LD}*"_"{OPC}+
        => (stok_val st "IDENT" Markup.free
            (yypos, yytext, Tokens.IDENT, yytext));
<INITIAL>"`"[^`\n]+"`"
        => (stok_val st "IDENT" Markup.free
            (yypos, yytext, Tokens.IDENT, yytext));

<INITIAL>0[xX]{H}({H}|_)*[lL]?
        => (stok_val st "INT_LIT" Markup.numeral
            (yypos, yytext, Tokens.INT_LIT, yytext));
<INITIAL>0[bB][01]([01]|_)*[lL]?
        => (stok_val st "INT_LIT" Markup.numeral
            (yypos, yytext, Tokens.INT_LIT, yytext));
<INITIAL>{N}[lL]?
        => (stok_val st "INT_LIT" Markup.numeral
            (yypos, yytext, Tokens.INT_LIT, yytext));
<INITIAL>{N}"."{N}{EXP}?{FT}?
        => (stok_val st "FLOAT_LIT" Markup.numeral
            (yypos, yytext, Tokens.FLOAT_LIT, yytext));
<INITIAL>{N}{EXP}{FT}?
        => (stok_val st "FLOAT_LIT" Markup.numeral
            (yypos, yytext, Tokens.FLOAT_LIT, yytext));
<INITIAL>{N}{FT}
        => (stok_val st "FLOAT_LIT" Markup.numeral
            (yypos, yytext, Tokens.FLOAT_LIT, yytext));

<INITIAL>"'"([^'\\\n]|\\(["'\\btnfr]|u+{H}{H}{H}{H}|[0-7][0-7]?[0-7]?))"'"
        => (stok_val st "CHAR_LIT" Markup.string
            (yypos, yytext, Tokens.CHAR_LIT,
             String.substring (yytext, 1, String.size yytext - 2)));

<INITIAL>["]["]["]
        => (str_open st yypos "" true;
            YYBEGIN MLSTR;
            continue ());
<INITIAL>{LET}{LD}*["]["]["]
        => (str_open st yypos (prefix_of yytext 3) true;
            YYBEGIN MLSTR;
            continue ());
<INITIAL>{LET}{LD}*["]
        => (str_open st yypos (prefix_of yytext 1) false;
            YYBEGIN ISTR;
            continue ());
<INITIAL>["]([^"\\\n]|\\.)*["]
        => (stok_val st "STRING_LIT" Markup.string
            (yypos, yytext, Tokens.STRING_LIT,
             (String.substring (yytext, 1, String.size yytext - 2), false)));

<INITIAL>({OPNS}{OPC}*|"/"|"/"{OPNSS}{OPC}*)
        => (op_tok st (yypos, yytext));
<INITIAL>.
        => (stok_val st "ILLEGAL" (Markup.bad ())
            (yypos, yytext, Tokens.ILLEGAL, yytext));

<ISTR>[^"\\$\n]+                    => (str_push st yytext; continue ());
<ISTR>"\\".                         => (str_push st yytext; continue ());
<ISTR>"$$"                          => (str_push st yytext; continue ());
<ISTR>"$"{LET}{LD}*                 => (str_push st yytext; continue ());
<ISTR>"${"
        => (str_push st yytext;
            #iexpr_depth st := 1;
            YYBEGIN IEXPR;
            continue ());
<ISTR>"$"                           => (str_push st yytext; continue ());
<ISTR>["]
        => (YYBEGIN INITIAL;
            str_finish st (yypos, yytext));
<ISTR>\n
        => (lex_fail st
            ("Unterminated string literal", gp st (!(#str_start st)));
            YYBEGIN INITIAL;
            continue ());
<ISTR>\\                            => (str_push st yytext; continue ());

<MLSTR>[^"$\n]+                     => (str_push st yytext; continue ());
<MLSTR>\n                           => (str_push st yytext; continue ());
<MLSTR>["]["]["]["]*
        => (str_push st (String.substring (yytext, 0, String.size yytext - 3));
            YYBEGIN INITIAL;
            str_finish st (yypos, yytext));
<MLSTR>["]["]?                      => (str_push st yytext; continue ());
<MLSTR>"$$"                         => (str_push st yytext; continue ());
<MLSTR>"${"
        => (str_push st yytext;
            if !(#str_prefix st) = "" then continue ()
              else (#iexpr_depth st := 1; YYBEGIN IEXPR; continue ()));
<MLSTR>"$"{LET}{LD}*                => (str_push st yytext; continue ());
<MLSTR>"$"                          => (str_push st yytext; continue ());

<IEXPR>[^"{}\n']+                   => (str_push st yytext; continue ());
<IEXPR>"'"([^'\\\n]|\\.)*"'"        => (str_push st yytext; continue ());
<IEXPR>["]([^"\\\n]|\\.)*["]        => (str_push st yytext; continue ());
<IEXPR>"{"
        => (str_push st yytext;
            #iexpr_depth st := !(#iexpr_depth st) + 1;
            continue ());
<IEXPR>"}"
        => (str_push st yytext;
            #iexpr_depth st := !(#iexpr_depth st) - 1;
            if !(#iexpr_depth st) = 0
              then (YYBEGIN (if !(#str_ml st) then MLSTR else ISTR); continue
                    ()) else continue ());
<IEXPR>\n                           => (str_push st yytext; continue ());
<IEXPR>.                            => (str_push st yytext; continue ());

<LCOMMENT>[^@\\\n]+
        => (push_raw_fragment st (yypos, yytext);
            continue ());
<LCOMMENT>"@"{ATAG}{HWS}*["]([^"\\\n]|{ES})*["]
        => (report st
            (yypos, String.size yytext, Markup.antiquote,
             "Scala antiquotation tag+body", "");
            antiq_tag_and_string_seen st (yypos, yytext);
            continue ());
<LCOMMENT>"@"{ATAG}
        => (antiq_tag_seen st (yypos, yytext);
            (if !(bodyless_ok st)
             then report st
               (yypos, String.size yytext, Markup.antiquote,
                "Scala antiquotation tag", "") else ());
            continue ());
<LCOMMENT>"@"
        => (push_raw_fragment st (yypos, yytext);
            continue ());
<LCOMMENT>"\\"
        => (push_raw_fragment st (yypos, yytext);
            continue ());
<LCOMMENT>{OPENCART}
        => (report st
            (yypos, String.size yytext, Markup.cartouche,
             "Scala antiquotation body", "");
            antiq_depth st := 1;
            antiq_from_block st := false;
            antiq_body_start st (yypos + String.size yytext);
            YYBEGIN ANTIQ;
            continue ());
<LCOMMENT>\n
        => (antiq_flush_pending_tag st;
            layout_newline st;
            YYBEGIN INITIAL;
            continue ());

<COMMENT>[^*/@\\\n]+
        => (push_raw_fragment st (yypos, yytext);
            continue ());
<COMMENT>\n
        => (push_raw_fragment st (yypos, yytext);
            layout_newline st;
            continue ());
<COMMENT>"/*"
        => (comment_depth st := !(comment_depth st) + 1;
            push_raw_fragment st (yypos, yytext);
            continue ());
<COMMENT>"*/"
        => (comment_depth st := !(comment_depth st) - 1;
            if !(comment_depth st) = 0
              then (antiq_flush_pending_tag st; YYBEGIN INITIAL; continue ())
                else (push_raw_fragment st (yypos, yytext); continue ()));
<COMMENT>"*"
        => (push_raw_fragment st (yypos, yytext);
            continue ());
<COMMENT>"/"
        => (push_raw_fragment st (yypos, yytext);
            continue ());
<COMMENT>"@"{ATAG}{HWS}*["]([^"\\\n]|{ES})*["]
        => (report st
            (yypos, String.size yytext, Markup.antiquote,
             "Scala antiquotation tag+body", "");
            antiq_tag_and_string_seen st (yypos, yytext);
            continue ());
<COMMENT>"@"{ATAG}
        => (antiq_tag_seen st (yypos, yytext);
            (if !(bodyless_ok st)
             then report st
               (yypos, String.size yytext, Markup.antiquote,
                "Scala antiquotation tag", "") else ());
            continue ());
<COMMENT>"@"
        => (push_raw_fragment st (yypos, yytext);
            continue ());
<COMMENT>"\\"
        => (push_raw_fragment st (yypos, yytext);
            continue ());
<COMMENT>{OPENCART}
        => (report st
            (yypos, String.size yytext, Markup.cartouche,
             "Scala antiquotation body", "");
            antiq_depth st := 1;
            antiq_from_block st := true;
            antiq_body_start st (yypos + String.size yytext);
            YYBEGIN ANTIQ;
            continue ());

<ANTIQ>[^\\\n]+                     => (antiq_body_push st yytext; continue ());
<ANTIQ>\n+
        => (antiq_body_push st yytext;
            List.app (fn _ => layout_newline st) (String.explode yytext);
            continue ());
<ANTIQ>"\\"                         => (antiq_body_push st yytext; continue ());
<ANTIQ>{OPENCART}
        => (antiq_depth st := !(antiq_depth st) + 1;
            antiq_body_push st yytext;
            continue ());
<ANTIQ>{CLOSECART}
        => (antiq_depth st := !(antiq_depth st) - 1;
            if !(antiq_depth st) = 0
              then (antiq_body_finish st
                    yypos; (if !(antiq_from_block st) then YYBEGIN COMMENT
                            else YYBEGIN LCOMMENT); continue ())
                              else (antiq_body_push st yytext; continue ()));
\<close>
and yacc_user_declarations\<open>
open Scala3_Ast

fun ndi st p = Scala3_Comments.mk_nodeInfo st p p
fun ndi2 st (p1, p2) =
  Scala3_Comments.mk_nodeInfo st p1 (Position.range_position (p1, p2))

(* A name token carries its true source span as its position, so the node's own
   range is exactly the name. *)
fun mkid st (s, l, r) = Ident (s, 0, ndi2 st (l, r))

(* The soft modifiers are told from names by the layout stream, which delivers
   the five words as SOFTMOD when they play the part of a modifier. *)
fun soft_modifier k =
  (case k of
     "OPEN" => MOpen | "INLINE" => MInline | "TRANSPARENT" => MTransparent
   | "INFIX" => MInfix | "OPAQUE" => MOpaque
   | _ => raise Fail ("soft_modifier: " ^ k))

(* In a pattern a lower-case (or "_"-prefixed) identifier is a variable binder;
   anything else, and every backquoted identifier, is a stable identifier. *)
fun is_varid s = s <> ""
  andalso (let val c = String.sub (s, 0) in Char.isLower c orelse c = #"_" end)
fun varpat (id as Ident (s, _, _)) = if is_varid s then PVar id
  else PRef (EIdent id)
fun path_pattern (EIdent id) = varpat id
  | path_pattern e = PRef e

fun type_to_expr (TName id) = EIdent id
  | type_to_expr (TSelect (t, id, ni)) = ESelect (type_to_expr t, id, ni)
  | type_to_expr _ = raise Fail "a singleton type needs a path"

(* "(A, B) => C" is a function of two arguments, "(A) => C" and "A => C" of one.
   *)
fun mk_fun st (ctx, t1, t2, l, r) =
  let val ni = ndi2 st (l, r)
  in (case t1 of TTuple (ts, _) => TFun (ctx, ts, t2, ni) | _ =>
      TFun (ctx, [t1], t2, ni)) end

fun paren_type st (ts, l, r) =
  (case ts of [t] => t | _ => TTuple (ts, ndi2 st (l, r)))

fun paren_expr st (es, l, r) =
  (case es of [e] => EParen (e, ndi2 st (l, r)) | _ =>
   ETuple (es, ndi2 st (l, r)))

(* A parenthesized list that turns out to be a lambda's parameters: "(x, y: Int,
   _) => ...". *)
fun to_binding st e =
  (case e of
     EIdent id => Binding (SOME id, NONE, nodeInfo_of_ident id)
   | ETyped (EIdent id, t, ni) => Binding (SOME id, SOME t, ni)
   | EPlaceholder ni => Binding (NONE, NONE, ni)
   | ETyped (EPlaceholder _, t, ni) => Binding (NONE, SOME t, ni)
   | _ => raise Fail "invalid lambda parameter")

fun to_arg e =
  (case e of EAssign (EIdent id, v, ni) => ANamed (id, v, ni) | _ => AExpr e)

fun this_of st (e, l, r) =
  (case e of EIdent id => EThis (SOME id, ndi2 st (l, r)) | _ =>
   raise Fail "invalid qualifier of this")

fun super_of st (e, mixin, l, r) =
  (case e of EIdent id => ESuper (SOME id, mixin, ndi2 st (l, r)) | _ =>
   raise Fail "invalid qualifier of super")

fun anon_param st t = Param ([], [], 0, NONE, t, NONE, nodeInfo_of_type t)

(* "import a.b.c" is the path "a.b" with the selector "c". *)
fun import_of_path st (p, l, r) =
  (case p of
     ESelect (pre, id, _) =>
       ImportExpr
         (pre, [SelName (id, NONE, nodeInfo_of_ident id)], ndi2 st (l, r))
   | _ => ImportExpr (p, [], ndi2 st (l, r)))

fun import_as st (p, name, l, r) =
  (case p of
     ESelect (pre, id, _) =>
       ImportExpr
         (pre, [SelName (id, SOME name, ndi2 st (l, r))], ndi2 st (l, r))
   | EIdent id =>
     ImportExpr (p, [SelName (id, SOME name, ndi2 st (l, r))], ndi2 st (l, r))
   | _ => raise Fail "invalid import")
\<close>
yacc_definitions\<open>
%eop EOF
%arg (st) : Scala3_State.T
%noshift EOF

(* Precedences. TYLOW is a pseudo-token, the lowest of all: a rule marked
   "%prec TYLOW" loses against the shift of any token declared after it. It
   declares, for the cases where the grammar is ambiguous and Scala means the
   longer reading (a type continuing with an operator, a refinement or "with";
   "(implicit", "(using"; a statement list absorbing a separator ...), that
   shifting is intended - a precedence resolves a conflict silently, where the
   default of the tool would report it. The levels are, from the lowest: TYLOW;
   the tokens that begin or continue a modifier, parameter or statement;
   ARROW; the expression operators; "." "[" "#" "@" "<:"; "{" and "with".
   (The soft modifiers are not a matter of precedence: the layout stream tells
   them from names, see "is_soft_modifier".) *)
%nonassoc TYLOW
%right ABSTRACT AS CATCH COLON EXTENSION FINAL FINALLY IF IMPLICIT INFIX INLINE
%right LAZY LPAREN OPAQUE OPEN OVERRIDE PRIVATE PROTECTED SEALED TRANSPARENT
%right NEWLINE SEMI SOFTMOD UNDERSCORE USING VAL VAR
%right ARROW CTXARROW
%left MATCH
%nonassoc LOWIF
%nonassoc ELSE
%left IDENT
%left BAR OPBAR
%left OPCARET
%left OPAMP
%left OPEQ BANG
%left OPLT
%right OPCOLON
%left OPCOLONL
%left PLUS MINUS OPADD
%left STAR OPMUL
%left OPOTHER TILDE
%right DOT LBRACKET HASH AT SUBTYPE
%nonassoc LBRACE WITH

%term
        IDENT of string | INT_LIT of string | FLOAT_LIT of string | CHAR_LIT
          of string
      | STRING_LIT of string * bool | INTERP_LIT of string * string * bool
          | ILLEGAL of string
      | AS of string | EXTENSION of string | INFIX of string | INLINE of string
          | OPAQUE of string
      | OPEN of string | TRANSPARENT of string | USING of string
      | TYLOW | SOFTMOD of string
      | PLUS of string | MINUS of string | STAR of string | BAR of string
          | BANG of string
      | TILDE of string | QMARK of string
      | OPBAR of string | OPCARET of string | OPAMP of string | OPEQ of string
          | OPLT of string
      | OPCOLON of string | OPCOLONL of string | OPADD of string | OPMUL
          of string | OPOTHER of string
      | ABSTRACT | CASE | CASEMOD | CATCH | CLASS | DEF | DO | ELSE | ENUM
          | EXPORT | EXTENDS
      | FALSE | FINAL | FINALLY | FOR | GIVEN | IF | IMPLICIT | IMPORT | LAZY
          | MATCH | NEW | NULL
      | OBJECT | OVERRIDE | PACKAGE | PRIVATE | PROTECTED | RETURN | SEALED
          | SUPER | THEN | THIS
      | THROW | TRAIT | TRUE | TRY | TYPE | VAL | VAR | WHILE | WITH | YIELD
      | COLON | EQUALS | LARROW | ARROW | CTXARROW | TYARROW | SUBTYPE
          | SUPERTYPE | HASH | AT
      | UNDERSCORE | LPAREN | RPAREN | LBRACKET | RBRACKET | LBRACE | RBRACE
          | COMMA | DOT | SEMI
      | ENUMCASE | NEWLINE | ENTRY_UNIT | ENTRY_EXPR | ENTRY_TYPE | ENTRY_ID
          | LOWIF | EOF

%nonterm
        opt_nl of unit
      |        opt_semis of unit
      |        semis of unit
      |        semi of unit
      |        start_rule of Position.T root option
      |        name of Position.T ident
      |        opname of Position.T ident
      |        any_id of Position.T ident
      |        stat_list of Position.T sStat list
      |        new_parents of Position.T sParent list
      |        literal of Position.T sLit
      |        typ of Position.T sType
      |        infix_type of Position.T sType
      |        refined_type of Position.T sType
      |        annot_type of Position.T sType
      |        simple_type of Position.T sType
      |        types of Position.T sType list
      |        fun_arg_type of Position.T sType
      |        fun_arg_types of Position.T sType list
      |        type_args of Position.T sType list
      |        param_type of Position.T sType
      |        opt_bounds of Position.T sTypeBounds
      |        type_cases of Position.T sTypeCase list
      |        type_case of Position.T sTypeCase
      |        tparams of Position.T sTypeParam list
      |        tparam of Position.T sTypeParam
      |        tparam_body of Position.T sAnnot list -> Position.T sTypeParam
      |        ctx_bounds of Position.T sType list
      |        opt_hk of Position.T sTypeParam list
      |        annotation of Position.T sAnnot
      |        annotations_ne of Position.T sAnnot list
      |        annotations_plain of Position.T sAnnot list
      |        modifier of modifier
      |        mod_item of Position.T sAnnot list * modifier list
      |        mods_ne of Position.T sAnnot list * modifier list
      |        cmodifier of modifier
      |        cmod_item of Position.T sAnnot list * modifier list
      |        cmods_ne of Position.T sAnnot list * modifier list
      |        expr of Position.T sExpr
      |        expr_nb of Position.T sExpr
      |        infix_expr of Position.T sExpr
      |        prefix_expr of Position.T sExpr
      |        simple_expr of Position.T sExpr
      |        exprs_in_parens of Position.T sExpr list
      |        paren_group of Position.T sExpr list
      |        par_args of Position.T sArg list * bool
      |        par_argss of (Position.T sArg list * bool) list
      |        lam_params of Position.T sBinding list * bool
      |        block_expr of Position.T sExpr
      |        stat of Position.T sStat
      |        stat_seq of Position.T sStat list
      |        stat_seq_ne of Position.T sStat list
      |        definition
          of (Position.T * Position.T sAnnot list * modifier list)
            -> Position.T sDef
      |        case_clauses of Position.T sCase list
      |        case_clause of Position.T sCase
      |        opt_guard of Position.T sExpr option
      |        enumerators of Position.T sEnum list
      |        enumerator_seq of Position.T sEnum list
      |        enumerator of Position.T sEnum
      |        for_body of bool * Position.T sExpr
      |        pattern of Position.T sPat
      |        pattern_t of Position.T sPat
      |        pattern_b of Position.T sPat
      |        infix_pattern of Position.T sPat
      |        simple_pattern of Position.T sPat
      |        path_pat of Position.T sExpr
      |        patterns of Position.T sPat list
      |        arg_patterns of Position.T sPat list
      |        pattern2_list of Position.T sPat list
      |        opt_ptype of Position.T sType option
      |        opt_peq of Position.T sExpr option
      |        opt_colon_type of Position.T sType option
      |        def_clauses of Position.T sClause list
      |        def_clauses_ne of Position.T sClause list
      |        def_clause of Position.T sClause
      |        given_clause of Position.T sClause
      |        given_clauses_ne of Position.T sClause list
      |        dparams of Position.T sParam list
      |        dparam of Position.T sParam
      |        dparam_pre of Position.T sAnnot list * modifier list
      |        cparam_clauses of Position.T sClause list
      |        cparam_clause of Position.T sClause
      |        cparams of Position.T sParam list
      |        cparam of Position.T sParam
      |        cparam_head of Position.T sAnnot list * modifier list * int
      |        opt_default of Position.T sExpr option
      |        opt_ctor_mods of modifier list
      |        opt_tparams_clause of Position.T sTypeParam list
      |        class_def of classKind
          -> (Position.T * Position.T sAnnot list * modifier list)
            -> Position.T sDef
      |        opt_template
          of Position.T sParent list * Position.T sTemplateBody option
      |        template_body of Position.T sTemplateBody
      |        self_type of Position.T sSelf
      |        constr_apps of Position.T sParent list
      |        constr_app of Position.T sParent
      |        enum_case
          of (Position.T * Position.T sAnnot list * modifier list)
            -> Position.T sDef
      |        names_comma of Position.T ident list
      |        given_def
          of (Position.T * Position.T sAnnot list * modifier list)
            -> Position.T sDef
      |        given_tail
          of Position.T sExpr option * Position.T sTemplateBody option
      |        ext_body of Position.T sStat list
      |        import_exprs of Position.T sImport list
      |        import_expr of Position.T sImport
      |        import_path of Position.T sExpr
      |        import_spec of Position.T sSelector list
      |        selectors of Position.T sSelector list
      |        selector of Position.T sSelector
      |        compilation_unit of Position.T sStat list
      |        package_path of Position.T sExpr
      |        opt_extends_parents of Position.T sParent list
      |        opt_eq_expr of Position.T sExpr option
      |        catch_part of Position.T sExpr option
      |        finally_part of Position.T sExpr option
\<close>
yacc_rules\<open>
start_rule:
        ENTRY_UNIT compilation_unit
        (SOME (Unit compilation_unit))
|       ENTRY_EXPR opt_semis expr opt_semis
        (SOME (Expr expr))
|       ENTRY_TYPE opt_semis typ opt_semis
        (SOME (Type typ))
|       ENTRY_ID opt_semis name opt_semis
        (SOME (Id name))
semi:
        SEMI
        (())
|       NEWLINE
        (())
semis:
        semi
        (())
|       semis semi
        (())
opt_semis:
        
        (())
|       semis
        (())
opt_nl:
        
        (())
|       NEWLINE
        (())
modifier:
        ABSTRACT
        (MAbstract)
|       FINAL
        (MFinal)
|       SEALED
        (MSealed)
|       IMPLICIT %prec TYLOW
        (MImplicit)
|       LAZY
        (MLazy)
|       OVERRIDE
        (MOverride)
|       SOFTMOD
        (soft_modifier SOFTMOD)
|       PRIVATE
        (MPrivate NONE)
|       PROTECTED
        (MProtected NONE)
|       PRIVATE LBRACKET name RBRACKET
        (MPrivate (SOME (ident_name name)))
|       PROTECTED LBRACKET name RBRACKET
        (MProtected (SOME (ident_name name)))
|       PRIVATE LBRACKET THIS RBRACKET
        (MPrivate (SOME "this"))
|       PROTECTED LBRACKET THIS RBRACKET
        (MProtected (SOME "this"))
mod_item:
        annotation opt_nl
        (([annotation], []))
|       modifier
        (([], [modifier]))
mods_ne:
        mod_item
        (mod_item)
|       mods_ne mod_item
        ((#1 mods_ne @ #1 mod_item, #2 mods_ne @ #2 mod_item))
dparam_pre:
        annotations_ne %prec TYLOW
        ((annotations_ne, []))
|       SOFTMOD
        (([], [soft_modifier SOFTMOD]))
|       annotations_ne SOFTMOD
        ((annotations_ne, [soft_modifier SOFTMOD]))
cmodifier:
        ABSTRACT
        (MAbstract)
|       FINAL
        (MFinal)
|       SEALED
        (MSealed)
|       IMPLICIT %prec TYLOW
        (MImplicit)
|       LAZY
        (MLazy)
|       OVERRIDE
        (MOverride)
|       SOFTMOD
        (soft_modifier SOFTMOD)
|       PRIVATE
        (MPrivate NONE)
|       PROTECTED
        (MProtected NONE)
|       PRIVATE LBRACKET name RBRACKET
        (MPrivate (SOME (ident_name name)))
|       PROTECTED LBRACKET name RBRACKET
        (MProtected (SOME (ident_name name)))
|       PRIVATE LBRACKET THIS RBRACKET
        (MPrivate (SOME "this"))
|       PROTECTED LBRACKET THIS RBRACKET
        (MProtected (SOME "this"))
cmod_item:
        annotation opt_nl
        (([annotation], []))
|       cmodifier
        (([], [cmodifier]))
cmods_ne:
        cmod_item
        (cmod_item)
|       cmods_ne cmod_item
        ((#1 cmods_ne @ #1 cmod_item, #2 cmods_ne @ #2 cmod_item))
name:
        IDENT
        (mkid st (IDENT, IDENTleft, IDENTright))
|       AS
        (mkid st (AS, ASleft, ASright))
|       EXTENSION %prec TYLOW
        (mkid st (EXTENSION, EXTENSIONleft, EXTENSIONright))
|       INFIX
        (mkid st (INFIX, INFIXleft, INFIXright))
|       INLINE
        (mkid st (INLINE, INLINEleft, INLINEright))
|       OPAQUE
        (mkid st (OPAQUE, OPAQUEleft, OPAQUEright))
|       OPEN
        (mkid st (OPEN, OPENleft, OPENright))
|       TRANSPARENT
        (mkid st (TRANSPARENT, TRANSPARENTleft, TRANSPARENTright))
|       USING %prec TYLOW
        (mkid st (USING, USINGleft, USINGright))
opname:
        PLUS
        (mkid st (PLUS, PLUSleft, PLUSright))
|       MINUS
        (mkid st (MINUS, MINUSleft, MINUSright))
|       STAR
        (mkid st (STAR, STARleft, STARright))
|       BAR
        (mkid st (BAR, BARleft, BARright))
|       BANG
        (mkid st (BANG, BANGleft, BANGright))
|       TILDE
        (mkid st (TILDE, TILDEleft, TILDEright))
|       QMARK
        (mkid st (QMARK, QMARKleft, QMARKright))
|       OPBAR
        (mkid st (OPBAR, OPBARleft, OPBARright))
|       OPCARET
        (mkid st (OPCARET, OPCARETleft, OPCARETright))
|       OPAMP
        (mkid st (OPAMP, OPAMPleft, OPAMPright))
|       OPEQ
        (mkid st (OPEQ, OPEQleft, OPEQright))
|       OPLT
        (mkid st (OPLT, OPLTleft, OPLTright))
|       OPCOLON
        (mkid st (OPCOLON, OPCOLONleft, OPCOLONright))
|       OPCOLONL
        (mkid st (OPCOLONL, OPCOLONLleft, OPCOLONLright))
|       OPADD
        (mkid st (OPADD, OPADDleft, OPADDright))
|       OPMUL
        (mkid st (OPMUL, OPMULleft, OPMULright))
|       OPOTHER
        (mkid st (OPOTHER, OPOTHERleft, OPOTHERright))
any_id:
        name
        (name)
|       opname
        (opname)
literal:
        INT_LIT
        (LInt (INT_LIT, ndi2 st (INT_LITleft, INT_LITright)))
|       FLOAT_LIT
        (LFloat (FLOAT_LIT, ndi2 st (FLOAT_LITleft, FLOAT_LITright)))
|       CHAR_LIT
        (LChar (CHAR_LIT, ndi2 st (CHAR_LITleft, CHAR_LITright)))
|       STRING_LIT
        (LString (#1 STRING_LIT, #2 STRING_LIT,
                  ndi2 st (STRING_LITleft, STRING_LITright)))
|       INTERP_LIT
        (LInterp (#1 INTERP_LIT, #2 INTERP_LIT, #3 INTERP_LIT,
                  ndi2 st (INTERP_LITleft, INTERP_LITright)))
|       TRUE
        (LBool (true, ndi2 st (TRUEleft, TRUEright)))
|       FALSE
        (LBool (false, ndi2 st (FALSEleft, FALSEright)))
|       NULL
        (LNull (ndi2 st (NULLleft, NULLright)))
typ:
        infix_type %prec TYLOW
        (infix_type)
|       infix_type ARROW typ
        (mk_fun st (false, infix_type, typ, infix_typeleft, typright))
|       infix_type CTXARROW typ
        (mk_fun st (true, infix_type, typ, infix_typeleft, typright))
|       LBRACKET tparams RBRACKET TYARROW typ
        (TLambda (tparams, typ, ndi2 st (LBRACKETleft, typright)))
|       LBRACKET tparams RBRACKET ARROW typ
        (TPolyFun (tparams, typ, ndi2 st (LBRACKETleft, typright)))
|       infix_type MATCH LBRACE type_cases RBRACE
        (TMatch (infix_type, type_cases, ndi2 st (infix_typeleft, RBRACEright)))
type_cases:
        type_case
        ([type_case])
|       type_cases type_case
        (type_cases @ [type_case])
type_case:
        CASE infix_type ARROW typ opt_semis
        (TypeCase (SOME infix_type, typ, ndi2 st (CASEleft, typright)))
|       CASE UNDERSCORE ARROW typ opt_semis
        (TypeCase (NONE, typ, ndi2 st (CASEleft, typright)))
infix_type:
        refined_type %prec TYLOW
        (refined_type)
|       infix_type IDENT opt_nl refined_type
        (TInfix (infix_type, mkid st (IDENT, IDENTleft, IDENTright),
                 refined_type, ndi2 st (infix_typeleft, refined_typeright)))
|       infix_type BAR refined_type
        (TInfix (infix_type, mkid st (BAR, BARleft, BARright), refined_type,
                 ndi2 st (infix_typeleft, refined_typeright)))
|       infix_type OPBAR refined_type
        (TInfix (infix_type, mkid st (OPBAR, OPBARleft, OPBARright),
                 refined_type, ndi2 st (infix_typeleft, refined_typeright)))
|       infix_type OPCARET refined_type
        (TInfix (infix_type, mkid st (OPCARET, OPCARETleft, OPCARETright),
                 refined_type, ndi2 st (infix_typeleft, refined_typeright)))
|       infix_type OPAMP refined_type
        (TInfix (infix_type, mkid st (OPAMP, OPAMPleft, OPAMPright),
                 refined_type, ndi2 st (infix_typeleft, refined_typeright)))
|       infix_type OPEQ refined_type
        (TInfix (infix_type, mkid st (OPEQ, OPEQleft, OPEQright), refined_type,
                 ndi2 st (infix_typeleft, refined_typeright)))
|       infix_type OPLT refined_type
        (TInfix (infix_type, mkid st (OPLT, OPLTleft, OPLTright), refined_type,
                 ndi2 st (infix_typeleft, refined_typeright)))
|       infix_type OPCOLON refined_type
        (TInfix (infix_type, mkid st (OPCOLON, OPCOLONleft, OPCOLONright),
                 refined_type, ndi2 st (infix_typeleft, refined_typeright)))
|       infix_type OPCOLONL refined_type
        (TInfix (infix_type, mkid st (OPCOLONL, OPCOLONLleft, OPCOLONLright),
                 refined_type, ndi2 st (infix_typeleft, refined_typeright)))
|       infix_type PLUS refined_type
        (TInfix (infix_type, mkid st (PLUS, PLUSleft, PLUSright), refined_type,
                 ndi2 st (infix_typeleft, refined_typeright)))
|       infix_type MINUS refined_type
        (TInfix (infix_type, mkid st (MINUS, MINUSleft, MINUSright),
                 refined_type, ndi2 st (infix_typeleft, refined_typeright)))
|       infix_type OPADD refined_type
        (TInfix (infix_type, mkid st (OPADD, OPADDleft, OPADDright),
                 refined_type, ndi2 st (infix_typeleft, refined_typeright)))
|       infix_type OPMUL refined_type
        (TInfix (infix_type, mkid st (OPMUL, OPMULleft, OPMULright),
                 refined_type, ndi2 st (infix_typeleft, refined_typeright)))
|       infix_type OPOTHER refined_type
        (TInfix (infix_type, mkid st (OPOTHER, OPOTHERleft, OPOTHERright),
                 refined_type, ndi2 st (infix_typeleft, refined_typeright)))
refined_type:
        annot_type %prec TYLOW
        (annot_type)
|       refined_type LBRACE stat_seq RBRACE
        (TRefine (SOME refined_type, stat_seq,
                  ndi2 st (refined_typeleft, RBRACEright)))
|       refined_type WITH annot_type %prec TYLOW
        (TWith (refined_type, annot_type,
                ndi2 st (refined_typeleft, annot_typeright)))
annot_type:
        simple_type %prec TYLOW
        (simple_type)
|       annot_type annotation
        ((case annot_type of TAnnot (t, anns, ni) =>
          TAnnot (t, anns
                  @ [annotation], ndi2 st (annot_typeleft, annotationright))
                    | t => TAnnot
                        (t, [annotation],
                         ndi2 st (annot_typeleft, annotationright))))
simple_type:
        name
        (TName name)
|       simple_type DOT name
        (TSelect (simple_type, name, ndi2 st (simple_typeleft, nameright)))
|       simple_type DOT TYPE
        (TSingleton
         (type_to_expr simple_type, ndi2 st (simple_typeleft, TYPEright)))
|       THIS DOT TYPE
        (TSingleton
         (EThis (NONE, ndi2 st (THISleft, THISright)),
          ndi2 st (THISleft, TYPEright)))
|       simple_type type_args
        (TApply (simple_type, type_args,
                 ndi2 st (simple_typeleft, type_argsright)))
|       simple_type DOT THIS
        (TSelect (simple_type, mkid st ("this", THISleft, THISright),
                  ndi2 st (simple_typeleft, THISright)))
|       simple_type HASH name
        (TProject (simple_type, name, ndi2 st (simple_typeleft, nameright)))
|       LPAREN RPAREN
        (TTuple ([], ndi2 st (LPARENleft, RPARENright)))
|       LPAREN fun_arg_types RPAREN
        (paren_type st (fun_arg_types, LPARENleft, RPARENright))
|       literal
        (TLit (literal, nodeInfo_of_lit literal))
|       UNDERSCORE opt_bounds
        (TWild (opt_bounds, ndi2 st (UNDERSCOREleft, UNDERSCOREright)))
|       QMARK opt_bounds
        (TWild (opt_bounds, ndi2 st (QMARKleft, QMARKright)))
types:
        typ
        ([typ])
|       types COMMA typ
        (types @ [typ])
fun_arg_type:
        typ
        (typ)
|       ARROW typ
        (TByName (typ, ndi2 st (ARROWleft, typright)))
fun_arg_types:
        fun_arg_type
        ([fun_arg_type])
|       fun_arg_types COMMA fun_arg_type
        (fun_arg_types @ [fun_arg_type])
type_args:
        LBRACKET types RBRACKET
        (types)
|       LBRACKET types COMMA RBRACKET
        (types)
param_type:
        typ
        (typ)
|       typ STAR
        (TRepeated (typ, ndi2 st (typleft, STARright)))
|       ARROW typ
        (TByName (typ, ndi2 st (ARROWleft, typright)))
|       ARROW typ STAR
        (TByName (TRepeated (typ, ndi2 st (typleft, STARright)),
                  ndi2 st (ARROWleft, STARright)))
opt_bounds:
        %prec TYLOW
        (Bounds (NONE, NONE))
|       SUPERTYPE typ %prec TYLOW
        (Bounds (SOME typ, NONE))
|       SUBTYPE typ
        (Bounds (NONE, SOME typ))
|       SUPERTYPE typ SUBTYPE typ
        (Bounds (SOME typ1, SOME typ2))
tparams:
        tparam
        ([tparam])
|       tparams COMMA tparam
        (tparams @ [tparam])
tparam:
        tparam_body
        (tparam_body [])
|       annotations_ne tparam_body
        (tparam_body annotations_ne)
tparam_body:
        name opt_hk opt_bounds ctx_bounds
        ((fn an =>
          TParam (an, 0, name, opt_hk, opt_bounds, ctx_bounds,
                  ndi2 st (nameleft, ctx_boundsright))))
|       PLUS name opt_hk opt_bounds ctx_bounds
        ((fn an =>
          TParam (an, 1, name, opt_hk, opt_bounds, ctx_bounds,
                  ndi2 st (PLUSleft, ctx_boundsright))))
|       MINUS name opt_hk opt_bounds ctx_bounds
        ((fn an =>
          TParam (an, 2, name, opt_hk, opt_bounds, ctx_bounds,
                  ndi2 st (MINUSleft, ctx_boundsright))))
|       UNDERSCORE opt_hk opt_bounds
        ((fn an =>
          TParam (an, 0, mkid st ("_", UNDERSCOREleft, UNDERSCOREright),
                  opt_hk, opt_bounds, [],
                    ndi2 st (UNDERSCOREleft, UNDERSCOREright))))
opt_hk:
        
        ([])
|       LBRACKET tparams RBRACKET
        (tparams)
ctx_bounds:
        
        ([])
|       ctx_bounds COLON typ
        (ctx_bounds @ [typ])
annotation:
        AT simple_type par_argss %prec TYLOW
        (Annot (simple_type, map #1 par_argss,
                ndi2 st (ATleft, par_argssright)))
annotations_plain:
        annotation
        ([annotation])
|       annotations_plain annotation
        (annotations_plain @ [annotation])
annotations_ne:
        annotation opt_nl
        ([annotation])
|       annotations_ne annotation opt_nl
        (annotations_ne @ [annotation])
expr:
        lam_params expr
        (ELambda (#1 lam_params, expr, #2 lam_params,
                  ndi2 st (lam_paramsleft, exprright)))
|       expr_nb
        (expr_nb)
lam_params:
        name ARROW
        (([Binding (SOME name, NONE, nodeInfo_of_ident name)], false))
|       UNDERSCORE ARROW
        (([Binding (NONE, NONE, ndi2 st (UNDERSCOREleft, UNDERSCOREright))],
          false))
|       paren_group ARROW
        ((map (to_binding st) paren_group, false))
|       name CTXARROW
        (([Binding (SOME name, NONE, nodeInfo_of_ident name)], true))
|       paren_group CTXARROW
        ((map (to_binding st) paren_group, true))
expr_nb:
        IF LPAREN expr RPAREN opt_nl expr %prec LOWIF
        (EIf (expr1, expr2, NONE, ndi2 st (IFleft, expr2right)))
|       IF LPAREN expr RPAREN opt_nl expr ELSE expr
        (EIf (expr1, expr2, SOME expr3, ndi2 st (IFleft, expr3right)))
|       WHILE LPAREN expr RPAREN opt_nl expr
        (EWhile (expr1, expr2, ndi2 st (WHILEleft, expr2right)))
|       TRY expr catch_part finally_part
        (ETry (expr, catch_part, finally_part,
               ndi2 st (TRYleft, finally_partright)))
|       THROW expr
        (EThrow (expr, ndi2 st (THROWleft, exprright)))
|       RETURN %prec TYLOW
        (EReturn (NONE, ndi2 st (RETURNleft, RETURNright)))
|       RETURN expr
        (EReturn (SOME expr, ndi2 st (RETURNleft, exprright)))
|       FOR LPAREN enumerators RPAREN opt_nl for_body
        (EFor (enumerators, #1 for_body, #2 for_body,
               ndi2 st (FORleft, for_bodyright)))
|       FOR LBRACE enumerators RBRACE opt_nl for_body
        (EFor (enumerators, #1 for_body, #2 for_body,
               ndi2 st (FORleft, for_bodyright)))
|       infix_expr EQUALS expr
        (EAssign (infix_expr, expr, ndi2 st (infix_exprleft, exprright)))
|       infix_expr COLON typ
        (ETyped (infix_expr, typ, ndi2 st (infix_exprleft, typright)))
|       infix_expr COLON annotations_plain
        (EAnnotated
         (infix_expr, annotations_plain,
          ndi2 st (infix_exprleft, annotations_plainright)))
|       infix_expr COLON UNDERSCORE STAR
        (ESplat (infix_expr, ndi2 st (infix_exprleft, STARright)))
|       infix_expr
        (infix_expr)
catch_part:
        %prec TYLOW
        (NONE)
|       CATCH expr
        (SOME expr)
finally_part:
        %prec TYLOW
        (NONE)
|       FINALLY expr
        (SOME expr)
for_body:
        expr
        ((false, expr))
|       DO expr
        ((false, expr))
|       YIELD expr
        ((true, expr))
infix_expr:
        prefix_expr
        (prefix_expr)
|       prefix_expr UNDERSCORE
        (EPostfix
         (prefix_expr, mkid st ("_", UNDERSCOREleft, UNDERSCOREright),
          ndi2 st (prefix_exprleft, UNDERSCOREright)))
|       infix_expr MATCH LBRACE case_clauses RBRACE
        (EMatch (infix_expr, case_clauses,
                 ndi2 st (infix_exprleft, RBRACEright)))
|       infix_expr IDENT opt_nl infix_expr
        (EInfix (infix_expr1, mkid st (IDENT, IDENTleft, IDENTright),
                 infix_expr2, ndi2 st (infix_expr1left, infix_expr2right)))
|       infix_expr BAR infix_expr
        (EInfix (infix_expr1, mkid st (BAR, BARleft, BARright), infix_expr2,
                 ndi2 st (infix_expr1left, infix_expr2right)))
|       infix_expr OPBAR infix_expr
        (EInfix (infix_expr1, mkid st (OPBAR, OPBARleft, OPBARright),
                 infix_expr2, ndi2 st (infix_expr1left, infix_expr2right)))
|       infix_expr OPCARET infix_expr
        (EInfix (infix_expr1, mkid st (OPCARET, OPCARETleft, OPCARETright),
                 infix_expr2, ndi2 st (infix_expr1left, infix_expr2right)))
|       infix_expr OPAMP infix_expr
        (EInfix (infix_expr1, mkid st (OPAMP, OPAMPleft, OPAMPright),
                 infix_expr2, ndi2 st (infix_expr1left, infix_expr2right)))
|       infix_expr OPEQ infix_expr
        (EInfix (infix_expr1, mkid st (OPEQ, OPEQleft, OPEQright), infix_expr2,
                 ndi2 st (infix_expr1left, infix_expr2right)))
|       infix_expr OPLT infix_expr
        (EInfix (infix_expr1, mkid st (OPLT, OPLTleft, OPLTright), infix_expr2,
                 ndi2 st (infix_expr1left, infix_expr2right)))
|       infix_expr OPCOLON infix_expr
        (EInfix (infix_expr1, mkid st (OPCOLON, OPCOLONleft, OPCOLONright),
                 infix_expr2, ndi2 st (infix_expr1left, infix_expr2right)))
|       infix_expr OPCOLONL infix_expr
        (EInfix (infix_expr1, mkid st (OPCOLONL, OPCOLONLleft, OPCOLONLright),
                 infix_expr2, ndi2 st (infix_expr1left, infix_expr2right)))
|       infix_expr PLUS infix_expr
        (EInfix (infix_expr1, mkid st (PLUS, PLUSleft, PLUSright), infix_expr2,
                 ndi2 st (infix_expr1left, infix_expr2right)))
|       infix_expr MINUS infix_expr
        (EInfix (infix_expr1, mkid st (MINUS, MINUSleft, MINUSright),
                 infix_expr2, ndi2 st (infix_expr1left, infix_expr2right)))
|       infix_expr OPADD infix_expr
        (EInfix (infix_expr1, mkid st (OPADD, OPADDleft, OPADDright),
                 infix_expr2, ndi2 st (infix_expr1left, infix_expr2right)))
|       infix_expr STAR infix_expr
        (EInfix (infix_expr1, mkid st (STAR, STARleft, STARright), infix_expr2,
                 ndi2 st (infix_expr1left, infix_expr2right)))
|       infix_expr OPMUL infix_expr
        (EInfix (infix_expr1, mkid st (OPMUL, OPMULleft, OPMULright),
                 infix_expr2, ndi2 st (infix_expr1left, infix_expr2right)))
|       infix_expr OPOTHER infix_expr
        (EInfix (infix_expr1, mkid st (OPOTHER, OPOTHERleft, OPOTHERright),
                 infix_expr2, ndi2 st (infix_expr1left, infix_expr2right)))
|       infix_expr BANG infix_expr
        (EInfix (infix_expr1, mkid st (BANG, BANGleft, BANGright), infix_expr2,
                 ndi2 st (infix_expr1left, infix_expr2right)))
|       infix_expr TILDE infix_expr
        (EInfix (infix_expr1, mkid st (TILDE, TILDEleft, TILDEright),
                 infix_expr2, ndi2 st (infix_expr1left, infix_expr2right)))
prefix_expr:
        simple_expr
        (simple_expr)
|       MINUS simple_expr
        (EPrefix (mkid st (MINUS, MINUSleft, MINUSright), simple_expr,
                  ndi2 st (MINUSleft, simple_exprright)))
|       PLUS simple_expr
        (EPrefix (mkid st (PLUS, PLUSleft, PLUSright), simple_expr,
                  ndi2 st (PLUSleft, simple_exprright)))
|       BANG simple_expr
        (EPrefix (mkid st (BANG, BANGleft, BANGright), simple_expr,
                  ndi2 st (BANGleft, simple_exprright)))
|       TILDE simple_expr
        (EPrefix (mkid st (TILDE, TILDEleft, TILDEright), simple_expr,
                  ndi2 st (TILDEleft, simple_exprright)))
simple_expr:
        name %prec TYLOW
        (EIdent name)
|       THIS %prec TYLOW
        (EThis (NONE, ndi2 st (THISleft, THISright)))
|       SUPER %prec TYLOW
        (ESuper (NONE, NONE, ndi2 st (SUPERleft, SUPERright)))
|       SUPER LBRACKET name RBRACKET
        (ESuper (NONE, SOME name, ndi2 st (SUPERleft, RBRACKETright)))
|       literal
        (ELit literal)
|       UNDERSCORE
        (EPlaceholder (ndi2 st (UNDERSCOREleft, UNDERSCOREright)))
|       block_expr
        (block_expr)
|       NEW new_parents %prec TYLOW
        (ENew (new_parents, NONE, ndi2 st (NEWleft, new_parentsright)))
|       NEW new_parents template_body
        (ENew (new_parents, SOME template_body,
               ndi2 st (NEWleft, template_bodyright)))
|       NEW template_body
        (ENew ([], SOME template_body, ndi2 st (NEWleft, template_bodyright)))
|       paren_group
        (paren_expr st (paren_group, paren_groupleft, paren_groupright))
|       simple_expr DOT any_id
        (ESelect (simple_expr, any_id, ndi2 st (simple_exprleft, any_idright)))
|       simple_expr DOT THIS
        (this_of st (simple_expr, simple_exprleft, THISright))
|       simple_expr DOT SUPER %prec TYLOW
        (super_of st (simple_expr, NONE, simple_exprleft, SUPERright))
|       simple_expr DOT SUPER LBRACKET name RBRACKET
        (super_of st (simple_expr, SOME name, simple_exprleft, RBRACKETright))
|       simple_expr type_args
        (ETypeApply
         (simple_expr, type_args, ndi2 st (simple_exprleft, type_argsright)))
|       simple_expr par_args
        (EApply (simple_expr, #1 par_args, #2 par_args,
                 ndi2 st (simple_exprleft, par_argsright)))
|       simple_expr block_expr
        (EApply (simple_expr, [AExpr block_expr], false,
                 ndi2 st (simple_exprleft, block_exprright)))
new_parents:
        constr_app
        ([constr_app])
|       new_parents WITH constr_app
        (new_parents @ [constr_app])
paren_group:
        LPAREN RPAREN
        ([])
|       LPAREN exprs_in_parens RPAREN
        (exprs_in_parens)
|       LPAREN exprs_in_parens COMMA RPAREN
        (exprs_in_parens)
exprs_in_parens:
        expr
        ([expr])
|       exprs_in_parens COMMA expr
        (exprs_in_parens @ [expr])
par_args:
        LPAREN RPAREN
        (([], false))
|       LPAREN exprs_in_parens RPAREN
        ((map to_arg exprs_in_parens, false))
|       LPAREN exprs_in_parens COMMA RPAREN
        ((map to_arg exprs_in_parens, false))
|       LPAREN USING exprs_in_parens RPAREN
        ((map to_arg exprs_in_parens, true))
par_argss:
        %prec TYLOW
        ([])
|       par_argss par_args
        (par_argss @ [par_args])
block_expr:
        LBRACE RBRACE
        (EBlock ([], ndi2 st (LBRACEleft, RBRACEright)))
|       LBRACE stat_list RBRACE
        (EBlock (stat_list, ndi2 st (LBRACEleft, RBRACEright)))
|       LBRACE case_clauses RBRACE
        (ECases (case_clauses, ndi2 st (LBRACEleft, RBRACEright)))
case_clauses:
        case_clause
        ([case_clause])
|       case_clauses case_clause
        (case_clauses @ [case_clause])
case_clause:
        CASE pattern opt_guard ARROW stat_seq
        (Case (pattern, opt_guard, stat_seq, ndi2 st (CASEleft, stat_seqright)))
opt_guard:
        
        (NONE)
|       IF infix_expr
        (SOME infix_expr)
pattern:
        pattern_t
        (pattern_t)
|       pattern BAR pattern_t
        ((case pattern of PAlt (ps, ni) =>
          PAlt (ps @ [pattern_t], ndi2 st (patternleft, pattern_tright)) | p =>
            PAlt ([p, pattern_t], ndi2 st (patternleft, pattern_tright))))
pattern_t:
        pattern_b
        (pattern_b)
|       name COLON refined_type
        (PTyped (varpat name, refined_type,
                 ndi2 st (nameleft, refined_typeright)))
|       UNDERSCORE COLON refined_type
        (PTyped (PWild (ndi2 st (UNDERSCOREleft, UNDERSCOREright)),
                 refined_type, ndi2 st (UNDERSCOREleft, refined_typeright)))
pattern_b:
        infix_pattern
        (infix_pattern)
|       name AT infix_pattern
        (PBind (name, infix_pattern, ndi2 st (nameleft, infix_patternright)))
infix_pattern:
        simple_pattern
        (simple_pattern)
|       infix_pattern IDENT opt_nl simple_pattern
        (PInfix (infix_pattern, mkid st (IDENT, IDENTleft, IDENTright),
                 simple_pattern,
                   ndi2 st (infix_patternleft, simple_patternright)))
|       infix_pattern OPBAR simple_pattern
        (PInfix (infix_pattern, mkid st (OPBAR, OPBARleft, OPBARright),
                 simple_pattern,
                   ndi2 st (infix_patternleft, simple_patternright)))
|       infix_pattern OPCARET simple_pattern
        (PInfix (infix_pattern, mkid st (OPCARET, OPCARETleft, OPCARETright),
                 simple_pattern,
                   ndi2 st (infix_patternleft, simple_patternright)))
|       infix_pattern OPAMP simple_pattern
        (PInfix (infix_pattern, mkid st (OPAMP, OPAMPleft, OPAMPright),
                 simple_pattern,
                   ndi2 st (infix_patternleft, simple_patternright)))
|       infix_pattern OPEQ simple_pattern
        (PInfix (infix_pattern, mkid st (OPEQ, OPEQleft, OPEQright),
                 simple_pattern,
                   ndi2 st (infix_patternleft, simple_patternright)))
|       infix_pattern OPLT simple_pattern
        (PInfix (infix_pattern, mkid st (OPLT, OPLTleft, OPLTright),
                 simple_pattern,
                   ndi2 st (infix_patternleft, simple_patternright)))
|       infix_pattern OPCOLON simple_pattern
        (PInfix (infix_pattern, mkid st (OPCOLON, OPCOLONleft, OPCOLONright),
                 simple_pattern,
                   ndi2 st (infix_patternleft, simple_patternright)))
|       infix_pattern OPCOLONL simple_pattern
        (PInfix (infix_pattern,
                 mkid st (OPCOLONL, OPCOLONLleft, OPCOLONLright),
                   simple_pattern,
                     ndi2 st (infix_patternleft, simple_patternright)))
|       infix_pattern PLUS simple_pattern
        (PInfix (infix_pattern, mkid st (PLUS, PLUSleft, PLUSright),
                 simple_pattern,
                   ndi2 st (infix_patternleft, simple_patternright)))
|       infix_pattern MINUS simple_pattern
        (PInfix (infix_pattern, mkid st (MINUS, MINUSleft, MINUSright),
                 simple_pattern,
                   ndi2 st (infix_patternleft, simple_patternright)))
|       infix_pattern OPADD simple_pattern
        (PInfix (infix_pattern, mkid st (OPADD, OPADDleft, OPADDright),
                 simple_pattern,
                   ndi2 st (infix_patternleft, simple_patternright)))
|       infix_pattern STAR simple_pattern
        (PInfix (infix_pattern, mkid st (STAR, STARleft, STARright),
                 simple_pattern,
                   ndi2 st (infix_patternleft, simple_patternright)))
|       infix_pattern OPMUL simple_pattern
        (PInfix (infix_pattern, mkid st (OPMUL, OPMULleft, OPMULright),
                 simple_pattern,
                   ndi2 st (infix_patternleft, simple_patternright)))
|       infix_pattern OPOTHER simple_pattern
        (PInfix (infix_pattern, mkid st (OPOTHER, OPOTHERleft, OPOTHERright),
                 simple_pattern,
                   ndi2 st (infix_patternleft, simple_patternright)))
|       infix_pattern TILDE simple_pattern
        (PInfix (infix_pattern, mkid st (TILDE, TILDEleft, TILDEright),
                 simple_pattern,
                   ndi2 st (infix_patternleft, simple_patternright)))
simple_pattern:
        UNDERSCORE %prec TYLOW
        (PWild (ndi2 st (UNDERSCOREleft, UNDERSCOREright)))
|       UNDERSCORE STAR
        (PSplat (PWild (ndi2 st (UNDERSCOREleft, UNDERSCOREright)),
                 ndi2 st (UNDERSCOREleft, STARright)))
|       path_pat
        (path_pattern path_pat)
|       literal
        (PLit literal)
|       MINUS INT_LIT
        (PLit (LInt ("-" ^ INT_LIT, ndi2 st (MINUSleft, INT_LITright))))
|       MINUS FLOAT_LIT
        (PLit (LFloat ("-" ^ FLOAT_LIT, ndi2 st (MINUSleft, FLOAT_LITright))))
|       LPAREN RPAREN
        (PTuple ([], ndi2 st (LPARENleft, RPARENright)))
|       LPAREN patterns RPAREN
        ((case patterns of [p] => p | ps =>
          PTuple (ps, ndi2 st (LPARENleft, RPARENright))))
|       LPAREN patterns COMMA RPAREN
        ((case patterns of [p] => p | ps =>
          PTuple (ps, ndi2 st (LPARENleft, RPARENright))))
|       path_pat arg_patterns
        (PApply (path_pat, [], arg_patterns,
                 ndi2 st (path_patleft, arg_patternsright)))
|       path_pat type_args arg_patterns
        (PApply (path_pat, type_args, arg_patterns,
                 ndi2 st (path_patleft, arg_patternsright)))
|       GIVEN refined_type
        (PGiven (refined_type, ndi2 st (GIVENleft, refined_typeright)))
path_pat:
        name
        (EIdent name)
|       path_pat DOT name
        (ESelect (path_pat, name, ndi2 st (path_patleft, nameright)))
patterns:
        pattern
        ([pattern])
|       patterns COMMA pattern
        (patterns @ [pattern])
arg_patterns:
        LPAREN RPAREN
        ([])
|       LPAREN patterns RPAREN
        (patterns)
|       LPAREN patterns COMMA RPAREN
        (patterns)
enumerators:
        opt_semis enumerator_seq opt_semis
        (enumerator_seq)
enumerator_seq:
        enumerator
        ([enumerator])
|       enumerator_seq semis enumerator
        (enumerator_seq @ [enumerator])
|       enumerator_seq IF infix_expr
        (enumerator_seq
         @ [EnGuard (infix_expr, ndi2 st (IFleft, infix_exprright))])
enumerator:
        pattern_t LARROW expr
        (EnGen (false, pattern_t, expr, ndi2 st (pattern_tleft, exprright)))
|       CASE pattern_t LARROW expr
        (EnGen (true, pattern_t, expr, ndi2 st (CASEleft, exprright)))
|       IF infix_expr
        (EnGuard (infix_expr, ndi2 st (IFleft, infix_exprright)))
|       pattern_t EQUALS expr
        (EnVal (pattern_t, expr, ndi2 st (pattern_tleft, exprright)))
stat_seq:
        %prec TYLOW
        ([])
|       stat_list
        (stat_list)
stat_list:
        stat_seq_ne %prec TYLOW
        (stat_seq_ne)
|       semis %prec TYLOW
        ([])
|       semis stat_seq_ne %prec TYLOW
        (stat_seq_ne)
stat_seq_ne:
        stat
        ([stat])
|       stat_seq_ne semis stat
        (stat_seq_ne @ [stat])
|       stat_seq_ne semis %prec TYLOW
        (stat_seq_ne)
stat:
        IMPORT import_exprs
        (SImport (false, import_exprs, ndi2 st (IMPORTleft, import_exprsright)))
|       EXPORT import_exprs
        (SImport (true, import_exprs, ndi2 st (EXPORTleft, import_exprsright)))
|       PACKAGE package_path
        (SDef (DPackage
               (package_path, NONE, ndi2 st (PACKAGEleft, package_pathright))))
|       PACKAGE package_path LBRACE stat_seq RBRACE
        (SDef (DPackage
               (package_path, SOME stat_seq,
                ndi2 st (PACKAGEleft, RBRACEright))))
|       PACKAGE OBJECT class_def
        (SDef (class_def KPackageObject (PACKAGEleft, [], [])))
|       definition
        (SDef (definition (definitionleft, [], [])))
|       mods_ne definition
        (SDef (definition (mods_neleft, #1 mods_ne, #2 mods_ne)))
|       EXTENSION def_clauses_ne ext_body
        (SDef (DExtension
               (def_clauses_ne, ext_body,
                ndi2 st (EXTENSIONleft, ext_bodyright))))
|       expr_nb
        (SExpr expr_nb)
|       lam_params stat_seq
        (SExpr (ELambda
                (#1 lam_params,
                 EBlock (stat_seq, ndi2 st (lam_paramsleft, stat_seqright)),
                   #2 lam_params, ndi2 st (lam_paramsleft, stat_seqright))))
package_path:
        name
        (EIdent name)
|       package_path DOT name
        (ESelect (package_path, name, ndi2 st (package_pathleft, nameright)))
ext_body:
        LBRACE stat_seq RBRACE
        (stat_seq)
|       definition
        ([SDef (definition (definitionleft, [], []))])
|       mods_ne definition
        ([SDef (definition (mods_neleft, #1 mods_ne, #2 mods_ne))])
definition:
        VAL pattern2_list opt_ptype opt_peq
        ((fn (l, an, ms) =>
          DVal (an, ms, false, pattern2_list, opt_ptype, opt_peq,
                ndi2 st (l, opt_peqright))))
|       VAR pattern2_list opt_ptype opt_peq
        ((fn (l, an, ms) =>
          DVal (an, ms, true, pattern2_list, opt_ptype, opt_peq,
                ndi2 st (l, opt_peqright))))
|       DEF any_id def_clauses opt_colon_type opt_eq_expr
        ((fn (l, an, ms) =>
          DDef (an, ms, any_id, def_clauses, opt_colon_type, opt_eq_expr,
                ndi2 st (l, opt_eq_exprright))))
|       DEF THIS def_clauses EQUALS expr
        ((fn (l, an, ms) =>
          DDef (an, ms, mkid st ("this", THISleft, THISright), def_clauses,
                NONE, SOME expr, ndi2 st (l, exprright))))
|       TYPE opt_nl name opt_hk opt_bounds
        ((fn (l, an, ms) =>
          DType (an, ms, name,
                 (case opt_hk of [] => [] | tps =>
                  [TClause (tps, ndi2 st (opt_hkleft, opt_hkright))]),
                    opt_bounds, NONE, ndi2 st (l, opt_boundsright))))
|       TYPE opt_nl name opt_hk opt_bounds EQUALS typ
        ((fn (l, an, ms) =>
          DType (an, ms, name,
                 (case opt_hk of [] => [] | tps =>
                  [TClause (tps, ndi2 st (opt_hkleft, opt_hkright))]),
                    opt_bounds, SOME typ, ndi2 st (l, typright))))
|       CLASS class_def
        ((fn pos => class_def KClass pos))
|       CASEMOD CLASS class_def
        ((fn pos => class_def KCaseClass pos))
|       TRAIT class_def
        ((fn pos => class_def KTrait pos))
|       OBJECT class_def
        ((fn pos => class_def KObject pos))
|       CASEMOD OBJECT class_def
        ((fn pos => class_def KCaseObject pos))
|       ENUM class_def
        ((fn pos => class_def KEnum pos))
|       GIVEN given_def
        (given_def)
|       ENUMCASE enum_case
        (enum_case)
pattern2_list:
        pattern_b
        ([pattern_b])
|       pattern2_list COMMA pattern_b
        (pattern2_list @ [pattern_b])
opt_ptype:
        
        (NONE)
|       COLON typ
        (SOME typ)
opt_peq:
        
        (NONE)
|       EQUALS expr
        (SOME expr)
opt_colon_type:
        
        (NONE)
|       COLON typ
        (SOME typ)
opt_eq_expr:
        
        (NONE)
|       EQUALS expr
        (SOME expr)
def_clauses:
        
        ([])
|       def_clauses def_clause
        (def_clauses @ [def_clause])
def_clauses_ne:
        def_clause
        ([def_clause])
|       def_clauses_ne def_clause
        (def_clauses_ne @ [def_clause])
def_clause:
        LBRACKET tparams RBRACKET
        (TClause (tparams, ndi2 st (LBRACKETleft, RBRACKETright)))
|       LPAREN RPAREN
        (PClause (CPlain, [], ndi2 st (LPARENleft, RPARENright)))
|       LPAREN dparams RPAREN
        (PClause (CPlain, dparams, ndi2 st (LPARENleft, RPARENright)))
|       LPAREN dparams COMMA RPAREN
        (PClause (CPlain, dparams, ndi2 st (LPARENleft, RPARENright)))
|       LPAREN IMPLICIT dparams RPAREN
        (PClause (CImplicit, dparams, ndi2 st (LPARENleft, RPARENright)))
|       LPAREN USING dparams RPAREN
        (PClause (CUsing, dparams, ndi2 st (LPARENleft, RPARENright)))
|       LPAREN USING fun_arg_types RPAREN
        (PClause (CUsing, map (anon_param st) fun_arg_types,
                  ndi2 st (LPARENleft, RPARENright)))
given_clause:
        LBRACKET tparams RBRACKET
        (TClause (tparams, ndi2 st (LBRACKETleft, RBRACKETright)))
|       LPAREN dparams RPAREN
        (PClause (CPlain, dparams, ndi2 st (LPARENleft, RPARENright)))
|       LPAREN dparams COMMA RPAREN
        (PClause (CPlain, dparams, ndi2 st (LPARENleft, RPARENright)))
|       LPAREN IMPLICIT dparams RPAREN
        (PClause (CImplicit, dparams, ndi2 st (LPARENleft, RPARENright)))
|       LPAREN USING dparams RPAREN
        (PClause (CUsing, dparams, ndi2 st (LPARENleft, RPARENright)))
|       LPAREN USING fun_arg_types RPAREN
        (PClause (CUsing, map (anon_param st) fun_arg_types,
                  ndi2 st (LPARENleft, RPARENright)))
given_clauses_ne:
        given_clause
        ([given_clause])
|       given_clauses_ne given_clause
        (given_clauses_ne @ [given_clause])
dparams:
        dparam
        ([dparam])
|       dparams COMMA dparam
        (dparams @ [dparam])
dparam:
        name COLON param_type opt_default
        (Param ([], [], 0, SOME name, param_type, opt_default,
                ndi2 st (nameleft, opt_defaultright)))
|       dparam_pre name COLON param_type opt_default
        (Param (#1 dparam_pre, #2 dparam_pre, 0, SOME name, param_type,
                opt_default, ndi2 st (dparam_preleft, opt_defaultright)))
opt_default:
        
        (NONE)
|       EQUALS expr
        (SOME expr)
cparam_clauses:
        
        ([])
|       cparam_clauses cparam_clause
        (cparam_clauses @ [cparam_clause])
cparam_clause:
        LPAREN RPAREN
        (PClause (CPlain, [], ndi2 st (LPARENleft, RPARENright)))
|       LPAREN cparams RPAREN
        (PClause (CPlain, cparams, ndi2 st (LPARENleft, RPARENright)))
|       LPAREN cparams COMMA RPAREN
        (PClause (CPlain, cparams, ndi2 st (LPARENleft, RPARENright)))
|       LPAREN IMPLICIT cparams RPAREN
        (PClause (CImplicit, cparams, ndi2 st (LPARENleft, RPARENright)))
|       LPAREN USING cparams RPAREN
        (PClause (CUsing, cparams, ndi2 st (LPARENleft, RPARENright)))
|       LPAREN USING fun_arg_types RPAREN
        (PClause (CUsing, map (anon_param st) fun_arg_types,
                  ndi2 st (LPARENleft, RPARENright)))
cparams:
        cparam
        ([cparam])
|       cparams COMMA cparam
        (cparams @ [cparam])
cparam:
        name COLON param_type opt_default
        (Param ([], [], 0, SOME name, param_type, opt_default,
                ndi2 st (nameleft, opt_defaultright)))
|       cparam_head name COLON param_type opt_default
        (Param (#1 cparam_head, #2 cparam_head, #3 cparam_head, SOME name,
                param_type, opt_default,
                  ndi2 st (cparam_headleft, opt_defaultright)))
cparam_head:
        cmods_ne %prec TYLOW
        ((#1 cmods_ne, #2 cmods_ne, 0))
|       VAL
        (([], [], 1))
|       VAR
        (([], [], 2))
|       cmods_ne VAL
        ((#1 cmods_ne, #2 cmods_ne, 1))
|       cmods_ne VAR
        ((#1 cmods_ne, #2 cmods_ne, 2))
class_def:
        name opt_tparams_clause opt_ctor_mods cparam_clauses opt_template
        ((fn kind => fn (l, an, ms) =>
          DClass (an, ms, kind, name, opt_tparams_clause, opt_ctor_mods,
                  cparam_clauses,
                    Template (#1 opt_template, [], #2 opt_template,
                              ndi2 st (nameleft, opt_templateright)),
                                ndi2 st (l, opt_templateright))))
opt_tparams_clause:
        
        ([])
|       LBRACKET tparams RBRACKET
        (tparams)
opt_ctor_mods:
        
        ([])
|       modifier
        ([modifier])
opt_template:
        
        (([], NONE))
|       opt_extends_parents
        ((opt_extends_parents, NONE))
|       template_body
        (([], SOME template_body))
|       opt_extends_parents template_body
        ((opt_extends_parents, SOME template_body))
opt_extends_parents:
        EXTENDS constr_apps
        (constr_apps)
template_body:
        LBRACE stat_seq RBRACE
        (case stat_seq of
           [SExpr (ELambda ([Binding (SOME nm, NONE, bni)],
                            EBlock (rest, _), false, _))] =>
             TemplateBody (SOME (Self (nm, NONE, bni)), rest,
                           ndi2 st (LBRACEleft, RBRACEright))
         | _ => TemplateBody (NONE, stat_seq,
                              ndi2 st (LBRACEleft, RBRACEright)))
|       LBRACE self_type stat_seq RBRACE
        (TemplateBody
         (SOME self_type, stat_seq, ndi2 st (LBRACEleft, RBRACEright)))
self_type:
        name COLON infix_type ARROW
        (Self (name, SOME infix_type, ndi2 st (nameleft, ARROWright)))
|       THIS COLON infix_type ARROW
        (Self (mkid st ("this", THISleft, THISright), SOME infix_type,
               ndi2 st (THISleft, ARROWright)))
constr_apps:
        constr_app
        ([constr_app])
|       constr_apps COMMA constr_app
        (constr_apps @ [constr_app])
|       constr_apps WITH constr_app
        (constr_apps @ [constr_app])
constr_app:
        simple_type par_argss %prec TYLOW
        (Parent (simple_type, map #1 par_argss, map #2 par_argss,
                 ndi2 st (simple_typeleft, par_argssright)))
enum_case:
        name opt_tparams_clause cparam_clauses
        ((fn (l, an, ms) =>
          DEnumCase
            (an, ms, [name], opt_tparams_clause, cparam_clauses, [],
             ndi2 st (l, cparam_clausesright))))
|       name opt_tparams_clause cparam_clauses EXTENDS constr_apps
        ((fn (l, an, ms) =>
          DEnumCase
            (an, ms, [name], opt_tparams_clause, cparam_clauses, constr_apps,
             ndi2 st (l, constr_appsright))))
|       name COMMA names_comma
        ((fn (l, an, ms) =>
          DEnumCase
            (an, ms, name
             :: names_comma, [], [], [], ndi2 st (l, names_commaright))))
names_comma:
        name
        ([name])
|       names_comma COMMA name
        (names_comma @ [name])
given_def:
        name COLON infix_type given_tail
        ((fn (l, an, ms) =>
          DGiven (an, ms, SOME name, [], infix_type, #1 given_tail,
                  #2 given_tail, [], ndi2 st (l, given_tailright))))
|       infix_type given_tail
        ((fn (l, an, ms) =>
          DGiven (an, ms, NONE, [], infix_type, #1 given_tail, #2 given_tail,
                  [], ndi2 st (l, given_tailright))))
|       given_clauses_ne COLON infix_type given_tail
        ((fn (l, an, ms) =>
          DGiven (an, ms, NONE, given_clauses_ne, infix_type, #1 given_tail,
                  #2 given_tail, [], ndi2 st (l, given_tailright))))
given_tail:
        EQUALS expr
        ((SOME expr, NONE))
|       template_body
        ((NONE, SOME template_body))
|       WITH template_body
        ((NONE, SOME template_body))
import_exprs:
        import_expr
        ([import_expr])
|       import_exprs COMMA import_expr
        (import_exprs @ [import_expr])
import_path:
        name
        (EIdent name)
|       import_path DOT name
        (ESelect (import_path, name, ndi2 st (import_pathleft, nameright)))
import_expr:
        import_path
        (import_of_path st (import_path, import_pathleft, import_pathright))
|       import_path DOT import_spec
        (ImportExpr
         (import_path, import_spec,
          ndi2 st (import_pathleft, import_specright)))
|       import_path AS name
        (import_as st (import_path, name, import_pathleft, nameright))
import_spec:
        STAR
        ([SelWild (ndi2 st (STARleft, STARright))])
|       UNDERSCORE
        ([SelWild (ndi2 st (UNDERSCOREleft, UNDERSCOREright))])
|       GIVEN
        ([SelGiven (NONE, ndi2 st (GIVENleft, GIVENright))])
|       GIVEN infix_type
        ([SelGiven (SOME infix_type, ndi2 st (GIVENleft, infix_typeright))])
|       LBRACE selectors RBRACE
        (selectors)
|       LBRACE selectors COMMA RBRACE
        (selectors)
selectors:
        selector
        ([selector])
|       selectors COMMA selector
        (selectors @ [selector])
selector:
        name
        (SelName (name, NONE, nodeInfo_of_ident name))
|       name AS name
        (SelName (name1, SOME name2, ndi2 st (name1left, name2right)))
|       name AS UNDERSCORE
        (SelName (name, SOME (mkid st ("_", UNDERSCOREleft, UNDERSCOREright)),
                  ndi2 st (nameleft, UNDERSCOREright)))
|       name ARROW name
        (SelName (name1, SOME name2, ndi2 st (name1left, name2right)))
|       name ARROW UNDERSCORE
        (SelName (name, SOME (mkid st ("_", UNDERSCOREleft, UNDERSCOREright)),
                  ndi2 st (nameleft, UNDERSCOREright)))
|       STAR
        (SelWild (ndi2 st (STARleft, STARright)))
|       UNDERSCORE
        (SelWild (ndi2 st (UNDERSCOREleft, UNDERSCOREright)))
|       GIVEN
        (SelGiven (NONE, ndi2 st (GIVENleft, GIVENright)))
|       GIVEN infix_type
        (SelGiven (SOME infix_type, ndi2 st (GIVENleft, infix_typeright)))
compilation_unit:
        stat_seq
        (stat_seq)
\<close>

text\<open>
  \<^verbatim>\<open>Scala3_Parse\<close> runs the generated lexer/parser pair on a source, from one of
  four entry points (a compilation unit, an expression, a type, a name: a
  synthetic first token selects the grammar's start, as for occam 2), through
  the layout stream described in the introduction. Every call creates its own
  \<^verbatim>\<open>Scala3_State\<close>, so calls are independent and may run concurrently.

  The layout stream inserts a \<open>NEWLINE\<close> token between two real tokens \<open>t1\<close> and
  \<open>t2\<close> exactly if

  \<^enum> at least one newline separates them (the lexer counts them, comments
    included), and
  \<^enum> \<open>t1\<close> can end a statement (an identifier, a literal, \<open>this\<close>, \<open>null\<close>, \<open>true\<close>,
    \<open>false\<close>, \<open>return\<close>, \<open>type\<close>, \<open>_\<close>, a closing bracket - and \<open>*\<close> after a dot, the
    wildcard import), and
  \<^enum> \<open>t2\<close> can begin one (everything except \<open>catch else extends finally match with
    yield , . ; : = => <- <: >: # [ ) ] }\<close> and \<open>then do =>> ?=>\<close>), and
  \<^enum> the innermost open bracket is a brace or none (newlines are disabled inside
    parentheses and brackets, and between \<open>case\<close> and its \<open>=>\<close>), and
  \<^enum> \<open>t2\<close> is not a \<open>{\<close> after a single newline, and
  \<^enum> \<open>t2\<close> is not a leading infix operator (followed on its line by an operand; for
    \<open>+\<close> and \<open>-\<close> only with a blank after the operator). A \<open>case\<close> opens a \<open>case
    ... =>\<close> region only if a \<open>=>\<close> follows on the same logical line - which tells
    a match clause from an enum case.

\<close>

ML\<open>
structure Scala3_Parse = struct

structure P = Scala3.Scala3Parser
structure T = Scala3.Scala3LrVals.Tokens

datatype entry = Entry_Unit | Entry_Expr | Entry_Type | Entry_Id

fun entry_token Entry_Unit p = T.ENTRY_UNIT (p, p)
  | entry_token Entry_Expr p = T.ENTRY_EXPR (p, p)
  | entry_token Entry_Type p = T.ENTRY_TYPE (p, p)
  | entry_token Entry_Id p = T.ENTRY_ID (p, p)

val soft_modifier_kinds = ["INFIX", "INLINE", "OPAQUE", "OPEN", "TRANSPARENT"]

val modifier_follow_kinds =
  ["VAL", "VAR", "DEF", "TYPE", "CLASS", "TRAIT", "OBJECT", "ENUM", "GIVEN",
   "CASE", "CASEMOD", "ABSTRACT", "FINAL", "SEALED", "IMPLICIT", "LAZY",
   "OVERRIDE", "PRIVATE", "PROTECTED"] @ soft_modifier_kinds

val can_end_kinds =
  ["IDENT", "INT_LIT", "FLOAT_LIT", "CHAR_LIT", "STRING_LIT", "INTERP_LIT",
   "THIS", "NULL", "TRUE",
   "FALSE", "RETURN", "TYPE", "UNDERSCORE", "RPAREN", "RBRACKET", "RBRACE",
     "AS", "EXTENSION", "INFIX",
   "INLINE", "OPAQUE", "OPEN", "TRANSPARENT", "USING"]

val cannot_begin_kinds =
  ["CATCH", "ELSE", "EXTENDS", "FINALLY", "MATCH", "WITH", "YIELD", "COMMA",
   "DOT", "SEMI", "COLON",
   "EQUALS", "ARROW", "LARROW", "SUBTYPE", "SUPERTYPE", "HASH", "LBRACKET",
     "RPAREN", "RBRACKET",
   "RBRACE", "THEN", "DO", "TYARROW", "CTXARROW"]

val infix_kinds =
  ["PLUS", "MINUS", "STAR", "BAR", "OPBAR", "OPCARET", "OPAMP", "OPEQ", "OPLT",
   "OPCOLON", "OPCOLONL",
   "OPADD", "OPMUL", "OPOTHER"]

datatype region = RParen | RBrace | RCase

(* "err" is the parser's usual error callback. *)
fun layout_stream err entry st raw_lex pos eof_pos =
  let
    val eof_tok = T.EOF (eof_pos, eof_pos)
    fun nl_tok p = T.NEWLINE (p, p)

    val queue = Unsynchronized.ref [entry_token entry (pos 0)]
    val buf : ((P.svalue, P.pos) P.Token.token * Scala3_State.layout) list
      Unsynchronized.ref =
      Unsynchronized.ref []
    val regions : region list Unsynchronized.ref = Unsynchronized.ref []
    val prev_kind = Unsynchronized.ref ""
    val prev2_kind = Unsynchronized.ref ""
    val prev_stop = Unsynchronized.ref 0
    val eof_seen = Unsynchronized.ref false

    fun read_raw () =
      let
        val tok = raw_lex ()
        val lay = Scala3_Layout.get st
        val _ = Scala3_Layout.clear_newlines st
        val is_eof = P.sameToken (tok, eof_tok)
      in (tok, if is_eof
          then {nl = #nl lay, start = #stop lay, stop = #stop lay, kind =
                "EOF"} else lay) end

    fun take_raw () =
      (case !buf of
         x :: xs => (buf := xs; x)
       | [] => read_raw ())

    (* the i-th token (0-based) after the current one, without consuming it *)
    fun peek i =
      let
        fun fill () = if length (!buf) > i then ()
          else (buf := !buf @ [read_raw ()]; fill ())
        val _ = fill ()
      in nth (!buf) i end

    fun can_end kind =
      member (op =) can_end_kinds kind
        orelse (kind = "STAR" andalso !prev2_kind = "DOT")
    val can_begin = not o member (op =) cannot_begin_kinds

    fun newlines_enabled () =
      (case !regions of RParen :: _ => false | RCase :: _ => false | _ => true)

    (* a line that starts with an infix operator continues the previous line, if
       an operand follows on the same line *)
    fun leading_infix (lay : Scala3_State.layout) =
      member (op =) infix_kinds (#kind lay) andalso
        let val (_, lay2) = peek 0
        in #kind lay2 <> "EOF" andalso #nl lay2 = 0 andalso
           (not (member (op =) ["PLUS", "MINUS"] (#kind lay))
            orelse #stop lay < #start lay2)
        end

    (* A "case" starts a match clause if a "=>" follows, outside nested
       brackets, before the end of the logical line; a generator ("for (case p
       <- e)") if a "<-" does; otherwise it is the beginning of an enum case. *)
    datatype case_kind = Clause | Generator | Enum_case
    val stop_kinds =
      ["DEF", "VAL", "VAR", "TYPE", "CLASS", "TRAIT", "OBJECT", "ENUM",
       "GIVEN", "IMPORT", "EXPORT",
       "PACKAGE", "CASE", "CASEMOD", "ABSTRACT", "FINAL", "SEALED", "IMPLICIT",
         "LAZY", "OVERRIDE", "PRIVATE",
       "PROTECTED", "EQUALS", "EXTENDS"]
    fun classify_case () =
      let
        fun scan i depth =
          if i > 600 then Enum_case
          else
            let val (_, l) = peek i
            in
              (case #kind l of
                 "EOF" => Enum_case
               | k =>
                   if k = "LPAREN" orelse k = "LBRACKET"
                     then scan (i + 1) (depth + 1)
                   else if k = "RPAREN" orelse k = "RBRACKET" then
                     (if depth = 0 then Enum_case else scan (i + 1) (depth - 1))
                   else if depth = 0 andalso k = "ARROW" then Clause
                   else if depth = 0 andalso k = "LARROW" then Generator
                   else if depth = 0
                     andalso (k = "LBRACE" orelse k = "RBRACE" orelse k =
                              "SEMI" orelse
                                              member (op =) stop_kinds k)
                                                then Enum_case
                   else scan (i + 1) depth)
            end
      in scan 0 0 end

    (* One of the five soft words is a modifier, not a name, if what follows is
       a modifier, a definition keyword or an annotation (written as "@a", not
       as a pattern binder "x @ p"), or a parameter name and a colon
       ("inline x: Int"), on the same line: a word that ends a line ends a
       statement, as the name it is. *)
    fun is_soft_modifier (lay0 : Scala3_State.layout) =
      member (op =) soft_modifier_kinds (#kind lay0) andalso
        let
          val (_, l1) = peek 0
          val k1 = #kind l1
        in
          #nl l1 = 0 andalso
          (member (op =) modifier_follow_kinds k1
          orelse (k1 = "AT" andalso #start l1 > #stop lay0
                  andalso #start (#2 (peek 1)) = #stop l1)
          orelse (k1 = "IDENT" andalso #kind (#2 (peek 1)) = "COLON"))
        end

    fun update_regions (lay : Scala3_State.layout) =
      (case #kind lay of
         "LPAREN" => regions := RParen :: !regions
       | "LBRACKET" => regions := RParen :: !regions
       | "RPAREN" => regions := drop_close RParen (!regions)
       | "RBRACKET" => regions := drop_close RParen (!regions)
       | "LBRACE" => regions := RBrace :: !regions
       | "RBRACE" => regions := drop_close RBrace (!regions)
       | "ARROW" =>
         (case !regions of RCase :: rest => regions := rest | _ => ())
       | "CASE" => regions := RCase :: !regions
       | _ => ())
    and drop_close r regs =
      (case regs of
         [] => []
       | x :: rest =>
         if x = r then rest else if r = RBrace orelse x <> RBrace
           then drop_close r rest else regs)

    fun next () =
      (case !queue of
         t :: ts => (queue := ts; t)
       | [] =>
           if !eof_seen then eof_tok
           else
             let
               val (tok0, lay0) = take_raw ()
               val is_casemod =
                 #kind lay0 = "CASE"
                   andalso member (op =) ["CLASS", "OBJECT"]
                     (#kind (#2 (peek 0)))
               val is_softmod = is_soft_modifier lay0
               val case_kind = if #kind lay0 = "CASE" andalso not is_casemod
                 then SOME (classify_case ()) else NONE
               val (tok, lay) =
                 if is_casemod
                 then (T.CASEMOD (pos (#start lay0), pos (#stop lay0)),
                       {nl = #nl lay0, start = #start lay0, stop =
                        #stop lay0, kind = "CASEMOD"})
                 else if is_softmod
                 then (T.SOFTMOD (#kind lay0, pos (#start lay0),
                                  pos (#stop lay0)), lay0)
                 else if case_kind = SOME Enum_case
                 then (T.ENUMCASE (pos (#start lay0), pos (#stop lay0)),
                       {nl = #nl lay0, start = #start lay0, stop =
                        #stop lay0, kind = "ENUMCASE"})
                 else if case_kind = SOME Generator
                 then (tok0,
                       {nl = #nl lay0, start = #start lay0, stop =
                        #stop lay0, kind = "CASEGEN"})
                 else (tok0, lay0)
             in
               if #kind lay = "EOF" then (eof_seen := true; eof_tok)
               else
                 let
                   val kind = #kind lay
                   val need_nl =
                     #nl lay >= 1 andalso !prev_kind <> ""
                       andalso can_end (!prev_kind) andalso can_begin kind
                     andalso newlines_enabled ()
                     andalso not (kind = "LBRACE" andalso #nl lay = 1)
                     andalso not (leading_infix lay)
                   val before = if need_nl then [nl_tok (pos (!prev_stop))]
                     else []
                 in
                   update_regions lay;
                   prev2_kind := !prev_kind;
                   prev_kind := kind;
                   prev_stop := #stop lay;
                   queue := before @ [tok];
                   next ()
                 end
             end)
  in P.Stream.streamify next end

(* Runs the parser on "source" from the given entry point; "mk_err" makes the
   parser's error callback from the parse's state. Every parse creates its own
   state. *)
fun parse mk_err entry ctxt source =
  let
    val st = Scala3_State.init ctxt source
    val err = mk_err st
    val input_text = Lex_yacc_state.text_of (#base st)
    val consumed = Unsynchronized.ref false
    fun input_string _ = if !consumed then ""
      else (consumed := true; input_text)
    val raw_lex = Scala3.Scala3Lex.makeLexer input_string st
    val pos = Lex_yacc_state.get_pos (#base st)
    val eof_pos = pos (String.size input_text)
    val stream = layout_stream err entry st raw_lex pos eof_pos
    val (result, _) = P.parse (0, stream, err, st)
      handle Fail msg => (err (msg, pos 0, pos 0); raise Fail msg)
    val _ = (case !(#lex_error st) of SOME (msg, p) =>
             err (msg, p, p) | NONE => ())
  in result end

fun parse_loud entry ctxt source =
  parse (fn st => Lex_yacc_state.print_error (#base st)) entry ctxt source

(* The silent variant the "_reject" commands use: a locally declared exception,
   not the library's "print_error" (which reports PIDE error markup before
   raising, and raises an exception Isabelle/ML cannot reliably catch by
   identity across the SML sandbox boundary). *)
exception Rejected of string
fun quiet_error (s : string, _ : Position.T, _ : Position.T) = raise Rejected s

fun parse_quiet entry ctxt source = parse (K quiet_error) entry ctxt source

end
\<close>

end
