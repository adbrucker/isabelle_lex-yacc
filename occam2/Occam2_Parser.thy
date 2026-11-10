theory Occam2_Parser
  imports "../Isabelle_Lex-Yacc/LexYacc" "Occam2_Ast"
begin

section\<open>Lexer and Parser for occam 2\<close>

text\<open>
  This theory formalizes the occam 2 grammar of the INMOS \<^emph>\<open>occam 2 Reference Manual\<close>
  (appendix G, "Syntax summary") as an ml-lex/ml-yacc lexer/parser pair, built, exactly
  like \<^verbatim>\<open>C11_Parser.thy\<close> is, with this repository's own \<^verbatim>\<open>ml_lex_yacc\<close> command. Two
  things set occam apart from C and drive everything unusual below.

  \<^enum> \<^bold>\<open>Layout is syntax.\<close> A process is a keyword line followed by its component
    processes, one per line, indented two spaces further; there are no braces or
    \<open>end\<close> keywords. The grammar therefore wants explicit \<open>NEWLINE\<close>, \<open>INDENT\<close> and
    \<open>OUTDENT\<close> tokens, which no regular expression can produce on its own (a
    single dedent can close several nested blocks at once, and ml-lex's \<open>lex()\<close>
    hands back exactly one token per call). The lexer instead only \<^emph>\<open>records\<close>
    the indentation of each new line (\<open>Occam2_Layout\<close>, below), and a thin stream
    wrapper (\<open>Occam2_Parse\<close>, at the end of this theory) turns those records into
    layout tokens, in front of the next real token, with an indentation stack:
    a deeper line yields \<open>NEWLINE INDENT\<close>, an equally deep one \<open>NEWLINE\<close>, a
    shallower one \<open>NEWLINE OUTDENT\<close>\<open>\<^sup>+\<close> (one \<open>OUTDENT\<close> per level closed, which
    must land exactly on an enclosing level), and the end of input closes every
    open level. Doing this \<^emph>\<open>lazily\<close> - when the next real token arrives - makes
    blank lines and comment-only lines harmless by construction: only the
    indentation of the line the next token actually sits on is ever used.
    A line is a \<^emph>\<open>continuation line\<close>, and produces no layout tokens at all, when
    the previous token is one the manual allows a statement to be broken after:
    an operator, a comma, a semicolon, an assignment, or one of \<open>IS\<close>, \<open>FROM\<close>,
    \<open>FOR\<close> (the lexer flags those tokens as it creates them).
  \<^enum> \<^bold>\<open>There is no operator precedence.\<close> The manual's grammar for expressions is
    \<open>operand dyadic.operator operand\<close>, with every larger expression bracketed
    explicitly; the only chaining allowed is a run of \<open>AND\<close>s or a run of \<open>OR\<close>s.
    The yacc grammar below mirrors that directly, and so needs no \<open>%left\<close>
    declarations at all.

  Everything the C11 front-end gives its comments carries over unchanged: a
  \<open>--\<close> comment may contain \<open>@tag(level)[navi] \<open>...\<close>\<close> antiquotations (the
  same lexical shape as C11's \<open>//@ ...\<close>), collected as they are lexed
  (\<open>Occam2_Comments\<close>) and attached to the AST node of whichever real token
  follows. A comment body may span lines (it is a cartouche), so, unlike an
  ordinary \<open>--\<close> comment, it can legitimately contain newlines without those
  counting as layout.

  Entry points: occam has no single obvious start symbol (a program unit is a run
  of specifications followed by a process, but a bare expression or a bare name
  is also a useful thing to check), and \<open>f(x)\<close> is simultaneously a valid
  procedure instance \<^emph>\<open>and\<close> a valid function-call expression. Rather than letting
  ml-yacc resolve such overlaps by accident, the stream wrapper prepends one of
  three synthetic entry tokens (\<open>ENTRY_UNIT\<close>, \<open>ENTRY_EXPR\<close>, \<open>ENTRY_ID\<close>) chosen by the
  calling command, so each entry point has a grammar of its own.
\<close>

ML\<open>
(* Everything the lexer and the grammar actions need to remember during one parse lives in
   one state object, created per parse ("init") and handed to the lexer (ML-Lex %arg) and
   the parser (ML-Yacc %arg) by the "[state]" mode of ml_lex_yacc - nothing is shared
   between parses, so any number can run at once. (The previous versions of this theory kept
   the same data in process-wide variables, which two simultaneous parses corrupted.)
     base        - the library's own part: source, context, position table
     pending     - comments lexed since the previous real token
     attached    - the comments that have been attached to a token position
     layout      - the layout recorder, see "Occam2_Layout"
     antiq_*     - the antiquotation scanner (see the lexer below): nesting depth of the
                   cartouche being skipped, the most recent tag, the body text so far and
                   its start position *)
structure Occam2_State = struct
  type comments = Position.T Occam2_Ast.comment list
  type layout = {nl_seen: bool, indent: int, start: int, stop: int, cont: bool}
  val layout_init : layout = {nl_seen = false, indent = 0, start = 0, stop = 0, cont = false}

  type T = {base : Lex_yacc_state.T,
            pending : comments Unsynchronized.ref,
            attached : (Position.T * comments) list Unsynchronized.ref,
            layout : layout Unsynchronized.ref,
            antiq_depth : int Unsynchronized.ref,
            antiq_tag : (string * Occam2_Ast.navi list * int * Position.T) Unsynchronized.ref,
            antiq_buf : string list Unsynchronized.ref,
            antiq_start : Position.T Unsynchronized.ref}

  fun init ctxt source : T =
    {base = Lex_yacc_state.init ctxt source,
     pending = Unsynchronized.ref [],
     attached = Unsynchronized.ref [],
     layout = Unsynchronized.ref layout_init,
     antiq_depth = Unsynchronized.ref 0,
     antiq_tag = Unsynchronized.ref ("", [], 0, Position.none),
     antiq_buf = Unsynchronized.ref [],
     antiq_start = Unsynchronized.ref Position.none}
end

(* The comments/antiquotations collected while lexing, attached to whichever
   real token follows (mirrors C11_Comments - see its rationale in C11_Parser.thy). *)
structure Occam2_Comments = struct
  fun push (st : Occam2_State.T) c = #pending st := !(#pending st) @ [c]

  fun push_raw st (text, pos) =
    if List.all Char.isSpace (String.explode text) then ()
    else push st (Occam2_Ast.Raw_txt [(text, pos)])

  fun push_antiquotation st tag navi level cartouche =
    push st (Occam2_Ast.Antiquotation (tag, navi, level, cartouche))

  fun attach_pending (st : Occam2_State.T) (p : Position.T) =
    (case !(#pending st) of
       [] => ()
     | cs => (#pending st := []; #attached st := (p, cs) :: !(#attached st)))

  (* Non-destructive on purpose, for the same reason as in C11: several grammar
     rules build a nodeInfo for the same leftmost token, and only some of those
     nodes are ever walked for antiquotations. *)
  fun claim (st : Occam2_State.T) (p : Position.T) : Position.T Occam2_Ast.comment list =
    (case AList.lookup (op =) (!(#attached st)) p of NONE => [] | SOME cs => cs)

  fun mk_nodeInfo st (claimed_at : Position.T) (report_pos : Position.T) : Position.T Occam2_Ast.nodeInfo =
    (case claim st claimed_at of
       [] => Occam2_Ast.OnlyPos report_pos
     | cs => Occam2_Ast.NodeInfo (cs, report_pos))
end

(* Layout bookkeeping shared between the lexer actions and the stream wrapper.
   The lexer only ever records facts here; it never emits a layout token itself:
     nl_seen  - a newline was lexed since the previous real token
     indent   - the number of leading blanks of the line the newest newline began
                (an earlier line's value is simply overwritten by a later one, so
                blank and comment-only lines cost nothing)
     start/stop - character offsets of the newest real token
     cont     - whether that token is one a statement may be broken after *)
structure Occam2_Layout = struct
  fun get (st : Occam2_State.T) = !(#layout st)

  fun newline (st : Occam2_State.T) indent =
    let val {start, stop, cont, ...} = get st
    in #layout st := {nl_seen = true, indent = indent, start = start, stop = stop, cont = cont} end

  fun token (st : Occam2_State.T) (start, stop, cont) =
    let val {nl_seen, indent, ...} = get st
    in #layout st := {nl_seen = nl_seen, indent = indent, start = start, stop = stop, cont = cont} end

  fun clear_newline (st : Occam2_State.T) =
    let val {indent, start, stop, cont, ...} = get st
    in #layout st := {nl_seen = false, indent = indent, start = start, stop = stop, cont = cont} end
end
\<close>
SML_import \<open>structure Occam2_State = struct open Occam2_State end\<close>
SML_import \<open>structure Occam2_Ast = struct open Occam2_Ast end\<close>
SML_import \<open>structure Occam2_Comments = struct open Occam2_Comments end\<close>
SML_import \<open>structure Occam2_Layout = struct open Occam2_Layout end\<close>

ml_lex_yacc [verbose, state] "Occam2" where
lex_user_declarations\<open>
(* The lexer's and the parser's argument is the per-parse state of "Occam2_State" (the lexer
   rules and the grammar actions call it "st"); "init" creates it, "base" is its part the
   library functions work on. *)
type arg = Occam2_State.T
fun init ctxt source : arg = Occam2_State.init ctxt source
fun base (st : arg) : Lex_yacc_state.T = #base st

fun gp (st : arg) yypos = Lex_yacc_state.get_pos (base st) yypos
fun report (st : arg) x = Lex_yacc_state.report_token (base st) x

(* The antiquotation scanner's state (see the ANTIQ state below): the nesting depth of the
   cartouche currently being skipped (a comment is always a line comment in occam, so,
   unlike C11, there is no block-comment state to remember to return to), the most recently
   seen tag, the text of the cartouche body being scanned (accumulated fragment by
   fragment across nested cartouches), and that body's start position. *)
fun antiq_depth (st : arg) = #antiq_depth st
fun antiq_tag (st : arg) = #antiq_tag st
fun antiq_buf (st : arg) = #antiq_buf st
fun antiq_start (st : arg) = #antiq_start st

(* Every token goes through one of the three constructors below, which, before
   handing over to the library's tok/tok_val (positions, PIDE markup), (1) let the
   comments gathered since the previous token attach themselves to this one,
   and (2) tell the layout recorder where this token starts and stops and
   whether a statement may be broken after it. Unlike C11's lexer, value-carrying
   tokens get their true start/end span as position too (not a zero-width
   point), so that "Xright" in a grammar action is really the end of X. *)
fun otok st cont (yypos, yytext, markup, typ, sort, cons) =
    (Occam2_Comments.attach_pending st (gp st yypos);
     Occam2_Layout.token st (yypos, yypos + String.size yytext, cont);
     tok (base st) (yypos, yytext, markup, typ, sort, cons))

fun otok_val st cont (yypos, yytext, markup, typ, sort, cons, value) =
    let
      val _ = Occam2_Comments.attach_pending st (gp st yypos)
      val _ = Occam2_Layout.token st (yypos, yypos + String.size yytext, cont)
      val p = gp st yypos
      val p' = gp st (yypos + String.size yytext)
      val _ = report st (yypos, String.size yytext, markup, typ, sort)
    in cons (value, p, p') end

fun okw st cont markup (yypos, yytext, cons) =
    (Occam2_Comments.attach_pending st (gp st yypos);
     Occam2_Layout.token st (yypos, yypos + String.size yytext, cont);
     tok (base st) (yypos, yytext, markup, yytext, "", cons))

(* Accumulate one fragment of raw comment text, tagged with its own span. *)
fun push_raw_fragment st (yypos, yytext) =
    Occam2_Comments.push_raw st (yytext, Position.range_position (gp st yypos, gp st (yypos + String.size yytext)))

fun char_to_navi #"u" = Occam2_Ast.up
  | char_to_navi #"U" = Occam2_Ast.Up
  | char_to_navi #"r" = Occam2_Ast.right
  | char_to_navi #"d" = Occam2_Ast.down
  | char_to_navi c = raise Fail ("invalid navigation character " ^ String.str c)

(* Splits the text matched after the leading "@" into the tag name, its optional
   bracketed navigation string, and its optional parenthesized level. *)
fun parse_tag_navi_level text =
    let
      val trim = Substring.string o Substring.dropr Char.isSpace o Substring.full
      val after_at =
        Substring.dropl (fn c => c = #"@" orelse Char.isSpace c) (Substring.full text)
      val (name_ss, rest1) =
        Substring.splitl (fn c => Char.isAlphaNum c orelse c = #"_") after_at
      val rest1' = Substring.dropl Char.isSpace rest1
      val (navi, rest2) =
        if Substring.size rest1' > 0 andalso Substring.sub (rest1', 0) = #"[" then
          let
            val (navi_ss, after) = Substring.splitl (fn c => c <> #"]") (Substring.triml 1 rest1')
          in (map char_to_navi (String.explode (Substring.string navi_ss)), Substring.triml 1 after) end
        else ([], rest1')
      val rest2' = Substring.dropl Char.isSpace rest2
      val level =
        if Substring.size rest2' > 0 andalso Substring.sub (rest2', 0) = #"(" then
          let val (lvl_ss, _) = Substring.splitl (fn c => c <> #")") (Substring.triml 1 rest2')
          in valOf (Int.fromString (Substring.string lvl_ss)) end
        else 0
    in (trim (Substring.string name_ss), navi, level) end

(* A bodyless tag is a complete antiquotation with the empty body; see the
   corresponding note in C11_Parser.thy. *)
fun antiq_flush_pending_tag st =
    let val (name, navi, level, pos) = !(antiq_tag st) in
      if name = "" then ()
      else
        (antiq_tag st := ("", [], 0, Position.none);
         Occam2_Comments.push_antiquotation st {tag = (name, pos)} navi {level = level} {cartouche = ("", pos)})
    end

fun antiq_tag_seen st (yypos, yytext) =
    let val (name, navi, level) = parse_tag_navi_level yytext
    in antiq_flush_pending_tag st; antiq_tag st := (name, navi, level, gp st yypos) end

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
      Occam2_Comments.push_antiquotation st {tag = (tag_text, tag_pos)} navi {level = level} {cartouche = (body_text, body_pos)}
    end

(* The quoted-string alternative to a cartouche body: unlike a cartouche, it
   cannot nest, so tag, level and body are matched by one single rule. *)
fun antiq_tag_and_string_seen st (yypos, yytext) =
    let
      fun find_quote i = if String.sub (yytext, i) = #"\"" then i else find_quote (i + 1)
      val qpos = find_quote 0
      val (name, navi, level) = parse_tag_navi_level (String.substring (yytext, 0, qpos))
      val body_len = String.size yytext - qpos - 2
      val body_text = String.substring (yytext, qpos + 1, body_len)
      val body_start = yypos + qpos + 1
      val body_pos = Position.range_position (gp st body_start, gp st (body_start + body_len))
    in
      Occam2_Comments.push_antiquotation st {tag = (name, gp st yypos)} navi {level = level} {cartouche = (body_text, body_pos)}
    end

(* A newline: the number of blanks following it (tabs count as one blank each -
   the manual's two-space convention is about spaces, and a tab has no defined
   width in occam) is the indentation of the line that starts here. *)
fun layout_newline st yytext = Occam2_Layout.newline st (String.size yytext - 1)

(* Shadows the default "eof" of the "[state]" header: an antiquotation
   cartouche still open at the end of the input is a genuine error, reported at
   the cartouche's own start, not silently swallowed; otherwise a bodyless tag
   still pending at the end of the last comment is flushed. *)
fun eof (st : arg) =
    let
      val _ =
        if !(antiq_depth st) > 0
        then (antiq_depth st := 0;
              print_error (base st)
                ("Unterminated antiquotation body: no matching closing cartouche before the end of input",
                 !(antiq_start st), !(antiq_start st)))
        else antiq_flush_pending_tag st
    in Tokens.EOF (Position.none, Position.none) end
\<close>
lex_definitions\<open>
D=[0-9];
L=[A-Za-z];
A=[A-Za-z0-9.];
TL=[A-Za-z_];
TA=[A-Za-z_0-9];
H=[0-9A-F];
HWS=[\ \t];
NAVI=[uUrd];
ES=(\*(['"*cCnNtTsS]|#{H}{H}));
OPENCART=\\\<open>;
CLOSECART=\\\<close>;
%s LCOMMENT ANTIQ;
\<close>
lex_rules\<open>
<INITIAL>"--"                            => (YYBEGIN LCOMMENT; continue ());
<INITIAL>\n{HWS}*                        => (layout_newline st yytext; continue ());
<INITIAL>[\ \t\r]+                       => (continue ());

<INITIAL>"AFTER"       => (okw st true Markup.keyword1 (yypos, yytext, Tokens.AFTER));
<INITIAL>"AND"         => (okw st true Markup.keyword1 (yypos, yytext, Tokens.AND));
<INITIAL>"ALT"         => (okw st false Markup.keyword1 (yypos, yytext, Tokens.ALT));
<INITIAL>"ANY"         => (okw st false Markup.keyword1 (yypos, yytext, Tokens.ANY));
<INITIAL>"AT"          => (okw st false Markup.keyword1 (yypos, yytext, Tokens.AT));
<INITIAL>"BITAND"      => (okw st true Markup.keyword1 (yypos, yytext, Tokens.BITAND));
<INITIAL>"BITNOT"      => (okw st true Markup.keyword1 (yypos, yytext, Tokens.BITNOT));
<INITIAL>"BITOR"       => (okw st true Markup.keyword1 (yypos, yytext, Tokens.BITOR));
<INITIAL>"BOOL"        => (okw st false Markup.keyword1 (yypos, yytext, Tokens.BOOL));
<INITIAL>"BYTE"        => (okw st false Markup.keyword1 (yypos, yytext, Tokens.BYTE));
<INITIAL>"CASE"        => (okw st false Markup.keyword1 (yypos, yytext, Tokens.CASE));
<INITIAL>"CHAN"        => (okw st false Markup.keyword1 (yypos, yytext, Tokens.CHAN));
<INITIAL>"ELSE"        => (okw st false Markup.keyword1 (yypos, yytext, Tokens.ELSE));
<INITIAL>"FALSE"       => (okw st false Markup.keyword1 (yypos, yytext, Tokens.FALSE));
<INITIAL>"FOR"         => (okw st true Markup.keyword1 (yypos, yytext, Tokens.FOR));
<INITIAL>"FROM"        => (okw st true Markup.keyword1 (yypos, yytext, Tokens.FROM));
<INITIAL>"FUNCTION"    => (okw st false Markup.keyword1 (yypos, yytext, Tokens.FUNCTION));
<INITIAL>"IF"          => (okw st false Markup.keyword1 (yypos, yytext, Tokens.IF));
<INITIAL>"IS"          => (okw st true Markup.keyword1 (yypos, yytext, Tokens.IS));
<INITIAL>"INT"         => (okw st false Markup.keyword1 (yypos, yytext, Tokens.INT));
<INITIAL>"INT16"       => (okw st false Markup.keyword1 (yypos, yytext, Tokens.INT16));
<INITIAL>"INT32"       => (okw st false Markup.keyword1 (yypos, yytext, Tokens.INT32));
<INITIAL>"INT64"       => (okw st false Markup.keyword1 (yypos, yytext, Tokens.INT64));
<INITIAL>"MINUS"       => (okw st true Markup.keyword1 (yypos, yytext, Tokens.MINUS));
<INITIAL>"MOSTNEG"     => (okw st false Markup.keyword1 (yypos, yytext, Tokens.MOSTNEG));
<INITIAL>"MOSTPOS"     => (okw st false Markup.keyword1 (yypos, yytext, Tokens.MOSTPOS));
<INITIAL>"NOT"         => (okw st true Markup.keyword1 (yypos, yytext, Tokens.NOT));
<INITIAL>"OF"          => (okw st false Markup.keyword1 (yypos, yytext, Tokens.OF));
<INITIAL>"OR"          => (okw st true Markup.keyword1 (yypos, yytext, Tokens.OR));
<INITIAL>"PAR"         => (okw st false Markup.keyword1 (yypos, yytext, Tokens.PAR));
<INITIAL>"PLACE"       => (okw st false Markup.keyword1 (yypos, yytext, Tokens.PLACE));
<INITIAL>"PLACED"      => (okw st false Markup.keyword1 (yypos, yytext, Tokens.PLACED));
<INITIAL>"PLUS"        => (okw st true Markup.keyword1 (yypos, yytext, Tokens.PLUS));
<INITIAL>"PORT"        => (okw st false Markup.keyword1 (yypos, yytext, Tokens.PORT));
<INITIAL>"PRI"         => (okw st false Markup.keyword1 (yypos, yytext, Tokens.PRI));
<INITIAL>"PROC"        => (okw st false Markup.keyword1 (yypos, yytext, Tokens.PROC));
<INITIAL>"PROCESSOR"   => (okw st false Markup.keyword1 (yypos, yytext, Tokens.PROCESSOR));
<INITIAL>"PROTOCOL"    => (okw st false Markup.keyword1 (yypos, yytext, Tokens.PROTOCOL));
<INITIAL>"REAL32"      => (okw st false Markup.keyword1 (yypos, yytext, Tokens.REAL32));
<INITIAL>"REAL64"      => (okw st false Markup.keyword1 (yypos, yytext, Tokens.REAL64));
<INITIAL>"REM"         => (okw st true Markup.keyword1 (yypos, yytext, Tokens.REM));
<INITIAL>"RESULT"      => (okw st false Markup.keyword1 (yypos, yytext, Tokens.RESULT));
<INITIAL>"RETYPES"     => (okw st false Markup.keyword1 (yypos, yytext, Tokens.RETYPES));
<INITIAL>"ROUND"       => (okw st true Markup.keyword1 (yypos, yytext, Tokens.ROUND));
<INITIAL>"SEQ"         => (okw st false Markup.keyword1 (yypos, yytext, Tokens.SEQ));
<INITIAL>"SIZE"        => (okw st true Markup.keyword1 (yypos, yytext, Tokens.SIZE));
<INITIAL>"SKIP"        => (okw st false Markup.keyword1 (yypos, yytext, Tokens.SKIP));
<INITIAL>"STOP"        => (okw st false Markup.keyword1 (yypos, yytext, Tokens.STOP));
<INITIAL>"TIMER"       => (okw st false Markup.keyword1 (yypos, yytext, Tokens.TIMER));
<INITIAL>"TIMES"       => (okw st true Markup.keyword1 (yypos, yytext, Tokens.TIMES));
<INITIAL>"TRUE"        => (okw st false Markup.keyword1 (yypos, yytext, Tokens.TRUE));
<INITIAL>"TRUNC"       => (okw st true Markup.keyword1 (yypos, yytext, Tokens.TRUNC));
<INITIAL>"VAL"         => (okw st false Markup.keyword1 (yypos, yytext, Tokens.VAL));
<INITIAL>"VALOF"       => (okw st false Markup.keyword1 (yypos, yytext, Tokens.VALOF));
<INITIAL>"WHILE"       => (okw st false Markup.keyword1 (yypos, yytext, Tokens.WHILE));

<INITIAL>{L}{A}*       => (otok_val st false (yypos, yytext, Markup.free, "NAME", "", Tokens.NAME, yytext));

<INITIAL>{D}+"."{D}+("E"[+-]{D}+)?      => (otok_val st false (yypos, yytext, Markup.numeral, "REAL_LIT", "", Tokens.REAL_LIT, yytext));
<INITIAL>{D}+                           => (otok_val st false (yypos, yytext, Markup.numeral, "INT_LIT", "", Tokens.INT_LIT, yytext));
<INITIAL>"#"{H}+                        => (otok_val st false (yypos, yytext, Markup.numeral, "INT_LIT", "", Tokens.INT_LIT, yytext));
<INITIAL>"'"([^*'"\n]|{ES})"'"          => (otok_val st false (yypos, yytext, Markup.string, "BYTE_LIT", "", Tokens.BYTE_LIT,
                                                                           String.substring (yytext, 1, String.size yytext - 2)));
<INITIAL>["]([^*'"\n]|{ES})*["]         => (otok_val st false (yypos, yytext, Markup.string, "STRING_LIT", "", Tokens.STRING_LIT,
                                                                           String.substring (yytext, 1, String.size yytext - 2)));

<INITIAL>":="  => (otok st true (yypos, yytext, Markup.operator, "ASSIGN", "", Tokens.ASSIGN));
<INITIAL>"::"  => (otok st true (yypos, yytext, Markup.operator, "COLONCOLON", "", Tokens.COLONCOLON));
<INITIAL>":"   => (otok st false (yypos, yytext, Markup.operator, "COLON", "", Tokens.COLON));
<INITIAL>";"   => (otok st true (yypos, yytext, Markup.operator, "SEMI", "", Tokens.SEMI));
<INITIAL>","   => (otok st true (yypos, yytext, Markup.operator, "COMMA", "", Tokens.COMMA));
<INITIAL>"("   => (otok st false (yypos, yytext, Markup.operator, "LPAREN", "", Tokens.LPAREN));
<INITIAL>")"   => (otok st false (yypos, yytext, Markup.operator, "RPAREN", "", Tokens.RPAREN));
<INITIAL>"["   => (otok st false (yypos, yytext, Markup.operator, "LBRACKET", "", Tokens.LBRACKET));
<INITIAL>"]"   => (otok st false (yypos, yytext, Markup.operator, "RBRACKET", "", Tokens.RBRACKET));
<INITIAL>"!"   => (otok st true (yypos, yytext, Markup.operator, "BANG", "", Tokens.BANG));
<INITIAL>"?"   => (otok st true (yypos, yytext, Markup.operator, "QUERY", "", Tokens.QUERY));
<INITIAL>"&"   => (otok st true (yypos, yytext, Markup.operator, "AMP", "", Tokens.AMP));
<INITIAL>"+"   => (otok st true (yypos, yytext, Markup.operator, "ADD", "", Tokens.ADD));
<INITIAL>"-"   => (otok st true (yypos, yytext, Markup.operator, "SUB", "", Tokens.SUB));
<INITIAL>"*"   => (otok st true (yypos, yytext, Markup.operator, "MUL", "", Tokens.MUL));
<INITIAL>"/"   => (otok st true (yypos, yytext, Markup.operator, "DIV", "", Tokens.DIV));
<INITIAL>"\\"  => (otok st true (yypos, yytext, Markup.operator, "BSLASH", "", Tokens.BSLASH));
<INITIAL>"/\\" => (otok st true (yypos, yytext, Markup.operator, "AND_SYM", "", Tokens.AND_SYM));
<INITIAL>"\\/" => (otok st true (yypos, yytext, Markup.operator, "OR_SYM", "", Tokens.OR_SYM));
<INITIAL>"><"  => (otok st true (yypos, yytext, Markup.operator, "XOR_SYM", "", Tokens.XOR_SYM));
<INITIAL>"~"   => (otok st true (yypos, yytext, Markup.operator, "TILDE", "", Tokens.TILDE));
<INITIAL>"<<"  => (otok st true (yypos, yytext, Markup.operator, "SHL", "", Tokens.SHL));
<INITIAL>">>"  => (otok st true (yypos, yytext, Markup.operator, "SHR", "", Tokens.SHR));
<INITIAL>"="   => (otok st true (yypos, yytext, Markup.operator, "EQ", "", Tokens.EQ));
<INITIAL>"<>"  => (otok st true (yypos, yytext, Markup.operator, "NE", "", Tokens.NE));
<INITIAL>"<="  => (otok st true (yypos, yytext, Markup.operator, "LE", "", Tokens.LE));
<INITIAL>">="  => (otok st true (yypos, yytext, Markup.operator, "GE", "", Tokens.GE));
<INITIAL>"<"   => (otok st true (yypos, yytext, Markup.operator, "LT", "", Tokens.LT));
<INITIAL>">"   => (otok st true (yypos, yytext, Markup.operator, "GT", "", Tokens.GT));

<INITIAL>.     => (otok_val st false (yypos, yytext, Markup.bad (), "ILLEGAL", "", Tokens.ILLEGAL, yytext));

<LCOMMENT>[^@\\\n]+                        => (push_raw_fragment st (yypos, yytext); continue ());
<LCOMMENT>"@"{HWS}*{TL}{TA}*({HWS}*"["{NAVI}*"]")?({HWS}*"("{D}+")")?{HWS}*["]([^"\\\n]|{ES})*["]
                                            => (report st (yypos, String.size yytext, Markup.antiquote, "occam antiquotation tag+body", "");
                                                antiq_tag_and_string_seen st (yypos, yytext); continue ());
<LCOMMENT>"@"{HWS}*{TL}{TA}*({HWS}*"["{NAVI}*"]")?({HWS}*"("{D}+")")?
                                            => (report st (yypos, String.size yytext, Markup.antiquote, "occam antiquotation tag", "");
                                                antiq_tag_seen st (yypos, yytext); continue ());
<LCOMMENT>"@"                              => (push_raw_fragment st (yypos, yytext); continue ());
<LCOMMENT>"\\"                             => (push_raw_fragment st (yypos, yytext); continue ());
<LCOMMENT>{OPENCART}                       => (report st (yypos, String.size yytext, Markup.cartouche, "occam antiquotation body", "");
                                                antiq_depth st := 1;
                                                antiq_body_start st (yypos + String.size yytext); YYBEGIN ANTIQ; continue ());
<LCOMMENT>\n{HWS}*                         => (antiq_flush_pending_tag st; layout_newline st yytext; YYBEGIN INITIAL; continue ());

<ANTIQ>[^\\\n]+                            => (antiq_body_push st yytext; continue ());
<ANTIQ>\n+                                  => (antiq_body_push st yytext; continue ());
<ANTIQ>"\\"                                => (antiq_body_push st yytext; continue ());
<ANTIQ>{OPENCART}                          => (antiq_depth st := !(antiq_depth st) + 1; antiq_body_push st yytext; continue ());
<ANTIQ>{CLOSECART}                         => (antiq_depth st := !(antiq_depth st) - 1;
                                                if !(antiq_depth st) = 0
                                                then (antiq_body_finish st yypos; YYBEGIN LCOMMENT; continue ())
                                                else (antiq_body_push st yytext; continue ()));
\<close>
and yacc_user_declarations\<open>
open Occam2_Ast

fun ndi st p = Occam2_Comments.mk_nodeInfo st p p
fun ndi2 st (p1, p2) = Occam2_Comments.mk_nodeInfo st p1 (Position.range_position (p1, p2))

(* A name token carries its true source span as its position, so the node's own
   range is exactly the name. *)
fun mkid st (s, l, r) = Ident (s, 0, ndi2 st (l, r))

(* "formal" is "[VAL] specifier {1 , name}" in the manual, but a flat, left-
   recursive "formal COMMA formal" cannot be parsed as one LALR(1) production
   (after a name, a comma may continue either the same name list or start the
   next formal, and one token of lookahead cannot tell which). The grammar
   instead reads every comma-separated item as either a fresh specifier-plus-
   name or a bare name, and a bare name is appended here to the name list of
   the formal before it. *)
fun add_bare_name (Formal (v, t, ids, ni)) id = Formal (v, t, ids @ [id], ni)

fun extend_last [] _ = raise Fail "occam2: formal parameter list without leading specifier"
  | extend_last fs id =
      let val (init, last) = (List.take (fs, length fs - 1), List.last fs)
      in init @ [add_bare_name last id] end

fun conv_of_prim (k, _) = k
fun type_of_prim (k, ni) = TPrim (k, ni)
\<close>
yacc_definitions\<open>
%eop EOF
%arg (st) : Occam2_State.T
%pure
%noshift EOF

%term
        NAME of string | INT_LIT of string | REAL_LIT of string | BYTE_LIT of string
      | STRING_LIT of string | ILLEGAL of string |
        AFTER | AND | ALT | ANY | AT | BITAND | BITNOT | BITOR | BOOL | BYTE | CASE | CHAN |
        ELSE | FALSE | FOR | FROM | FUNCTION | IF | IS | INT | INT16 | INT32 | INT64 |
        MINUS | MOSTNEG | MOSTPOS | NOT | OF | OR | PAR | PLACE | PLACED | PLUS | PORT |
        PRI | PROC | PROCESSOR | PROTOCOL | REAL32 | REAL64 | REM | RESULT | RETYPES |
        ROUND | SEQ | SIZE | SKIP | STOP | TIMER | TIMES | TRUE | TRUNC | VAL | VALOF | WHILE |
        ASSIGN | COLONCOLON | COLON | SEMI | COMMA | LPAREN | RPAREN | LBRACKET | RBRACKET |
        BANG | QUERY | AMP | ADD | SUB | MUL | DIV | BSLASH | AND_SYM | OR_SYM | XOR_SYM |
        TILDE | SHL | SHR | EQ | NE | LE | GE | LT | GT |
        NEWLINE | INDENT | OUTDENT |
        ENTRY_UNIT | ENTRY_EXPR | ENTRY_ID |
        EOF

%nonterm
        start_rule of Position.T root option
      | opt_newline of unit
      | program_unit of Position.T root
      | specs_only of Position.T oSpec list
      | spec of Position.T oSpec
      | name_list of Position.T ident list
      | data_type of primKind * Position.T nodeInfo
      | data_type_list of Position.T oType list
      | typ_nd of Position.T oType
      | typ of Position.T oType
      | protocol of Position.T oProtocol
      | simple_prot of Position.T oSimpleProt
      | simple_prot_list of Position.T oSimpleProt list
      | tagged_prot of Position.T oTagged
      | tagged_list of Position.T oTagged list
      | formal_head of Position.T oFormal
      | formal_list of Position.T oFormal list
      | formals of Position.T oFormal list
      | value_process of Position.T oValueProcess
      | process of Position.T oProcess
      | process_list of Position.T oProcess list
      | conditional of Position.T oProcess
      | alternation of Position.T oProcess
      | parallel of Position.T oProcess
      | placed_par of Position.T oProcess
      | replicator of Position.T oReplicator
      | variable_list of Position.T oElement list
      | o_input of Position.T oInput
      | input_item of Position.T oInputItem
      | input_items of Position.T oInputItem list
      | out_item of Position.T oOutItem
      | out_items of Position.T oOutItem list
      | choice of Position.T oChoice
      | choice_list of Position.T oChoice list
      | option_ of Position.T oOption
      | option_list of Position.T oOption list
      | variant of Position.T oVariant
      | variant_list of Position.T oVariant list
      | guard of Position.T oGuard
      | alt of Position.T oAlt
      | alt_list of Position.T oAlt list
      | placed of Position.T oPlaced
      | placed_list of Position.T oPlaced list
      | expression of Position.T oExpr
      | expression_list of Position.T oExpr list
      | expression_list0 of Position.T oExpr list
      | and_chain of Position.T oExpr list
      | or_chain of Position.T oExpr list
      | operand of Position.T oExpr
      | monop of monOp
      | dyop of dyOp
      | literal of Position.T oLit
      | element of Position.T oElement
      | table of Position.T oTable
\<close>
yacc_rules\<open>
start_rule:
        ENTRY_UNIT program_unit        (SOME program_unit)
|       ENTRY_EXPR expression opt_newline    (SOME (Expr expression))
|       ENTRY_ID NAME opt_newline      (SOME (Id (mkid st (NAME, NAMEleft, NAMEright))))

opt_newline:
        NEWLINE        (())
|                      (())

program_unit:
        process        (Proc process)
|       specs_only     (Specs specs_only)

specs_only:
        spec                (spec :: [])
|       spec specs_only     (spec :: specs_only)

(* ---- Specifications ---- *)

spec:
        data_type name_list COLON NEWLINE
                (SDecl (type_of_prim data_type, name_list, ndi2 st (data_typeleft, COLONright)))
|       typ_nd name_list COLON NEWLINE
                (SDecl (typ_nd, name_list, ndi2 st (typ_ndleft, COLONright)))
|       data_type NAME IS element COLON NEWLINE
                (SAbbrev (SOME (type_of_prim data_type), mkid st (NAME, NAMEleft, NAMEright), element, ndi2 st (data_typeleft, COLONright)))
|       typ_nd NAME IS element COLON NEWLINE
                (SAbbrev (SOME typ_nd, mkid st (NAME, NAMEleft, NAMEright), element, ndi2 st (typ_ndleft, COLONright)))
|       NAME IS element COLON NEWLINE
                (SAbbrev (NONE, mkid st (NAME, NAMEleft, NAMEright), element, ndi2 st (NAMEleft, COLONright)))
|       VAL typ NAME IS expression COLON NEWLINE
                (SValAbbrev (SOME typ, mkid st (NAME, NAMEleft, NAMEright), expression, ndi2 st (VALleft, COLONright)))
|       VAL NAME IS expression COLON NEWLINE
                (SValAbbrev (NONE, mkid st (NAME, NAMEleft, NAMEright), expression, ndi2 st (VALleft, COLONright)))
|       data_type NAME RETYPES element COLON NEWLINE
                (SRetypes (type_of_prim data_type, mkid st (NAME, NAMEleft, NAMEright), element, ndi2 st (data_typeleft, COLONright)))
|       typ_nd NAME RETYPES element COLON NEWLINE
                (SRetypes (typ_nd, mkid st (NAME, NAMEleft, NAMEright), element, ndi2 st (typ_ndleft, COLONright)))
|       VAL typ NAME RETYPES expression COLON NEWLINE
                (SValRetypes (typ, mkid st (NAME, NAMEleft, NAMEright), expression, ndi2 st (VALleft, COLONright)))
|       PROTOCOL NAME IS protocol COLON NEWLINE
                (SProtocol (mkid st (NAME, NAMEleft, NAMEright), protocol, ndi2 st (PROTOCOLleft, COLONright)))
|       PROTOCOL NAME NEWLINE INDENT CASE NEWLINE INDENT tagged_list OUTDENT OUTDENT COLON NEWLINE
                (SProtocolCase (mkid st (NAME, NAMEleft, NAMEright), tagged_list, ndi2 st (PROTOCOLleft, COLONright)))
|       PROC NAME LPAREN formals RPAREN NEWLINE INDENT process OUTDENT COLON NEWLINE
                (SProc (mkid st (NAME, NAMEleft, NAMEright), formals, process, ndi2 st (PROCleft, COLONright)))
|       data_type_list FUNCTION NAME LPAREN formals RPAREN NEWLINE INDENT value_process OUTDENT COLON NEWLINE
                (SFunction (data_type_list, mkid st (NAME, NAMEleft, NAMEright), formals, value_process,
                            ndi2 st (data_type_listleft, COLONright)))
|       data_type_list FUNCTION NAME LPAREN formals RPAREN IS expression_list COLON NEWLINE
                (SFunctionIs (data_type_list, mkid st (NAME, NAMEleft, NAMEright), formals, expression_list,
                              ndi2 st (data_type_listleft, COLONright)))

name_list:
        NAME                     ([mkid st (NAME, NAMEleft, NAMEright)])
|       name_list COMMA NAME     (name_list @ [mkid st (NAME, NAMEleft, NAMEright)])

formal_head:
        typ NAME         (Formal (false, typ, [mkid st (NAME, NAMEleft, NAMEright)], ndi2 st (typleft, NAMEright)))
|       VAL typ NAME     (Formal (true, typ, [mkid st (NAME, NAMEleft, NAMEright)], ndi2 st (VALleft, NAMEright)))

formal_list:
        formal_head                        ([formal_head])
|       formal_list COMMA formal_head      (formal_list @ [formal_head])
|       formal_list COMMA NAME             (extend_last formal_list (mkid st (NAME, NAMEleft, NAMEright)))

formals:
                       ([])
|       formal_list    (formal_list)

(* ---- Types and protocols ---- *)

data_type:
        BOOL      ((KBool, ndi2 st (BOOLleft, BOOLright)))
|       BYTE      ((KByte, ndi2 st (BYTEleft, BYTEright)))
|       INT       ((KInt, ndi2 st (INTleft, INTright)))
|       INT16     ((KInt16, ndi2 st (INT16left, INT16right)))
|       INT32     ((KInt32, ndi2 st (INT32left, INT32right)))
|       INT64     ((KInt64, ndi2 st (INT64left, INT64right)))
|       REAL32    ((KReal32, ndi2 st (REAL32left, REAL32right)))
|       REAL64    ((KReal64, ndi2 st (REAL64left, REAL64right)))

data_type_list:
        data_type                          ([type_of_prim data_type])
|       data_type_list COMMA data_type     (data_type_list @ [type_of_prim data_type])

(* "typ" is split into the bare primitive data types ("data_type") and everything
   else ("typ_nd", "not a data type"). The split exists for the declaration rules
   above: at the start of a choice, option or alternative both a specification
   ("INT x:") and an expression - a type conversion "INT x" - may begin, and they
   share the prefix "INT NAME". If a specification had to reduce "INT" to a "typ"
   before shifting NAME, the parser would be forced to decide between the two one
   token too early. Spelling the data-type alternatives out in "spec" itself keeps
   the shared prefix unreduced until the token after the name settles it. *)
typ_nd:
        CHAN OF protocol         (TChan (protocol, ndi2 st (CHANleft, protocolright)))
|       TIMER                    (TTimer (ndi2 st (TIMERleft, TIMERright)))
|       PORT OF typ              (TPort (typ, ndi2 st (PORTleft, typright)))
|       LBRACKET expression RBRACKET typ         (TArray (expression, typ, ndi2 st (LBRACKETleft, typright)))
|       LBRACKET RBRACKET typ                    (TOpenArray (typ, ndi2 st (LBRACKETleft, typright)))

typ:
        data_type                (type_of_prim data_type)
|       typ_nd                   (typ_nd)

protocol:
        ANY                      (PrAny (ndi2 st (ANYleft, ANYright)))
|       NAME                     (PrName (mkid st (NAME, NAMEleft, NAMEright)))
|       simple_prot_list         (PrSeq (simple_prot_list, ndi2 st (simple_prot_listleft, simple_prot_listright)))

simple_prot_list:
        simple_prot                        ([simple_prot])
|       simple_prot_list SEMI simple_prot  (simple_prot_list @ [simple_prot])

simple_prot:
        typ                                      (SPType typ)
|       data_type COLONCOLON LBRACKET RBRACKET typ
                (SPCounted (#1 data_type, #2 data_type, typ, ndi2 st (data_typeleft, typright)))

tagged_prot:
        NAME                     (Tagged (mkid st (NAME, NAMEleft, NAMEright), [], ndi2 st (NAMEleft, NAMEright)))
|       NAME SEMI simple_prot_list
                                 (Tagged (mkid st (NAME, NAMEleft, NAMEright), simple_prot_list,
                                          ndi2 st (NAMEleft, simple_prot_listright)))

tagged_list:
        tagged_prot NEWLINE                  ([tagged_prot])
|       tagged_list tagged_prot NEWLINE      (tagged_list @ [tagged_prot])

(* ---- Processes ---- *)

process_list:
        process                  ([process])
|       process_list process     (process_list @ [process])

process:
        SKIP NEWLINE             (PSkip (ndi2 st (SKIPleft, SKIPright)))
|       STOP NEWLINE             (PStop (ndi2 st (STOPleft, STOPright)))
|       variable_list ASSIGN expression_list NEWLINE
                (PAssign (variable_list, expression_list, ndi2 st (variable_listleft, expression_listright)))
|       o_input NEWLINE          (PInput (o_input, ndi2 st (o_inputleft, o_inputright)))
|       element BANG out_items NEWLINE
                (POutput (element, out_items, ndi2 st (elementleft, out_itemsright)))
|       element QUERY CASE NEWLINE INDENT variant_list OUTDENT
                (PCaseInput (element, variant_list, ndi2 st (elementleft, variant_listright)))
|       SEQ NEWLINE              (PSeq (NONE, [], ndi2 st (SEQleft, SEQright)))
|       SEQ NEWLINE INDENT process_list OUTDENT
                (PSeq (NONE, process_list, ndi2 st (SEQleft, process_listright)))
|       SEQ replicator NEWLINE INDENT process OUTDENT
                (PSeq (SOME replicator, [process], ndi2 st (SEQleft, processright)))
|       conditional              (conditional)
|       CASE expression NEWLINE  (PCase (expression, [], ndi2 st (CASEleft, expressionright)))
|       CASE expression NEWLINE INDENT option_list OUTDENT
                (PCase (expression, option_list, ndi2 st (CASEleft, option_listright)))
|       WHILE expression NEWLINE INDENT process OUTDENT
                (PWhile (expression, process, ndi2 st (WHILEleft, processright)))
|       parallel                 (parallel)
|       alternation              (alternation)
|       placed_par               (placed_par)
|       NAME LPAREN expression_list0 RPAREN NEWLINE
                (PInstance (mkid st (NAME, NAMEleft, NAMEright), expression_list0, ndi2 st (NAMEleft, RPARENright)))
|       spec process             (PSpecP (spec, process, ndi2 st (specleft, processright)))
|       PLACE NAME AT expression COLON NEWLINE process
                (PPlace (mkid st (NAME, NAMEleft, NAMEright), expression, process, ndi2 st (PLACEleft, processright)))

conditional:
        IF NEWLINE               (PIf (NONE, [], ndi2 st (IFleft, IFright)))
|       IF NEWLINE INDENT choice_list OUTDENT
                (PIf (NONE, choice_list, ndi2 st (IFleft, choice_listright)))
|       IF replicator NEWLINE INDENT choice OUTDENT
                (PIf (SOME replicator, [choice], ndi2 st (IFleft, choiceright)))

parallel:
        PAR NEWLINE              (PPar (false, NONE, [], ndi2 st (PARleft, PARright)))
|       PAR NEWLINE INDENT process_list OUTDENT
                (PPar (false, NONE, process_list, ndi2 st (PARleft, process_listright)))
|       PAR replicator NEWLINE INDENT process OUTDENT
                (PPar (false, SOME replicator, [process], ndi2 st (PARleft, processright)))
|       PRI PAR NEWLINE          (PPar (true, NONE, [], ndi2 st (PRIleft, PARright)))
|       PRI PAR NEWLINE INDENT process_list OUTDENT
                (PPar (true, NONE, process_list, ndi2 st (PRIleft, process_listright)))
|       PRI PAR replicator NEWLINE INDENT process OUTDENT
                (PPar (true, SOME replicator, [process], ndi2 st (PRIleft, processright)))

alternation:
        ALT NEWLINE              (PAlt (false, NONE, [], ndi2 st (ALTleft, ALTright)))
|       ALT NEWLINE INDENT alt_list OUTDENT
                (PAlt (false, NONE, alt_list, ndi2 st (ALTleft, alt_listright)))
|       ALT replicator NEWLINE INDENT alt OUTDENT
                (PAlt (false, SOME replicator, [alt], ndi2 st (ALTleft, altright)))
|       PRI ALT NEWLINE          (PAlt (true, NONE, [], ndi2 st (PRIleft, ALTright)))
|       PRI ALT NEWLINE INDENT alt_list OUTDENT
                (PAlt (true, NONE, alt_list, ndi2 st (PRIleft, alt_listright)))
|       PRI ALT replicator NEWLINE INDENT alt OUTDENT
                (PAlt (true, SOME replicator, [alt], ndi2 st (PRIleft, altright)))

placed_par:
        PLACED PAR NEWLINE       (PPlacedPar (NONE, [], ndi2 st (PLACEDleft, PARright)))
|       PLACED PAR NEWLINE INDENT placed_list OUTDENT
                (PPlacedPar (NONE, placed_list, ndi2 st (PLACEDleft, placed_listright)))
|       PLACED PAR replicator NEWLINE INDENT placed OUTDENT
                (PPlacedPar (SOME replicator, [placed], ndi2 st (PLACEDleft, placedright)))

placed_list:
        placed                   ([placed])
|       placed_list placed       (placed_list @ [placed])

placed:
        PROCESSOR expression NEWLINE INDENT process OUTDENT
                (PlProcessor (expression, process, ndi2 st (PROCESSORleft, processright)))
|       PLACED PAR NEWLINE INDENT placed_list OUTDENT
                (PlPar (NONE, placed_list, ndi2 st (PLACEDleft, placed_listright)))
|       PLACED PAR replicator NEWLINE INDENT placed OUTDENT
                (PlPar (SOME replicator, [placed], ndi2 st (PLACEDleft, placedright)))

replicator:
        NAME EQ expression FOR expression
                (Repl (mkid st (NAME, NAMEleft, NAMEright), expression1, expression2, ndi2 st (NAMEleft, expression2right)))

(* ---- Actions ---- *)

variable_list:
        element                          ([element])
|       variable_list COMMA element      (variable_list @ [element])

o_input:
        element QUERY input_items
                (InVars (element, input_items, ndi2 st (elementleft, input_itemsright)))
|       element QUERY AFTER expression
                (InAfter (element, expression, ndi2 st (elementleft, expressionright)))

input_item:
        element                          (IIVar element)
|       element COLONCOLON element       (IICounted (element1, element2))

input_items:
        input_item                       ([input_item])
|       input_items SEMI input_item      (input_items @ [input_item])

out_item:
        expression                       (OIExpr expression)
|       expression COLONCOLON expression (OICounted (expression1, expression2))

out_items:
        out_item                         ([out_item])
|       out_items SEMI out_item          (out_items @ [out_item])

(* ---- Choices, options, variants, alternatives ---- *)

choice_list:
        choice                   ([choice])
|       choice_list choice       (choice_list @ [choice])

choice:
        expression NEWLINE INDENT process OUTDENT
                (ChGuarded (expression, process, ndi2 st (expressionleft, processright)))
|       conditional              (ChNested conditional)
|       spec choice              (ChSpec (spec, choice, ndi2 st (specleft, choiceright)))

option_list:
        option_                  ([option_])
|       option_list option_      (option_list @ [option_])

option_:
        expression_list NEWLINE INDENT process OUTDENT
                (OpCases (expression_list, process, ndi2 st (expression_listleft, processright)))
|       ELSE NEWLINE INDENT process OUTDENT
                (OpElse (process, ndi2 st (ELSEleft, processright)))
|       spec option_             (OpSpec (spec, option_, ndi2 st (specleft, option_right)))

variant_list:
        variant                  ([variant])
|       variant_list variant     (variant_list @ [variant])

variant:
        NAME NEWLINE INDENT process OUTDENT
                (VaTagged (mkid st (NAME, NAMEleft, NAMEright), [], process, ndi2 st (NAMEleft, processright)))
|       NAME SEMI input_items NEWLINE INDENT process OUTDENT
                (VaTagged (mkid st (NAME, NAMEleft, NAMEright), input_items, process, ndi2 st (NAMEleft, processright)))
|       spec variant             (VaSpec (spec, variant, ndi2 st (specleft, variantright)))

alt_list:
        alt                      ([alt])
|       alt_list alt             (alt_list @ [alt])

guard:
        o_input                  (GInput (o_input, ndi2 st (o_inputleft, o_inputright)))
|       expression AMP o_input   (GCondInput (expression, o_input, ndi2 st (expressionleft, o_inputright)))
|       expression AMP SKIP      (GCondSkip (expression, ndi2 st (expressionleft, SKIPright)))

alt:
        guard NEWLINE INDENT process OUTDENT
                (AlGuarded (guard, process, ndi2 st (guardleft, processright)))
|       element QUERY CASE NEWLINE INDENT variant_list OUTDENT
                (AlCase (NONE, element, variant_list, ndi2 st (elementleft, variant_listright)))
|       expression AMP element QUERY CASE NEWLINE INDENT variant_list OUTDENT
                (AlCase (SOME expression, element, variant_list, ndi2 st (expressionleft, variant_listright)))
|       alternation              (AlNested alternation)
|       spec alt                 (AlSpec (spec, alt, ndi2 st (specleft, altright)))

(* ---- Value processes ---- *)

value_process:
        VALOF NEWLINE INDENT process OUTDENT RESULT expression_list NEWLINE
                (VPValof (process, expression_list, ndi2 st (VALOFleft, expression_listright)))
|       spec value_process       (VPSpec (spec, value_process, ndi2 st (specleft, value_processright)))

(* ---- Expressions: no precedence; the only unparenthesized chaining is AND/OR ---- *)

expression_list:
        expression                          ([expression])
|       expression_list COMMA expression    (expression_list @ [expression])

expression_list0:
                           ([])
|       expression_list    (expression_list)

expression:
        operand                  (operand)
|       monop operand            (EMon (monop, operand, ndi2 st (monopleft, operandright)))
|       operand dyop operand     (EBin (operand1, dyop, operand2, ndi2 st (operand1left, operand2right)))
|       and_chain                (EChain (LAnd, and_chain, ndi2 st (and_chainleft, and_chainright)))
|       or_chain                 (EChain (LOr, or_chain, ndi2 st (or_chainleft, or_chainright)))
|       data_type operand        (EConv (ConvPlain, #1 data_type, operand, ndi2 st (data_typeleft, operandright)))
|       data_type ROUND operand  (EConv (ConvRound, #1 data_type, operand, ndi2 st (data_typeleft, operandright)))
|       data_type TRUNC operand  (EConv (ConvTrunc, #1 data_type, operand, ndi2 st (data_typeleft, operandright)))
|       MOSTPOS typ              (EMost (true, typ, ndi2 st (MOSTPOSleft, typright)))
|       MOSTNEG typ              (EMost (false, typ, ndi2 st (MOSTNEGleft, typright)))

and_chain:
        operand AND operand      ([operand1, operand2])
|       and_chain AND operand    (and_chain @ [operand])

or_chain:
        operand OR operand       ([operand1, operand2])
|       or_chain OR operand      (or_chain @ [operand])

operand:
        element                  (EElem element)
|       literal                  (ELit literal)
|       table                    (ETable table)
|       LPAREN expression RPAREN (EParen (expression, ndi2 st (LPARENleft, RPARENright)))
|       LPAREN NEWLINE INDENT value_process OUTDENT RPAREN
                (EValof (value_process, ndi2 st (LPARENleft, RPARENright)))
|       NAME LPAREN expression_list0 RPAREN
                (ECall (mkid st (NAME, NAMEleft, NAMEright), expression_list0, ndi2 st (NAMEleft, RPARENright)))

monop:
        SUB                      (MNeg)
|       MINUS                    (MMinus)
|       NOT                      (MNot)
|       BITNOT                   (MBitNot)
|       TILDE                    (MBitNot)
|       SIZE                     (MSize)

dyop:
        ADD                      (DAdd)
|       SUB                      (DSub)
|       MUL                      (DMul)
|       DIV                      (DDiv)
|       BSLASH                   (DRem)
|       REM                      (DRem)
|       PLUS                     (DPlus)
|       MINUS                    (DMinus)
|       TIMES                    (DTimes)
|       AND_SYM                  (DBitAnd)
|       BITAND                   (DBitAnd)
|       OR_SYM                   (DBitOr)
|       BITOR                    (DBitOr)
|       XOR_SYM                  (DBitXor)
|       SHL                      (DShl)
|       SHR                      (DShr)
|       EQ                       (DEq)
|       NE                       (DNe)
|       LT                       (DLt)
|       GT                       (DGt)
|       LE                       (DLe)
|       GE                       (DGe)
|       AFTER                    (DAfter)

literal:
        INT_LIT                  (LInt (INT_LIT, ndi2 st (INT_LITleft, INT_LITright)))
|       BYTE_LIT                 (LByte (BYTE_LIT, ndi2 st (BYTE_LITleft, BYTE_LITright)))
|       INT_LIT LPAREN typ RPAREN
                (LTyped (LInt (INT_LIT, ndi2 st (INT_LITleft, INT_LITright)), typ, ndi2 st (INT_LITleft, RPARENright)))
|       BYTE_LIT LPAREN typ RPAREN
                (LTyped (LByte (BYTE_LIT, ndi2 st (BYTE_LITleft, BYTE_LITright)), typ, ndi2 st (BYTE_LITleft, RPARENright)))
|       REAL_LIT LPAREN typ RPAREN
                (LTyped (LReal (REAL_LIT, ndi2 st (REAL_LITleft, REAL_LITright)), typ, ndi2 st (REAL_LITleft, RPARENright)))
|       STRING_LIT               (LString (STRING_LIT, ndi2 st (STRING_LITleft, STRING_LITright)))
|       TRUE                     (LTrue (ndi2 st (TRUEleft, TRUEright)))
|       FALSE                    (LFalse (ndi2 st (FALSEleft, FALSEright)))

element:
        NAME                     (ENamed (mkid st (NAME, NAMEleft, NAMEright)))
|       element LBRACKET expression RBRACKET
                (ESub (element, expression, ndi2 st (elementleft, RBRACKETright)))
|       LBRACKET element FROM expression FOR expression RBRACKET
                (ESlice (element, expression1, expression2, ndi2 st (LBRACKETleft, RBRACKETright)))

table:
        LBRACKET expression_list RBRACKET
                (TabList (expression_list, ndi2 st (LBRACKETleft, RBRACKETright)))
|       LBRACKET table FROM expression FOR expression RBRACKET
                (TabSlice (table, expression1, expression2, ndi2 st (LBRACKETleft, RBRACKETright)))
|       LBRACKET STRING_LIT FROM expression FOR expression RBRACKET
                (TabSlice (TabString (STRING_LIT, ndi2 st (STRING_LITleft, STRING_LITright)),
                           expression1, expression2, ndi2 st (LBRACKETleft, RBRACKETright)))
|       table LBRACKET expression RBRACKET
                (TabSub (table, expression, ndi2 st (tableleft, RBRACKETright)))
|       STRING_LIT LBRACKET expression RBRACKET
                (TabSub (TabString (STRING_LIT, ndi2 st (STRING_LITleft, STRING_LITright)),
                         expression, ndi2 st (STRING_LITleft, RBRACKETright)))
\<close>

text\<open>
  The layout stage and the parse entry points. \<open>Occam2_Parse.parse\<close> drives the
  generated lexer through a wrapper that injects the layout tokens (see the
  introduction of this theory for the algorithm) and a synthetic first token that
  selects the grammar's entry point. It takes the parser's error callback as a
  parameter, so one implementation serves both the ordinary commands (which want
  YaccLib's error-reporting \<open>print_error\<close>) and the \<open>_reject\<close> commands (which want a
  silent callback that raises a locally declared exception - see \<^verbatim>\<open>Occam2.thy\<close>).
\<close>

ML\<open>
structure Occam2_Parse = struct

structure P = Occam2.Occam2Parser
structure T = Occam2.Occam2LrVals.Tokens

datatype entry = Entry_Unit | Entry_Expr | Entry_Id

fun entry_token Entry_Unit p = T.ENTRY_UNIT (p, p)
  | entry_token Entry_Expr p = T.ENTRY_EXPR (p, p)
  | entry_token Entry_Id p = T.ENTRY_ID (p, p)

(* "err" is the parser's usual error callback; layout errors (an indentation
   that does not return to any enclosing level) are reported through it too, so
   they are located, and (for the reject commands) silenced, exactly like a
   syntax error. *)
fun layout_stream err entry st raw_lex pos eof_pos =
  let
    fun fail msg p = (err (msg, p, p); raise Fail msg)
    fun nl p = T.NEWLINE (p, p)
    fun indent p = T.INDENT (p, p)
    fun outdent p = T.OUTDENT (p, p)
    val eof_tok = T.EOF (eof_pos, eof_pos)

    val queue = Unsynchronized.ref [entry_token entry (pos 0)]
    val stack : int list Unsynchronized.ref = Unsynchronized.ref []   (* [] : no token seen yet *)
    val prev_cont = Unsynchronized.ref false
    val prev_end = Unsynchronized.ref 0
    val eof_seen = Unsynchronized.ref false

    fun close_all p =
      (case !stack of
         [] => []
       | _ :: rest => nl (pos (!prev_end)) :: map (fn _ => outdent p) rest)

    (* The layout tokens due in front of a real token starting at "p", on a line
       indented by "n", given that a newline was seen since the previous token. *)
    fun layout_before p n =
      (case !stack of
         [] => (stack := [n]; [])
       | top :: _ =>
           let val pre = [nl (pos (!prev_end))] in
             if n > top then (stack := n :: !stack; pre @ [indent p])
             else if n = top then pre
             else
               let
                 fun pop (s as t :: r) acc =
                       if t > n then pop r (outdent p :: acc)
                       else if t = n then (s, rev acc)
                       else fail "Inconsistent indentation: this line does not return to the indentation of any enclosing block" p
                   | pop [] _ = fail "Inconsistent indentation" p
                 val (s', outs) = pop (!stack) []
               in stack := s'; pre @ outs end
           end)

    fun next () =
      (case !queue of
         t :: ts => (queue := ts; t)
       | [] =>
           if !eof_seen then eof_tok
           else
             let
               val tok = raw_lex ()
               val lay = Occam2_Layout.get st
             in
               if P.sameToken (tok, eof_tok) then
                 (eof_seen := true;
                  queue := close_all eof_pos @ [eof_tok];
                  next ())
               else
                 let
                   val p = pos (#start lay)
                   val before =
                     if !stack = [] then (* first real token: its own line fixes the base level *)
                       layout_before p (if #nl_seen lay then #indent lay else 0)
                     else if #nl_seen lay andalso not (!prev_cont) then layout_before p (#indent lay)
                     else []
                 in
                   Occam2_Layout.clear_newline st;
                   prev_cont := #cont lay;
                   prev_end := #stop lay;
                   queue := before @ [tok];
                   next ()
                 end
             end)
  in P.Stream.streamify next end

(* Runs the parser on "source" from the given entry point; "mk_err" makes the parser's error
   callback from the parse's state (see "parse_loud" and "parse_quiet"). Every parse creates its own
   state ("Occam2_State.init"), given to the lexer and to the parser, so parses can run
   concurrently. *)
fun parse mk_err entry ctxt source =
  let
    val st = Occam2_State.init ctxt source
    val err = mk_err st
    val input_text = Lex_yacc_state.text_of (#base st)
    val consumed = Unsynchronized.ref false
    fun input_string _ = if !consumed then "" else (consumed := true; input_text)
    val raw_lex = Occam2.Occam2Lex.makeLexer input_string st
    val pos = Lex_yacc_state.get_pos (#base st)
    val eof_pos = pos (String.size input_text)
    val stream = layout_stream err entry st raw_lex pos eof_pos
    val (result, _) = P.parse (0, stream, err, st)
  in result end

fun parse_loud entry ctxt source =
  parse (fn st => Lex_yacc_state.print_error (#base st)) entry ctxt source

(* The silent variant the "_reject" commands use: a locally declared exception,
   not YaccLib's "print_error" (which reports PIDE error markup before raising,
   and raises an exception Isabelle/ML cannot reliably catch by identity across
   the SML sandbox boundary - the same reasoning as in C11.thy). *)
exception Rejected of string
fun quiet_error (s : string, _ : Position.T, _ : Position.T) = raise Rejected s

fun parse_quiet entry ctxt source = parse (K quiet_error) entry ctxt source

end
\<close>

end
