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

theory
  YaccLib
imports
  Main
begin 

SML_import \<open>val pide_error = error \<close>
SML_import \<open>val pide_warning = warning \<close>
SML_import \<open>val pide_writeln = writeln \<close>

SML_file\<open>mlyacc-polyml/mlyacc-lib/base.sig\<close> 
SML_file\<open>mlyacc-polyml/mlyacc-lib/join.sml\<close>
SML_file\<open>mlyacc-polyml/mlyacc-lib/lrtable.sml\<close>
SML_file\<open>mlyacc-polyml/mlyacc-lib/stream.sml\<close>   
SML_file\<open>mlyacc-polyml/mlyacc-lib/parser2.sml\<close>

ML\<open>

signature ISABELLE_LEX_YACC = 
  sig
    eqtype pos
    val get_pos: int -> Position.T
    val header: unit -> string
    val linker: string -> string
    val parse_source:
       (int * 'a * (string * Position.T * Position.T -> 'b) * unit -> 'c * 'd) ->
         (('e -> string) -> 'a) -> ('d -> 'f * 'a) -> ('f * 'g -> bool) -> (Position.T * Position.T -> 'g) -> Input.source -> 'c
    val print_error: string * Position.T * Position.T -> 'a
    val report_token: int * int * Markup.T * string * string -> unit
    val reset: unit -> unit
    val set: Input.source -> Proof.context -> unit
    val tok: int * string * Markup.T * string * string * (Position.T * Position.T -> 'a) -> 'a
    val tok_val: int * string * Markup.T * string * string * ('a * Position.T * Position.T -> 'b) * 'a -> 'b
  end

structure Isabelle_lex_yacc: ISABELLE_LEX_YACC = struct
  type pos = Position.T

  (* Use a Synchronized variable instead of raw Thread_Data to coordinate state cleanly *)
  type state = Input.source * Proof.context
  val global_state : state Synchronized.var =
    Synchronized.var "isabelle_lex_yacc_state" (Input.string "", Context.the_local_context ())

  fun set source ctx =
    Synchronized.change global_state (fn _ => (source, ctx))

  fun get_src () = #1 (Synchronized.value global_state)
  fun get_ctxt () = #2 (Synchronized.value global_state)

  fun reset () =
    Synchronized.change global_state (fn _ => (Input.string "", Context.the_local_context ()))

  (* Helper: Explodes the source but strips the ‹ and › markers *)
  fun get_inner_syms source =
    let
      val syms = Input.source_explode source
    in
      if length syms >= 2 then List.take (tl syms, length syms - 2) else syms
    end

  fun get_pos yypos =
    let
      val src = get_src ()
      val inner_syms = get_inner_syms src
      val pos_vec = Vector.fromList inner_syms
      val idx = yypos - 1
    in
      if Vector.length pos_vec = 0 then Input.pos_of src
      else if idx < 0 then #2 (Vector.sub (pos_vec, 0))
      else if idx >= Vector.length pos_vec then
        #2 (Vector.sub (pos_vec, Vector.length pos_vec - 1))
      else #2 (Vector.sub (pos_vec, idx))
    end

  fun report_token (start_idx, len, markup, token_type, token_sort) =
    if 0 < len then
      let
        val p_start = get_pos start_idx
        val p_end = get_pos (start_idx + len)
        val p = Position.range_position (Position.range(p_start, p_end))
        val ctxt = get_ctxt ()
      in
        Context_Position.report ctxt p markup;
        Context_Position.report_text ctxt p Markup.typing token_type;
        Context_Position.report_text ctxt p Markup.sorting token_sort
      end
    else ()

  fun get_line_col p =
    let
      val src = get_src ()
      val inner_syms = get_inner_syms src
      val pos_vec = Vector.fromList inner_syms
      val (input_text, _) = Input.source_content src
      val target_offset = Position.offset_of p

      fun is_target pos =
        case (Position.offset_of pos, target_offset) of
          (SOME o1, SOME o2) => o1 = o2
        | _ => false

      fun find_idx i =
        if i >= Vector.length pos_vec then Vector.length pos_vec
        else if is_target (#2 (Vector.sub (pos_vec, i))) then i
        else find_idx (i + 1)

      val limit = find_idx 0

      fun scan 0 _ line col = (line, col)
        | scan n i line col =
            if i = limit then (line, col)
            else if String.sub (input_text, i) = #"\n" then scan (n - 1) (i + 1) (line + 1) 1
            else scan (n - 1) (i + 1) line (col + 1)
    in scan limit 0 1 1 end

  fun print_error (s, p: Position.T, p') =
    let
      val src = get_src ()
      val start_line = the_default 1 (Position.line_of (Input.pos_of src))
      val _ = Position.report (Position.range_position (Position.range(p, p'))) Markup.error 
      val (local_line, col) = get_line_col p
      val abs_line = start_line + local_line - 1
    in
      error ("Parse Error at line " ^ Int.toString abs_line ^
             ", column " ^ Int.toString (col + 1) ^ ": " ^ s ^ Position.here p)
    end

  fun tok (yypos, yytext, markup, typ, sort, cons) =
    let
      val p = get_pos yypos
      val p' = get_pos (yypos + (String.size yytext))
      val _ = report_token (yypos, String.size yytext, markup, typ, sort)
    in cons (p, p') end

  fun tok_val (yypos, yytext, markup, typ, sort, cons, value) =
    let
      val p = get_pos yypos
      val _ = report_token (yypos, String.size yytext, markup, typ, sort)
    in cons (value, p, p) end

  fun parse_source parse makeLexer get sameToken EOF source =
    let
      val (input_text, _) = Input.source_content source

      fun invoke lexstream =
        parse (0, lexstream, print_error, ())
      
      (* Use a local synchronization variable for parsing state instead of thread-local cells *)
      val parsed = Synchronized.var "parsed_flag" false

      fun input_string _ =
        Synchronized.guarded_access parsed
          (fn true => SOME ("", true)
            | false => SOME (input_text, true))

      val lexer = makeLexer input_string
      
      val eof_pos = get_pos (String.size input_text + 1)
      val dummyEOF = EOF (eof_pos, eof_pos)
      
      fun loop lexer =
        let
          val (res, lexer) = invoke lexer
          val (nextToken, lexer) = get lexer
        in 
          if sameToken (nextToken, dummyEOF) then ((), res) 
          else loop lexer 
        end
    in
      (#2 (loop lexer))
    end

  fun header () =
    "open Isabelle_lex_yacc\n" ^
    "structure Tokens = Tokens\n" ^
    "type svalue = Tokens.svalue\n" ^
    "type ('a,'b) token = ('a,'b) Tokens.token\n" ^
    "type lexresult= (svalue,pos) token\n" ^
    "fun eof () = Tokens.EOF(Position.none, Position.none)\n"

  fun linker name = 
    "structure "^name^" =\n"^
    "struct\n"^
    "  structure "^name^"LrVals =\n"^
    "    "^name^"LrValsFun(structure Token = LrParser.Token)\n"^
    "  structure "^name^"Lex =\n"^
    "    "^name^"LexFun(structure Tokens = "^name^"LrVals.Tokens)\n"^
    "  structure "^name^"Parser =\n"^
    "    Join(\n"^
    "      structure LrParser = LrParser\n"^
    "      structure ParserData = "^name^"LrVals.ParserData\n"^
    "      structure Lex = "^name^"Lex\n"^
    "    )\n"^
    "  fun parse_source ctxt source =\n"^
    "    let\n"^
    "      val _ = "^name^"Lex.UserDeclarations.set source ctxt\n"^
    "    in\n"^
    "      Isabelle_lex_yacc.parse_source\n"^
    "        "^name^"Parser.parse\n"^
    "        "^name^"Parser.makeLexer\n"^
    "        "^name^"Parser.Stream.get\n"^
    "        "^name^"Parser.sameToken\n"^
    "        "^name^"LrVals.Tokens.EOF\n"^
    "        source\n"^
    "    end\n"^
    "end\n"

end

(* ---------------------------------------------------------------------------
   Per-parse state.

   "Isabelle_lex_yacc" above keeps *one* process-wide state (source, context) and so cannot
   serve two parses at the same time; Isabelle runs commands (and, in a build, whole theories)
   in parallel, so two concurrent parses interleave their state and fail with spurious
   errors. "Lex_yacc_state" is the re-entrant alternative: every parse creates its own state
   object ("init"), hands it to the lexer (ML-Lex "%arg") and to the parser (ML-Yacc "%arg"),
   and nothing is shared between parses. It is opt-in: "ml_lex_yacc [state]" (LexYacc.thy)
   generates a lexer/parser pair that uses it; everything else is unchanged.

   Position lookup. ML-Lex's "yypos" is the 0-based index, in the *characters of the text
   handed to the lexer*, of the first character of a match. A source may contain symbols that
   are several characters long (e.g. "\<le>", 4 characters, one symbol), so the lookup table
   has one entry per character, each carrying the position of the symbol it belongs to, plus
   one final entry for the end of the text. It is computed once in "init" (the global
   "Isabelle_lex_yacc.get_pos" recomputes it on every call).
   --------------------------------------------------------------------------- *)

signature LEX_YACC_STATE =
sig
  type T
  type pos = Position.T
  val init: Proof.context -> Input.source -> T
  val source_of: T -> Input.source
  val context_of: T -> Proof.context
  val text_of: T -> string
  val get_pos: T -> int -> Position.T
  val report_token: T -> int * int * Markup.T * string * string -> unit
  val tok: T -> int * string * Markup.T * string * string * (Position.T * Position.T -> 'a) -> 'a
  val tok_val: T -> int * string * Markup.T * string * string * ('a * Position.T * Position.T -> 'b) * 'a -> 'b
  val print_error: T -> string * Position.T * Position.T -> 'a
  val parse_source:
    (int * 'a * (string * Position.T * Position.T -> 'b) * 'c -> 'd * 'e) ->
      ((int -> string) -> 'f -> 'a) -> ('e -> 'g * 'a) -> ('g * 'h -> bool) ->
      (Position.T * Position.T -> 'h) -> T -> 'f -> 'c -> 'd
  val header: unit -> string
  val linker: string -> string
end

structure Lex_yacc_state: LEX_YACC_STATE =
struct

type pos = Position.T

datatype T = State of {source: Input.source, ctxt: Proof.context, text: string, pos_vec: Position.T vector}

fun init ctxt source =
  let
    val syms = Input.source_explode source
    val text = Symbol_Pos.content syms
    (* one entry per character of "text", then the end position *)
    val per_char = maps (fn (s, p) => replicate (size s) p) syms
    val end_pos =
      (case try List.last syms of
         NONE => Input.pos_of source
       | SOME (s, p) => Position.symbol s p)
  in State {source = source, ctxt = ctxt, text = text, pos_vec = Vector.fromList (per_char @ [end_pos])} end

fun source_of (State {source, ...}) = source
fun context_of (State {ctxt, ...}) = ctxt
fun text_of (State {text, ...}) = text

fun get_pos (State {pos_vec, ...}) yypos =
  Vector.sub (pos_vec, Int.min (Int.max (0, yypos), Vector.length pos_vec - 1))

fun report_token st (start_idx, len, markup, token_type, token_sort) =
  if 0 < len then
    let
      val p = Position.range_position (Position.range (get_pos st start_idx, get_pos st (start_idx + len)))
      val ctxt = context_of st
    in
      Context_Position.report ctxt p markup;
      Context_Position.report_text ctxt p Markup.typing token_type;
      Context_Position.report_text ctxt p Markup.sorting token_sort
    end
  else ()

fun tok st (yypos, yytext, markup, typ, sort, cons) =
  let
    val p = get_pos st yypos
    val p' = get_pos st (yypos + String.size yytext)
    val _ = report_token st (yypos, String.size yytext, markup, typ, sort)
  in cons (p, p') end

fun tok_val st (yypos, yytext, markup, typ, sort, cons, value) =
  let
    val p = get_pos st yypos
    val _ = report_token st (yypos, String.size yytext, markup, typ, sort)
  in cons (value, p, p) end

(* line and column (1-based, within the source text) of the first character at position "p" *)
fun get_line_col (State {pos_vec, text, ...}) p =
  let
    val target = Position.offset_of p
    fun same pos = (case (Position.offset_of pos, target) of (SOME o1, SOME o2) => o1 = o2 | _ => false)
    fun find i = if i >= size text orelse same (Vector.sub (pos_vec, i)) then i else find (i + 1)
    val limit = find 0
    fun scan i line col =
      if i >= limit then (line, col)
      else if String.sub (text, i) = #"\n" then scan (i + 1) (line + 1) 1
      else scan (i + 1) line (col + 1)
  in scan 0 1 1 end

fun print_error st (s, p: Position.T, p') =
  let
    val start_line = the_default 1 (Position.line_of (Input.pos_of (source_of st)))
    val _ = Position.report (Position.range_position (Position.range (p, p'))) Markup.error
    val (local_line, col) = get_line_col st p
    val abs_line = start_line + local_line - 1
  in
    error ("Parse Error at line " ^ Int.toString abs_line ^
           ", column " ^ Int.toString col ^ ": " ^ s ^ Position.here p)
  end

(* The driver loop of "Isabelle_lex_yacc.parse_source", with the lexer and parser arguments
   ("lex_arg", "parser_arg" - usually the very same state object) passed explicitly. *)
fun parse_source parse makeLexer get sameToken EOF st lex_arg parser_arg =
  let
    val input_text = text_of st
    val consumed = Unsynchronized.ref false
    fun input_string _ = if !consumed then "" else (consumed := true; input_text)
    val lexer = makeLexer input_string lex_arg
    val eof_pos = get_pos st (String.size input_text)
    val dummyEOF = EOF (eof_pos, eof_pos)
    fun invoke lexstream = parse (0, lexstream, print_error st, parser_arg)
    fun loop lexer =
      let
        val (res, lexer) = invoke lexer
        val (nextToken, lexer) = get lexer
      in if sameToken (nextToken, dummyEOF) then res else loop lexer end
  in loop lexer end

(* Header of the generated lexer in "[state]" mode: like "Isabelle_lex_yacc.header", but the
   helpers take the state object, and "arg", "init" and "base" are defined with defaults that a
   language overrides in its "lex_user_declarations" (they come first in the generated file's
   user part, later definitions shadow earlier ones; "eof" is polymorphic in the argument so that
   it stays valid after an override of "arg"):
     arg   - the lexer's (and parser's) argument type, by default the bare state;
     init  - creates the argument for a parse from the context and the source;
     base  - projects the argument to the bare state. *)
fun header () =
  "open Lex_yacc_state\n" ^
  "structure Tokens = Tokens\n" ^
  "type svalue = Tokens.svalue\n" ^
  "type ('a,'b) token = ('a,'b) Tokens.token\n" ^
  "type lexresult= (svalue,pos) token\n" ^
  "type arg = Lex_yacc_state.T\n" ^
  "fun base (st : arg) : Lex_yacc_state.T = st\n" ^
  "fun eof _ = Tokens.EOF(Position.none, Position.none)\n"

fun linker name =
  "structure "^name^" =\n"^
  "struct\n"^
  "  structure "^name^"LrVals =\n"^
  "    "^name^"LrValsFun(structure Token = LrParser.Token)\n"^
  "  structure "^name^"Lex =\n"^
  "    "^name^"LexFun(structure Tokens = "^name^"LrVals.Tokens)\n"^
  "  structure "^name^"Parser =\n"^
  "    JoinWithArg(\n"^
  "      structure LrParser = LrParser\n"^
  "      structure ParserData = "^name^"LrVals.ParserData\n"^
  "      structure Lex = "^name^"Lex\n"^
  "    )\n"^
  "  fun parse_source ctxt source =\n"^
  "    let\n"^
  "      val st = "^name^"Lex.UserDeclarations.init ctxt source\n"^
  "    in\n"^
  "      Lex_yacc_state.parse_source\n"^
  "        "^name^"Parser.parse\n"^
  "        "^name^"Parser.makeLexer\n"^
  "        "^name^"Parser.Stream.get\n"^
  "        "^name^"Parser.sameToken\n"^
  "        "^name^"LrVals.Tokens.EOF\n"^
  "        ("^name^"Lex.UserDeclarations.base st) st st\n"^
  "    end\n"^
  "end\n"

end
\<close>

SML_import \<open>structure Position = struct open Position end\<close>
SML_import \<open>structure Markup = struct open Markup end\<close>
SML_import \<open>structure Isabelle_lex_yacc = struct open Isabelle_lex_yacc end\<close> 
SML_import \<open>structure Lex_yacc_state = struct open Lex_yacc_state end\<close>
SML_export \<open>structure LrParser = struct open LrParser end\<close>

end
