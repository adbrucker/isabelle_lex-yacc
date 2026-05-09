theory
  YaccLib
imports
  Main
begin 
SML_file\<open>mlyacc-polyml/mlyacc-lib/base.sig\<close> 
SML_file\<open>mlyacc-polyml/mlyacc-lib/join.sml\<close>
SML_file\<open>mlyacc-polyml/mlyacc-lib/lrtable.sml\<close>
SML_file\<open>mlyacc-polyml/mlyacc-lib/stream.sml\<close>   
SML_file\<open>mlyacc-polyml/mlyacc-lib/parser2.sml\<close>

ML\<open>
structure Isabelle_lex_yacc = struct
  type pos = Position.T
  val src = Unsynchronized.ref (Input.string "")
  val ctxt = Unsynchronized.ref (Context.the_local_context ())

  fun set source ctx =
    let
      val _ = src := source
      val _ = ctxt := ctx
    in () end

  fun reset () =
    let
      val _ = src := Input.string ""
      val _ = ctxt := Context.the_local_context ()
    in () end

  fun get_pos yypos =
    let
      val syms = Input.source_explode (!src)
      val pos_vec = Vector.fromList syms
      val idx = yypos - 1
    in
      if Vector.length pos_vec = 0 then Input.pos_of (!src)
      else if idx < 0 then #2 (Vector.sub (pos_vec, 0))
      else if idx >= Vector.length pos_vec then
        #2 (Vector.sub (pos_vec, Vector.length pos_vec - 1))
      else #2 (Vector.sub (pos_vec, idx))
    end

  fun report_token (start_idx, len, markup, token_type) =
    let
      fun report_char i =
        if i < len then
          let val p = get_pos (start_idx + i) in
            Context_Position.report (!ctxt) p markup;
            Context_Position.report_text (!ctxt) p Markup.typing ("Token: " ^ token_type);
            report_char (i + 1)
          end
        else ()
    in report_char 0 end

  fun get_line_col p =
    let
      val syms = Input.source_explode (!src)
      val pos_vec = Vector.fromList syms
      val input_text = Input.text_of (!src)
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

  fun print_error (s, p: Position.T, _) =
    let
      val start_line = the_default 1 (Position.line_of (Input.pos_of (!src)))
      val _ = Position.report p Markup.error
      val (local_line, col) = get_line_col p
      val abs_line = start_line + local_line - 1
    in
      error ("Parse Error at line " ^ Int.toString abs_line ^
             ", column " ^ Int.toString (col + 1) ^ ": " ^ s ^
             Position.here p)
    end

  fun tok (yypos, yytext, markup, name, cons) =
    let
      val p = get_pos yypos
      val _ = report_token (yypos, String.size yytext, markup, name)
    in cons (p, p) end

  fun tok_val (yypos, yytext, markup, name, cons, value) =
    let
      val p = get_pos yypos
      val _ = report_token (yypos, String.size yytext, markup, name)
    in cons (value, p, p) end

  fun parse_source parse makeLexer get sameToken EOF source =
    let
      val input_text = Input.text_of source
      
      fun invoke lexstream =
        parse (0, lexstream, print_error, ())
      
      val parsed = Unsynchronized.ref false
      fun input_string _ = if !parsed then "" else (parsed := true; input_text)
      
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
      the (#2 (loop lexer))
    end

  fun header () =
    "open Isabelle_lex_yacc\n" ^
    "structure Tokens = Tokens\n" ^
    "type svalue = Tokens.svalue\n" ^
    "type ('a,'b) token = ('a,'b) Tokens.token\n" ^
    "type lexresult= (svalue,pos) token\n" ^
    "fun eof () = Tokens.EOF(Position.none, Position.none)\n"

  fun linker name = 
    "structure "^name^": sig\n"^
    "  val parse_source : Proof.context -> Input.source -> int\n"^
    "end =\n"^
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
\<close>

SML_import \<open>structure Position = struct open Position end\<close>
SML_import \<open>structure Markup = struct open Markup end\<close>
SML_import \<open>structure Isabelle_lex_yacc = struct open Isabelle_lex_yacc end\<close> 
SML_export \<open>structure LrParser = struct open LrParser end\<close>

end
