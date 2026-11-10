theory
  StateTests
imports
  LexYacc
keywords
  "check_positions" :: diag
begin

section\<open>Tests for the Per-Parse State\<close>

text\<open>
  The position table of \<^ML_structure>\<open>Lex_yacc_state\<close>. ML-Lex's \<open>yypos\<close> is the 0-based
  index of a character in the text handed to the lexer, and the table has one entry per
  \<^emph>\<open>character\<close>, so a symbol of several characters (\<open>\<le>\<close> is written \<open>\\<le>\<close>, 5 characters)
  must give every one of its characters the position of the symbol, and the character after
  it the position of the next symbol.
\<close>

ML\<open>
fun offset p = the (Position.offset_of p)

fun check_positions source =
  let
    val syms = Input.source_explode source
    val text = #1 (Input.source_content source)
    val st = Lex_yacc_state.init @{context} source
    val first = offset (#2 (hd syms))

    (* expected offset, per character index, by walking the symbols *)
    fun expected _ [] = []
      | expected i ((s, p) :: rest) = replicate (size s) (offset p) @ expected (i + size s) rest
    val exp = expected 0 syms
    val _ = if length exp = size text then () else error "test setup: symbol sizes do not add up"
    fun fail i = error ("position of character " ^ Int.toString i ^ ": expected offset " ^
                        Int.toString (nth exp i) ^ ", got " ^ Int.toString (offset (Lex_yacc_state.get_pos st i)))
    val _ = List.app (fn i => if offset (Lex_yacc_state.get_pos st i) = nth exp i then () else fail i)
              (0 upto size text - 1)
    (* the entry after the last character is the end of the text; out-of-range indices clamp *)
    val end_off = offset (Lex_yacc_state.get_pos st (size text))
    val _ = if end_off > first + length syms - 1 then ()
            else error "the end position must lie after the last symbol"
    val _ = if offset (Lex_yacc_state.get_pos st (size text + 5)) = end_off andalso
               offset (Lex_yacc_state.get_pos st ~3) = first then ()
            else error "out-of-range indices must clamp"
  in () end
\<close>

ML\<open>
val _ = Outer_Syntax.command @{command_keyword "check_positions"} "check the position table"
  (Parse.input Parse.cartouche >> (fn source => Toplevel.keep (fn _ => check_positions source)))
\<close>

check_positions\<open>abc\<close>
check_positions\<open>a \<le> b \<Longrightarrow> c\<close>
check_positions\<open>\<alpha>\<beta>\<gamma> x
  y \<le> z\<close>

text\<open>An empty source has just the end entry:\<close>
ML\<open>
val _ = (ignore (Lex_yacc_state.get_pos (Lex_yacc_state.init @{context} (Input.string "")) 0); ())
\<close>

end
