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
    val pos_lookup = Unsynchronized.ref (fn (yypos: int) => Position.none)
    val report_token = Unsynchronized.ref (fn (idx: int, len: int, m: Markup.T, name: string) => ()) 
    fun get_pos yypos = (!pos_lookup) yypos
    fun tok (yypos, yytext, markup, name, cons) = 
        let val p = get_pos yypos
            val _ = (!report_token) (yypos, String.size yytext, markup, name)
        in cons (p, p) end 

    fun tok_val (yypos, yytext, markup, name, cons, value) =
        let val p = get_pos yypos
            val _ = (!report_token) (yypos, String.size yytext, markup, name)
        in cons (value, p, p) end 
    fun error' (e, p: Position.T, _) = ()  
    fun header () = "open Isabelle_lex\n"^
                    "structure Tokens = Tokens\n"^
                    "type svalue = Tokens.svalue\n"^
                    "type ('a,'b) token = ('a,'b) Tokens.token\n"^
                    "type lexresult= (svalue,pos) token\n"^
                    "fun eof () = Tokens.EOF(Position.none, Position.none)\n"

end
\<close>

SML_import \<open>structure Position = struct open Position end\<close>
SML_import \<open>structure Markup = struct open Markup end\<close>
SML_import \<open>structure isabelle_lex = struct open isabelle_lex end\<close> 

end
