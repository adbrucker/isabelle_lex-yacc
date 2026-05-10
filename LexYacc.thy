theory LexYacc
  imports 
  YaccLib
keywords "ml_lex_yacc" :: thy_decl
    and  "lex_user_declarations" "lex_definitions" "lex_rules" 
    "yacc_user_declarations" "yacc_definitions" "yacc_rules" :: quasi_command
begin 

SML_import \<open>val pide_error = error \<close>
SML_import \<open>val pide_warning = warning \<close>
SML_import \<open>val pide_writeln = writeln \<close>


section\<open>ML Lex\<close>
SML_file \<open>mllex-polyml/LexGen.sml\<close>
SML_export \<open>structure MlLexExe = struct val run = LexGen.lexGen end\<close> 



section\<open>ML Yacc\<close>

SML_file\<open>mlyacc-polyml/src/utils.sig\<close>
SML_file\<open>mlyacc-polyml/src/utils.sml\<close> 
SML_file\<open>mlyacc-polyml/src/sigs.sml\<close>  
SML_file\<open>mlyacc-polyml/src/verbose.sml\<close> 
SML_file\<open>mlyacc-polyml/src/coreutils.sml\<close> 
SML_file\<open>mlyacc-polyml/src/grammar.sml\<close> 
SML_file\<open>mlyacc-polyml/src/graph.sml\<close> 
SML_file\<open>mlyacc-polyml/src/hdr.sml\<close> 
SML_file\<open>mlyacc-polyml/src/lalr.sml\<close>  
SML_file\<open>mlyacc-polyml/src/absyn.sig\<close> 
SML_file\<open>mlyacc-polyml/src/absyn.sml\<close> 
SML_file\<open>mlyacc-polyml/src/core.sml\<close>  
SML_file\<open>mlyacc-polyml/src/look.sml\<close>
SML_file\<open>mlyacc-polyml/src/mklrtable.sml\<close> 
SML_file\<open>mlyacc-polyml/src/shrink.sml\<close>  
SML_file\<open>mlyacc-polyml/src/yacc.sml\<close>  
SML_file\<open>mlyacc-polyml/src/mkprstruct.sml\<close>  
SML_file\<open>mlyacc-polyml/src/parse.sml\<close> 

text\<open>Generated: \<close>
SML_file\<open>mlyacc-polyml/src/bootstrap/yacc.grm.sig\<close> 
SML_file\<open>mlyacc-polyml/src/bootstrap/yacc.grm.sml\<close>             
SML_file\<open>mlyacc-polyml/src/bootstrap/yacc.lex.sml\<close>     

text\<open>Final linking and export\<close>
SML_file\<open>mlyacc-polyml/src/link.sml\<close>
SML_export \<open>structure MlYaccExe = struct val run = ParseGen.parseGen end\<close> 


text\<open>Runtime Setup\<close>
SML_import \<open>structure Position = struct open Position end\<close>
SML_import \<open>structure Markup = struct open Markup end\<close>
ML_file\<open>mlyacc-polyml/mlyacc-lib/base.sig\<close>
ML_file\<open>mlyacc-polyml/mlyacc-lib/join.sml\<close>





section\<open>Glue Layer\<close>
ML\<open>
signature ML_LEX_YACC_HIGHLIGHTER =
  sig
    val scan_lex_defs: Proof.context -> Input.source -> unit
    val scan_lex_rules: Proof.context -> Input.source -> unit
    val scan_yacc_defs: Proof.context -> Input.source -> unit
    val scan_yacc_rules: Proof.context -> Input.source -> unit
  end

structure MlLexYaccHighlighter:ML_LEX_YACC_HIGHLIGHTER = struct
  fun is_alnum s = 
    Symbol.is_ascii_letter s orelse Symbol.is_ascii_digit s orelse s = "_" orelse s = "'"
  
  fun take_word [] acc = (rev acc, [])
    | take_word ((s, p) :: ss) acc =
        if is_alnum s then take_word ss ((s, p) :: acc)
        else (rev acc, (s, p) :: ss)

  fun report ctxt markup syms =
    List.app (fn (_, p) => Context_Position.report ctxt p markup) syms

  fun consume_comment [] acc = (rev acc, [])
    | consume_comment ((s1, p1) :: (s2, p2) :: rest) acc =
        if s1 = "*" andalso s2 = ")" then 
          (rev ((s2, p2) :: (s1, p1) :: acc), rest)
        else 
          consume_comment ((s2, p2) :: rest) ((s1, p1) :: acc)
    | consume_comment (x :: rest) acc = 
        consume_comment rest (x :: acc)

  fun consume_string [] acc = (rev acc, [])
    | consume_string ((s1, p1) :: rest) acc =
        if s1 = "\"" then 
          (rev ((s1, p1) :: acc), rest)
        else if s1 = "\\" andalso not (null rest) then
          consume_string (tl rest) (hd rest :: (s1, p1) :: acc)
        else 
          consume_string rest ((s1, p1) :: acc)

  (* Quick and dirty parser for  ML code inside Yacc/Lex rules. *)
  fun scan_sml_action _ _  [] = []
    | scan_sml_action ctxt depth ((s, p) :: ss) =
        if s = "(" andalso not (null ss) andalso #1 (hd ss) = "*" then
          let
            val (comment_syms, rest) = consume_comment (tl ss) [hd ss, (s, p)]
            val _ = report ctxt Markup.comment comment_syms
          in 
            scan_sml_action ctxt depth rest 
          end
        else if s = "\"" then
          let
            val (str_syms, rest) = consume_string ss [(s, p)]
            val _ = report ctxt Markup.string str_syms
          in 
            scan_sml_action ctxt depth rest 
          end
        else if s = "(" then
          (Context_Position.report ctxt p Markup.delimiter; 
           scan_sml_action ctxt (depth + 1) ss)
        else if s = ")" then
          (Context_Position.report ctxt p Markup.delimiter;
           if depth = 1 then ss 
           else scan_sml_action ctxt (depth - 1) ss)
        else if s = "=" andalso not (null ss) andalso #1 (hd ss) = ">" then
          (report ctxt Markup.keyword2 [(s, p), hd ss];
           scan_sml_action ctxt depth (tl ss))
        else if member (op =) ["+", "-", "*", "/", ":", "|", ",", ";", ".", "[", "]", "=", "<", ">", "~"] s then
          (Context_Position.report ctxt p Markup.delimiter;
           scan_sml_action ctxt depth ss)
        else if is_alnum s then
          let
            val (word_syms, rest) = take_word ss [(s, p)]
            val word = String.concat (map #1 word_syms)
            val ml_kws = [
              "val", "fun", "let", "in", "end", "case", "of", "if", "then", "else", 
              "SOME", "NONE", "true", "false", "structure", "sig", "struct", "open", "type"
            ]
            val markup = if member (op =) ml_kws word then Markup.keyword2 else Markup.free
          in
            report ctxt markup word_syms;
            scan_sml_action ctxt depth rest
          end
        else 
          scan_sml_action ctxt depth ss

  fun scan_lex_defs ctxt source =
    let
      val syms = Input.source_explode source
      fun scan _ [] = ()
        | scan awaiting_sml ((s, p) :: ss) =
            if s = "(" andalso not (null ss) andalso #1 (hd ss) = "*" then
              let
                val (comment_syms, rest) = consume_comment (tl ss) [hd ss, (s, p)]
                val _ = report ctxt Markup.comment comment_syms
              in 
                scan awaiting_sml rest 
              end
            else if s = "\"" then
              let
                val (str_syms, rest) = consume_string ss [(s, p)]
                val _ = report ctxt Markup.string str_syms
              in 
                scan awaiting_sml rest 
              end
            else if s = "%" then
              let
                val (word_syms, rest) = take_word ss []
                val word = "%" ^ String.concat (map #1 word_syms)
                
                val is_sml_trigger = member (op =) ["%header", "%arg"] word
                val is_kw = member (op =) [
                  "%header", "%s", "%S", "%arg", "%pos", "%pure", "%reject", "%count"
                ] word
                val markup = if is_kw then Markup.keyword1 else Markup.keyword3
              in
                Context_Position.report ctxt p markup;
                report ctxt markup word_syms;
                scan is_sml_trigger rest 
              end
            else if s = "(" then
              (Context_Position.report ctxt p Markup.delimiter;
               if awaiting_sml then
                 let
                   val remaining_stream = scan_sml_action ctxt 1 ss
                 in
                   scan false remaining_stream
                 end
               else
                 scan awaiting_sml ss)
            else if s = ")" then
              (Context_Position.report ctxt p Markup.delimiter; 
               scan awaiting_sml ss)
            else if s = "=" then
              (Context_Position.report ctxt p Markup.keyword2; 
               scan false ss)
            else if member (op =) ["{", "}", "[", "]", ";", "+", "*", "?", "|", "\\", "^", "$", "."] s then
              (Context_Position.report ctxt p Markup.keyword3; 
               scan awaiting_sml ss)
            else if is_alnum s then
              let
                val (word_syms, rest) = take_word ss [(s, p)]
                val _ = report ctxt Markup.free word_syms
              in 
                scan awaiting_sml rest 
              end
            else 
              scan awaiting_sml ss
    in 
      scan false syms 
    end

  fun scan_lex_rules ctxt source =
    let
      val syms = Input.source_explode source
      fun scan _ [] = ()
        | scan awaiting_action ((s, p) :: ss) =
            if s = "<" orelse s = ">" orelse s = "{" orelse s = "}" then
              (Context_Position.report ctxt p Markup.delimiter; 
               scan awaiting_action ss)
            else if s = "\"" then
              let
                val (str_syms, rest) = consume_string ss [(s, p)]
                val _ = report ctxt Markup.string str_syms
              in 
                scan awaiting_action rest 
              end
            else if s = "=" andalso not (null ss) andalso #1 (hd ss) = ">" then
              (report ctxt Markup.keyword2 [(s, p), hd ss]; 
               scan true (tl ss))
            else if s = "(" andalso not (null ss) andalso #1 (hd ss) <> "*" then
              (Context_Position.report ctxt p Markup.delimiter;
               if awaiting_action then
                 let
                   val remaining_stream = scan_sml_action ctxt 1 ss
                 in
                   scan false remaining_stream
                 end
               else
                 scan awaiting_action ss)
            else if s = ")" then
              (Context_Position.report ctxt p Markup.delimiter; 
               scan awaiting_action ss)
            else if s = "(" andalso not (null ss) andalso #1 (hd ss) = "*" then
              let
                val (comment_syms, rest) = consume_comment (tl ss) [hd ss, (s, p)]
                val _ = report ctxt Markup.comment comment_syms
              in 
                scan awaiting_action rest 
              end
            else if member (op =) ["+", "*", "?", "|", "\\", "^", "$", "."] s then
              (Context_Position.report ctxt p Markup.keyword3; 
               scan awaiting_action ss)
            else if is_alnum s then
              let
                val (word_syms, rest) = take_word ss [(s, p)]
                val _ = report ctxt Markup.free word_syms
              in 
                scan awaiting_action rest 
              end
            else 
              scan awaiting_action ss
    in 
      scan false syms 
    end

  fun scan_yacc_defs ctxt source =
    let
      val syms = Input.source_explode source
      
      fun scan [] = ()
        | scan ((s, p) :: ss) =
            if s = "|" then
              (Context_Position.report ctxt p Markup.keyword2; 
               scan ss)
            else if s = "(" andalso not (null ss) andalso #1 (hd ss) = "*" then
              let
                val (comment_syms, rest) = consume_comment (tl ss) [hd ss, (s, p)]
                val _ = report ctxt Markup.comment comment_syms
              in 
                scan rest 
              end
            else if s = "(" then
              let
                val _ = Context_Position.report ctxt p Markup.delimiter
                val remaining_stream = scan_sml_action ctxt 1 ss
              in
                scan remaining_stream
              end
            else if s = "%" then
              let
                val (word_syms, rest) = take_word ss []
                val word = "%" ^ String.concat (map #1 word_syms)
                val is_kw = member (op =) [
                  "%name", "%term", "%nonterm", "%pos", "%eop", "%pure", 
                  "%noshift", "%left", "%right", "%nonassoc", "%keyword", 
                  "%prefer", "%subst", "%header", "%verbose", "%value"
                ] word
                val markup = if is_kw then Markup.keyword1 else Markup.keyword3
              in
                Context_Position.report ctxt p markup;
                report ctxt markup word_syms;
                scan rest
              end
            else if is_alnum s then
              let
                val (word_syms, rest) = take_word ss [(s, p)]
                val word = String.concat (map #1 word_syms)
                val markup = if word = "of" then Markup.keyword2 else Markup.free
              in
                report ctxt markup word_syms;
                scan rest
              end
            else 
              scan ss
    in 
      scan syms 
    end


  fun scan_yacc_rules ctxt source =
    let
      val syms = Input.source_explode source
      
      fun scan [] = ()
        | scan ((s, p) :: ss) =
            if s = ":" orelse s = "|" orelse s = ";" then
              (Context_Position.report ctxt p Markup.keyword2; 
               scan ss)
            else if s = "(" andalso not (null ss) andalso #1 (hd ss) <> "*" then
              let
                val _ = Context_Position.report ctxt p Markup.delimiter
                val remaining_stream = scan_sml_action ctxt 1 ss
              in
                scan remaining_stream
              end
            else if s = "%" then
              let
                val (word_syms, rest) = take_word ss []
                val word = "%" ^ String.concat (map #1 word_syms)
              in
                if word = "%prec" then 
                  report ctxt Markup.keyword1 ((s, p) :: word_syms) 
                else ();
                scan rest
              end
            else if s = "(" andalso not (null ss) andalso #1 (hd ss) = "*" then
              let
                val (comment_syms, rest) = consume_comment (tl ss) [hd ss, (s, p)]
                val _ = report ctxt Markup.comment comment_syms
              in 
                scan rest 
              end
            else if is_alnum s then
              let
                val (word_syms, rest) = take_word ss [(s, p)]
                val _ = report ctxt Markup.free word_syms
              in
                scan rest
              end
            else 
              scan ss
    in 
      scan syms 
    end

end
\<close>
ML\<open>
structure MlLexYacc = struct

  fun generate verbose expert no_linking name lex_decl lex_defs lex_rules yacc_decl yacc_defs yacc_rules thy = 
      let
        fun store show_msg ext data  = 
          let
            val dir_name = "lex_yacc"
            fun path_of ext = (Path.make [dir_name, name^"."^ext])
            val _ = Export.export thy (Path.binding0 (path_of ext)) (Bytes.contents_blob (Bytes.string data))
          in
            if show_msg then writeln(Export.message thy (Path.make [dir_name])) else ()
          end
        val ctxt = Proof_Context.init_global thy

        val _ = Option.map ML_Lex.read_source lex_decl
        val _ = Option.map ML_Lex.read_source yacc_decl

        val _ = MlLexYaccHighlighter.scan_yacc_defs ctxt yacc_defs
        val _ = MlLexYaccHighlighter.scan_yacc_rules ctxt yacc_rules
        val _ = MlLexYaccHighlighter.scan_lex_defs ctxt lex_defs
        val _ = MlLexYaccHighlighter.scan_lex_rules ctxt lex_rules

        val lex_decl_syms = case lex_decl of NONE => [] | SOME l => Input.source_explode l
        val lex_syms = if expert
                       then (lex_decl_syms)@
                            (Symbol_Pos.explode("\n%%\n", Position.none))@
                            (Input.source_explode lex_defs)@
                            (Symbol_Pos.explode("\n%%\n", Position.none))@
                            (Input.source_explode lex_rules)
                       else (Symbol_Pos.explode(Isabelle_lex_yacc.header()^"\n", Position.none))@
                            (lex_decl_syms)@
                            (Symbol_Pos.explode("\n%%\n", Position.none))@
                            (Symbol_Pos.explode("%header (functor "^name^"LexFun(structure Tokens: "^name^"_TOKENS));\n", Position.none))@
                            (Input.source_explode lex_defs)@
                            (Symbol_Pos.explode("\n%%\n", Position.none))@
                            (Input.source_explode lex_rules)
        val lex_spec_string = Symbol_Pos.content lex_syms;
        val lex_pos_vec = Vector.fromList (map #2 lex_syms @ [Position.none]);
        fun lex_pos_map offset = Vector.sub (lex_pos_vec, Int.min (Int.max (0, offset), Vector.length lex_pos_vec - 1));
        val _ = Isabelle_lex_yacc.reset()  
        val _ = if verbose then store true "lex" lex_spec_string else ()
        val lex_sml = MlLexExe.run verbose (SOME lex_pos_map) lex_spec_string
        val _ = Isabelle_lex_yacc.reset()  
        val _ = if verbose then store false "lex.sml" lex_sml else ()

        val yacc_decl_syms = case yacc_decl of NONE => [] | SOME l => Input.source_explode l
        val yacc_syms = if expert
                       then (yacc_decl_syms)@
                            (Symbol_Pos.explode("\n%%\n", Position.none))@
                            (Input.source_explode yacc_defs)@
                            (Symbol_Pos.explode("\n%%\n", Position.none))@
                            (Input.source_explode yacc_rules)
                       else (yacc_decl_syms)@
                            (Symbol_Pos.explode("\n%%\n", Position.none))@
                            (Symbol_Pos.explode("%name "^name^"\n", Position.none))@
                            (Input.source_explode yacc_defs)@
                            (Symbol_Pos.explode("\n%%\n", Position.none))@
                            (Input.source_explode yacc_rules)
        val yacc_spec_string = Symbol_Pos.content yacc_syms;
        val yacc_pos_vec = Vector.fromList (map #2 yacc_syms @ [Position.none]);
        fun yacc_pos_map offset = Vector.sub (yacc_pos_vec, Int.min (Int.max (0, offset), Vector.length yacc_pos_vec - 1));
        val _ = if verbose then store false "grm" yacc_spec_string else ()

        val _ = Isabelle_lex_yacc.reset()
  
        val yacc_res = MlYaccExe.run verbose (SOME yacc_pos_map) yacc_spec_string
        val _ = Isabelle_lex_yacc.reset()  
        val yacc_sig = #sigs yacc_res
        val yacc_sml = #ml yacc_res
        val yacc_desc = #desc yacc_res
        val _ = Isabelle_lex_yacc.reset()  
        val _ = if verbose then store false "grm.sml" yacc_sml else ()
        val _ = if verbose then store false "grm.sig" yacc_sig else ()
        val _ = if verbose then case yacc_desc of SOME data => store false "grm.desc" data | NONE => () else ()

        val generated_code = yacc_sig^"\n\n"^lex_sml^"\n\n"^yacc_sml

        val toks =
          ML_Lex.read generated_code
          |> map (fn Antiquote.Text tok => tok 
                   | _ => error "Unexpected antiquote in generated code")
        val flags: ML_Compiler.flags =
           {environment = ML_Env.SML_export, redirect = false, verbose = false, catch_all = true,
            debug = NONE, writeln = writeln, warning = warning}
        val thy' = Context.theory_map (
          ML_Context.exec (fn () => 
            ML_Compiler.eval flags Position.none toks
          )
        ) thy

        val link_sml = Isabelle_lex_yacc.linker name
        val _ = if verbose then store false "link.sml" link_sml else ()
        val thy'' = if expert orelse no_linking 
                    then thy'
                    else let 
                    val toks =
                      ML_Lex.read link_sml
                      |> map (fn Antiquote.Text tok => tok 
                               | _ => error "Unexpected antiquote in generated code")
                    val flags: ML_Compiler.flags =
                       {environment = ML_Env.Isabelle, redirect = false, verbose = false, catch_all = true,
                        debug = NONE, writeln = writeln, warning = warning}
                    in
                      Context.theory_map (
                        ML_Context.exec (fn () => 
                          ML_Compiler.eval flags Position.none toks
                        )
                      ) thy'
                    end

      in
        thy''
      end;

end
\<close>

ML \<open>
local
  val parse_options =
    Scan.optional (\<^keyword>\<open>[\<close> |-- Parse.list Parse.name --| \<^keyword>\<open>]\<close>) []

  (* Parser for the lex specification blocks *)
  val parse_lex =
    Scan.optional (\<^keyword>\<open>lex_user_declarations\<close> |-- Parse.ML_source >> SOME) NONE --
    (\<^keyword>\<open>lex_definitions\<close> |-- Parse.input Parse.cartouche) --
    (\<^keyword>\<open>lex_rules\<close> |-- Parse.input Parse.cartouche)

  (* Parser for the yacc specification blocks *)
  val parse_yacc =
    Scan.optional (\<^keyword>\<open>yacc_user_declarations\<close> |-- Parse.ML_source >> SOME) NONE --
    (\<^keyword>\<open>yacc_definitions\<close> |-- Parse.input Parse.cartouche) --
    (\<^keyword>\<open>yacc_rules\<close> |-- Parse.input Parse.cartouche)
in
  val _ = Outer_Syntax.command @{command_keyword "ml_lex_yacc"}
          "Generate and load SML parser based on lex/yacc specifications." 
        (
          (parse_options -- Parse.name --| \<^keyword>\<open>where\<close> -- 
           parse_lex --| \<^keyword>\<open>and\<close> -- 
           parse_yacc)
        >> (fn (((opts, name), ((lex_user, lex_defs), lex_rules)), ((yacc_user, yacc_defs), yacc_rules)) =>
            let
              val is_verbose = member (op =) opts "verbose"
              val is_expert = member (op =) opts "expert" 
              val is_no_linking = member (op =) opts "no_linking" 
            in
              Toplevel.theory (fn thy => 
                MlLexYacc.generate is_verbose is_expert is_no_linking name 
                  lex_user lex_defs lex_rules 
                  yacc_user yacc_defs yacc_rules thy)
            end)
        )
end
\<close>

section \<open>Manual\<close>

text \<open>
  The @{command "ml_lex_yacc"} command provides an integrated, Isar-level interface for defining 
  and generating Standard ML parsers using ML-Lex and ML-Yacc directly within Isabelle theories. 
  It processes lexical and grammatical specifications, compiles them into SML structures, 
  and loads them into the current Isabelle theory context.

  @{rail \<open>
    @@{command ml_lex_yacc} ('[' (name + ',') ']')? name \<newline> 'where'
      lex_spec 'and' yacc_spec
    ;
    lex_spec: ('lex_user_declarations' text)?
              'lex_definitions'  \<newline> text
              'lex_rules' text
    ;
    yacc_spec: ('yacc_user_declarations' text)?
               'yacc_definitions'  \<newline> text
               'yacc_rules' text
  \<close>}

  Description
  \<^item> \<open>name\<close>: Specifies the name of the parser. By default, it is also used as prefix for the 
    generated SML structures. For example, providing the name "MyLang" will generate underlying 
    ML structures like \<open>MyLangLex\<close>, \<open>MyLangLrVals\<close>, and a unified \<open>MyLangParser\<close>. In expert mode 
    (see below), the SML structures will be named based on the lex and yacc directives that are 
    part of the lex and yacc specifications (e.g., \<open>%name\<close>). 

  \<^item> The lex specification is broken into three parts. In the original lex specification, these 
    parts are separated by \<open>%%\<close> (which should be omitted here). Furthermore, by default no directives
    specifying functors or names should be included, as they break the automated linking): 

    \<^item> \<open>lex_user_declarations\<close> (optional): An embedded ML source block containing user-level
      SML code (e.g., token type aliases, state variables, or helper functions). 

    \<^item> \<open>lex_definitions\<close>: The ml-lex definitions, such as regular expression macros (e.g., 
      \<open>alpha=[A-Za-z];\<close>) and lexer state declarations (e.g., \<open>%s COMMENT;\<close>).

    \<^item> \<open>lex_rules\<close>: The ml-lex scanning rules and their corresponding SML semantic actions.

  \<^item> The yacc specification is broken into three parts. In the original lex specification, these 
    parts are separated by \<open>%%\<close> (which should be omitted here). Furthermore, by default no directives
    specifying functors or names should be included, as they break the automated linking): 

    \<^item> \<open>yacc_user_declarations\<close> (optional): An embedded ML source block containing user-level 
      SML code to be injected at the top of the generated parser. Useful for defining custom 
      datatypes or helper functions used in semantic actions.

    \<^item> \<open>yacc_definitions\<close>: A cartouche containing ML-Yacc definitions, including \<open>%term\<close> and 
      \<open>%nonterm\<close> declarations, associativity, and start symbols.

    \<^item> \<open>yacc_rules\<close>: A cartouche containing the ML-Yacc grammar productions (BNF format) and 
      their corresponding SML semantic actions.

  \<^item> The command accepts two configuration options that can be provided as a comma-separated list 
    enclosed in square brackets \<open>[ ... ]\<close> immediately following the command name:

    \<^item> \<open>verbose\<close>: Instructs the underlying ML-Yacc/ML-Lex generator to output verbose
      information. Generated artifacts  (such as SML code or the automaton descrcripton) are stored
      for inspection in Isabelle's virtual file system. 

    \<^item> \<open>expert\<close>: Enables advanced/expert mode where the specified lex and yacc specifications are 
      passed unmodified to lex yacc (except adding the \<open>%%\<close> separators between the three block 
      of each specification. Furthermore, automated linking is disabled in expert mode. 

    \<^item> \<open>no_linking\<close>: Skips the automatic generation of the boilerplate "linking" structure 
      (the code that normally joins the Lexer, ParserData, and LrVals together). This is useful 
      if you intend to manually wire the generated ML functor blocks together later.
\<close>


end
