theory LexYacc
  imports 
  YaccLib
keywords "ml_lex_yacc" :: thy_decl
    and  "lex_user_declarations" "lex_definitions" "lex_rules" 
    "yacc_user_declarations" "yacc_definitions" "yacc_rules" :: quasi_command
begin 

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

structure MlLexYacc = struct
  fun generate_new verbose expert no_linking name lex_decl lex_defs lex_rules yacc_decl yacc_defs yacc_rules thy = 
    Isabelle_System.with_tmp_dir "lex_yacc" (fn input_path =>
      let
        val _ = Option.map ML_Lex.read_source lex_decl
        val _ = Option.map ML_Lex.read_source yacc_decl

        val (lex_decl_str, lex_decl_pos) = case lex_decl of SOME d => Input.source_content d | NONE => ("", Position.none) 
        val (lex_defs_str, lex_defs_pos) = Input.source_content lex_defs
        val (lex_rules_str, lex_rules_pos) = Input.source_content lex_rules

        val (yacc_decl_str, yacc_decl_pos) = case yacc_decl of SOME d => Input.source_content d | NONE => ("", Position.none)
        val (yacc_defs_str, yacc_defs_pos) = Input.source_content yacc_defs
        val (yacc_rules_str, yacc_rules_pos) = Input.source_content yacc_rules

        val lex_spec = if expert 
                       then lex_decl_str^"\n%%\n"^lex_defs_str^"\n%%\n"^lex_rules_str
                       else Isabelle_lex_yacc.header()^"\n"^
                            lex_decl_str^"\n%%\n"^
                            "%header (functor "^name^"LexFun(structure Tokens: "^name^"_TOKENS));\n"^
                            lex_defs_str^"\n%%\n"^lex_rules_str
        val yacc_spec = if expert 
                       then yacc_decl_str^"\n%%\n"^yacc_defs_str^"\n%%\n"^yacc_rules_str
                       else yacc_decl_str^"\n%%\n"^
                            "%name "^name^"\n"^
                            yacc_defs_str^"\n%%\n"^
                            yacc_rules_str  

        val input_path = (Path.append input_path (Path.make ["input"]))
        val lex_file = Path.ext "lex" input_path
        val yacc_file = Path.ext "grm" input_path
 
        val _ = File.write lex_file lex_spec
        val _ = File.write yacc_file yacc_spec
        val _ = MlLexExe.run (File.platform_path lex_file)
        val ctxt = Proof_Context.init_global thy

        (* val _ = Isabelle_lex_yacc.set yacc_defs ctxt *) 
        val _ = MlYaccExe.run (File.platform_path yacc_file)
        val _ = Isabelle_lex_yacc.reset()  

        val lex_sml = File.read (Path.ext "lex.sml" input_path)
        val yacc_sig = File.read (Path.ext "grm.sig" input_path)
        val yacc_sml = File.read (Path.ext "grm.sml" input_path)
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

        val _ = if verbose 
                then let
                  val dir_name = "lex_yacc"
                  fun path_of ext = (Path.make [dir_name, name^"."^ext])
                  val grm_desc_path = (Path.ext "grm.desc" input_path)
                  val _ = if File.exists grm_desc_path 
                          then let val txt = File.read (Path.ext "grm.desc" input_path) in 
                                Export.export thy (Path.binding0 (path_of "grm.desc")) (Bytes.contents_blob (Bytes.string txt))
                          end else {} 
                  val _ = Export.export thy (Path.binding0 (path_of "lex")) (Bytes.contents_blob (Bytes.string lex_spec))
                  val _ = Export.export thy (Path.binding0 (path_of "grm")) (Bytes.contents_blob (Bytes.string yacc_spec))
                  val _ = Export.export thy (Path.binding0 (path_of "lex.sml")) (Bytes.contents_blob (Bytes.string lex_sml))
                  val _ = Export.export thy (Path.binding0 (path_of "grm.sml")) (Bytes.contents_blob (Bytes.string yacc_sml))
                  val _ = Export.export thy (Path.binding0 (path_of "grm.sig")) (Bytes.contents_blob (Bytes.string yacc_sig))
                  val _ = if expert 
                          then () 
                          else Export.export thy (Path.binding0 (path_of "link.sml")) (Bytes.contents_blob (Bytes.string link_sml))
                in
                  writeln(Export.message thy (Path.make [dir_name]))
                end
        else ()
      in
        thy''
      end);

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
                MlLexYacc.generate_new is_verbose is_expert is_no_linking name 
                  lex_user lex_defs lex_rules 
                  yacc_user yacc_defs yacc_rules thy)
            end)
        )
end
\<close>


end
