theory LexYacc
  imports 
  YaccLib
keywords "ml_lex_yacc" :: thy_decl
   and "with_lex"::quasi_command
   and "and_yacc"::quasi_command

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
SML_file\<open>mlyacc-polyml_bootstrapping/yacc.grm.sig\<close> 

SML_file\<open>mlyacc-polyml_bootstrapping/yacc.grm.sml\<close>             
SML_file\<open>mlyacc-polyml_bootstrapping/yacc.lex.sml\<close>     
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

  fun generate name lex_input yacc_input thy =
    Isabelle_System.with_tmp_dir "lex_yacc" (fn input_path =>
      let
        val input_path = (Path.append input_path (Path.make ["input"]))
        val lex_file = Path.ext "lex" input_path
        val yacc_file = Path.ext "grm" input_path
        val _ = File.write lex_file lex_input
        val _ = File.write yacc_file yacc_input
        val _ = MlLexExe.run (File.platform_path lex_file)
        val _ = MlYaccExe.run (File.platform_path yacc_file)
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

        (* add automaton description to virtual file system *)
        val yacc_desc = File.read (Path.ext "grm.desc" input_path)
        val path_desc = (Path.make ["lex_yacc", name^".grm.desc"])
        val _ = Export.export thy (Path.binding0 path_desc) 
                                  (Bytes.contents_blob (Bytes.string yacc_desc))
        val _ = writeln(Export.message thy path_desc)
      in
        thy'
      end);
end
\<close>

ML\<open>
val _ = Outer_Syntax.command @{command_keyword "ml_lex_yacc"}
        "Generate and load SML parser based on lex/yacc specifications." 
        ((Parse.name --  \<^keyword>\<open>with_lex\<close> -- Parse.cartouche -- \<^keyword>\<open>and_yacc\<close> -- Parse.cartouche) 
      >> (fn ((((name,_),lex_spec), _), yacc_spec) =>
          Toplevel.theory (fn thy => MlLexYacc.generate name lex_spec yacc_spec thy)))
\<close>
end
