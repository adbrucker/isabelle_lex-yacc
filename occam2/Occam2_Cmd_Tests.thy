theory Occam2_Cmd_Tests
  imports Occam2 Occam2_Tests
begin

section\<open>Command-level Tests\<close>

text\<open>
  Imports \<open>Occam2_Tests\<close> (not merely \<open>Occam2\<close>) to force a sequential build order: the
  lexer's comment/layout state is process-wide (the project's known re-entrancy
  limitation), so two theories running parser commands with no import edge between
  them could race on it.
\<close>

subsection\<open>Accepting commands\<close>

occam2_ident\<open>foo.bar\<close>

occam2_expr\<open>(a + b) * c\<close>

occam2_expr\<open>x = 1\<close>

occam2\<open>
INT x:
SEQ
  x := 1
  x := x + 1
\<close>

occam2_reject\<open>
INT x:
SEQ
x := 1
\<close>

occam2_expr_reject\<open>a + b * c\<close>

occam2_ident_reject\<open>SEQ\<close>

subsection\<open>Binding\<close>

text\<open>Declarations, uses and the scoping rules. Hover/click in jEdit to check the links;
  here the commands merely have to be accepted, the hyperlinks being PIDE markup.\<close>

occam2\<open>
PROC inc (INT n)
  n := n + 1
:
INT counter:
SEQ
  counter := 0
  inc (counter)
  SEQ i = 0 FOR 10
    counter := counter + i
\<close>

text\<open>A library-style unit leaves its names in the environment: the next fragment can use
  \<open>twice\<close> without declaring it.\<close>

occam2\<open>
VAL INT limit IS 100:
INT FUNCTION twice (VAL INT n)
  INT r:
  VALOF
    r := n * 2
  RESULT r
:
\<close>

occam2\<open>
INT y:
SEQ
  y := twice (limit)
\<close>

ML\<open>
fun check name b = if b then writeln ("OK: " ^ name) else error ("FAILED: " ^ name)

val idents = (case OEnv.get (Context.Theory @{theory}) of OEnv.mk {idents, ...} => idents)
val _ = check "twice is registered"  (Symtab.defined idents "twice")
val _ = check "limit is registered"  (Symtab.defined idents "limit")
val _ = check "a unit's local names do not leak" (not (Symtab.defined idents "counter"))
val _ = check "a procedure's formals do not leak" (not (Symtab.defined idents "n"))
\<close>

subsection\<open>Antiquotations and navigation\<close>

text\<open>A comment attaches to the node starting at the next token; with no navigation string the
  handler sees that node (here the whole assignment).\<close>

occam2\<open>
INT x:
SEQ
  --@ probe_ast
  x := 1
  x := 2
\<close>

ML\<open>
val _ = check "probe_ast sees the commented assignment"
  (Occam2_Ast.pp_root (!OCCAM_AST) = "x := 1")
\<close>

text\<open>Navigation: \<open>uu\<close> re-targets to the enclosing process, \<open>d\<close> to the first child, \<open>rrd\<close> to
  the second (as in C11, the first \<open>r\<close> only starts the cursor at 1).\<close>

occam2\<open>
INT x:
SEQ
  --@ probe_ast[uu]
  x := 1
  x := 2
\<close>

ML\<open>
val _ = check "[uu] reaches the enclosing SEQ"
  (Occam2_Ast.pp_root (!OCCAM_AST) = "SEQ\n  x := 1\n  x := 2")
\<close>

occam2\<open>
INT x:
SEQ
  --@ probe_ast[d]
  x := 1
\<close>

ML\<open>
val _ = check "[d] reaches the first child" (Occam2_Ast.pp_root (!OCCAM_AST) = "x")
\<close>

occam2\<open>
INT x:
SEQ
  --@ probe_ast[rrd]
  x := 1
\<close>

ML\<open>
val _ = check "[rrd] reaches the second child" (Occam2_Ast.pp_root (!OCCAM_AST) = "1")
\<close>

text\<open>Evaluation order is by \<open>level\<close>, not by position: the \<open>(1)\<close> annotation runs after
  the \<open>(0)\<close> one although it comes first.\<close>

ML\<open>
val ORDER = Unsynchronized.ref ([] : int list)
val record = let fun probe (_, _, l) (_ : string * Position.T) thy = (ORDER := l :: !ORDER; thy)
             in OEnv.store_antiq ("record", OEnv.lift_theory_antiq probe) end
\<close>
setup\<open>record\<close>

occam2\<open>
SEQ
  --@ record(1)
  SKIP
  --@ record
  SKIP
\<close>

ML\<open>
val _ = check "levels order the evaluation" (rev (!ORDER) = [0, 1])
\<close>

text\<open>The real Isabelle machinery: a \<open>definition\<close> in a comment, then a \<open>lemma\<close> proved
  about it, then a \<open>term\<close> mentioning it.\<close>

occam2\<open>
-- A constant of the occam program, mirrored in HOL:
--@ definition \<open>occ_limit :: nat where "occ_limit = 100"\<close>
--@ lemma(1) \<open>occ_fact: "occ_limit * 2 = 200" by (simp add: occ_limit_def)\<close>
--@ term(2) \<open>occ_limit + 1\<close>
VAL INT limit IS 100:
SKIP
\<close>

thm occ_limit_def occ_fact

subsection\<open>Hyperlink markup\<close>

text\<open>The binding pass reports through \<^ML>\<open>Position.report\<close>; a position without a document
  id is never reported, so the test parses a source carrying a dummy id and captures the
  protocol messages. A declared use must produce an entity reference, an undeclared one
  \<^ML>\<open>Markup.bad\<close>; and, occam forbidding recursion, a procedure calling itself is undeclared
  in its own body.\<close>

ML\<open>
fun reports_of text =
  let
    val pos = Position.id "4711"
    val source = Input.source false text (pos, pos)
    val thy = @{theory}
    val collected = Unsynchronized.ref ([] : string list)
    val root = the (Occam2_Parse.parse_quiet Occam2_Parse.Entry_Unit (Proof_Context.init_global thy) source)
    val _ = Unsynchronized.setmp Private_Output.report_fn
              (fn outs => collected := map (String.concat o map (fn s => s)) [outs] @ !collected)
              (fn () => AnaEval.analyse_and_eval root thy) ()
  in String.concat (!collected) end

fun count sub s = length (String.fields (fn _ => false) s) * 0 +
  let fun go i n = case Substring.position sub (Substring.extract (s, i, NONE)) of
                        (_, rest) => if Substring.isEmpty rest then n else go (size s - Substring.size rest + size sub) (n + 1)
  in go 0 0 end

val r1 = reports_of "INT x:\nx := x + y"
val _ = check "a declared use is hyperlinked" (count "entity" r1 >= 2)
val _ = check "an undeclared use is marked bad" (count "bad" r1 >= 1)
val r2 = reports_of "PROC p ()\n  p ()\n:\nSKIP"
val _ = check "occam forbids recursion: the self-call is undeclared" (count "bad" r2 >= 1)
\<close>

subsection\<open>Export\<close>

occam2\<open>
INT x:
x := 1
\<close>

occam2_export "Occam2_Cmd_Tests" exports "Occam2_Cmd_Tests#13"

ML\<open>
val exported = File.read (Path.append (Resources.master_directory @{theory}) (Path.explode "Occam2_Cmd_Tests.occ"))
val _ = check "exported text is the pretty-printed unit" (exported = "INT x:\nx := 1\n")
\<close>

subsection\<open>\<open>occam2_file\<close> on external sources\<close>

text\<open>Two real files, read relative to this theory's master directory. The first
  (\<^verbatim>\<open>examples/mathlib.occ\<close>) is a library unit of specifications only, so its names stay in
  the environment; the second (\<^verbatim>\<open>examples/pipeline.occ\<close>) is a program that uses them, and
  carries two antiquotation comments of its own.\<close>

occam2_file \<open>examples/mathlib.occ\<close>

ML\<open>
val thy_lib = @{theory}
val key_lib = (case OEnv.get (Context.Theory thy_lib) of
                 OEnv.mk {units, ...} => OEnv.ast_store_key thy_lib (units - 1))
val path_lib = Path.append (Resources.master_directory thy_lib) (Path.explode "examples/mathlib.occ")
val idents_lib = (case OEnv.get (Context.Theory thy_lib) of OEnv.mk {idents, ...} => idents)
val _ = check "mathlib: the file's specifications are stored as a Specs unit"
  (case OEnv.get_ast key_lib thy_lib of SOME (Occam2_Ast.Specs ss) => length ss = 3 | _ => false)
val _ = check "mathlib: the source text stored is the file's own"
  (OEnv.get_source key_lib thy_lib = SOME (File.read path_lib))
val _ = check "mathlib: its names stay in the environment"
  (forall (Symtab.defined idents_lib) ["max.items", "square", "swap"])
\<close>

occam2_file \<open>examples/pipeline.occ\<close>

ML\<open>
val thy_pipe = @{theory}
val key_pipe = (case OEnv.get (Context.Theory thy_pipe) of
                  OEnv.mk {units, ...} => OEnv.ast_store_key thy_pipe (units - 1))
val idents_pipe = (case OEnv.get (Context.Theory thy_pipe) of OEnv.mk {idents, ...} => idents)
val _ = check "pipeline: stored as a process"
  (case OEnv.get_ast key_pipe thy_pipe of SOME (Occam2_Ast.Proc _) => true | _ => false)
val _ = check "pipeline: its own specifications are scoped to the program"
  (not (Symtab.defined idents_pipe "generate") andalso not (Symtab.defined idents_pipe "answer"))
val _ = check "pipeline: the probe_ast comment was dispatched on the first specification"
  (String.isPrefix "PROTOCOL num" (Occam2_Ast.pp_root (!OCCAM_AST)))
val _ = check "pipeline: the stored AST pretty-prints to a parsable program (idempotent)"
  (case OEnv.get_ast key_pipe thy_pipe of
     SOME root =>
       let val text = Occam2_Ast.pp_root root
           val again = Occam2_Parse.parse_quiet Occam2_Parse.Entry_Unit @{context} (Input.string text)
       in (case again of SOME r => Occam2_Ast.pp_root r = text | NONE => false) end
   | NONE => false)

fun reports_in thy text =
  let
    val pos = Position.id "4712"
    val source = Input.source false text (pos, pos)
    val collected = Unsynchronized.ref ([] : string list)
    val root = the (Occam2_Parse.parse_quiet Occam2_Parse.Entry_Unit (Proof_Context.init_global thy) source)
    val _ = Unsynchronized.setmp Private_Output.report_fn
              (fn outs => collected := String.concat outs :: !collected)
              (fn () => AnaEval.analyse_and_eval root thy) ()
  in String.concat (!collected) end

val pipeline_text = File.read (Path.append (Resources.master_directory thy_pipe) (Path.explode "examples/pipeline.occ"))
val _ = check "pipeline: with the library loaded, no name is reported as undeclared"
  (count "bad" (reports_in thy_pipe pipeline_text) = 0)
val _ = check "pipeline: without the library, square and max.items are reported as undeclared"
  (count "bad" (reports_in (OEnv.reset_oenv @{theory Occam2}) pipeline_text) >= 2)
\<close>

end
