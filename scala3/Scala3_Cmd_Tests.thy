theory Scala3_Cmd_Tests
  imports Scala3 Scala3_Tests
begin

section\<open>Command-level Tests\<close>

ML\<open>
fun check name b = if b then writeln ("OK: " ^ name) else error ("FAILED: " ^ name)
\<close>

subsection\<open>Accepting commands\<close>

scala3_ident\<open>foo_bar\<close>

scala3_expr\<open>(a + b) * c\<close>

scala3_type\<open>Map[String, List[Int]]\<close>

scala3\<open>
val x = 1
def inc(n: Int): Int = n + 1
\<close>

scala3_reject\<open>
val = 1
\<close>

scala3_expr_reject\<open>a +\<close>

scala3_type_reject\<open>List[\<close>

scala3_ident_reject\<open>a b\<close>

subsection\<open>Binding\<close>

text\<open>
  The binding pass reports through \<^ML>\<open>Position.report\<close>; a position without a document id is never
  reported, so the tests parse a source carrying a dummy id and capture the protocol messages.
  Every declaration and every resolved use is one entity markup; a name that resolves nowhere
  produces nothing (and, unlike C11 and occam 2, no error markup either).
\<close>

ML\<open>
fun reports_in thy text =
  let
    val pos = Position.id "4711"
    val source = Input.source false text (pos, pos)
    val collected = Unsynchronized.ref ([] : string list)
    val root = the (Scala3_Parse.parse_quiet Scala3_Parse.Entry_Unit 
                                             (Proof_Context.init_global thy) source)
    val _ = Unsynchronized.setmp Private_Output.report_fn
              (fn outs => collected := String.concat outs :: !collected)
              (fn () => AnaEval.analyse_and_eval root thy) ()
  in String.concat (!collected) end

fun count sub s =
  let fun go i n = case Substring.position sub (Substring.extract (s, i, NONE)) of
                        (_, rest) => if Substring.isEmpty rest then n
                                     else go (size s - Substring.size rest + size sub) (n + 1)
  in go 0 0 end

(* the number of entity markups: declarations plus resolved uses *)
fun entities text = count "entity" (reports_in (SEnv.reset_senv @{theory}) text)
fun ent name text n =
  let val got = entities text
  in if got = n then writeln ("OK: " ^ name) 
     else writeln ("FAILED: " ^ name ^ ": expected " 
                   ^ Int.toString n ^ ", got " ^ Int.toString got) 
  end

val _ = ent "a declaration and a use" "val x = 1\nval y = x" 3
val _ = check "an undeclared name is not marked" 
              (entities "val y = x" = 1 
               andalso count "bad" (reports_in (SEnv.reset_senv @{theory}) "val y = x") = 0)
(* a template's members are visible throughout it, a block's vals only after their definition *)
val _ = ent "forward reference in a template" "class C {\n  val a = b\n  val b = 1\n}" 4
val _ = ent "no forward reference to a local val" "def f = {\n  val a = b\n  val b = 1\n  a\n}" 4
val _ = ent "local defs are mutually visible" "def f = {\n  def g = h\n  def h = 1\n  g\n}" 5
(* scopes are closed again *)
val _ = ent "a parameter is not visible outside" "def f(x: Int) = x\nval y = x" 4
(* the two name spaces *)
val _ = ent "a class and a val of the same name" "class A\nval A = 1\nval y: A = A" 5
(* imports *)
val _ = ent "an import selector is a declaration" "import a.b.{c, d => e}\nval x = e" 4
(* patterns, lambdas, comprehensions *)
val _ = ent "pattern variables scope over a case clause" "def f(o: Int) = o match {\n  case Some(v) => v\n  case _ => 0\n}" 5
val _ = ent "a lambda parameter" "val g = (a: Int) => a + 1" 3
val _ = ent "a generator's variable scopes over the body" "val r = for { i <- xs; j = i } yield j" 5
(* type parameters and parameter clauses *)
val _ = ent "type parameters and bounds" "def f[A <: B](x: A): A = x" 6
(* the names of a unit stay for the following unit *)
\<close>

scala3\<open>
object Lib { def twice(n: Int): Int = n * 2 }
val LIMIT = 100
\<close>

scala3\<open>
val y = Lib.twice(LIMIT)
\<close>

ML\<open>
val thy_lib = @{theory}
val (terms_lib, types_lib) = (case SEnv.get (Context.Theory thy_lib) of 
                                     SEnv.mk {terms, types, ...} => (terms, types))
val _ = check "the top-level names of a unit stay in the environment"
              (Symtab.defined terms_lib "Lib" 
               andalso Symtab.defined terms_lib "LIMIT" 
               andalso Symtab.defined types_lib "Lib")
val _ = check "local names do not leak" (not (Symtab.defined terms_lib "n"))
val _ = ent "a later unit sees them" "val z = LIMIT" 1
val _ = check "... (in the theory after the declaring unit)" 
              (count "entity" (reports_in thy_lib "val z = LIMIT") = 2)
\<close>

subsection\<open>Antiquotations and navigation\<close>

text\<open>A comment attaches to the node starting at the next token; with no navigation string the
  handler sees that node (here the whole definition).\<close>

scala3\<open>
object A {
  //@ probe_ast
  //@ highlight
  def f(x: Int) = x + 1
}
\<close>

ML\<open>
val _ = check "probe_ast sees the commented definition"
  (String.isPrefix "def f(x: Int) = x + 1" (Scala3_Pp.pp_root (!SCALA_AST)))
\<close>

text\<open>Navigation: \<open>[u]\<close> and \<open>[uu]\<close> re-target to enclosing nodes, \<open>[d]\<close>/\<open>[rd]\<close> to the first child,
  \<open>[rrd]\<close> to the second (as in C11, the first \<open>r\<close> only starts the cursor at 1).\<close>

scala3\<open>
object B {
  //@ probe_ast[uu]
  //@ highlight[u]
  val a = 1 + 2
  val b = 3
}
\<close>

ML\<open>
val _ = check "[uu] reaches the enclosing object"
  (String.isPrefix "object B {" (Scala3_Pp.pp_root (!SCALA_AST)))
\<close>

scala3\<open>
val v = {
  //@ probe_ast[d]
  //@ highlight[d]
  x + y
}
\<close>

ML\<open>
val _ = check "[d] reaches the first child" (Scala3_Pp.pp_root (!SCALA_AST) = "x")
\<close>

scala3\<open>
val v = {
  //@ probe_ast[rrd]
  //@ highlight[rrd]
  x + y
}
\<close>

ML\<open>
val _ = check "[rrd] reaches the second child" (Scala3_Pp.pp_root (!SCALA_AST) = "y")
\<close>

text\<open>A Scaladoc tag in a comment is not an antiquotation (it would fail with an unregistered
  tag), whereas a tag with a cartouche body is one anywhere in a comment:\<close>

scala3\<open>
/** Docs.
 *  @param x the argument
 *  @return the result
 */
def f(x: Int): Int = x
\<close>

ML\<open>
val ORDER = Unsynchronized.ref ([] : int list)
val record = let fun probe (_, _, l) (_ : string * Position.T) thy = (ORDER := l :: !ORDER; thy)
             in SEnv.store_antiq ("record", SEnv.lift_theory_antiq probe) end
\<close>
setup\<open>record\<close>

text\<open>Evaluation order is by \<open>level\<close>, not by position:\<close>

scala3\<open>
object C {
  //@ record(1)
  val a = 1
  /* an ordinary comment @record(1) \<open>\<close> */
  //@ record
  val b = 2
}
\<close>

ML\<open>
val _ = check "levels order the evaluation" (rev (!ORDER) = [0, 1, 1] orelse rev (!ORDER) = [0, 1])
\<close>

text\<open>The real Isabelle machinery: a \<open>definition\<close> in a comment, then a \<open>lemma\<close> proved about it,
  then a \<open>term\<close> mentioning it.\<close>

scala3\<open>
// A constant of the Scala program, mirrored in HOL:
//@ definition \<open>scala_limit :: nat where "scala_limit = 100"\<close>
//@ lemma(1)   \<open>scala_fact: "scala_limit * 2 = 200" by (simp add: scala_limit_def)\<close>
//@ term(2)    \<open>scala_limit + 1\<close>
val limit = 100
\<close>

thm scala_limit_def scala_fact

subsection\<open>\<open>scala3_file\<close> on external sources\<close>

scala3_file \<open>examples/Lists.scala\<close>

ML\<open>
val thy_l = @{theory}
val key_l = (case SEnv.get (Context.Theory thy_l) of SEnv.mk {units, ...} => SEnv.ast_store_key thy_l (units - 1))
val path_l = Path.append (Resources.master_directory thy_l) (Path.explode "examples/Lists.scala")
val _ = check "Lists: stored as a compilation unit"
  (case SEnv.get_ast key_l thy_l of SOME (Scala3_Ast.Unit ss) => length ss = 4 | _ => false)
val _ = check "Lists: the source text stored is the file's own" (SEnv.get_source key_l thy_l = SOME (File.read path_l))
\<close>

scala3_file \<open>examples/Pipeline.scala\<close>

ML\<open>
val thy_p = @{theory}
val (terms_p, types_p) = (case SEnv.get (Context.Theory thy_p) of 
                                       SEnv.mk {terms, types, ...} => (terms, types))
val _ = check "Lists: its names are visible afterwards"
  (Symtab.defined terms_p "Shapes" andalso Symtab.defined types_p "Shape" 
                                   andalso Symtab.defined terms_p "Item")
val pipeline_text = File.read (Path.append (Resources.master_directory thy_p) 
                              (Path.explode "examples/Pipeline.scala"))
val _ = check "Pipeline: the stored AST pretty-prints to a parsable program (idempotent)"
  (let val key = SEnv.ast_store_key thy_p ((case SEnv.get (Context.Theory thy_p) of 
                                       SEnv.mk {units, ...} => units) - 1)
   in (case SEnv.get_ast key thy_p of
         SOME root =>
           let val text = Scala3_Pp.pp_root root
               val again = Scala3_Parse.parse_quiet Scala3_Parse.Entry_Unit @{context} 
                                                                            (Input.string text)
           in (case again of SOME r => Scala3_Pp.pp_root r = text | NONE => false) end
       | NONE => false) end)
(* the interpolated string's expression is skipped, not parsed; the class and its companion 
   are two names *)
val _ = check "Pipeline: class Item and object Item" (Symtab.defined types_p "Item")
\<close>

subsection\<open>Export\<close>

scala3\<open>
val x = 1
\<close>

scala3_export "Scala3_Cmd_Tests_x" exports "Scala3_Cmd_Tests#15"

ML\<open>
val exported = File.read (Path.append (Resources.master_directory @{theory}) 
                                      (Path.explode "Scala3_Cmd_Tests_x.scala"))
val _ = check "exported text is the pretty-printed unit" (exported = "val x = 1\n")
\<close>

subsection\<open>The semantic-backend hook\<close>

text\<open>\<open>setup_backend\<close> installs the function run on the parsed root and the freshly stored theory at 
  the end of every \<open>scala3\<close>/\<open>scala3_file\<close>; by default it is \<open>K I\<close>. A backend recording the kind of 
  root it receives is installed, exercised and removed again. The fragment commands must not 
  trigger it.\<close>

ML\<open>
val BACKEND_LOG = Unsynchronized.ref ([] : string list)
\<close>

setup_backend\<open>fn root => fn thy =>
  (BACKEND_LOG := (case root of
                     Scala3_Ast.Unit ss => "Unit " ^ Int.toString (length ss)
                   | Scala3_Ast.Expr _ => "Expr" | Scala3_Ast.Type _ => "Type" 
                   | Scala3_Ast.Id _ => "Id"     | Scala3_Ast.Stat _ => "Stat" 
                   | Scala3_Ast.Pat _ => "Pat")
                  :: !BACKEND_LOG;
   thy)\<close>

scala3_expr\<open>1 + 2\<close>

ML\<open>val _ = check "the backend does not run for a fragment" (null (!BACKEND_LOG))\<close>

scala3\<open>
val a = 1
val b = 2
\<close>

ML\<open>val _ = check "the backend ran once, with the unit" (!BACKEND_LOG = ["Unit 2"])\<close>

setup_backend\<open>K I\<close>

scala3\<open>val c = 3\<close>

ML\<open>val _ = check "the default backend does nothing" (length (!BACKEND_LOG) = 1)\<close>

end
