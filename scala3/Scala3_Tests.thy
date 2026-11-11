theory Scala3_Tests
  imports Scala3_Parser
begin

section\<open>Parser-level Tests\<close>

text\<open>
  Exercised directly through
  \<^ML>\<open>Scala3_Parse.parse_loud\<close>/\<^ML>\<open>Scala3_Parse.parse_quiet\<close> and the pretty-printer
  \<^ML>\<open>Scala3_Pp.pp_root\<close>, before any Isar command exists. A program already in the
  pretty-printer's canonical layout must come back unchanged (\<^emph>\<open>round trip\<close>), and
  every accepted program must be a fixed point of parse-then-print
  (\<^emph>\<open>idempotence\<close>).
\<close>

ML\<open>
fun prog lines = String.concatWith "\n" lines

fun parse_entry entry s =
  Scala3_Parse.parse_loud entry @{context} (Input.string s)

fun show_entry entry s =
  (case parse_entry entry s of
     SOME r => Scala3_Pp.pp_root r
   | NONE => error "parser returned NONE")

val show = show_entry Scala3_Parse.Entry_Unit

(* the pretty-printed result must itself be accepted and print identically *)
fun idempotent lines =
  let
    val s = prog lines
    val out = show s
    val out2 = show out
  in if out = out2 then out
    else error ("not idempotent:\n" ^ out ^ "\n--- vs ---\n" ^ out2) end

fun roundtrip lines =
  let
    val s = prog lines
    val out = idempotent lines
  in if out = s then ()
    else error ("round trip mismatch for:\n" ^ s ^ "\n--- got ---\n" ^ out) end

fun rejects_entry entry lines =
  (case Exn.capture
   (fn () =>
    Scala3_Parse.parse_quiet entry @{context} (Input.string (prog lines))) () of
     Exn.Exn (Scala3_Parse.Rejected _) => ()
   | Exn.Exn e => error ("unexpected exception: " ^ Runtime.exn_message e)
   | Exn.Res _ => error ("should have been rejected: " ^ prog lines))

val rejects = rejects_entry Scala3_Parse.Entry_Unit
\<close>

subsection\<open>Round trips: canonical layout comes back unchanged\<close>

ML\<open>
val _ = roundtrip ["val x = 1"]
val _ = roundtrip ["val x: Int = 1", "val y = x + 1"]
val _ = roundtrip ["def f(x: Int, y: String): Int = x + y.length"]
val _ = roundtrip ["def f[A <: B, +C](x: A)(implicit y: C): List[A] = Nil"]
val _ = roundtrip
  ["class C(val x: Int, y: String) extends B(x) with D {",
   "  override def toString = \"C\" + x", "}"]
val _ = roundtrip ["case class P(x: Int, y: Int)", "case object O"]
val _ = roundtrip ["trait T {", "  def f: Int", "  type U <: AnyRef", "}"]
val _ = roundtrip ["object A {", "  def f = 1", "  val g = f + 2", "}"]
val _ = roundtrip
  ["import scala.collection.mutable.{Map => MMap, Set}", "import a.b._"]
val _ = roundtrip ["package a.b", "import c.d", "object X {", "}"]
val _ = roundtrip ["val l = xs.map((x) => x + 1).filter(_ > 2)"]
val _ = roundtrip ["val g = (x: Int) => x + 1"]
val _ = roundtrip ["xs ::: ys :+ z"]
val _ = roundtrip ["val a = b.c.d(e)"]
val _ = roundtrip ["if (a) b else c"]
val _ = roundtrip ["while (x < 10) x += 1"]
val _ = roundtrip
  ["val s = s\"hello ${name} and $x\"", "val t = \"\"\"multi", "line\"\"\""]
val _ = roundtrip ["enum Color {", "  case Red, Green", "  case Blue", "}"]
val _ = roundtrip ["enum E {", "  case A(x: Int) extends E", "  case B", "}"]
val _ = roundtrip ["extension (s: String) {", "  def twice = s + s", "}"]
val _ = roundtrip
  ["given Ordering[Int] = Ordering.Int", "def f(using c: Ctx): Int = 1"]
val _ = roundtrip
  ["x match {", "  case 1 =>", "    \"a\"", "  case Some(y) if y > 2 =>",
   "    y.toString", "  case _ =>", "    \"b\"", "}"]
val _ = roundtrip
  ["try {", "  f()", "} catch {", "  case e: Exception =>", "    g(e)",
   "} finally {", "  h()", "}"]
val _ = roundtrip ["for {", "  i <- 1 to 10", "  if i > 2", "} yield i * 2"]
\<close>

subsection\<open>Layout: where a newline is a statement separator\<close>

text\<open>
  The same program written four ways must give one tree: newlines, semicolons,
  continuation lines after an operator, a leading infix operator, a method chain
  with leading dots, and newlines inside parentheses (which are not
  separators).\<close>

ML\<open>
fun same lines1 lines2 = if show (prog lines1) = show (prog lines2) then ()
                         else error
                           ("different trees for:\n" ^ prog lines1
                            ^ "\n--- and ---\n" ^ prog lines2)

val _ = same ["val a = 1", "val b = 2"] ["val a = 1; val b = 2"]
val _ = same ["val a = 1 +", "  2"] ["val a = 1 + 2"]
val _ = same ["val a = 1", "  + 2"] ["val a = 1 + 2"]
val _ = same ["val a = f", "  .g", "  .h(1)"] ["val a = f.g.h(1)"]
val _ = same ["val a = f(1,", "  2)"] ["val a = f(1, 2)"]
val _ = same ["val a = xs map", "  f"] ["val a = xs map f"]
val _ = same ["def f(", "  a: Int,", "  b: Int,", "): Int = a"]
  ["def f(a: Int, b: Int): Int = a"]
val _ = same ["import a.b.*", "val x = 1"] ["import a.b._; val x = 1"]
(* a negative number at the start of a line is a new statement, an infix minus
   is not *)
val _ = same ["val a = 1", "-x"] ["val a = 1; -x"]
val _ = same ["val a = 1", "- x"] ["val a = 1 - x"]
(* a single newline before a brace is ignored, a blank line is not *)
val _ = same ["foo", "{ 1 }"] ["foo { 1 }"]
\<close>

subsection\<open>Operators: precedence by first character, associativity by last\<close>

ML\<open>
fun tree s = show_entry Scala3_Parse.Entry_Expr s
val _ = if tree "a + b * c" = "a + b * c" then () else error "flat print"
(* the structure is checked by the AST itself *)
fun is_infix_with op_ (Scala3_Ast.EInfix (_, id, _, _)) =
  Scala3_Ast.ident_name id = op_
  | is_infix_with _ _ = false
fun expr_of s =
  (case parse_entry Scala3_Parse.Entry_Expr s of SOME (Scala3_Ast.Expr e) =>
   e | _ => error "expr")
val _ = if is_infix_with "+" (expr_of "a + b * c") then ()
  else error "* binds tighter than +"
val _ = if is_infix_with "*" (expr_of "a * b + c") then error "wrong" else ()
val _ = if is_infix_with "+" (expr_of "a * b + c") then ()
  else error "+ at the root"
(* left associative *)
val _ = (case expr_of "a - b - c" of
           Scala3_Ast.EInfix (Scala3_Ast.EInfix _, _, _, _) => () | _ =>
             error "- is left associative")
(* right associative: an operator ending in a colon *)
val _ = (case expr_of "a :: b :: c" of
           Scala3_Ast.EInfix (_, _, Scala3_Ast.EInfix _, _) => () | _ =>
             error ":: is right associative")
(* alphanumeric operators bind weakest *)
val _ = if is_infix_with "max" (expr_of "a + b max c * d") then ()
  else error "max binds weakest"
(* && binds tighter than || *)
val _ = if is_infix_with "||" (expr_of "a || b && c") then ()
  else error "|| binds weaker than &&"
(* comparison binds tighter than && *)
val _ = if is_infix_with "&&" (expr_of "a < b && c > d") then ()
  else error "&& binds weaker than <"
\<close>

subsection\<open>Rejected programs\<close>

ML\<open>
val _ = rejects ["val = 1"]
val _ = rejects ["def f(x: Int = 1"]
val _ = rejects ["class { }"]
val _ = rejects ["val x = (1, 2"]
val _ = rejects ["for (x <- xs"]
val _ = rejects ["val x = 'ab'"]
val _ = rejects ["val s = \"unterminated"]
val _ = rejects ["/* unterminated comment"]
val _ = rejects_entry Scala3_Parse.Entry_Expr ["a +"]
val _ = rejects_entry Scala3_Parse.Entry_Type ["List["]
val _ = rejects_entry Scala3_Parse.Entry_Id ["a b"]
\<close>

subsection\<open>Comments and strings\<close>

ML\<open>
val _ = same
  ["/* c /* nested */ still a comment */ val x = 1 // c2", "val y = 2"]
    ["val x = 1; val y = 2"]
(* a Scaladoc tag is no antiquotation: it would be an unregistered one *)
val _ = same
  ["/** Docs.", " *  @param x the x", " *  @return nothing", " */",
   "def f(x: Int) = x"] ["def f(x: Int) = x"]
(* an interpolated string with a nested string and braces in its expression *)
val _ = roundtrip ["val s = s\"a ${f(\"b\", { 1 })} c\""]
val _ = roundtrip ["val s = f\"$x%5.2f\""]
(* escapes stay as written *)
val _ = roundtrip
  ["val s = \"a\\n\\\"b\\\"\"", "val c = '\\n'", "val u = '\\u0041'"]
(* numbers *)
val _ = roundtrip ["val n = 0x1F + 0b101 + 1_000L + 1.5e3 + 2f"]
\<close>

subsection\<open>Parallel parses\<close>

text\<open>
  Every parse has its own state object (\<^ML_structure>\<open>Scala3_State\<close>), so any number of parses
  may run at once. Twelve different programs, with comments, nested blocks and
  an interpolated string, are parsed by \<^ML>\<open>Par_List.map\<close>, ten rounds in a row;
  each result must equal the sequential one.
\<close>

ML\<open>
local
  fun prog_k k =
    let val v = "v" ^ Int.toString k
    in String.concatWith "\n"
         ([ "// program " ^ Int.toString k, "object O" ^ Int.toString k 
                          ^ " {", "  def f(x: Int): Int = {" ] @
          List.concat (List.tabulate (30, fn i =>
            [ "    /* a /* nested */ comment */",
              "    val " ^ v ^ Int.toString i ^ " = x + "
                ^ Int.toString (k * 100 + i),
              "    if (" ^ v ^ Int.toString i ^ " > " ^ Int.toString i
                ^ ") println(s\"v ${x}\")" ])) 
            @
            [ "    x", "  }", "}" ]) ^ "\n"
    end
  val progs = List.tabulate (12, prog_k)
  val reference = map show progs
in
  val _ =
    List.app (fn _ =>
      List.app (fn (ref_text, result) =>
          (case result of
             Exn.Res text =>
               if text = ref_text then ()
                 else error "parallel parse: wrong result"
           | Exn.Exn e =>
             error ("parallel parse failed: " ^ Runtime.exn_message e)))
        (ListPair.zip
         (reference, Par_List.map (fn t => Exn.capture show t) progs)))
      (List.tabulate (10, I))
end
\<close>

section\<open>The Scala Sources of Isabelle\<close>

text\<open>
  The real test: every \<^verbatim>\<open>.scala\<close> file below \<^verbatim>\<open>~~/src\<close> of the Isabelle installation
  this theory is built with (380 files, 93\,000 lines, in Isabelle2026) must
  parse, and print back to text that parses again to the same tree (the parallel
  run is part of the test). If the directory is absent the test does nothing.
\<close>

ML\<open>
local
  fun scala_files dir =
    let
      fun walk p =
        if File.is_dir p
        then maps (fn n => walk (Path.append p (Path.basic n)))
          (sort_strings (File.read_dir p))
        else if String.isSuffix ".scala" (Path.implode p) then [p] else []
    in walk dir end

  val src = Path.explode "~~/src"
  val files = if File.is_dir src then scala_files src else []

  fun check_file file =
    let
      val text = File.read file
      fun parse t =
        Scala3_Parse.parse_quiet
          Scala3_Parse.Entry_Unit @{context} (Input.string t)
      fun fail msg = error (Path.implode file ^ ": " ^ msg)
    in
      (case Exn.capture parse text of
         Exn.Exn (Scala3_Parse.Rejected msg) => fail ("rejected: " ^ msg)
       | Exn.Exn e => fail (Runtime.exn_message e)
       | Exn.Res NONE => fail "no result"
       | Exn.Res (SOME r) =>
           let
             val p1 = Scala3_Pp.pp_root r
           in
             (case Exn.capture parse p1 of
                Exn.Res (SOME r2) => if Scala3_Pp.pp_root r2 = p1 then () 
                                     else fail "not idempotent"
              | _ => fail "the printed text does not parse")
           end)
    end
in
  val corpus_size = length files
  val _ = Par_List.map check_file files
  val _ = writeln ("Scala3_Tests: " ^ Int.toString corpus_size 
                                    ^ (" Isabelle Scala source file(s) " ^
                                       "parsed and printed back"))
end
\<close>

end
