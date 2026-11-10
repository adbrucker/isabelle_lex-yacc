theory Occam2_Tests
  imports Occam2_Parser
begin

section\<open>Parser-level Tests\<close>

text\<open>
  Exercised directly through \<^ML>\<open>Occam2_Parse.parse_loud\<close>/\<^ML>\<open>Occam2_Parse.parse_quiet\<close>
  and the pretty-printer \<^ML>\<open>Occam2_Ast.pp_root\<close>, before any Isar command exists. Programs
  are written as lists of lines; a program already in the pretty-printer's canonical
  layout must come back unchanged ("round trip"), and every accepted program must be a
  fixed point of parse-then-print ("idempotence").
\<close>

ML\<open>
fun prog lines = String.concatWith "\n" lines

fun parse_entry entry s = Occam2_Parse.parse_loud entry @{context} (Input.string s)

fun show_entry entry s =
  case parse_entry entry s of
    SOME r => Occam2_Ast.pp_root r
  | NONE => error "parser returned NONE"

val show = show_entry Occam2_Parse.Entry_Unit

(* the pretty-printed result must itself be accepted and print identically *)
fun idempotent lines =
  let
    val s = prog lines
    val out = show s
    val out2 = show out
  in if out = out2 then out else error ("not idempotent:\n" ^ out ^ "\n--- vs ---\n" ^ out2) end

fun roundtrip lines =
  let
    val s = prog lines
    val out = idempotent lines
  in if out = s then () else error ("round trip mismatch for:\n" ^ s ^ "\n--- got ---\n" ^ out) end

fun prints lines expected =
  let val out = idempotent lines
  in if out = prog expected then ()
     else error ("unexpected output for:\n" ^ prog lines ^ "\n--- got ---\n" ^ out) end

fun rejects_entry entry lines =
  (case SOME (Occam2_Parse.parse_quiet entry @{context} (Input.string (prog lines)))
          handle Occam2_Parse.Rejected _ => NONE of
     NONE => ()
   | SOME _ => error ("unexpectedly accepted:\n" ^ prog lines))

val rejects = rejects_entry Occam2_Parse.Entry_Unit
\<close>

subsection\<open>Primitive processes\<close>

ML\<open>
val _ = roundtrip ["SKIP"]
val _ = roundtrip ["STOP"]
val _ = roundtrip ["x := 1"]
val _ = roundtrip ["a, b := 1, 2"]
val _ = roundtrip ["a[i], b := b, a[i]"]
val _ = roundtrip ["c ? x"]
val _ = roundtrip ["c ? x; y; z"]
val _ = roundtrip ["c ? n :: buf"]
val _ = roundtrip ["c ! x + 1"]
val _ = roundtrip ["c ! a; b; 1"]
val _ = roundtrip ["c ! n :: buf"]
val _ = roundtrip ["t ? AFTER now PLUS 100"]
val _ = roundtrip ["t ? now"]
val _ = roundtrip ["port ? v"]
val _ = roundtrip ["port ! v"]
val _ = roundtrip ["p()"]
val _ = roundtrip ["p(x, y + 1, c)"]
\<close>

subsection\<open>Constructions\<close>

ML\<open>
val _ = roundtrip ["SEQ", "  x := 1", "  y := 2"]
val _ = roundtrip ["SEQ"]
val _ = roundtrip ["SEQ i = 0 FOR 10", "  a[i] := i"]
val _ = roundtrip ["IF", "  x > 0", "    SKIP", "  TRUE", "    STOP"]
val _ = roundtrip ["IF i = 0 FOR 3", "  a[i] = 0", "    SKIP"]
val _ = roundtrip ["IF", "  x > 0", "    IF", "      y > 0", "        SKIP", "      TRUE", "        STOP", "  TRUE", "    STOP"]
val _ = roundtrip ["CASE x", "  1, 2", "    SKIP", "  3", "    STOP", "  ELSE", "    SKIP"]
val _ = roundtrip ["WHILE x < 10", "  x := x + 1"]
val _ = roundtrip ["PAR", "  p()", "  q()"]
val _ = roundtrip ["PAR i = 0 FOR 4", "  worker(i)"]
val _ = roundtrip ["PRI PAR", "  hi()", "  lo()"]
val _ = roundtrip ["ALT", "  c ? x", "    SKIP", "  b & d ? y", "    STOP", "  TRUE & SKIP", "    SKIP"]
val _ = roundtrip ["PRI ALT", "  c ? x", "    SKIP"]
val _ = roundtrip ["ALT i = 0 FOR 2", "  cs[i] ? x", "    SKIP"]
val _ = roundtrip ["ALT", "  t ? AFTER deadline", "    SKIP"]
val _ = roundtrip ["c ? CASE", "  quit", "    SKIP", "  set; v", "    x := v"]
val _ = roundtrip ["ALT", "  c ? CASE", "    quit", "      SKIP", "    set; v", "      x := v"]
val _ = roundtrip ["ALT", "  go & c ? CASE", "    quit", "      SKIP"]
val _ = roundtrip ["PLACED PAR", "  PROCESSOR 1", "    p1()", "  PROCESSOR 2", "    p2()"]
val _ = roundtrip ["PLACED PAR i = 0 FOR 2", "  PROCESSOR i", "    p(i)"]
val _ = roundtrip ["PLACE c AT 4:", "SKIP"]
\<close>

subsection\<open>Specifications\<close>

ML\<open>
val _ = roundtrip ["INT x:", "SKIP"]
val _ = roundtrip ["INT x, y, z:", "SKIP"]
val _ = roundtrip ["[10]INT a:", "SKIP"]
val _ = roundtrip ["[n][m]REAL32 m2:", "SKIP"]
val _ = roundtrip ["CHAN OF INT c:", "SKIP"]
val _ = roundtrip ["[5]CHAN OF BYTE cs:", "SKIP"]
val _ = roundtrip ["TIMER t:", "SKIP"]
val _ = roundtrip ["PORT OF INT p:", "SKIP"]
val _ = roundtrip ["BOOL b:", "BYTE c:", "INT16 s:", "INT32 l:", "INT64 ll:", "REAL32 f:", "REAL64 d:", "SKIP"]
val _ = roundtrip ["VAL INT n IS 10:", "SKIP"]
val _ = roundtrip ["VAL []INT t IS [1, 2, 3]:", "SKIP"]
val _ = roundtrip ["VAL [3]BYTE s IS \"abc\":", "SKIP"]
val _ = roundtrip ["INT x IS y:", "SKIP"]
val _ = roundtrip ["x IS y[3]:", "SKIP"]
val _ = roundtrip ["VAL n IS 4:", "SKIP"]
val _ = roundtrip ["[]INT part IS [a FROM 2 FOR 4]:", "SKIP"]
val _ = roundtrip ["INT64 x RETYPES y:", "SKIP"]
val _ = roundtrip ["VAL INT64 x RETYPES y:", "SKIP"]
val _ = roundtrip ["PROTOCOL byte.stream IS BYTE:", "SKIP"]
val _ = roundtrip ["PROTOCOL complex IS REAL64; REAL64:", "SKIP"]
val _ = roundtrip ["PROTOCOL record IS INT16 :: []BYTE:", "SKIP"]
val _ = roundtrip ["PROTOCOL anything IS ANY:", "SKIP"]
val _ = roundtrip ["PROTOCOL files", "  CASE", "    request", "    filename; INT16 :: []BYTE", "    halt", ":", "SKIP"]
val _ = roundtrip ["CHAN OF files to.dfs:", "SKIP"]
val _ = roundtrip ["PROC p ()", "  SKIP", ":", "SKIP"]
val _ = roundtrip ["PROC p (VAL INT n, INT x, CHAN OF INT c)", "  SEQ", "    c ! n", "    c ? x", ":", "p(1, v, ch)"]
val _ = roundtrip ["PROC p (VAL INT a, b, CHAN OF INT c, d)", "  SKIP", ":", "SKIP"]
val _ = roundtrip ["PROC p (VAL []INT t, []BYTE buf, TIMER clock)", "  SKIP", ":", "SKIP"]
val _ = roundtrip ["INT FUNCTION f (VAL INT x)", "  VALOF", "    SKIP", "  RESULT x", ":", "y := f(1)"]
val _ = roundtrip ["INT FUNCTION sq (VAL INT x) IS x * x:", "y := sq(3)"]
val _ = roundtrip ["INT, INT FUNCTION swap (VAL INT a, b) IS b, a:", "x, y := swap(1, 2)"]
val _ = roundtrip ["INT FUNCTION g (VAL INT x)", "  INT r:", "  VALOF", "    SEQ", "      r := x", "      r := r + 1", "  RESULT r", ":", "SKIP"]
\<close>

subsection\<open>Expressions\<close>

ML\<open>
fun expr_rt s =
  let val out = show_entry Occam2_Parse.Entry_Expr s
  in if out = s then () else error ("expression round trip: " ^ s ^ " --> " ^ out) end

val _ = List.app expr_rt
  [ "x", "1", "#FF", "'a'", "'*n'", "\"hello\"", "TRUE", "FALSE", "5 (INT64)", "1.5 (REAL32)",
    "1.0E+3 (REAL64)", "'a' (INT)", "x + 1", "x - y", "x * y", "x / y", "x REM y", "x PLUS y", "x MINUS y",
    "x TIMES y", "x BITAND y", "x BITOR y", "x >< y", "x << 2", "x >> 2", "x = y", "x <> y", "x < y",
    "x > y", "x <= y", "x >= y", "t1 AFTER t2", "NOT b", "BITNOT x", "SIZE a", "-x", "MINUS x",
    "(x + 1)", "(x + 1) * (y - 2)", "a AND b AND c", "a OR b OR c", "(a AND b) OR c",
    "INT x", "REAL32 ROUND x", "INT TRUNC y", "MOSTPOS INT", "MOSTNEG INT16", "MOSTPOS [4]BYTE",
    "a[i]", "a[i][j]", "[a FROM 1 FOR 2]", "[1, 2, 3]", "[1, 2, 3][i]", "\"abc\"[1]",
    "[[1, 2] FROM 0 FOR 1]", "[\"abc\" FROM 1 FOR 2]", "f()", "f(x)", "f(x, g(y), 1)", "x + f(y)" ]
\<close>

subsection\<open>Layout: blank lines, comments, continuation lines, nesting\<close>

ML\<open>
val _ = prints ["-- a leading comment", "SEQ", "", "  -- an inner comment", "  x := 1   -- trailing", "  y := 2"]
                ["SEQ", "  x := 1", "  y := 2"]
val _ = prints ["SEQ", "  x := a +", "        b", "  y := 2"] ["SEQ", "  x := a + b", "  y := 2"]
val _ = prints ["SEQ", "  c ! a;", "    b;", "    c", "  SKIP"] ["SEQ", "  c ! a; b; c", "  SKIP"]
val _ = prints ["SEQ", "  x :=", "    1"] ["SEQ", "  x := 1"]
val _ = prints ["PROC p (VAL INT a,", "        INT b)", "  SKIP", ":", "SKIP"]
                ["PROC p (VAL INT a, INT b)", "  SKIP", ":", "SKIP"]
val _ = roundtrip ["SEQ", "  IF", "    TRUE", "      SEQ", "        x := 1", "  y := 2"]
val _ = roundtrip ["SEQ", "  SEQ", "    SEQ", "      x := 1", "  y := 2"]
val _ = prints ["SEQ", "  x := 1", "", "", "  y := 2", ""] ["SEQ", "  x := 1", "  y := 2"]
val _ = prints ["    SEQ", "      x := 1"] ["SEQ", "  x := 1"]
\<close>

subsection\<open>Entry points\<close>

ML\<open>
val _ =
  (case parse_entry Occam2_Parse.Entry_Id "foo.bar" of
     SOME (Occam2_Ast.Id (Occam2_Ast.Ident ("foo.bar", _, _))) => ()
   | _ => error "Entry_Id: expected Id foo.bar")
val _ =
  (case parse_entry Occam2_Parse.Entry_Expr "f(x)" of
     SOME (Occam2_Ast.Expr (Occam2_Ast.ECall _)) => ()
   | _ => error "Entry_Expr: f(x) must be a function call")
val _ =
  (case parse_entry Occam2_Parse.Entry_Unit "f(x)" of
     SOME (Occam2_Ast.Proc (Occam2_Ast.PInstance _)) => ()
   | _ => error "Entry_Unit: f(x) must be a procedure instance")
val _ =
  (case parse_entry Occam2_Parse.Entry_Unit "PROC p ()\n  SKIP\n:\nINT FUNCTION f ()\n  VALOF\n    SKIP\n  RESULT 1\n:\n" of
     SOME (Occam2_Ast.Specs [_, _]) => ()
   | _ => error "Entry_Unit: two definitions and no process must be Specs [_, _]")
\<close>

subsection\<open>Rejected programs\<close>

ML\<open>
(* dedent to a column that is not any enclosing block's *)
val _ = rejects ["SEQ", "    x := 1", "  y := 2"]
(* indent without a block header *)
val _ = rejects ["SEQ", "  x := 1", "    y := 2"]
(* keywords are upper case only *)
val _ = rejects ["seq", "  SKIP"]
val _ = rejects ["x :="]
val _ = rejects ["x := 1 +"]
val _ = rejects ["IF", "  x > 0"]
val _ = rejects ["INT x"]
val _ = rejects ["x := 1", "y := 2"]
val _ = rejects ["SEQ", "  x := 1 ?"]
(* no operator precedence: mixing dyadic operators needs parentheses *)
val _ = rejects ["x := a + b + c"]
val _ = rejects ["x := a AND b OR c"]
(* a real literal must carry its type *)
val _ = rejects ["x := 1.5"]
(* an illegal character *)
val _ = rejects ["x := 1 $ 2"]
val _ = rejects_entry Occam2_Parse.Entry_Expr ["a b"]
val _ = rejects_entry Occam2_Parse.Entry_Id ["a b"]
\<close>


section\<open>Parallel Parses\<close>

text\<open>
  Every parse has its own state object (\<^ML_structure>\<open>Occam2_State\<close>), so any number of parses
  may run at once. Twelve different programs, each with annotated comments and several
  indentation levels, are parsed by \<^ML>\<open>Par_List.map\<close>, ten rounds in a row; each result must
  equal the sequential one, and the comment in front of the first statement must be attached
  to that statement (the comments of one parse must never end up in another).
  (With the process-wide state of the earlier version nearly every one of these parses failed
  with a spurious syntax error.)
\<close>

ML\<open>
local
  fun prog k =
    let val v = "v" ^ Int.toString k
    in String.concatWith "\n"
         ([ "-- program " ^ Int.toString k, "INT " ^ v ^ ":", "SEQ" ] @
          List.concat (List.tabulate (30, fn i =>
            [ "  --@ probe_ast",
              "  " ^ v ^ " := " ^ v ^ " + " ^ Int.toString (k * 100 + i),
              "  IF",
              "    " ^ v ^ " > " ^ Int.toString i,
              "      SKIP",
              "    TRUE",
              "      STOP" ]))) ^ "\n"
    end

  fun parse text =
    the (Occam2_Parse.parse_quiet Occam2_Parse.Entry_Unit @{context} (Input.string text))

  fun first_has_probe (Occam2_Ast.Proc (Occam2_Ast.PSpecP (_, Occam2_Ast.PSeq (_, p1 :: _, _), _))) =
        exists (fn Occam2_Ast.Antiquotation ({tag = (t, _)}, _, _, _) => t = "probe_ast" | _ => false)
          (Occam2_Ast.comments_of_NodeInfo (Occam2_Ast.nodeInfo_of_process p1))
    | first_has_probe _ = false

  val progs = List.tabulate (12, prog)
  val reference = map (Occam2_Ast.pp_root o parse) progs
in
  val _ =
    List.app (fn _ =>
      List.app (fn (ref_text, result) =>
          (case result of
             Exn.Res (text, probe) =>
               if text = ref_text andalso probe then ()
               else error "parallel parse: wrong result"
           | Exn.Exn e => error ("parallel parse failed: " ^ Runtime.exn_message e)))
        (ListPair.zip (reference,
           Par_List.map (fn t => Exn.capture (fn () => let val r = parse t in (Occam2_Ast.pp_root r, first_has_probe r) end) ()) progs)))
      (List.tabulate (10, I))
end
\<close>

end
