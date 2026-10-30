(* Imports "Occam2_Cmd_Tests" - not plain "Occam2" - purely to force a
   sequential build order: the lexer's comment/layout state (Occam2_Comments,
   Occam2_Layout in Occam2_Parser.thy) is process-wide, so two theories of
   one session that both run "occam2"-family commands with no import edge
   between them can be scheduled in parallel and race on it (the same reason
   SelectionSort.thy imports AntiqProbe in the C11 session). The environment
   the test theories leave behind is thrown away again right below. *)
theory Occam2_Example
  imports Occam2_Cmd_Tests
begin

(* Back to the environment that holds exactly the standard handlers, and to a
   fresh unit counter: the store keys below ("Occam2_Example#N") are then the
   ones this theory's own commands report. *)
reset_oenv

section\<open>The Problem\<close>

text\<open>
  Two small occam 2 programs, in the spirit of the worked examples of the C11 project
  (\<^verbatim>\<open>SelectionSort.thy\<close> and friends): a sequential one that exercises the
  contract-style annotations, and a concurrent one that exercises channels and \<open>PAR\<close>.
  As there, no semantic interpretation and therefore no formal verification is
  intended; the annotations are \<^emph>\<open>mockups\<close> that check their HOL content and keep it
  for a later semantic backend.

  \<^enum> \<^bold>\<open>Euclid's algorithm\<close> as an occam \<open>FUNCTION\<close>: the sequential \<open>VALOF\<close>/\<open>WHILE\<close> idiom,
    annotated with a precondition, a postcondition, a loop invariant and a termination
    measure - the four annotation kinds of the C11 examples (which took them from the WhyML
    of the why3 suite).
  \<^enum> \<^bold>\<open>A one-place buffer\<close> between a producer and a consumer: three processes in a \<open>PAR\<close>,
    connected by two synchronous channels. It shows what is characteristic of occam - an
    unbuffered channel makes sender and receiver wait for each other, so the buffer
    process is what turns "send and wait" into "send and carry on".

  The definition of the mockups follows. They read their body as a HOL term, exactly like
  the standard \<open>term\<close> antiquotation, but keep the result in a list instead of
  discarding it:
\<close>

ML\<open>
val ANNOTATION_PROBE = Unsynchronized.ref ([] : (string * term) list)
fun mockup_annotation_antiq name =
  let
    fun probe (_, ast, _) (body, body_pos) thy =
      let
        val ctxt = Proof_Context.init_global thy
        val encoded = Syntax.implode_input (body_source (body, body_pos))
        val t = Syntax.read_term ctxt encoded
          handle exn =>
            if Exn.is_interrupt exn then Exn.reraise exn
            else error (name ^ " antiquotation: " ^ Runtime.exn_message exn ^
                         Position.here (AnaEval.pos_of_root ast))
      in (ANNOTATION_PROBE := (name, t) :: !ANNOTATION_PROBE; thy) end
  in OEnv.store_antiq (name, OEnv.lift_theory_antiq probe) end
\<close>

setup\<open>mockup_annotation_antiq "requires"\<close>
setup\<open>mockup_annotation_antiq "ensures"\<close>
setup\<open>mockup_annotation_antiq "inv"\<close>
setup\<open>mockup_annotation_antiq "measure"\<close>

section\<open>Euclid's Algorithm\<close>

text\<open>
  An occam function is a value process: specifications, then a \<open>VALOF\<close> whose process
  computes the result, then \<open>RESULT\<close>. Values of type \<open>INT\<close> are the (bounded) machine
  integers; the HOL mockups below read them as \<^typ>\<open>int\<close>, a small, honest gap for a later
  semantic backend to close. \<open>REM\<close> is occam's remainder, which for non-negative operands
  is HOL's \<open>mod\<close>.

  The comment block in front of the function carries its contract; the loop's invariant and
  measure sit directly above the \<open>WHILE\<close> and are attached to it. The \<open>lemma\<close> annotation is
  not a mockup but the real, standard one: it states, and proves with one terminal
  \<open>by\<close> proof, the HOL fact that makes the loop invariant preserved - proof-carrying code
  in the sense of the manual (\<open>\<section>2.5\<close>); its \<open>(1)\<close> orders it after the mockups, which
  are of level \<open>0\<close>.
\<close>

occam2\<open>
--@ requires \<open>(0::int) \<le> a \<and> 0 \<le> b\<close>
--@ ensures \<open>(x::int) = gcd a b\<close>
--@ lemma(1) \<open>gcd_step: "(y::int) \<noteq> 0 \<Longrightarrow> gcd y (x mod y) = gcd x y"
             by (metis gcd_red_int)\<close>
INT FUNCTION gcd (VAL INT a, b)
  INT x, y:
  VALOF
    SEQ
      x := a
      y := b
      --@ inv \<open>(gcd (x::int) y) = gcd a b\<close>
      --@ measure \<open>nat (y::int)\<close>
      WHILE y <> 0
        INT t:
        SEQ
          t := x REM y
          x := y
          y := t
  RESULT x
:
\<close>

text\<open>
  The four annotations, as the mockup collected them (newest first), and the proved
  lemma:
\<close>

ML\<open>
val _ = map (fn (name, t) => writeln (name ^ ": " ^ Syntax.string_of_term @{context} t))
            (rev (!ANNOTATION_PROBE))
\<close>

thm gcd_step

text\<open>The function is a specification-only unit, so its name stays in scope for the
  programs that follow. A call - below, an \<open>EValof\<close>-free function instance - is
  hyperlinked back to the declaration, and the program is a process like any other:\<close>

occam2\<open>
INT g:
SEQ
  g := gcd (84, 36)
  SKIP
\<close>

text\<open>
  And, as always in occam, a procedure may not call itself. Writing a recursive
  variant of the algorithm is therefore not an error in the grammar but an
  \<^emph>\<open>underlined name\<close> (the recursive call, \<open>euclid.rec\<close>, is not yet declared in its own
  body) that the reader can spot in the editor:
\<close>

occam2\<open>
PROC euclid.rec (VAL INT a, b, INT r)
  IF
    b = 0
      r := a
    TRUE
      euclid.rec (b, a REM b, r)
:
SKIP
\<close>

section\<open>A One-Place Buffer\<close>

text\<open>
  The three processes, as procedures. A \<open>CHAN OF INT\<close> is a synchronous, unbuffered,
  point-to-point channel: \<open>c ! v\<close> does not complete before the partner's \<open>c ? x\<close> does.
  The producer sends the numbers \<open>1\<close> to \<open>n\<close> (a replicated \<open>SEQ\<close>); the buffer forever
  copies its input to its output; the consumer adds up \<open>n\<close> numbers and reports the
  total. The \<open>ensures\<close> on the consumer says what a semantic backend would have to
  prove: whatever the interleaving of the three processes, the consumer ends with the
  Gauss sum. (The accumulator is called \<open>acc\<close>, not \<open>total\<close>: \<open>total\<close> is a HOL constant,
  and a mockup reads an occam name as a free HOL variable - the same trap as \<open>min\<close> in
  the C11 \<^verbatim>\<open>SelectionSort.thy\<close>.)
\<close>

occam2\<open>
PROC producer (VAL INT n, CHAN OF INT out)
  SEQ i = 1 FOR n
    out ! i
:

PROC buffer (CHAN OF INT in, out)
  INT x:
  WHILE TRUE
    SEQ
      in ? x
      out ! x
:

--@ requires \<open>(0::nat) \<le> n\<close>
--@ ensures \<open>(acc::nat) = n * (n + 1) div 2\<close>
PROC consumer (VAL INT n, CHAN OF INT in, INT acc)
  INT x:
  SEQ
    acc := 0
    SEQ i = 1 FOR n
      SEQ
        in ? x
        acc := acc + x
:
\<close>

text\<open>
  The whole system. The three branches of the \<open>PAR\<close> run concurrently, connected by the
  channels \<open>a\<close> and \<open>b\<close>. The two annotations show navigation: the first, attached to
  the \<open>PAR\<close> as a whole, is made to point at its \<^emph>\<open>third\<close> branch, the consumer
  (\<open>[rrrd]\<close>: the children are the three processes, and the first \<open>r\<close> only starts the
  cursor); the second, without navigation, highlights the \<open>SKIP\<close> it is attached to.
\<close>

occam2\<open>
CHAN OF INT a, b:
INT sum:
SEQ
  --@ highlight[rrrd]
  PAR
    producer (10, a)
    buffer (a, b)
    consumer (10, b, sum)
  --@ highlight
  SKIP
\<close>

section\<open>Exporting\<close>

text\<open>
  The stored sections are rendered back to occam text with the canonical two-space layout and
  written next to this theory. The keys are this theory's own: the commands above ran in
  the order function (\<open>#0\<close>), call (\<open>#1\<close>), recursive procedure (\<open>#2\<close>), buffer procedures
  (\<open>#3\<close>) and system (\<open>#4\<close>), as the \<open>[stored as ...]\<close> messages report. The function becomes
  \<^verbatim>\<open>euclid.occ\<close> and the buffer a second file, \<^verbatim>\<open>buffer.occ\<close> - one with the procedures, one
  with the system that uses them, in dependency order.
\<close>

occam2_export "euclid" exports "Occam2_Example#0"
occam2_export "buffer" exports "Occam2_Example#3" "Occam2_Example#4"

ML\<open>
val dir = Resources.master_directory @{theory}
val _ = check "euclid.occ re-parses as a library unit and prints identically"
  (let val text = File.read (Path.append dir (Path.explode "euclid.occ"))
       val again = Occam2_Parse.parse_quiet Occam2_Parse.Entry_Unit @{context} (Input.string text)
   in (case again of SOME r => Occam2_Ast.pp_root r ^ "\n" = text | NONE => false) end)
\<close>

end
