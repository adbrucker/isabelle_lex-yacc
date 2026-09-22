(* Imports "AntiqProbe" - the last theory in the pre-existing "C11 ->
   C11_Tests -> AntiqProbe" chain - rather than plain "C11" directly, purely
   to force a sequential build order: C11_Comments/C11_Typedefs
   (C11_Parser.thy) are process-wide "Synchronized.var"s, not per-theory
   state (the project's own known, not-yet-fixed lexer re-entrancy
   limitation), so two theories that both run "c11"-family commands and
   have no import edge between them can be scheduled in parallel by
   "isabelle build" and genuinely race on that shared state - observed
   directly here: this theory's own "requires"/"ensures"/"inv"/"measure"
   antiquotations, registered only here, occasionally got cross-attached to
   a node being walked concurrently in "C11_Tests.thy" (which never
   registers them), surfacing as a spurious "no antiquotation handler
   registered for tag ..." error there. C11_Manual.thy still imports plain
   "C11" and so still shares this same latent risk with C11_Tests/
   AntiqProbe - pre-existing, not introduced here - left alone rather than
   restructured as part of this fix. *)
theory SelectionSort
  imports AntiqProbe
begin

section\<open>The Problem\<close>

text\<open>We re-formulate the SelectionSort Example from the Suite of the why-tool \<^url>\<open>https://why3.org/\<close>.
In its specific language WhyML, it reads as follows:
@{verbatim \<open>
module SelectionSort

use import int.Int
use import ref.Ref
use import array.Array

val swap (t : array int) (i j : int): unit
  (* seule la premiere post-condition est necessaire pour la preuve... *)
  requires { 0 <= i < length t }
  requires { 0 <= j < length t }
  ensures { t[i] = old t[j] /\ t[j] = old t[i] }
  ensures { forall k:int. 0 <= k < length t /\ k <> i /\ k <> j -> t[k] = (old t)[k] }

let selectionsort (t : array int) =
  ensures { forall i j:int. 0 <= i <= j < length t -> t[i] <= t[j] }
  for i = 0 to length t - 1 do
    invariant { forall k l:int. 0 <= k <= l < i -> t[k] <= t[l] }
    invariant { forall k l:int. 0 <= k < i /\ i <= l < length t -> t[k] <= t[l] }
    let min = ref i in
    for j = i + 1 to length t - 1 do
      invariant { i <= !min < j }
      invariant { forall k:int. i <= k < j -> t[!min] <= t[k] }
      if (t[j] < t[!min])
      then min := j
    done;
    swap t i !min
  done
end\<close>}

  In this example demonstrating syntactic issues, no semantic interpretation 
  and therefore no formal verification is intended.

  As a consequence, the WhyML front- end's own \<open>requires\<close>/\<open>ensures\<close>/\<open>invariant\<close> specification 
  language, kept for reference in the genuine \<open>C11\<close> example below, is realized by mockups.
  This concerns the four WhyML annotation kinds - \<open>requires\<close>, \<open>ensures\<close>, loop \<open>invariant\<close>,
  and the implicit termination argument every WhyML \<open>for\<close> loop carries, which become
  become four C-antiquotations of the same shape (\<open>@tag \<open>...\<close>\<close>.

  The definition of these mockups follows here:
\<close>

ML\<open>

val ANNOTATION_PROBE = Unsynchronized.ref ([] : (string * term) list)
fun mockup_annotation_antiq name =
  let
    fun probe (_, c_ast, _) (body, body_pos) thy =
      let
        val ctxt = Proof_Context.init_global thy
        val start_pos = Position.no_range_position body_pos
        val end_pos = Position.symbol_explode body start_pos
        val encoded = Syntax.implode_input (Input.source true body (start_pos, end_pos))
        val t = Syntax.read_term ctxt encoded
          handle exn =>
            if Exn.is_interrupt exn then Exn.reraise exn
            else error (name ^ " antiquotation: " ^ Runtime.exn_message exn ^
                         Position.here (AnaEval.pos_of_root c_ast))
      in (ANNOTATION_PROBE := (name, t) :: !ANNOTATION_PROBE; thy) end
  in CEnv.store_antiq (name, CEnv.lift_theory_antiq probe) end
\<close>

setup\<open>mockup_annotation_antiq "requires"\<close>
setup\<open>mockup_annotation_antiq "ensures"\<close>
setup\<open>mockup_annotation_antiq "inv"\<close>
setup\<open>mockup_annotation_antiq "measure"\<close>

text\<open>
  WhyML's \<open>array int\<close> becomes a C \<open>int *\<close> parameter plus an explicit
  length \<open>n\<close> (C arrays, unlike WhyML's, do not carry their own length);
  WhyML's \<open>old t\<close> (the array's value on entry) becomes a second, otherwise
  unconstrained free variable \<open>t0\<close> in the \<open>ensures\<close> proposition - both are
  exactly the kind of small, honest gap a \<^emph>\<open>mockup\<close> annotation is allowed
  to leave for a later semantic backend to actually give meaning to.
\<close>

section\<open>The "selectionSort" Unit\<close>

text\<open>
  The interface: forward declarations for \<open>swap\<close> and \<open>selectionSort\<close>,
  each annotated with the \<open>requires\<close>/\<open>ensures\<close> WhyML gave the corresponding
  declaration. This is exactly what a real \<open>selectionSort.h\<close> would contain -
  and, via \<open>c11_export_h\<close> below, is exactly what it becomes.\<close>
c11\<open>
//@ requires \<open>(0::nat) \<le> i \<and> i < n\<close>
//@ requires \<open>(0::nat) \<le> j \<and> j < n\<close>
//@ ensures \<open>t i = t0 j \<and> t j = t0 i\<close>
//@ ensures \<open>\<forall>k::nat. 0 \<le> k \<and> k < n \<and> k \<noteq> i \<and> k \<noteq> j \<longrightarrow> t k = t0 k\<close>
void swap(int *t, int n, int i, int j);

//@ ensures \<open>\<forall>i j::nat. 0 \<le> i \<and> i \<le> j \<and> j < n \<longrightarrow> t i \<le> t j\<close>
void selectionSort(int *t, int n);
\<close>

text\<open>
  The implementation: \<open>swap\<close>'s body needs no further annotation of its own
  (its whole contract already sits on the forward declaration above);
  \<open>selectionSort\<close>'s two nested loops each carry the loop invariant WhyML's
  \<open>for\<close> required, plus an explicit \<open>measure\<close> - the number of remaining
  iterations - standing in for the termination argument WhyML's own bounded
  \<open>for\<close> gives for free. The inner loop's own C variable \<open>min\<close> (WhyML's
  \<open>!min\<close>) is spelled \<open>m\<close> inside its \<open>inv\<close> propositions - \<open>min\<close> itself
  already names a real HOL constant (\<^const>\<open>min\<close>), so using it as a free
  variable there would silently force \<open>t\<close> to expect a binary function as
  its argument instead of a plain index, a genuine trap for a mockup
  annotation to fall into.\<close>
c11\<open>
void swap(int *t, int n, int i, int j) {
  int tmp = t[i];
  t[i] = t[j];
  t[j] = tmp;
}

void selectionSort(int *t, int n) {
  for (/*@ inv \<open>\<forall>k l::nat. 0 \<le> k \<and> k \<le> l \<and> l < i \<longrightarrow> t k \<le> t l\<close>
        @ inv \<open>\<forall>k l::nat. 0 \<le> k \<and> k < i \<and> i \<le> l \<and> l < n \<longrightarrow> t k \<le> t l\<close>
        @ measure \<open>n - i\<close> */
       int i = 0; i < n; i = i + 1) {
    int min = i;
    for (/*@ inv \<open>i \<le> m \<and> m < j\<close>
          @ inv \<open>\<forall>k::nat. i \<le> k \<and> k < j \<longrightarrow> t m \<le> t k\<close>
          @ measure \<open>n - j\<close> */
         int j = i + 1; j < n; j = j + 1) {
      if (t[j] < t[min]) {
        min = j;
      }
    }
    swap(t, n, i, min);
  }
}
\<close>

section\<open>The "driver" Unit\<close>

text\<open>
  A small demo \<open>main\<close>: reads up to \<open>N\<close> integers from standard input into
  an array, sorts it with \<open>selectionSort\<close>, and prints the result, one
  value per line. \<open>scanf\<close> is not among \<open>stdio.h\<close>'s own predefined names
  (\<open>\<section>3\<close> of the Manual only lists \<open>printf\<close>/\<open>putchar\<close>/\<open>getchar\<close>/\<open>puts\<close>), so
  it gets an ordinary forward declaration here, exactly as a real C file
  would need if it used \<open>scanf\<close> without a matching header.\<close>
c11\<open>
#include <stdio.h>

int scanf(const char *format, ...);

#define N 100

int main(void) {
  int t[N];
  int n = 0;

  while (n < N) {
    if (scanf("%d", &t[n]) != 1) {
      break;
    }
    n = n + 1;
  }

  selectionSort(t, n);

  for (int i = 0; i < n; i = i + 1) {
    printf("%d\n", t[i]);
  }

  return 0;
}
\<close>

section\<open>Exporting\<close>

text\<open>
  \<open>selectionSort\<close>'s own two stored sections - the interface and the
  implementation above - become \<open>selectionSort.h\<close> and \<open>selectionSort.c\<close>;
  the driver's single stored section becomes \<open>driver.c\<close>. The store keys
  below are this theory's own three (\<open>SelectionSort#79\<close>, \<open>#80\<close>, \<open>#81\<close> -
  everything before that already belongs to the \<^verbatim>\<open>c11\<close>-family commands
  this theory's own import chain runs first: \<^verbatim>\<open>C11.thy\<close>'s own four
  \<open>c11_predef\<close> declarations (\<open>\<section>3\<close>), then \<^verbatim>\<open>C11_Tests.thy\<close>'s and
  \<^verbatim>\<open>AntiqProbe.thy\<close>'s own, both inherited via this theory's own
  \<open>imports\<close>, chosen precisely to force that sequencing - see this theory's
  own header comment), exactly as \<open>c11\<close>'s own "[stored as ...]" output
  reports them.\<close>
c11_export_h "selectionSort" exports "SelectionSort#79"
c11_export_c "selectionSort" exports "SelectionSort#80"
c11_export_c "driver" exports "SelectionSort#81"

end
