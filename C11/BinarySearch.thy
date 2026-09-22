(* Imports "SelectionSort" - not plain "C11" - for two reasons at once:
   first, the same sequential-build-order concern documented in
   SelectionSort.thy's own header comment (C11_Comments/C11_Typedefs,
   C11_Parser.thy, are process-wide "Synchronized.var"s, not per-theory
   state, so two theories that both run "c11"-family commands and have no
   import edge between them can race on that shared state if "isabelle
   build" schedules them in parallel) - extending the existing
   "C11 -> C11_Tests -> AntiqProbe -> SelectionSort" chain one further
   theory, rather than opening a new, unchained branch of it. Second,
   and just as important: "SelectionSort" is exactly where the four mockup
   antiquotations this theory itself uses below - "requires"/"ensures"/
   "inv"/"measure" - were registered ("mockup_annotation_antiq"), so
   importing it is what makes them available here at all, with nothing to
   redefine: they are inherited, unchanged, via the very same "cenv" this
   theory's own "c11" commands already thread through. *)
theory BinarySearch
  imports SelectionSort
begin

section\<open>The Problem\<close>

text\<open>We re-formulate the BinarySearch example from the same why-tool suite
\<^url>\<open>https://why3.org/\<close> \<open>\<section>1\<close> of \<^verbatim>\<open>SelectionSort.thy\<close> already draws on. In WhyML,
it reads as follows:
@{verbatim \<open>
module BinarySearch

use import int.Int
use import int.ComputerDivision
use import ref.Ref
use import array.Array

exception Return int

let binarysearch (t : array int) (v : int) : int =
  (* formulation du tri generale necessaire pour la preuve *)
  (* ca ne passe pas avec t[i] <= t[i+1] *)
  requires { forall i j:int. 0 <= i <= j < length t -> t[i] <= t[j] }
  (* attention, si on met deux implications, il faut ajouter que le resultat
  est entre -1 et length t *)
  ensures { (0 <= result < length t /\ t[result] = v) \/
            (result = -1 /\ forall i:int. 0 <= i < length t -> t[i] <> v) }
  let l = ref 0 in
  let u = ref (length t - 1) in
  try
    while (!l <= !u) do
    invariant { forall i:int. 0 <= i < !l \/ !u < i < length t -> t[i] <> v }
    invariant { 0 <= !l <= length t }
    invariant { -1 <= !u < length t }
    variant { !u - !l }
      let m = !l + div (!u - !l) 2 in
      if (t[m] < v)
      then l := m + 1
      else if (t[m] > v)
           then u := m - 1
           else raise (Return m)
    done;
    -1
  with
    Return m -> m
  end

end\<close>}

  As with \<open>SelectionSort.thy\<close>, no semantic interpretation and therefore no
  formal verification is intended in this example - only the syntactic
  translation of a genuinely non-trivial, doubly-nested-condition
  specification into \<open>C11\<close> mockup antiquotations.

  WhyML's own \<open>result\<close> (the function's return value, bound implicitly
  inside \<open>ensures\<close>) becomes an ordinary free variable \<open>result\<close> in the
  \<open>ensures\<close> proposition below - exactly the kind of small, honest gap a
  \<^emph>\<open>mockup\<close> annotation is allowed to leave for a later semantic backend to
  actually give meaning to, the same way \<open>SelectionSort.thy\<close>'s own \<open>t0\<close>
  stands in for WhyML's \<open>old t\<close>. WhyML's \<open>try ... with Return m -> m end\<close>
  (an exception used purely for an early return from inside the loop)
  becomes a plain C \<open>return\<close> statement - C has no need of an exception to
  express "stop the loop and hand back this value now".
\<close>

section\<open>The "binarySearch" Unit\<close>

text\<open>
  The interface: a forward declaration for \<open>binarySearch\<close>, carrying both
  of WhyML's own conditions - the \<open>requires\<close> that \<open>t\<close> is sorted (without
  it, nothing below can be proved once a real semantic backend is
  attached), and the \<open>ensures\<close> that a non-negative result is a genuine
  hit and \<open>-1\<close> means \<open>v\<close> is nowhere in \<open>t\<close>.\<close>
c11\<open>
//@ requires \<open>\<forall>i j::int. 0 \<le> i \<and> i \<le> j \<and> j < n \<longrightarrow> t i \<le> t j\<close>
//@ ensures \<open>(0 \<le> result \<and> result < n \<and> t result = v) \<or>
             (result = -1 \<and> (\<forall>i::int. 0 \<le> i \<and> i < n \<longrightarrow> t i \<noteq> v))\<close>
int binarySearch(int *t, int n, int v);
\<close>

text\<open>
  The implementation: the \<open>while\<close> loop carries all three of WhyML's own
  invariants - the two range bounds on \<open>l\<close>/\<open>u\<close>, and the "\<open>v\<close> is not among
  what has already been ruled out" invariant that is the crux of the whole
  proof - plus a \<open>measure\<close> standing in for WhyML's own explicit \<open>variant
  { !u - !l }\<close> (unlike \<open>SelectionSort\<close>'s bounded \<open>for\<close> loops, a \<open>while\<close>
  loop's termination is never implicit, in WhyML or in this mockup).\<close>
c11\<open>
int binarySearch(int *t, int n, int v) {
  int l = 0;
  int u = n - 1;
  while (/*@ inv \<open>\<forall>i::int. (0 \<le> i \<and> i < l) \<or> (u < i \<and> i < n) \<longrightarrow> t i \<noteq> v\<close>
          @ inv \<open>0 \<le> l \<and> l \<le> n\<close>
          @ inv \<open>-1 \<le> u \<and> u < n\<close>
          @ measure \<open>u - l\<close> */
         l <= u) {
    int m = l + (u - l) / 2;
    if (t[m] < v) {
      l = m + 1;
    } else if (t[m] > v) {
      u = m - 1;
    } else {
      return m;
    }
  }
  return -1;
}
\<close>

section\<open>The "driver" Unit\<close>

text\<open>
  A small demo \<open>main\<close>: reads up to \<open>N\<close> already-sorted integers into an
  array (the \<open>requires\<close> above is exactly the contract this driver must
  itself honour, not something \<open>binarySearch\<close> checks), then one further
  integer \<open>v\<close> to search for, and prints whichever index (or \<open>-1\<close>)
  \<open>binarySearch\<close> returns.\<close>
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

  int v;
  if (scanf("%d", &v) != 1) {
    return 1;
  }

  int result = binarySearch(t, n, v);
  printf("%d\n", result);

  return 0;
}
\<close>

section\<open>Exporting\<close>

text\<open>
  \<open>binarySearch\<close>'s own two stored sections - the interface and the
  implementation above - become \<open>binarySearch.h\<close> and \<open>binarySearch.c\<close>;
  the driver's single stored section becomes \<open>binarySearchDriver.c\<close> -
  named for this theory specifically, not just \<open>driver.c\<close>: both this
  theory and \<^verbatim>\<open>SelectionSort.thy\<close> live in the same master directory
  (both under \<^verbatim>\<open>C11/\<close>), so a bare \<open>driver.c\<close> from each would actually
  collide on disk, whichever theory happened to build last silently
  overwriting the other's. The store keys below are this theory's own
  three - everything before them already belongs to the \<open>c11\<close>-family
  commands this theory's own import chain runs first (\<^verbatim>\<open>C11.thy\<close>'s
  \<open>c11_predef\<close> declarations, then \<^verbatim>\<open>C11_Tests.thy\<close>'s,
  \<^verbatim>\<open>AntiqProbe.thy\<close>'s, and \<^verbatim>\<open>SelectionSort.thy\<close>'s own three), exactly
  as \<open>c11\<close>'s own "[stored as ...]" output reports them.\<close>
c11_export_h "binarySearch" exports "BinarySearch#82"
c11_export_c "binarySearch" exports "BinarySearch#83"
c11_export_c "binarySearchDriver" exports "BinarySearch#84"

end
