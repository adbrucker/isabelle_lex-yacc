(* Imports "BinarySearch" - not plain "C11" - for the same two reasons
   documented in "SelectionSort.thy"'s and "BinarySearch.thy"'s own header
   comments: it extends the "C11 -> C11_Tests -> AntiqProbe -> SelectionSort
   -> BinarySearch" chain one further theory, to force a sequential build
   order (C11_Comments/C11_Typedefs, C11_Parser.thy, are process-wide
   "Synchronized.var"s, not per-theory state - the project's known lexer
   re-entrancy limitation - so two theories that both run "c11"-family
   commands with no import edge between them can race on that shared state
   if "isabelle build" schedules them in parallel), and it is what makes
   the "requires"/"ensures"/"inv"/"measure" mockup antiquotations this
   theory uses below available at all - they were registered once, in
   "SelectionSort.thy", and are inherited unchanged via "cenv", with
   nothing to redefine here. *)
theory MergeSort
  imports BinarySearch
begin

section\<open>The Problem\<close>

text\<open>A third example from the same why-tool suite \<^url>\<open>https://why3.org/\<close>
\<open>\<section>1\<close> of \<^verbatim>\<open>SelectionSort.thy\<close> and \<^verbatim>\<open>BinarySearch.thy\<close> already draw on -
unlike those two, no pre-existing WhyML formulation was at hand for this
one, so it is written here from scratch, in the same style and using the
same WhyML idioms (\<open>array int\<close>, \<open>ref\<close>, \<open>requires\<close>/\<open>ensures\<close>/\<open>invariant\<close>/
\<open>variant\<close>) as the other two:
@{verbatim \<open>
module MergeSort

use import int.Int
use import ref.Ref
use import array.Array

let merge (t : array int) (l m u : int) : unit
  requires { 0 <= l <= m <= u <= length t }
  requires { forall i j:int. l <= i <= j < m -> t[i] <= t[j] }
  requires { forall i j:int. m <= i <= j < u -> t[i] <= t[j] }
  ensures { forall i j:int. l <= i <= j < u -> t[i] <= t[j] }
=
  let tmp = Array.make (u - l) 0 in
  let i = ref l in
  let j = ref m in
  let k = ref 0 in
  while (!i < m || !j < u) do
    invariant { l <= !i <= m }
    invariant { m <= !j <= u }
    invariant { !k = (!i - l) + (!j - m) }
    variant { (u - !i) + (u - !j) }
    if (!j >= u || (!i < m && t[!i] <= t[!j]))
    then begin tmp[!k] <- t[!i]; i := !i + 1 end
    else begin tmp[!k] <- t[!j]; j := !j + 1 end;
    k := !k + 1
  done;
  Array.blit tmp 0 t l (u - l)

let rec mergesort (t : array int) (l u : int) : unit
  requires { 0 <= l <= u <= length t }
  variant { u - l }
  ensures { forall i j:int. l <= i <= j < u -> t[i] <= t[j] }
= if u - l > 1 then begin
    let m = l + (u - l) / 2 in
    mergesort t l m;
    mergesort t m u;
    merge t l m u
  end

end\<close>}

  As with the other two examples, no semantic interpretation and therefore
  no formal verification is intended here - only the syntactic translation
  of \<open>merge\<close>'s own three-way \<open>requires\<close>/one \<open>ensures\<close> contract and its
  \<open>while\<close> loop's four annotations (three \<open>invariant\<close>s plus a \<open>variant\<close>
  built from \<^emph>\<open>two\<close> summands, unlike \<open>SelectionSort\<close>'s or
  \<open>BinarySearch\<close>'s own single-quantity measures), and of \<open>mergesort\<close>'s
  own recursive \<open>variant\<close> - into \<open>C11\<close> mockup antiquotations.\<close>

section\<open>The "mergeSort" Unit\<close>

text\<open>
  The interface: forward declarations for \<open>merge\<close> and \<open>mergeSort\<close>. WhyML's
  \<open>array int\<close> becomes a C \<open>int *\<close> parameter plus an explicit length \<open>n\<close>,
  exactly as in \<open>SelectionSort.thy\<close>/\<open>BinarySearch.thy\<close>; \<open>merge\<close>'s own three
  \<open>requires\<close> - the sub-range bounds, and the two halves already being
  individually sorted - sit on its own declaration, and its single
  \<open>ensures\<close> is the postcondition \<open>mergeSort\<close>'s own \<open>ensures\<close> ultimately
  relies on.\<close>
c11\<open>
//@ requires \<open>0 \<le> l \<and> l \<le> m \<and> m \<le> u \<and> u \<le> n\<close>
//@ requires \<open>\<forall>i j::nat. l \<le> i \<and> i \<le> j \<and> j < m \<longrightarrow> t i \<le> t j\<close>
//@ requires \<open>\<forall>i j::nat. m \<le> i \<and> i \<le> j \<and> j < u \<longrightarrow> t i \<le> t j\<close>
//@ ensures \<open>\<forall>i j::nat. l \<le> i \<and> i \<le> j \<and> j < u \<longrightarrow> t i \<le> t j\<close>
void merge(int *t, int n, int l, int m, int u);

//@ requires \<open>0 \<le> l \<and> l \<le> u \<and> u \<le> n\<close>
//@ ensures \<open>\<forall>i j::nat. l \<le> i \<and> i \<le> j \<and> j < u \<longrightarrow> t i \<le> t j\<close>
void mergeSort(int *t, int n, int l, int u);
\<close>

text\<open>
  The implementation: \<open>merge\<close>'s own \<open>while\<close> loop carries all three of
  WhyML's own invariants - the two range bounds on \<open>i\<close>/\<open>j\<close>, and the "\<open>k\<close>
  already accounts for exactly what has been merged so far" bookkeeping
  invariant - plus a \<open>measure\<close> built the same way WhyML's own \<open>variant
  { (u - !i) + (u - !j) }\<close> is: the sum of what remains on \<^emph>\<open>each\<close> side, not
  a single quantity, since either side alone need not shrink on a given
  iteration. \<open>mergeSort\<close> itself is a genuine recursive C function - a
  forward-declared function calling itself is nothing new here (the
  regression suite's own \<open>fact\<close> example, \<open>\<section>2.2\<close>, already exercises this) -
  with its own \<open>measure\<close> standing in for WhyML's \<open>variant { u - l }\<close> on the
  recursive call. WhyML's \<open>Array.make\<close>/\<open>Array.blit\<close> (a fresh temporary
  array, then copied back) become an ordinary C array with a runtime size
  and a plain copy-back loop.\<close>
c11\<open>
void merge(int *t, int n, int l, int m, int u) {
  int tmp[u - l];
  int i = l;
  int j = m;
  int k = 0;
  while (/*@ inv \<open>l \<le> i \<and> i \<le> m\<close>
          @ inv \<open>m \<le> j \<and> j \<le> u\<close>
          @ inv \<open>k = (i - l) + (j - m)\<close>
          @ measure \<open>(u - i) + (u - j)\<close> */
         i < m || j < u) {
    if (j >= u || (i < m && t[i] <= t[j])) {
      tmp[k] = t[i];
      i = i + 1;
    } else {
      tmp[k] = t[j];
      j = j + 1;
    }
    k = k + 1;
  }
  for (int p = 0; p < u - l; p = p + 1) {
    t[l + p] = tmp[p];
  }
}

void mergeSort(int *t, int n, int l, int u) {
  if (/*@ measure \<open>u - l\<close> */ u - l > 1) {
    int m = l + (u - l) / 2;
    mergeSort(t, n, l, m);
    mergeSort(t, n, m, u);
    merge(t, n, l, m, u);
  }
}
\<close>

section\<open>The "driver" Unit\<close>

text\<open>
  A small demo \<open>main\<close>: reads up to \<open>N\<close> integers from standard input into
  an array, sorts the whole array with \<open>mergeSort\<close>, and prints the
  result, one value per line - the same shape as \<open>SelectionSort.thy\<close>'s
  own driver, just calling \<open>mergeSort\<close> instead of \<open>selectionSort\<close>.\<close>
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

  mergeSort(t, n, 0, n);

  for (int i = 0; i < n; i = i + 1) {
    printf("%d\n", t[i]);
  }

  return 0;
}
\<close>

section\<open>Exporting\<close>

text\<open>
  \<open>mergeSort\<close>'s own two stored sections - the interface and the
  implementation above - become \<open>mergeSort.h\<close> and \<open>mergeSort.c\<close>; the
  driver's single stored section becomes \<open>mergeSortDriver.c\<close> - named for
  this theory specifically, not just \<open>driver.c\<close>, for the same reason
  \<open>SelectionSort.thy\<close>/\<open>BinarySearch.thy\<close> each name theirs
  \<open>selectionSortDriver.c\<close>/\<open>binarySearchDriver.c\<close>: all three theories share
  the same master directory (\<^verbatim>\<open>C11/\<close>), so a bare \<open>driver.c\<close> from any of
  them would silently overwrite whichever one built last. The store keys
  below are this theory's own three - everything before them already
  belongs to the \<open>c11\<close>-family commands this theory's own import chain
  runs first (\<^verbatim>\<open>C11.thy\<close>'s \<open>c11_predef\<close> declarations, then
  \<^verbatim>\<open>C11_Tests.thy\<close>'s, \<^verbatim>\<open>AntiqProbe.thy\<close>'s, \<^verbatim>\<open>SelectionSort.thy\<close>'s, and
  \<^verbatim>\<open>BinarySearch.thy\<close>'s own three each), exactly as \<open>c11\<close>'s own
  "[stored as ...]" output reports them.\<close>
c11_export_h "mergeSort" exports "MergeSort#85"
c11_export_c "mergeSort" exports "MergeSort#86"
c11_export_c "mergeSortDriver" exports "MergeSort#87"

end
