(******************************************************************************
 * Copyright (c) University of Paris-Saclay
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 ******************************************************************************)

theory Occam2_AnaEval
  imports "Occam2_Env"
begin

section\<open>Analyse and Eval\<close>

text\<open>
  \<open>analyse_and_eval\<close> is the occam 2 counterpart of the C11 pass of the same name
  (\<^verbatim>\<open>C11_AnaEval.thy\<close>, whose long explanation applies here almost verbatim and is
  not repeated): a single, purely functional, scoped walk over a parsed \<open>root\<close>,
  threading \<open>oenv\<close> through the descent, collecting every antiquotation action
  paired with its \<open>level\<close> instead of applying it, and hyperlinking every name
  use to its declaration. What is specific to occam:

  \<^item> \<^bold>\<open>Scoping.\<close> A specification is in scope exactly in the process (or value
    process, choice, option, variant, alternative) it prefixes: \<open>PSpecP (spec,
    p)\<close> registers \<open>spec\<close>'s names, walks \<open>p\<close>, and then restores the incoming
    \<open>idents\<close> table - the same shadow-and-restore discipline as C11's blocks. A
    replicator (\<open>SEQ i = 0 FOR n\<close>) scopes its index over its body only; its base
    and count are walked \<^emph>\<open>before\<close> the index is registered. A \<open>Specs\<close> unit (a
    library-style run of specifications) is the one case that does \<^emph>\<open>not\<close>
    restore: its names stay in \<open>idents\<close> and so are visible to every later
    fragment of the theory.
  \<^item> \<^bold>\<open>No recursion.\<close> occam 2 forbids recursive procedures and functions: the body
    of a \<open>PROC\<close>/\<open>FUNCTION\<close> is walked \<^emph>\<open>before\<close> its own name is registered, so a
    self-call is reported as an undeclared name (\<^ML>\<open>Markup.bad ()\<close>), exactly as
    the language demands. A declaration likewise sees only the names above it:
    \<open>x IS x:\<close> refers to an \<^emph>\<open>outer\<close> \<open>x\<close>.
  \<^item> \<^bold>\<open>Formals.\<close> Formal parameters are registered one by one, each type walked
    \<^emph>\<open>before\<close> its names, so a later formal's array size may use an earlier formal
    (\<open>PROC p (VAL INT n, []BYTE s)\<close> and \<open>[n]BYTE\<close> alike).
  \<^item> \<^bold>\<open>One name space.\<close> Variables, channels, abbreviations, parameters, replicator
    indices, procedures, functions, protocols and protocol tags are all names in
    the one \<open>idents\<close> table (see \<^verbatim>\<open>Occam2_Env.thy\<close>); a use is hyperlinked whatever
    it was declared as, and the entity kind in the markup says which.
  \<^item> \<^bold>\<open>The closest-context stack\<close> \<open>ctx : pos root list\<close>. \<open>walk_expr\<close>, \<open>walk_proc\<close>
    and \<open>walk_spec\<close> always push their own node (\<open>Expr\<close>/\<open>Proc\<close>/\<open>Spec\<close>);
    everything else (types, protocols, formals, replicators, choices, options,
    variants, alternatives, guards) never pushes and uses \<open>hd ctx\<close>. An element
    used as an expression (an assignment target, a channel, a variable on the
    right) is pushed as \<open>Expr (EElem el)\<close>, so \<open>x[i]\<close> navigates to \<open>x\<close> and \<open>i\<close> as
    its two children.
  \<^item> \<^bold>\<open>Navigation\<close> (\<open>u\<close>/\<open>U\<close>/\<open>r\<close>/\<open>d\<close>) is identical to C11's. The children of a node
    are, in source order, its sub-expressions, sub-processes and
    sub-specifications; a \<open>PSpecP (s, p)\<close> has the two children \<open>Spec s\<close> and
    \<open>Proc p\<close> (a chain of specifications is therefore a right-nested chain of
    \<open>PSpecP\<close> nodes, each reached by one more \<open>d\<close> step into \<open>r\<close>-th child 2);
    choices, options, variants, alternatives, guards and replicators have no
    \<open>root\<close> variant and are flattened into their parent's child list; types and
    protocols are dropped, as C11 drops type-names.

\<close>
ML\<open>
structure AnaEval = struct

structure A = Occam2_Ast
open OEnv

type acts = (int * (Context.generic -> Context.generic)) list

fun idents_of (mk {idents, ...} : oenv) = idents

fun set_idents idents' (mk {idents = _, occam_antiq, units}) =
  mk {idents = idents', occam_antiq = occam_antiq, units = units}

(* The position a "root" itself spans - what a "type_antiq_fun" sees as its own
   "current term". A "Specs" has no single span, so falls back to
   "Position.none" like C11's multi-unit "Units". *)
fun pos_of_root (A.Id id) = A.pos_of_ident id
  | pos_of_root (A.Expr e) = A.pos_of_expr e
  | pos_of_root (A.Proc p) = A.pos_of_process p
  | pos_of_root (A.Spec s) = A.pos_of_spec s
  | pos_of_root (A.Specs _) = Position.none

(* Exactly-once dispatch of every physical antiquotation, whatever number of AST
   nodes share its leftmost source position - the same design, for the same
   reason, as C11's "Dispatched_Antiqs" (see C11_AnaEval.thy). The set of
   comments already dispatched belongs to one walk ("analyse_and_eval" below
   installs a fresh one for its dynamic extent) and is kept per thread: a walk
   is plain, synchronous recursion on a single thread, so two walks running at
   the same time (in different threads) cannot see each other's set - a
   process-wide variable, as before, made them interfere. *)
structure Dispatched_Antiqs = struct
  val state : Position.T A.comment list Unsynchronized.ref Thread_Data.var =
    Thread_Data.var ()
  fun current () =
    (case Thread_Data.get state of
       SOME r => r
     | NONE => raise Fail "Dispatched_Antiqs: outside of analyse_and_eval")
  fun with_fresh f = Thread_Data.setmp state (SOME (Unsynchronized.ref [])) f ()
  fun already_dispatched c = member (op =) (!(current ())) c
  fun mark c = let val r = current () in r := c :: !r end
end

(* A navigation step's coarse target category, ignoring the constructor within.
   *)
fun category (A.Id _)    = 0
  | category (A.Expr _)  = 1
  | category (A.Proc _)  = 2
  | category (A.Spec _)  = 3
  | category (A.Specs _) = 4

fun run_length (ctx as top :: _) =
      let
        val cat = category top
        fun count (x :: xs) = if category x = cat then 1 + count xs else 0
          | count [] = 0
      in count ctx end

(* Resolves the "(u|U)*" prefix of a navigation string against "ctx",
   returning the unconsumed "(r|d)*" suffix together with the resulting
   stack. Derived directly from the user's own worked examples (each
   rule below cited by number):

   \<^item> Rule 1: "[u]" (the *whole* string, nothing left after it) on
     "[expr, ...]" is "that expr, unchanged" - a lone, final "u" is a no-op:
     "select_u" returns "ctx" as-is once it sees "up" with an empty tail.
   \<^item> Rule 2: "[u, R]" (a non-final "u") on "[expr, ...]" continues with
     "R" on whatever "..." was - i.e. "u" pops exactly one frame, unless
     "ctx" is already a singleton (nothing left to ascend past), in which
     case it is a no-op instead of an error.
   \<^item> Rule 3: "[U, R]" on a same-category run of length > 1 (e.g.
     "[expr, expr, expr, stmt, ...]") collapses the run down to its single
     outermost member and continues with "R" - it does *not* also pop that
     surviving member (contrast with rule 4).
   \<^item> Rule 4: "[U, R]" on a run of length 1 (e.g. "[expr, stmt, ...]") "is
     just [u, R] on [stmt, ...]" - read literally: the sole run member is
     already popped, and processing continues as an ordinary (not
     necessarily final) "u" step against the smaller stack, i.e. "U" with a
     trivial run always moves past it, whereas a written-out "u" alone would
     not (rule 1) - "U" and "u" are deliberately not fully interchangeable. *)

fun select_u ([], ctx) = ([], ctx)
  | select_u (A.up :: rest_navi, ctx) =
      if null rest_navi then ([], ctx)
      else (case ctx of
              [_] => select_u (rest_navi, ctx)
            | _ :: rest_ctx => select_u (rest_navi, rest_ctx))
  | select_u (A.Up :: rest_navi, ctx) =
      let val n = run_length ctx in
        if n > 1 then select_u (rest_navi, List.drop (ctx, n - 1))
        else (case ctx of
                [_] => select_u (A.up :: rest_navi, ctx)
              | _ :: rest_ctx => select_u (A.up :: rest_navi, rest_ctx))
      end
  | select_u (navi, ctx) =
      (navi, ctx) (* first "r"/"d": the "(u|U)*" phase is over *)

(* The ordered, per-node-kind list of children "r"/"d" may navigate into
   (see the top-of-theory note): sub-expressions, sub-processes and
   sub-specifications in source order. Nodes with no "root" variant (types,
   protocols, replicators, choices, options, variants, alternatives, guards,
   formals) are flattened into their parent's list or dropped, never counted
   as a gap in the index. An element in expression position is wrapped as
   "Expr (EElem el)", exactly as "walk_expr" pushes it. *)
fun elem_expr el = A.Expr (A.EElem el)

fun children_of_repl NONE = []
  | children_of_repl (SOME (A.Repl (_, base, count, _))) =
      [A.Expr base, A.Expr count]

fun children_of_input (A.InVars (ch, items, _)) =
      elem_expr ch ::
      maps (fn A.IIVar el => [elem_expr el]
             | A.IICounted (el1, el2) => [elem_expr el1, elem_expr el2]) items
  | children_of_input (A.InAfter (tm, e, _)) = [elem_expr tm, A.Expr e]

fun children_of_outitem (A.OIExpr e) = [A.Expr e]
  | children_of_outitem (A.OICounted (e1, e2)) = [A.Expr e1, A.Expr e2]

fun children_of_inputitem (A.IIVar el) = [elem_expr el]
  | children_of_inputitem (A.IICounted (el1, el2)) =
      [elem_expr el1, elem_expr el2]

fun children_of_vp (A.VPValof (p, es, _)) = A.Proc p :: map A.Expr es
  | children_of_vp (A.VPSpec (s, vp, _)) = A.Spec s :: children_of_vp vp

fun children_of_variant (A.VaTagged (_, items, p, _)) =
      maps children_of_inputitem items @ [A.Proc p]
  | children_of_variant (A.VaSpec (s, v, _)) = A.Spec s :: children_of_variant v

fun children_of_choice (A.ChGuarded (e, p, _)) = [A.Expr e, A.Proc p]
  | children_of_choice (A.ChNested p) = [A.Proc p]
  | children_of_choice (A.ChSpec (s, c, _)) = A.Spec s :: children_of_choice c

fun children_of_option (A.OpCases (es, p, _)) = map A.Expr es @ [A.Proc p]
  | children_of_option (A.OpElse (p, _)) = [A.Proc p]
  | children_of_option (A.OpSpec (s, o_, _)) = A.Spec s :: children_of_option o_

fun children_of_guard (A.GInput (inp, _)) = children_of_input inp
  | children_of_guard (A.GCondInput (e, inp, _)) = A.Expr e
      :: children_of_input inp
  | children_of_guard (A.GCondSkip (e, _)) = [A.Expr e]

fun children_of_alt (A.AlGuarded (g, p, _)) = children_of_guard g @ [A.Proc p]
  | children_of_alt (A.AlCase (eo, ch, vs, _)) =
      (case eo of NONE => [] | SOME e => [A.Expr e]) @ [elem_expr ch] @
      maps children_of_variant vs
  | children_of_alt (A.AlNested p) = [A.Proc p]
  | children_of_alt (A.AlSpec (s, a, _)) = A.Spec s :: children_of_alt a

fun children_of_placed (A.PlProcessor (e, p, _)) = [A.Expr e, A.Proc p]
  | children_of_placed (A.PlPar (repl, pls, _)) = children_of_repl repl
      @ maps children_of_placed pls

fun children_of_expr e =
  case e of
    A.EElem (A.ENamed _) => []
  | A.EElem (A.ESub (el, sub, _)) => [elem_expr el, A.Expr sub]
  | A.EElem (A.ESlice (el, from, for, _)) =>
    [elem_expr el, A.Expr from, A.Expr for]
  | A.ELit _ => [] (* a typed literal's type is dropped, like any type *)
  | A.ETable (A.TabString _) => []
  | A.ETable (A.TabList (es, _)) => map A.Expr es
  | A.ETable (A.TabSub (t, sub, _)) => [A.Expr (A.ETable t), A.Expr sub]
  | A.ETable (A.TabSlice (t, from, for, _)) =>
    [A.Expr (A.ETable t), A.Expr from, A.Expr for]
  | A.EParen (e1, _) => [A.Expr e1]
  | A.EMon (_, e1, _) => [A.Expr e1]
  | A.EBin (e1, _, e2, _) => [A.Expr e1, A.Expr e2]
  | A.EChain (_, es, _) => map A.Expr es
  | A.EConv (_, _, e1, _) => [A.Expr e1]
  | A.EMost _ => []
  | A.ECall (_, args, _) => map A.Expr args
  | A.EValof (vp, _) => children_of_vp vp

fun children_of_spec s =
  case s of
    A.SDecl _ => []
  | A.SAbbrev (_, _, el, _) => [elem_expr el]
  | A.SValAbbrev (_, _, e, _) => [A.Expr e]
  | A.SRetypes (_, _, el, _) => [elem_expr el]
  | A.SValRetypes (_, _, e, _) => [A.Expr e]
  | A.SProtocol _ => []
  | A.SProtocolCase _ => []
  | A.SProc (_, _, body, _) => [A.Proc body]
  | A.SFunction (_, _, _, vp, _) => children_of_vp vp
  | A.SFunctionIs (_, _, _, es, _) => map A.Expr es

fun children_of_proc p =
  case p of
    A.PSkip _ => []
  | A.PStop _ => []
  | A.PAssign (lhs, rhs, _) => map elem_expr lhs @ map A.Expr rhs
  | A.PInput (inp, _) => children_of_input inp
  | A.POutput (ch, items, _) => elem_expr ch :: maps children_of_outitem items
  | A.PCaseInput (ch, vs, _) => elem_expr ch :: maps children_of_variant vs
  | A.PSeq (repl, ps, _) => children_of_repl repl @ map A.Proc ps
  | A.PIf (repl, chs, _) => children_of_repl repl @ maps children_of_choice chs
  | A.PCase (e, opts, _) => A.Expr e :: maps children_of_option opts
  | A.PWhile (e, p1, _) => [A.Expr e, A.Proc p1]
  | A.PPar (_, repl, ps, _) => children_of_repl repl @ map A.Proc ps
  | A.PAlt (_, repl, alts, _) =>
    children_of_repl repl @ maps children_of_alt alts
  | A.PPlacedPar (repl, pls, _) =>
    children_of_repl repl @ maps children_of_placed pls
  | A.PInstance (_, args, _) => map A.Expr args
  | A.PSpecP (s, p1, _) => [A.Spec s, A.Proc p1]
  | A.PPlace (_, e, p1, _) => [A.Expr e, A.Proc p1]

fun children_of _ (A.Proc p) = children_of_proc p
  | children_of _ (A.Expr e) = children_of_expr e
  | children_of _ (A.Spec s) = children_of_spec s
  | children_of _ (A.Specs ss) = map A.Spec ss
  | children_of antiq_pos (A.Id _) =
      error ("select_ast: an identifier is a leaf, no \"r\"/\"d\" children"
             ^ Position.here antiq_pos)

(* Resolves the "(r|d)*" suffix against a single "node" (the result of
   "select_u"'s ascent phase): "r" advances a 1-based cursor rightward among
   "children_of node"; "d" descends into the child the cursor currently
   points at (cursor 1, i.e. "d" alone, if no "r" preceded it) and continues
   processing the remaining navigation string against *that* child. Per the
   user: no wrapping/saturation - a cursor beyond the children list's length
   is a hard "error", and a "d" with no children to descend into likewise.

   Every "error" here reports "antiq_pos" - the antiquotation's own tag
   position (threaded in from "check_antiq"/"select_ast" below), not the
   position of whatever AST node "node" currently is: a "navi" step (see
   "A.navi") carries no source position of its own, and "node" can by
   now be arbitrarily far from where the user actually wrote the mistaken
   "[navi]" bracket - "antiq_pos" is the closest thing available to "where
   the string was written", and is what a user actually needs to jump to. *)
fun select_rd (antiq_pos, [], node) = node
  | select_rd (antiq_pos, navi as A.down :: _, node) =
      select_count_r (antiq_pos, 1, navi, node)
  | select_rd (antiq_pos, A.right :: rest, node) =
      select_count_r (antiq_pos, 1, rest, node)
  | select_rd (antiq_pos, A.up :: _, _) =
      error ("select_ast: \"u\" after \"r\"/\"d\"" ^ Position.here antiq_pos)
  | select_rd (antiq_pos, A.Up :: _, _) =
      error ("select_ast: \"U\" after \"r\"/\"d\"" ^ Position.here antiq_pos)
and select_count_r (antiq_pos, n, A.right :: rest, node) =
  select_count_r (antiq_pos, n + 1, rest, node)
  | select_count_r (antiq_pos, n, A.down :: rest, node) =
      let val cs = children_of antiq_pos node in
        if n > length cs then
          error ("select_ast: navigation index " ^ Int.toString n
                 ^ " out of range (only " ^
                 Int.toString (length cs) ^ " navigable children here)"
                   ^ Position.here antiq_pos)
        else select_rd (antiq_pos, rest, List.nth (cs, n - 1))
      end
  | select_count_r (antiq_pos, _, A.up :: _, _) =
      error ("select_ast: \"u\" after \"r\"" ^ Position.here antiq_pos)
  | select_count_r (antiq_pos, _, A.Up :: _, _) =
      error ("select_ast: \"U\" after \"r\"" ^ Position.here antiq_pos)
  | select_count_r (antiq_pos, _, [], _) =
      error (("select_ast: navigation string ends with a dangling \"r\", " ^
              "expected a final \"d\"") ^
             Position.here antiq_pos)

(* Maps an antiquotation's own "navi list" (the "@tag[navi] ..." bracket -
   see "A.navi") together with the closest-surrounding-context stack to
   the single concrete AST node the antiquotation refers to: first resolves
   the "(u|U)*" prefix against the whole stack ("select_u"), then the
   "(r|d)*" suffix against whatever that leaves on top ("select_rd").
   "antiq_pos" (the antiquotation's own tag position) is carried along
   purely for error reporting - see the note on "select_rd". An empty navi
   list is the identity (matches every antiquotation predating this
   feature: "select_ast antiq_pos [] ctx = hd ctx"). *)
fun select_ast antiq_pos navi ctx =
  let val (rd, ctx') = select_u (navi, ctx)
  in select_rd (antiq_pos, rd, hd ctx') end

(* The shared antiquotation-dispatch helper: looks up every "Antiquotation" in
   "ni"'s comment list by tag in "oenv"'s "occam_antiq", instantiates it with
   (oenv, select_ast tag_pos navi ctx, level), and pairs the resulting
   "Context.generic -> Context.generic" with its level - "select_ast" (and so
   "children_of",
   which can "error") is only forced when an "Antiquotation" genuinely needs
   it, never for an ordinary "Raw_txt" or an empty comment list. "tag_pos"
   (the antiquotation's own tag position, previously discarded here) is
   passed through purely so a "select_ast" navigation error can be reported
   at "@tag[navi] ..." itself rather than at whatever AST node the failed
   navigation happened to reach - see the note on "select_rd". An
   "Antiquotation" already dispatched earlier in this same walk (see
   "Dispatched_Antiqs" above) is silently skipped the second (or third, ...)
   time some other node sharing its position reaches it - whichever node the
   walk reaches *first* (which, since every "walk_*" checks its own
   antiquotations before recursing into its children, is always the
   outermost of any nodes genuinely tied at one position) is the one that
   wins. The handler receives "(body, body_pos)", not just "body" - see
   "type_antiq_fun" in Occam2_Env.thy for why the cartouche's own position now
   travels all the way to the handler instead of being discarded here - and
   the *resolved* AST node ("select_ast tag_pos navi ctx"), not the raw navi
   list: a handler is never itself responsible for interpreting "up"/"Up"/
   "right"/"down". *)
fun check_antiq oenv (ctx : pos A.root list) (ni : pos A.nodeInfo)
    : (int * (Context.generic -> Context.generic)) list =
  case ni of
    A.OnlyPos _ => []
  | A.NodeInfo (cs, _) =>
      List.mapPartial
        (fn c as A.Antiquotation
         ({tag = (tag, tag_pos)}, navi, {level},
          {cartouche = (body, body_pos)}) =>
              if Dispatched_Antiqs.already_dispatched c then NONE
              else
                let val mk {occam_antiq, ...} = oenv in
                  case Symtab.lookup occam_antiq tag of
                    NONE =>
                      error (("analyse_and_eval: no antiquotation handler " ^
                              "registered for tag ") ^
                             quote tag)
                  | SOME antiq_fun =>
                      (Dispatched_Antiqs.mark c;
                       SOME (level,
                             antiq_fun
                               (oenv, select_ast tag_pos navi ctx, level)
                                 (body, body_pos)))
                end
          | A.Raw_txt _ => NONE)
        cs

(* The full-token range a name spans, starting at "pos": an identifier's own
   "nodeInfo" carries a bare point, which would make an entity report claim a
   single character (see the same note on "name_range" in C11_AnaEval.thy). *)
fun name_range (name, pos) =
  Position.range_position
    (Position.range (pos, Position.symbol_explode name pos))

fun report_decl kind name decl_pos =
  let val range_pos = name_range (name, decl_pos)
  in Position.report range_pos (Position.entity_markup kind (name, range_pos))
    end

(* Hyperlinks a use of "name" to its declaration, or marks it with
   \<^ML>\<open>Markup.bad ()\<close> (a highlight, deliberately not an error: "undeclared here"
   routinely just means "declared in a unit this parse never saw"). *)
fun report_use oenv name use_pos =
  let
    val mk {idents, ...} = oenv
    val use_range = name_range (name, use_pos)
  in
    case Symtab.lookup idents name of
      NONE => Position.report use_range (Markup.bad ())
    | SOME k =>
        Position.report use_range
          (Position.entity_markup (describe_kind k)
           (name, name_range (name, pos_of_kind k)))
  end

fun report_ident_use oenv (A.Ident (name, _, ni)) =
  report_use oenv name (A.pos_of_NodeInfo ni)

(* Registers one declared name, reporting its own declaration site. *)
fun register mk_kind oenv (A.Ident (name, _, ni)) =
  let
    val mk {idents, occam_antiq, units} = oenv
    val pos = A.pos_of_NodeInfo ni
    val kind = mk_kind pos
    val _ = report_decl (describe_kind kind) name pos
  in mk {idents = Symtab.update (name, kind) idents, occam_antiq =
         occam_antiq, units = units} end

(* A declaration "T x:" declares a channel when T is (an array of) a channel,
   timer or port type, a variable otherwise. *)
fun kind_of_type t =
  case t of
    A.TChan _ => Channel
  | A.TTimer _ => Channel
  | A.TPort _ => Channel
  | A.TArray (_, t1, _) => kind_of_type t1
  | A.TOpenArray (t1, _) => kind_of_type t1
  | A.TPrim _ => Variable

(* Sequential walk of a list, threading "oenv" and collecting the actions. *)
fun seq (f : oenv -> 'a -> oenv * acts) oenv xs =
  fold (fn x => fn (oenv, acc) =>
        let val (oenv', a) = f oenv x in (oenv', acc @ a) end)
    xs (oenv, [])

(* Runs "f" in a nested scope: the incoming "idents" table is restored on exit.
   *)
fun scoped oenv f =
  let
    val outer = idents_of oenv
    val (oenv1, acts) = f oenv
  in (set_idents outer oenv1, acts) end

fun walk_exprs oenv ctx es =
  seq (fn oenv => fn e => walk_expr oenv ctx e) oenv es

(* Always pushes its own node (see the top-of-theory note). *)
and walk_expr oenv ctx (e : pos A.oExpr) : oenv * acts =
  let
    val ctx' = A.Expr e :: ctx
    val here = check_antiq oenv ctx' (A.nodeInfo_of_expr e)
    fun plus (oenv1, acts) = (oenv1, here @ acts)
  in
    case e of
      A.EElem (A.ENamed id) => (report_ident_use oenv id; (oenv, here))
    | A.EElem (A.ESub (el, sub, _)) =>
      plus (walk_exprs oenv ctx' [A.EElem el, sub])
    | A.EElem (A.ESlice (el, from, for, _)) =>
      plus (walk_exprs oenv ctx' [A.EElem el, from, for])
    | A.ELit (A.LTyped (_, t, _)) => plus (walk_type oenv ctx' t)
    | A.ELit _ => (oenv, here)
    | A.ETable (A.TabString _) => (oenv, here)
    | A.ETable (A.TabList (es, _)) => plus (walk_exprs oenv ctx' es)
    | A.ETable (A.TabSub (t, sub, _)) =>
      plus (walk_exprs oenv ctx' [A.ETable t, sub])
    | A.ETable (A.TabSlice (t, from, for, _)) =>
      plus (walk_exprs oenv ctx' [A.ETable t, from, for])
    | A.EParen (e1, _) => plus (walk_exprs oenv ctx' [e1])
    | A.EMon (_, e1, _) => plus (walk_exprs oenv ctx' [e1])
    | A.EBin (e1, _, e2, _) => plus (walk_exprs oenv ctx' [e1, e2])
    | A.EChain (_, es, _) => plus (walk_exprs oenv ctx' es)
    | A.EConv (_, _, e1, _) => plus (walk_exprs oenv ctx' [e1])
    | A.EMost (_, t, _) => plus (walk_type oenv ctx' t)
    | A.ECall (id, args, _) =>
        (report_ident_use oenv id; plus (walk_exprs oenv ctx' args))
    | A.EValof (vp, _) => plus (walk_vp oenv ctx' vp)
  end

(* Types, protocols, formals, replicators, choices, options, variants,
   alternatives and guards never push: they check their own antiquotations
   against "ctx" as given, i.e. against whatever node encloses them. *)
and walk_type oenv ctx (t : pos A.oType) : oenv * acts =
  let val here = check_antiq oenv ctx (A.nodeInfo_of_type t)
  in
    case t of
      A.TPrim _ => (oenv, here)
    | A.TTimer _ => (oenv, here)
    | A.TChan (p, _) =>
      let val (o1, a1) = walk_protocol oenv ctx p in (o1, here @ a1) end
    | A.TPort (t1, _) =>
      let val (o1, a1) = walk_type oenv ctx t1 in (o1, here @ a1) end
    | A.TArray (e, t1, _) =>
        let
          val (o1, a1) = walk_expr oenv ctx e
          val (o2, a2) = walk_type o1 ctx t1
        in (o2, here @ a1 @ a2) end
    | A.TOpenArray (t1, _) =>
      let val (o1, a1) = walk_type oenv ctx t1 in (o1, here @ a1) end
  end

and walk_simple_prot oenv ctx sp =
  case sp of
    A.SPType t => walk_type oenv ctx t
  | A.SPCounted (_, ni, t, _) =>
      let
        val here = check_antiq oenv ctx ni
        val (o1, a1) = walk_type oenv ctx t
      in (o1, here @ a1) end

and walk_protocol oenv ctx (p : pos A.oProtocol) : oenv * acts =
  case p of
    A.PrName id =>
      (report_ident_use oenv
       id; (oenv, check_antiq oenv ctx (A.nodeInfo_of_ident id)))
  | A.PrSeq (sps, ni) =>
      let
        val here = check_antiq oenv ctx ni
        val (o1, a1) =
          seq (fn oenv => fn sp => walk_simple_prot oenv ctx sp) oenv sps
      in (o1, here @ a1) end
  | A.PrAny ni => (oenv, check_antiq oenv ctx ni)

(* Formals: each type is walked before its names are registered, so a later
   formal's type may use an earlier formal. *)
and walk_formals oenv ctx fs =
  seq (fn oenv => fn (A.Formal (_, t, ids, ni)) =>
         let
           val here = check_antiq oenv ctx ni
           val (o1, a1) = walk_type oenv ctx t
           val o2 = fold (fn id => fn o_ => register Param o_ id) ids o1
         in (o2, here @ a1) end)
    oenv fs

(* A replicator's base and count see the scope *outside* the replicator; only
   afterwards is the index registered (the caller restores the table). *)
and walk_repl oenv ctx (A.Repl (id, base, count, ni)) =
  let
    val here = check_antiq oenv ctx ni
    val (o1, a1) = walk_exprs oenv ctx [base, count]
    val o2 = register Replicator o1 id
  in (o2, here @ a1) end

and walk_opt_repl_then oenv ctx repl body =
  scoped oenv (fn oenv =>
    let
      val (o1, a1) =
        (case repl of NONE => (oenv, []) | SOME r => walk_repl oenv ctx r)
      val (o2, a2) = body o1
    in (o2, a1 @ a2) end)

and walk_input oenv ctx (inp : pos A.oInput) : oenv * acts =
  case inp of
    A.InVars (ch, items, ni) =>
      let
        val here = check_antiq oenv ctx ni
        val (o1, a1) = walk_exprs oenv ctx (A.EElem ch ::
          maps (fn A.IIVar el => [A.EElem el] | A.IICounted (e1, e2) =>
                [A.EElem e1, A.EElem e2]) items)
      in (o1, here @ a1) end
  | A.InAfter (tm, e, ni) =>
      let
        val here = check_antiq oenv ctx ni
        val (o1, a1) = walk_exprs oenv ctx [A.EElem tm, e]
      in (o1, here @ a1) end

and walk_input_items oenv ctx items =
  walk_exprs oenv ctx
    (maps (fn A.IIVar el => [A.EElem el] | A.IICounted (e1, e2) =>
           [A.EElem e1, A.EElem e2]) items)

and walk_choice oenv ctx (c : pos A.oChoice) : oenv * acts =
  case c of
    A.ChGuarded (e, p, ni) =>
      let
        val here = check_antiq oenv ctx ni
        val (o1, a1) = walk_expr oenv ctx e
        val (o2, a2) = walk_proc o1 ctx p
      in (o2, here @ a1 @ a2) end
  | A.ChNested p => walk_proc oenv ctx p
  | A.ChSpec (s, c1, ni) =>
      let val here = check_antiq oenv ctx ni
      in scoped oenv (fn oenv =>
           let
             val (o1, a1) = walk_spec oenv ctx s
             val (o2, a2) = walk_choice o1 ctx c1
           in (o2, here @ a1 @ a2) end) end

and walk_option oenv ctx (o_ : pos A.oOption) : oenv * acts =
  case o_ of
    A.OpCases (es, p, ni) =>
      let
        val here = check_antiq oenv ctx ni
        val (o1, a1) = walk_exprs oenv ctx es
        val (o2, a2) = walk_proc o1 ctx p
      in (o2, here @ a1 @ a2) end
  | A.OpElse (p, ni) =>
      let
        val here = check_antiq oenv ctx ni
        val (o1, a1) = walk_proc oenv ctx p
      in (o1, here @ a1) end
  | A.OpSpec (s, o1, ni) =>
      let val here = check_antiq oenv ctx ni
      in scoped oenv (fn oenv =>
           let
             val (oa, a1) = walk_spec oenv ctx s
             val (ob, a2) = walk_option oa ctx o1
           in (ob, here @ a1 @ a2) end) end

and walk_variant oenv ctx (v : pos A.oVariant) : oenv * acts =
  case v of
    A.VaTagged (tag, items, p, ni) =>
      let
        val here = check_antiq oenv ctx ni
        val _ = report_ident_use oenv tag
        val (o1, a1) = walk_input_items oenv ctx items
        val (o2, a2) = walk_proc o1 ctx p
      in (o2, here @ a1 @ a2) end
  | A.VaSpec (s, v1, ni) =>
      let val here = check_antiq oenv ctx ni
      in scoped oenv (fn oenv =>
           let
             val (o1, a1) = walk_spec oenv ctx s
             val (o2, a2) = walk_variant o1 ctx v1
           in (o2, here @ a1 @ a2) end) end

and walk_guard oenv ctx (g : pos A.oGuard) : oenv * acts =
  case g of
    A.GInput (inp, ni) =>
      let
        val here = check_antiq oenv ctx ni
        val (o1, a1) = walk_input oenv ctx inp
      in (o1, here @ a1) end
  | A.GCondInput (e, inp, ni) =>
      let
        val here = check_antiq oenv ctx ni
        val (o1, a1) = walk_expr oenv ctx e
        val (o2, a2) = walk_input o1 ctx inp
      in (o2, here @ a1 @ a2) end
  | A.GCondSkip (e, ni) =>
      let
        val here = check_antiq oenv ctx ni
        val (o1, a1) = walk_expr oenv ctx e
      in (o1, here @ a1) end

and walk_alt oenv ctx (a : pos A.oAlt) : oenv * acts =
  case a of
    A.AlGuarded (g, p, ni) =>
      let
        val here = check_antiq oenv ctx ni
        val (o1, a1) = walk_guard oenv ctx g
        val (o2, a2) = walk_proc o1 ctx p
      in (o2, here @ a1 @ a2) end
  | A.AlCase (eo, ch, vs, ni) =>
      let
        val here = check_antiq oenv ctx ni
        val (o1, a1) =
          (case eo of NONE => (oenv, []) | SOME e => walk_expr oenv ctx e)
        val (o2, a2) = walk_expr o1 ctx (A.EElem ch)
        val (o3, a3) = seq (fn oenv => fn v => walk_variant oenv ctx v) o2 vs
      in (o3, here @ a1 @ a2 @ a3) end
  | A.AlNested p => walk_proc oenv ctx p
  | A.AlSpec (s, a1, ni) =>
      let val here = check_antiq oenv ctx ni
      in scoped oenv (fn oenv =>
           let
             val (o1, x1) = walk_spec oenv ctx s
             val (o2, x2) = walk_alt o1 ctx a1
           in (o2, here @ x1 @ x2) end) end

and walk_placed oenv ctx (pl : pos A.oPlaced) : oenv * acts =
  case pl of
    A.PlProcessor (e, p, ni) =>
      let
        val here = check_antiq oenv ctx ni
        val (o1, a1) = walk_expr oenv ctx e
        val (o2, a2) = walk_proc o1 ctx p
      in (o2, here @ a1 @ a2) end
  | A.PlPar (repl, pls, ni) =>
      let
        val here = check_antiq oenv ctx ni
        val (o1, a1) = walk_opt_repl_then oenv ctx repl
          (fn oenv => seq (fn oenv => fn p => walk_placed oenv ctx p) oenv pls)
      in (o1, here @ a1) end

and walk_vp oenv ctx (vp : pos A.oValueProcess) : oenv * acts =
  case vp of
    A.VPValof (p, es, ni) =>
      let
        val here = check_antiq oenv ctx ni
        val (o1, a1) = walk_proc oenv ctx p
        val (o2, a2) = walk_exprs o1 ctx es
      in (o2, here @ a1 @ a2) end
  | A.VPSpec (s, vp1, ni) =>
      let val here = check_antiq oenv ctx ni
      in scoped oenv (fn oenv =>
           let
             val (o1, a1) = walk_spec oenv ctx s
             val (o2, a2) = walk_vp o1 ctx vp1
           in (o2, here @ a1 @ a2) end) end

(* Walks a specification and *adds* its names to the table (the enclosing
   construct decides when to restore it). Pushes its own "Spec s" frame. *)
and walk_spec oenv ctx (s : pos A.oSpec) : oenv * acts =
  let
    val ctx' = A.Spec s :: ctx
    val here = check_antiq oenv ctx' (A.nodeInfo_of_spec s)
    fun plus (oenv1, acts) = (oenv1, here @ acts)
    fun walk_opt_type oenv NONE = (oenv, [])
      | walk_opt_type oenv (SOME t) = walk_type oenv ctx' t
    fun decl_ids kind oenv ids =
      fold (fn id => fn o_ => register kind o_ id) ids oenv
  in
    case s of
      A.SDecl (t, ids, _) =>
        let val (o1, a1) = walk_type oenv ctx' t
        in plus (decl_ids (kind_of_type t) o1 ids, a1) end
    | A.SAbbrev (to, id, el, _) =>
        let
          val (o1, a1) = walk_opt_type oenv to
          val (o2, a2) = walk_expr o1 ctx' (A.EElem el)
        in plus (register Abbrev o2 id, a1 @ a2) end
    | A.SValAbbrev (to, id, e, _) =>
        let
          val (o1, a1) = walk_opt_type oenv to
          val (o2, a2) = walk_expr o1 ctx' e
        in plus (register Abbrev o2 id, a1 @ a2) end
    | A.SRetypes (t, id, el, _) =>
        let
          val (o1, a1) = walk_type oenv ctx' t
          val (o2, a2) = walk_expr o1 ctx' (A.EElem el)
        in plus (register Abbrev o2 id, a1 @ a2) end
    | A.SValRetypes (t, id, e, _) =>
        let
          val (o1, a1) = walk_type oenv ctx' t
          val (o2, a2) = walk_expr o1 ctx' e
        in plus (register Abbrev o2 id, a1 @ a2) end
    | A.SProtocol (id, p, _) =>
        let val (o1, a1) = walk_protocol oenv ctx' p
        in plus (register Protocol o1 id, a1) end
    | A.SProtocolCase (id, tagged, _) =>
        let
          val (o1, a1) = seq (fn oenv => fn (A.Tagged (tag, sps, ni)) =>
                               let
                                 val th = check_antiq oenv ctx' ni
                                 val (oa, aa) =
                                   seq (fn oenv => fn sp =>
                                        walk_simple_prot oenv ctx' sp) oenv sps
                               in (register Tag oa tag, th @ aa) end)
                             oenv tagged
        in plus (register Protocol o1 id, a1) end
    | A.SProc (id, formals, body, _) =>
        let
          val (o1, a1) = scoped oenv (fn oenv =>
                           let
                             val (oa, aa) = walk_formals oenv ctx' formals
                             val (ob, ab) = walk_proc oa ctx' body
                           in (ob, aa @ ab) end)
        in plus (register Proc o1 id, a1) end
    | A.SFunction (ts, id, formals, vp, _) =>
        let
          val (o0, a0) = seq (fn oenv => fn t => walk_type oenv ctx' t) oenv ts
          val (o1, a1) = scoped o0 (fn oenv =>
                           let
                             val (oa, aa) = walk_formals oenv ctx' formals
                             val (ob, ab) = walk_vp oa ctx' vp
                           in (ob, aa @ ab) end)
        in plus (register Function o1 id, a0 @ a1) end
    | A.SFunctionIs (ts, id, formals, es, _) =>
        let
          val (o0, a0) = seq (fn oenv => fn t => walk_type oenv ctx' t) oenv ts
          val (o1, a1) = scoped o0 (fn oenv =>
                           let
                             val (oa, aa) = walk_formals oenv ctx' formals
                             val (ob, ab) = walk_exprs oa ctx' es
                           in (ob, aa @ ab) end)
        in plus (register Function o1 id, a0 @ a1) end
  end

(* Always pushes its own node. *)
and walk_proc oenv ctx (p : pos A.oProcess) : oenv * acts =
  let
    val ctx' = A.Proc p :: ctx
    val here = check_antiq oenv ctx' (A.nodeInfo_of_process p)
    fun plus (oenv1, acts) = (oenv1, here @ acts)
    fun procs oenv ps = seq (fn oenv => fn q => walk_proc oenv ctx' q) oenv ps
  in
    case p of
      A.PSkip _ => (oenv, here)
    | A.PStop _ => (oenv, here)
    | A.PAssign (lhs, rhs, _) =>
      plus (walk_exprs oenv ctx' (map A.EElem lhs @ rhs))
    | A.PInput (inp, _) => plus (walk_input oenv ctx' inp)
    | A.POutput (ch, items, _) =>
        plus (walk_exprs oenv ctx'
                (A.EElem ch ::
                 maps (fn A.OIExpr e => [e] | A.OICounted (e1, e2) => [e1, e2])
                   items))
    | A.PCaseInput (ch, vs, _) =>
        let
          val (o1, a1) = walk_expr oenv ctx' (A.EElem ch)
          val (o2, a2) = seq (fn oenv => fn v => walk_variant oenv ctx' v) o1 vs
        in plus (o2, a1 @ a2) end
    | A.PSeq (repl, ps, _) =>
      plus (walk_opt_repl_then oenv ctx' repl (fn oenv => procs oenv ps))
    | A.PIf (repl, chs, _) =>
        plus (walk_opt_repl_then oenv ctx' repl
                (fn oenv =>
                 seq (fn oenv => fn c => walk_choice oenv ctx' c) oenv chs))
    | A.PCase (e, opts, _) =>
        let
          val (o1, a1) = walk_expr oenv ctx' e
          val (o2, a2) =
            seq (fn oenv => fn o_ => walk_option oenv ctx' o_) o1 opts
        in plus (o2, a1 @ a2) end
    | A.PWhile (e, q, _) =>
        let
          val (o1, a1) = walk_expr oenv ctx' e
          val (o2, a2) = walk_proc o1 ctx' q
        in plus (o2, a1 @ a2) end
    | A.PPar (_, repl, ps, _) =>
      plus (walk_opt_repl_then oenv ctx' repl (fn oenv => procs oenv ps))
    | A.PAlt (_, repl, alts, _) =>
        plus (walk_opt_repl_then oenv ctx' repl
                (fn oenv =>
                 seq (fn oenv => fn a => walk_alt oenv ctx' a) oenv alts))
    | A.PPlacedPar (repl, pls, _) =>
        plus (walk_opt_repl_then oenv ctx' repl
                (fn oenv =>
                 seq (fn oenv => fn pl => walk_placed oenv ctx' pl) oenv pls))
    | A.PInstance (id, args, _) =>
        (report_ident_use oenv id; plus (walk_exprs oenv ctx' args))
    | A.PSpecP (s, q, _) =>
        let
          val (o1, a1) = scoped oenv (fn oenv =>
                           let
                             val (oa, aa) = walk_spec oenv ctx' s
                             val (ob, ab) = walk_proc oa ctx' q
                           in (ob, aa @ ab) end)
        in plus (o1, a1) end
    | A.PPlace (id, e, q, _) =>
        let
          val _ = report_ident_use oenv id
          val (o1, a1) = walk_expr oenv ctx' e
          val (o2, a2) = walk_proc o1 ctx' q
        in plus (o2, a1 @ a2) end
  end

fun analyse_and_eval0 (root : pos A.root) thy =
  let
    val oenv0 = get (Context.Theory thy)
    (* The bottom frame is always the top-level root itself: the one thing
       every antiquotation can fall back to, so "ctx" is never empty. *)
    val ctx0 = [root]
    fun finish (oenv1, acts) = (Context.theory_map (put oenv1) thy, acts)
  in
    case root of
      A.Id (id as A.Ident (name, _, ni)) =>
        let
          val here = check_antiq oenv0 ctx0 ni
          val _ = report_use oenv0 name (A.pos_of_NodeInfo ni)
        in (thy, here) end
    | A.Expr e => finish (walk_expr oenv0 ctx0 e)
    | A.Proc p => finish (walk_proc oenv0 ctx0 p)
    | A.Spec s => finish (walk_spec oenv0 ctx0 s)
    | A.Specs ss =>
      finish (seq (fn oenv => fn s => walk_spec oenv ctx0 s) oenv0 ss)
  end

fun analyse_and_eval root thy =
  Dispatched_Antiqs.with_fresh (fn () => analyse_and_eval0 root thy)

end
\<close>

subsection\<open>Some Basic Antiquotation Settings\<close>

text\<open>
  The same eight demonstration antiquotations as C11's (\<open>C11_AnaEval.thy\<close>, whose
  notes on each apply unchanged): \<open>probe_oenv\<close>, \<open>probe_ast\<close>, \<open>highlight\<close>,
  \<open>term\<close>, \<open>ML\<close>, \<open>text\<close>, \<open>definition\<close> and \<open>lemma\<close>. They are written in an occam
  comment as \<^verbatim>\<open>-- @term \<open>x + 1 = (2::nat)\<close>\<close> (or \<^verbatim>\<open>--@ term \<open>...\<close>\<close>) and attach to
  the node that begins on the next token; \<^verbatim>\<open>@tag[navi](level)\<close> selects another
  node and an evaluation order exactly as in C11. Handlers are registered under
  their tag in \<open>oenv\<close>'s \<open>occam_antiq\<close> table; nothing here knows occam, only the
  \<open>root\<close> they are handed.
\<close>

declare [[ML_catch_all = true]]

ML\<open>
val OENV = Unsynchronized.ref(OEnv.empty_oenv);
val probe_oenv = let fun probe (oenv, _ , _) (_ : string * Position.T) thy =
                              (OENV := oenv; thy)
                 in  OEnv.store_antiq
                   ("probe_oenv",  OEnv.lift_theory_antiq probe) end

val OCCAM_AST =
  Unsynchronized.ref((Occam2_Ast.Specs []): (Position.T Occam2_Ast.root) )
val probe_ast = let fun probe (_, ast , l) (_ : string * Position.T) thy =
                              (writeln("Level: "^ Int.toString l);
                               writeln("Read : " ^ Occam2_Ast.pp_root ast);
                               OCCAM_AST := ast; thy)
                in  OEnv.store_antiq
                  ("probe_ast",  OEnv.lift_theory_antiq probe) end

val highlight = let fun probe (_, ast , _) (_ : string * Position.T) thy =
                              (Position.report (AnaEval.pos_of_root ast)
                               Markup.intensify;
                               thy)
                in  OEnv.store_antiq
                  ("highlight",  OEnv.lift_theory_antiq probe) end

(* The cartouche body as an "Input.source" with the body's own real position,
   rebuilt from the merged range position the lexer records: see the long note
   on "term_antiq" in C11_AnaEval.thy for why a bare string would lose
   per-symbol positions. *)
fun body_source (body, body_pos) =
  let
    val start_pos = Position.no_range_position body_pos
    val end_pos = Position.symbol_explode body start_pos
  in Input.source true body (start_pos, end_pos) end

(* A genuine HOL term, read against the theory's current context; a malformed
   term is a real Isabelle error positioned in the occam source. The catch-all
   handler is needed because "Syntax.read_term" fails with "Par_Exn", not
   "ERROR". *)
val OCCAM_TERM_PROBE =
  Unsynchronized.ref (Free ("dummy_term_probe", dummyT) : term)
val term_antiq =
  let
    fun probe (_, ast, _) (body, body_pos) thy =
      let
        val ctxt = Proof_Context.init_global thy
        val encoded = Syntax.implode_input (body_source (body, body_pos))
        val t = Syntax.read_term ctxt encoded
          handle exn =>
            if Exn.is_interrupt exn then Exn.reraise exn
            else error ("term antiquotation: " ^ Runtime.exn_message exn ^
                         Position.here (AnaEval.pos_of_root ast))
      in (OCCAM_TERM_PROBE := t; thy) end
  in OEnv.store_antiq ("term", OEnv.lift_theory_antiq probe) end

(* Runs its body as real ML source, so a definition written in an occam
   comment becomes a later-visible ML binding - the one handler that needs
   "Context.generic -> Context.generic" rather than "theory -> theory". *)
val ml_antiq =
  let
    fun probe (_, _, _) (body, body_pos) : Context.generic -> Context.generic =
      ML_Context.exec (fn () =>
        ML_Context.eval_source (ML_Compiler.verbose true ML_Compiler.flags)
          (body_source (body, body_pos)))
      #> Local_Theory.propagate_ml_env
  in OEnv.store_antiq ("ML", probe) end

(* Isabelle's "text" command: the body goes through the real
   "Document_Output.output_document" (inner antiquotations are checked,
   hyperlinked and hoverable); the result is stashed, not typeset, for the
   reason given in the Limitations of the C11 manual. *)
val OCCAM_TEXT_PROBE = Unsynchronized.ref ([] : Latex.text)
val text_antiq =
  let
    fun probe (_, _, _) (body, body_pos) thy =
      let
        val ctxt = Proof_Context.init_global thy
        val source = body_source (body, body_pos)
        val _ = Context_Position.reports ctxt
          (Document_Output.document_reports source)
        val latex =
          Document_Output.output_document ctxt {markdown = true} source
      in (OCCAM_TEXT_PROBE := latex; thy) end
  in OEnv.store_antiq ("text", OEnv.lift_theory_antiq probe) end

(* Isabelle's "definition" command, run on the body via "Parse.read_embedded";
   the new constant is a genuine, later-visible theory constant. *)
val definition_antiq =
  let
    fun probe (_, ast, _) (body, body_pos) thy =
      let
        val ctxt = Proof_Context.init_global thy
        val source = body_source (body, body_pos)
        val keywords = Keyword.no_major_keywords (Thy_Header.get_keywords' ctxt)
        val parser =
          Scan.option
            Parse_Spec.constdecl -- (Parse_Spec.opt_thm_name
                                     ":" -- Parse.prop) --
            Parse_Spec.if_assumes -- Parse.for_fixes
        val (((decl, spec), prems), params) =
          Parse.read_embedded ctxt keywords parser source
          handle exn =>
            if Exn.is_interrupt exn then Exn.reraise exn
            else error ("definition antiquotation: " ^ Runtime.exn_message exn ^
                         Position.here (AnaEval.pos_of_root ast))
        val lthy' =
          #2 (Specification.definition_cmd {verbose = false} decl params prems
              spec
                (Named_Target.theory_init thy))
      in Local_Theory.exit_global lthy' end
  in OEnv.store_antiq ("definition", OEnv.lift_theory_antiq probe) end

(* A statement plus one terminal "by" proof, actually proved - proof-carrying
   code: e.g. a property of a VAL abbreviation's value, discharged right where
   the occam text that motivates it lives. *)
val lemma_antiq =
  let
    val short_statement =
      Parse_Spec.statement -- Parse_Spec.if_statement -- Parse.for_fixes
        >> (fn ((shows, assumes), fixes) =>
          (Binding.empty_atts, [Element.Fixes fixes, Element.Assumes assumes],
           Element.Shows shows))
    val parser =
      short_statement -- (Parse.$$$ "by" |-- Method.parse -- Scan.option
                          Method.parse)
    fun probe (_, ast, _) (body, body_pos) thy =
      let
        val ctxt = Proof_Context.init_global thy
        val source = body_source (body, body_pos)
        val keywords = Keyword.no_major_keywords (Thy_Header.get_keywords' ctxt)
        fun fail exn =
          if Exn.is_interrupt exn then Exn.reraise exn
          else error ("lemma antiquotation: " ^ Runtime.exn_message exn ^
                       Position.here (AnaEval.pos_of_root ast))
        val ((binding, elems, concl), (m1, m2)) =
          Parse.read_embedded ctxt keywords parser source handle exn => fail exn
        val lthy' =
          (Specification.theorem_cmd {verbose = false, long = false, kind =
                                      Thm.theoremK}
             NONE (K I) binding [] elems concl
             (Named_Target.theory_init thy)
           |> tap (fn _ =>
                   (Method.report m1; Option.map Method.report m2 |> ignore))
           |> Proof.global_terminal_proof (m1, m2))
          handle exn => fail exn
      in Local_Theory.exit_global lthy' end
  in OEnv.store_antiq ("lemma", OEnv.lift_theory_antiq probe) end
\<close>

setup\<open>probe_oenv\<close>
setup\<open>probe_ast\<close>
setup\<open>highlight\<close>
setup\<open>term_antiq\<close>
setup\<open>text_antiq\<close>
setup\<open>ml_antiq\<close>
setup\<open>definition_antiq\<close>
setup\<open>lemma_antiq\<close>

end
