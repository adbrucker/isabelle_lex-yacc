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


theory AdaSpark_AnaEval
  imports "AdaSpark_Env"
begin

section\<open>Analyse and Eval\<close>

text\<open>
  \<open>analyse_and_eval\<close> is the AdaSpark counterpart of the passes of the same name
  of the other front-ends (\<^verbatim>\<open>C11_AnaEval.thy\<close>, \<^verbatim>\<open>Occam2_AnaEval.thy\<close>,
  \<^verbatim>\<open>Scala3_AnaEval.thy\<close>, \<^verbatim>\<open>MicroRust_AnaEval.thy\<close>, whose long explanations apply
  here and are not repeated): a single, purely functional, scoped walk over a
  parsed \<open>root\<close>, threading \<open>aenv\<close> through the descent, collecting every
  antiquotation action paired with its \<open>level\<close> instead of applying it, and
  hyperlinking every name use to its declaration. What is specific to Ada:

  \<^item> \<^bold>\<open>One name space, case insensitive.\<close> An object, a type, a subprogram, a
    package, an exception and an enumeration literal are all names of one table,
    keyed by the lower-case spelling. A declaration or a use is reported with
    its own spelling.
  \<^item> \<^bold>\<open>Sequential visibility.\<close> A declaration is visible after its own
    declaration: an object's initial value does not see the object, but a type
    sees itself (access types and records are routinely recursive), and a
    subprogram sees itself (recursion). The body of a subprogram whose
    specification is in the same declarative region is hyperlinked to that
    specification rather than declared anew.
  \<^item> \<^bold>\<open>Scoping.\<close> A subprogram (parameters, then aspects, then the declarative
    part, then the statements and handlers), a package, a block, a loop with an
    iteration scheme, a quantified expression and the discriminants of a type
    are scopes; a scope simply does not hand its extension back. The
    enumeration literals of a type are declared in the enclosing scope.
  \<^item> \<^bold>\<open>Packages and selected names.\<close> The entities a package \<open>P\<close> declares are
    entered twice: under their own name, in the package's scope, and under the
    qualified name \<open>p.x\<close>, which survives it. A selected name \<open>P.X\<close> hyperlinks
    \<open>P\<close> and, if \<open>p.x\<close> is known, \<open>X\<close>. The body of a package re-opens the scope of
    its specification (the names \<open>p.x\<close> become visible as \<open>x\<close>), and so does a
    \<open>use P;\<close> clause, which makes the names of a package directly visible.
  \<^item> \<^bold>\<open>Names that resolve nowhere are not marked.\<close> A name very often comes from a
    \<open>with\<close>ed unit, a predefined package or a predefined attribute, none of which
    this pass sees; underlining all of them would drown the useful markup.
    Selected components (\<open>R.F\<close>) and attributes are not resolved either (that
    needs types), nor are the names of formal parameters in a call \<open>F (X => 1)\<close>.
    In an aggregate, however, the choices of a named association \<^emph>\<open>are\<close>
    expressions, as the dependency aspects of SPARK (\<open>Depends => (Y => X)\<close>,
    \<open>Global => (Input => V)\<close>) need.
  \<^item> \<^bold>\<open>The compilation file\<close> (\<open>Crate\<close>) is the one root whose names persist: after
    \<open>adaspark\<close> has analysed a file, the names its units declare stay in \<open>aenv\<close>
    for the following ones; a \<open>use\<close> clause is local to its unit.
  \<^item> \<^bold>\<open>Closest context and navigation\<close> as in the other front-ends: expressions,
    subtype indications (\<open>Type\<close>), statements and declarations push their own
    node (\<open>Expr\<close>, \<open>Type\<close>, \<open>Stmt\<close>, \<open>Decl\<close>); everything else (parameters,
    components, aspects, associations, choices, handlers, \<dots>) uses \<open>hd ctx\<close>. The
    children of a node are, in source order, its sub-expressions, subtype
    indications, statements and declarations.

\<close>
ML\<open>
structure AnaEval = struct

structure A = AdaSpark_Ast
open AEnv

type acts = (int * (Context.generic -> Context.generic)) list

fun names_of (mk {names, ...} : aenv) = names

fun set_names names' (mk {names = _, ada_antiq, units}) =
  mk {names = names', ada_antiq = ada_antiq, units = units}

(* Ada is case insensitive: the table is keyed by the lower-case name. *)
fun lc s = String.map Char.toLower s

(* The position a "root" itself spans: what a "type_antiq_fun" sees as its own
   "current term". A source file has no single span. *)
fun pos_of_root (A.Id id) = A.pos_of_ident id
  | pos_of_root (A.Expr e) = A.pos_of_expr e
  | pos_of_root (A.Type t) = A.pos_of_sub t
  | pos_of_root (A.Stmt s) = A.pos_of_stmt s
  | pos_of_root (A.Decl d) = A.pos_of_decl d
  | pos_of_root (A.Body (s :: _)) = A.pos_of_stmt s
  | pos_of_root (A.Body []) = Position.none
  | pos_of_root (A.Crate _) = Position.none

(* Exactly-once dispatch of every physical antiquotation, whatever number of AST
   nodes share its leftmost source position - the same design as in the other
   front-ends. The set of comments already dispatched belongs to one walk
   ("analyse_and_eval" installs a fresh one for its dynamic extent) and is kept
   per thread, so two walks running at the same time cannot see each other's. *)
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
  | category (A.Type _)  = 2
  | category (A.Stmt _)  = 3
  | category (A.Decl _)  = 4
  | category (A.Body _)  = 5
  | category (A.Crate _) = 6

fun run_length (ctx as top :: _) =
      let
        val cat = category top
        fun count (x :: xs) = if category x = cat then 1 + count xs else 0
          | count [] = 0
      in count ctx end

(* Resolves the "(u|U)*" prefix of a navigation string against "ctx",
   returning the unconsumed "(r|d)*" suffix together with the resulting
   stack. The four rules are those of the other front-ends:

   \<^item> Rule 1: a lone, final "u" is a no-op.
   \<^item> Rule 2: a non-final "u" pops exactly one frame, unless "ctx" is a
     singleton, in which case it is a no-op.
   \<^item> Rule 3: "U" on a same-category run of length > 1 collapses the run down
     to its single outermost member and continues; it does not also pop that
     member.
   \<^item> Rule 4: "U" on a run of length 1 is an ordinary, non-final "u". *)

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

(* The ordered list of children "r"/"d" may navigate into (see the top-of-theory
   note): sub-expressions, subtype indications, statements and declarations in
   source order; nodes without a "root" counterpart (associations, choices,
   parameters, components, aspects, handlers, ...) are flattened into their
   parent's list or dropped. *)
fun exprs es = map A.Expr es
fun opt_expr eo = (case eo of SOME e => [A.Expr e] | NONE => [])

fun choice_children ch = (case ch of
    A.ChExpr e => [A.Expr e]
  | A.ChRange (l, h, _) => [A.Expr l, A.Expr h]
  | A.ChOthers _ => [])

fun assoc_children a = (case a of
    A.APos e => [A.Expr e]
  | A.ARange (l, h, _) => [A.Expr l, A.Expr h]
  | A.ANamed (chs, e, _) => maps choice_children chs @ [A.Expr e])

fun range_children ro = (case ro of
    SOME (l, h) => [A.Expr l, A.Expr h]
  | NONE => [])

fun sub_children (A.Sub (_, e, ro, _)) = A.Expr e :: range_children ro

fun iter_children it = (case it of
    A.IterIn (_, A.DRRange (l, h, _)) => [A.Expr l, A.Expr h]
  | A.IterIn (_, A.DRSub s) => [A.Type s]
  | A.IterOf (_, e) => [A.Expr e])

fun aspect_children (A.Aspect (_, _, eo, _)) = opt_expr eo

fun idx_children ix = (case ix of
    A.IdxRange (l, h, _) => [A.Expr l, A.Expr h]
  | A.IdxSub e => [A.Expr e]
  | A.IdxUnconstrained (e, _) => [A.Expr e])

fun param_children (A.Param (_, _, s, eo, _)) = A.Type s :: opt_expr eo

fun spec_children (A.Spec (_, _, _, ps, ret, _)) =
  maps param_children ps @ (case ret of SOME s => [A.Type s] | NONE => [])

fun component_children (A.Comp (_, _, s, eo, _)) = A.Type s :: opt_expr eo

fun recdef_children rd = (case rd of
    A.RecNull => []
  | A.RecComps (cs, vp) =>
      maps component_children cs
      @ (case vp of
           NONE => []
         | SOME (A.VariantPart (_, alts, _)) =>
             maps (fn (chs, r) => maps choice_children chs @ recdef_children r)
               alts))

fun typedef_children td = (case td of
    A.TEnum _ => []
  | A.TRange (l, h) => [A.Expr l, A.Expr h]
  | A.TMod e => [A.Expr e]
  | A.TDigits (e, ro) => A.Expr e :: range_children ro
  | A.TDelta (e, ro) => A.Expr e :: range_children ro
  | A.TArray (ixs, _, s) => maps idx_children ixs @ [A.Type s]
  | A.TRecord (_, _, _, rd) => recdef_children rd
  | A.TDerived (_, _, s, ext) =>
      A.Type s :: (case ext of A.ExtRecord rd => recdef_children rd | _ => [])
  | A.TPrivate _ => []
  | A.TAccess (_, _, s) => [A.Type s])

fun objdef_children od = (case od of
    A.OSub s => [A.Type s]
  | A.OArray (ixs, _, s) => maps idx_children ixs @ [A.Type s])

fun children_of_expr e = (case e of
    A.EId _ => [] | A.EInt _ => [] | A.EReal _ => [] | A.EChar _ => []
  | A.EStr _ => [] | A.ENull _ => []
  | A.ESel (e1, _, _) => [A.Expr e1]
  | A.EDeref (e1, _) => [A.Expr e1]
  | A.EApply (f, as1, _) => A.Expr f :: maps assoc_children as1
  | A.EAttr (e1, _, _) => [A.Expr e1]
  | A.EQual (e1, as1, _) => A.Expr e1 :: maps assoc_children as1
  | A.EUn (_, e1, _) => [A.Expr e1]
  | A.EBin (_, a, b, _) => [A.Expr a, A.Expr b]
  | A.EIn (_, e1, chs, _) => A.Expr e1 :: maps choice_children chs
  | A.EParen (e1, _) => [A.Expr e1]
  | A.EAgg (as1, _) => maps assoc_children as1
  | A.EExtAgg (e1, as1, _) => A.Expr e1 :: maps assoc_children as1
  | A.EDeltaAgg (e1, as1, _) => A.Expr e1 :: maps assoc_children as1
  | A.ENew (e1, _) => [A.Expr e1]
  | A.EIf (conds, els, _) =>
      maps (fn (c, a) => [A.Expr c, A.Expr a]) conds @ opt_expr els
  | A.ECase (e1, alts, _) =>
      A.Expr e1 :: maps (fn (chs, a) => maps choice_children chs @ [A.Expr a])
                     alts
  | A.EQuant (_, _, it, p, _) => iter_children it @ [A.Expr p])

fun handler_children (A.Handler (chs, stmts, _)) =
  maps choice_children chs @ map A.Stmt stmts

fun children_of_stmt s = (case s of
    A.SNull _ => []
  | A.SAssign (a, b, _) => [A.Expr a, A.Expr b]
  | A.SCall (e, _) => [A.Expr e]
  | A.SIf (conds, els, _) =>
      maps (fn (c, ss) => A.Expr c :: map A.Stmt ss) conds
      @ (case els of SOME ss => map A.Stmt ss | NONE => [])
  | A.SCase (e, alts, _) =>
      A.Expr e :: maps
        (fn (chs, ss) => maps choice_children chs @ map A.Stmt ss)
                    alts
  | A.SLoop (_, sch, ss, _) =>
      (case sch of
         A.LoopPlain => []
       | A.LoopWhile c => [A.Expr c]
       | A.LoopFor (_, it) => iter_children it)
      @ map A.Stmt ss
  | A.SBlock (_, ds, ss, hs, _) =>
      map A.Decl ds @ map A.Stmt ss @ maps handler_children hs
  | A.SExit (l, c, _) => opt_expr l @ opt_expr c
  | A.SReturn (eo, _) => opt_expr eo
  | A.SRaise (e, m, _) => opt_expr e @ opt_expr m
  | A.SPragma (_, as1, _) => maps assoc_children as1)

fun children_of_decl d = (case d of
    A.DObject (_, _, _, od, eo, asps, _) =>
      objdef_children od @ opt_expr eo @ maps aspect_children asps
  | A.DNumber (_, e, _) => [A.Expr e]
  | A.DException _ => []
  | A.DType (_, ps, td, asps, _) =>
      maps param_children ps @ typedef_children td @ maps aspect_children asps
  | A.DIncomplete _ => []
  | A.DSubtype (_, s, asps, _) => A.Type s :: maps aspect_children asps
  | A.DSpec (sp, _, asps, _) => spec_children sp @ maps aspect_children asps
  | A.DNullProc (sp, asps, _) => spec_children sp @ maps aspect_children asps
  | A.DExprFun (sp, e, asps, _) =>
      spec_children sp @ [A.Expr e] @ maps aspect_children asps
  | A.DBody (sp, asps, ds, ss, hs, _) =>
      spec_children sp @ maps aspect_children asps @ map A.Decl ds
      @ map A.Stmt ss @ maps handler_children hs
  | A.DPackage (n, asps, vis, priv, _) =>
      A.Expr n :: maps aspect_children asps @ map A.Decl vis @ map A.Decl priv
  | A.DPackageBody (n, asps, ds, body, _) =>
      A.Expr n :: maps aspect_children asps @ map A.Decl ds
      @ (case body of
           NONE => []
         | SOME (ss, hs) => map A.Stmt ss @ maps handler_children hs)
  | A.DUse (_, es, _) => exprs es
  | A.DPragma (_, as1, _) => maps assoc_children as1
  | A.DAttrDef (a, b, _) => [A.Expr a, A.Expr b])

fun children_of _ (A.Expr e) = children_of_expr e
  | children_of _ (A.Type s) = sub_children s
  | children_of _ (A.Stmt s) = children_of_stmt s
  | children_of _ (A.Decl d) = children_of_decl d
  | children_of _ (A.Body ss) = map A.Stmt ss
  | children_of _ (A.Crate us) = map (fn A.Unit (_, d, _) => A.Decl d) us
  | children_of antiq_pos (A.Id _) =
      error ("select_ast: an identifier is a leaf, no \"r\"/\"d\" children"
             ^ Position.here antiq_pos)

(* Resolves the "(r|d)*" suffix against a single "node" (the result of
   "select_u"'s ascent phase): "r" advances a 1-based cursor rightward among
   "children_of node"; "d" descends into the child the cursor currently
   points at (cursor 1, i.e. "d" alone, if no "r" preceded it) and continues
   processing the remaining navigation string against *that* child. No
   wrapping/saturation - a cursor beyond the children list's length is a hard
   "error", and a "d" with no children to descend into likewise.

   Every "error" here reports "antiq_pos" - the antiquotation's own tag
   position, which is the closest thing available to "where the string was
   written" and what a user actually needs to jump to. *)
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
      error ("select_ast: navigation string ends with a dangling \"r\", " ^
             "expected a final \"d\"" ^ Position.here antiq_pos)

(* Maps an antiquotation's own "navi list" together with the
   closest-surrounding-context stack to the single concrete AST node the
   antiquotation refers to: first the "(u|U)*" prefix against the whole stack
   ("select_u"), then the "(r|d)*" suffix against whatever that leaves on top
   ("select_rd"). An empty navi list is the identity. *)
fun select_ast antiq_pos navi ctx =
  let val (rd, ctx') = select_u (navi, ctx)
  in select_rd (antiq_pos, rd, hd ctx') end

(* The shared antiquotation-dispatch helper: looks up every "Antiquotation" in
   "ni"'s comment list by tag in "aenv"'s "ada_antiq", instantiates it with
   (aenv, select_ast tag_pos navi ctx, level), and pairs the resulting
   "Context.generic -> Context.generic" with its level - "select_ast" (and so
   "children_of", which can "error") is only forced when an "Antiquotation"
   genuinely needs it. "tag_pos" is passed through purely so that a navigation
   error is reported at "@tag[navi] ..." itself. An "Antiquotation" already
   dispatched earlier in this same walk (see "Dispatched_Antiqs") is silently
   skipped the second time some other node sharing its position reaches it:
   the walk reaches the outermost of any nodes tied at one position first,
   since every "walk_*" checks its own antiquotations before recursing. The
   handler receives "(body, body_pos)" and the *resolved* AST node, never the
   raw navi list. *)
fun check_antiq aenv (ctx : pos A.root list) (ni : pos A.nodeInfo)
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
                let val mk {ada_antiq, ...} = aenv in
                  case Symtab.lookup ada_antiq tag of
                    NONE =>
                      error ("analyse_and_eval: no antiquotation handler " ^
                             "registered for tag " ^ quote tag)
                  | SOME antiq_fun =>
                      (Dispatched_Antiqs.mark c;
                       SOME (level,
                             antiq_fun
                               (aenv, select_ast tag_pos navi ctx, level)
                                 (body, body_pos)))
                end
          | A.Raw_txt _ => NONE)
        cs


(* The full-token range a name spans, starting at "pos" (an identifier's
   "nodeInfo" carries a bare point, which would make an entity report claim a
   single character). *)
fun name_range (name, pos) =
  Position.range_position
    (Position.range (pos, Position.symbol_explode name pos))

fun report_decl kind name decl_pos =
  let val range_pos = name_range (name, decl_pos)
  in Position.report range_pos (Position.entity_markup kind (name, range_pos))
    end

(* Hyperlinks a use of "name" to the declaration registered under "key", if
   there is one; nothing is reported otherwise (see the top-of-theory note). *)
fun use_key aenv key name use_pos =
  (case Symtab.lookup (names_of aenv) key of
     NONE => ()
   | SOME k =>
       Position.report (name_range (name, use_pos))
         (Position.entity_markup (describe_kind k)
          (name, name_range (name, pos_of_kind k))))

fun use_name aenv (A.Ident (name, _, ni)) =
  use_key aenv (lc name) name (A.pos_of_NodeInfo ni)

fun declare kind aenv key =
  set_names (Symtab.update (key, kind) (names_of aenv)) aenv

(* Declares an identifier (reporting its declaration site); "qual" is the
   qualifier of the package whose visible declarations are being walked, under
   which the name is entered a second time. *)
fun reg_q qual mk_kind aenv (A.Ident (name, _, ni)) =
  let
    val pos = A.pos_of_NodeInfo ni
    val kind = mk_kind pos
    val _ = report_decl (describe_kind kind) name pos
    val aenv1 = declare kind aenv (lc name)
  in
    (case qual of
       NONE => aenv1
     | SOME q => declare kind aenv1 (q ^ "." ^ lc name))
  end

fun reg mk_kind aenv id = reg_q NONE mk_kind aenv id

fun decl_only mk_kind (A.Ident (name, _, ni)) =
  let val pos = A.pos_of_NodeInfo ni
  in report_decl (describe_kind (mk_kind pos)) name pos end

(* Runs "f" in a nested scope: the table is restored on exit. *)
fun scoped aenv f =
  let
    val names = names_of aenv
    val (aenv1, acts) = f aenv
  in (set_names names aenv1, acts) end

fun seq (f : aenv -> 'a -> aenv * acts) aenv xs =
  fold (fn x => fn (e, acc) => let val (e', a) = f e x in (e', acc @ a) end) xs
    (aenv, [])

fun optl f x = (case x of NONE => [] | SOME y => f y)

(* A compact wrapper for the antiquotations a node carries (its "nodeInfo"). *)
fun chk aenv ctx ni = check_antiq aenv ctx ni

(* The lower-case dotted name an expression spells, if it is a (selected) name
   made of identifiers only. *)
fun dotted e = (case e of
    A.EId (A.Ident (n, _, _)) => SOME (lc n)
  | A.ESel (e1, A.Ident (n, _, _), _) =>
      (case dotted e1 of SOME p => SOME (p ^ "." ^ lc n) | NONE => NONE)
  | _ => NONE)

(* The identifier a package name ends in. *)
fun last_ident e = (case e of
    A.EId id => SOME id
  | A.ESel (_, id, _) => SOME id
  | _ => NONE)

(* Makes the entities of the package "key" directly visible (a "use" clause, the
   body of a package): every "key.rest" is entered as "rest". Returns the new
   environment and the names of the subprograms it made visible. *)
fun open_package key aenv =
  let
    val pre = key ^ "."
    val names = names_of aenv
    fun add (k, v) (tab, subs) =
      if String.isPrefix pre k then
        let val rest = String.extract (k, size pre, NONE)
        in (Symtab.update (rest, v) tab,
            (case v of Proc _ => rest :: subs | Func _ => rest :: subs
                     | _ => subs)) end
      else (tab, subs)
    val (names', subs) = Symtab.fold add names (names, [])
  in (set_names names' aenv, subs) end

(* Completes a subprogram's registration: a body (or expression function) whose
   specification is in the same declarative region ("specs") is hyperlinked to
   it, any other subprogram is declared. *)
fun reg_subprogram qual aenv specs is_decl (A.Spec (_, is_func, id, _, _, _)) =
  let
    val A.Ident (name, _, ni) = id
    val lname = lc name
    val mk_kind = if is_func then Func else Proc
  in
    if not is_decl andalso member (op =) specs lname
       andalso Symtab.defined (names_of aenv) lname
    then (use_key aenv lname name (A.pos_of_NodeInfo ni); (aenv, specs))
    else (reg_q qual mk_kind aenv id,
          if is_decl then lname :: specs else specs)
  end

fun walk_sub senv ctx (s as A.Sub (_, e, ro, ni)) : acts =
  let
    val ctx' = A.Type s :: ctx
    val here = chk senv ctx' ni
  in
    here @ walk_expr senv ctx' e
    @ optl (fn (l, h) => walk_expr senv ctx' l @ walk_expr senv ctx' h) ro
  end

(* A choice. A lone identifier is resolved as an expression if "rc" holds - in a
   named association of a call it is a formal parameter's name instead. *)
and walk_choice rc senv ctx ch : acts =
  (case ch of
     A.ChExpr (e as A.EId _) =>
       if rc then walk_expr senv ctx e
       else chk senv (A.Expr e :: ctx) (A.nodeInfo_of_expr e)
   | A.ChExpr e => walk_expr senv ctx e
   | A.ChRange (l, h, ni) =>
       chk senv ctx ni @ walk_expr senv ctx l @ walk_expr senv ctx h
   | A.ChOthers ni => chk senv ctx ni)

and walk_assoc rc senv ctx a : acts =
  (case a of
     A.APos e => walk_expr senv ctx e
   | A.ARange (l, h, ni) =>
       chk senv ctx ni @ walk_expr senv ctx l @ walk_expr senv ctx h
   | A.ANamed (chs, e, ni) =>
       chk senv ctx ni @ maps (walk_choice rc senv ctx) chs
       @ walk_expr senv ctx e)

(* The iteration scheme "for X in .." / "for X of .." of a loop or a quantified
   expression: its range or array is seen outside of the variable's scope. *)
and walk_iter senv ctx it : acts =
  (case it of
     A.IterIn (_, A.DRRange (l, h, ni)) =>
       chk senv ctx ni @ walk_expr senv ctx l @ walk_expr senv ctx h
   | A.IterIn (_, A.DRSub s) => walk_sub senv ctx s
   | A.IterOf (_, e) => walk_expr senv ctx e)

and walk_expr senv ctx (e : pos A.aExpr) : acts =
  let
    val ctx' = A.Expr e :: ctx
    val here = chk senv ctx' (A.nodeInfo_of_expr e)
    val w = walk_expr senv ctx'
  in
    here @
    (case e of
       A.EId id => (use_name senv id; [])
     | A.EInt _ => []
     | A.EReal _ => []
     | A.EChar _ => []
     | A.EStr _ => []
     | A.ENull _ => []
     | A.ESel (e1, A.Ident (name, _, ni), _) =>
         let val a1 = w e1
         in
           (case dotted e of
              SOME key => use_key senv key name (A.pos_of_NodeInfo ni)
            | NONE => ());
           a1
         end
     | A.EDeref (e1, _) => w e1
     | A.EApply (f, as1, _) => w f @ maps (walk_assoc false senv ctx') as1
     | A.EAttr (e1, _, _) => w e1
     | A.EQual (e1, as1, _) => w e1 @ maps (walk_assoc false senv ctx') as1
     | A.EUn (_, e1, _) => w e1
     | A.EBin (_, a, b, _) => w a @ w b
     | A.EIn (_, e1, chs, _) => w e1 @ maps (walk_choice true senv ctx') chs
     | A.EParen (e1, _) => w e1
     | A.EAgg (as1, _) => maps (walk_assoc true senv ctx') as1
     | A.EExtAgg (e1, as1, _) => w e1 @ maps (walk_assoc true senv ctx') as1
     | A.EDeltaAgg (e1, as1, _) => w e1 @ maps (walk_assoc true senv ctx') as1
     | A.ENew (e1, _) => w e1
     | A.EIf (conds, els, _) =>
         maps (fn (c, a) => w c @ w a) conds @ optl w els
     | A.ECase (e1, alts, _) =>
         w e1 @ maps (fn (chs, a) =>
                        maps (walk_choice true senv ctx') chs @ w a) alts
     | A.EQuant (_, id, it, p, _) =>
         let
           val a1 = walk_iter senv ctx' it
           val (_, a2) = scoped senv (fn s =>
             let val s1 = reg Obj s id in (s1, walk_expr s1 ctx' p) end)
         in a1 @ a2 end)
  end

and walk_aspect senv ctx (A.Aspect (_, _, eo, ni)) : acts =
  chk senv ctx ni @ optl (walk_expr senv ctx) eo

and walk_aspects senv ctx asps : acts = maps (walk_aspect senv ctx) asps

and walk_idx senv ctx ix : acts =
  (case ix of
     A.IdxRange (l, h, ni) =>
       chk senv ctx ni @ walk_expr senv ctx l @ walk_expr senv ctx h
   | A.IdxSub e => walk_expr senv ctx e
   | A.IdxUnconstrained (e, ni) => chk senv ctx ni @ walk_expr senv ctx e)

and walk_range senv ctx ro : acts =
  optl (fn (l, h) => walk_expr senv ctx l @ walk_expr senv ctx h) ro

and walk_objdef senv ctx od : acts =
  (case od of
     A.OSub s => walk_sub senv ctx s
   | A.OArray (ixs, _, s) =>
       maps (walk_idx senv ctx) ixs @ walk_sub senv ctx s)

(* Components are declared (their declaration sites are reported) but not
   entered into the environment: they are visible only as selectors, which this
   pass does not resolve. A discriminant used by a variant part is a use. *)
and walk_recdef senv ctx rd : acts =
  (case rd of
     A.RecNull => []
   | A.RecComps (cs, vp) =>
       maps (walk_component senv ctx) cs
       @ optl (walk_variant_part senv ctx) vp)

and walk_component senv ctx (A.Comp (ids, _, s, eo, ni)) : acts =
  let
    val a1 = chk senv ctx ni
    val a2 = walk_sub senv ctx s
    val a3 = optl (walk_expr senv ctx) eo
    val _ = List.app (decl_only Comp) ids
  in a1 @ a2 @ a3 end

and walk_variant_part senv ctx (A.VariantPart (disc, alts, ni)) : acts =
  let
    val a1 = chk senv ctx ni
    val _ = use_name senv disc
  in
    a1 @ maps (fn (chs, rd) =>
                 maps (walk_choice true senv ctx) chs
                 @ walk_recdef senv ctx rd) alts
  end

and walk_typedef senv ctx td : acts =
  (case td of
     A.TEnum _ => []
   | A.TRange (l, h) => walk_expr senv ctx l @ walk_expr senv ctx h
   | A.TMod e => walk_expr senv ctx e
   | A.TDigits (e, ro) => walk_expr senv ctx e @ walk_range senv ctx ro
   | A.TDelta (e, ro) => walk_expr senv ctx e @ walk_range senv ctx ro
   | A.TArray (ixs, _, s) =>
       maps (walk_idx senv ctx) ixs @ walk_sub senv ctx s
   | A.TRecord (_, _, _, rd) => walk_recdef senv ctx rd
   | A.TDerived (_, _, s, ext) =>
       walk_sub senv ctx s
       @ (case ext of A.ExtRecord rd => walk_recdef senv ctx rd | _ => [])
   | A.TPrivate _ => []
   | A.TAccess (_, _, s) => walk_sub senv ctx s)

(* Parameters (or discriminants) are declared one after the other, each seeing
   its predecessors; the returned environment has them all. *)
and walk_params mk_kind senv ctx params : aenv * acts =
  seq (fn s => fn (A.Param (ids, _, sub, def, ni)) =>
         let
           val a0 = chk s ctx ni
           val a1 = walk_sub s ctx sub
           val a2 = optl (walk_expr s ctx) def
           val s1 = fold (fn id => fn e => reg mk_kind e id) ids s
         in (s1, a0 @ a1 @ a2) end) senv params

(* The environment returned sees the parameters: the caller opens the scope. *)
and walk_spec senv ctx (A.Spec (_, _, _, params, ret, ni)) : aenv * acts =
  let
    val a0 = chk senv ctx ni
    val (s1, a1) = walk_params Param senv ctx params
    val a2 = optl (walk_sub s1 ctx) ret
  in (s1, a0 @ a1 @ a2) end

and walk_handler senv ctx (A.Handler (chs, stmts, ni)) : acts =
  chk senv ctx ni @ maps (walk_choice true senv ctx) chs
  @ walk_stmts senv ctx stmts

and walk_stmts senv ctx stmts : acts = maps (walk_stmt senv ctx) stmts

and walk_stmt senv ctx (s : pos A.aStmt) : acts =
  let
    val ctx' = A.Stmt s :: ctx
    val here = chk senv ctx' (A.nodeInfo_of_stmt s)
    val we = walk_expr senv ctx'
    val ws = walk_stmts senv ctx'
  in
    here @
    (case s of
       A.SNull _ => []
     | A.SAssign (a, b, _) => we a @ we b
     | A.SCall (e, _) => we e
     | A.SIf (conds, els, _) =>
         maps (fn (c, ss) => we c @ ws ss) conds @ optl ws els
     | A.SCase (e, alts, _) =>
         we e @ maps (fn (chs, ss) =>
                        maps (walk_choice true senv ctx') chs @ ws ss) alts
     | A.SLoop (label, sch, body, _) =>
         let
           val (a1, loop_var) =
             (case sch of
                A.LoopPlain => ([], NONE)
              | A.LoopWhile c => (we c, NONE)
              | A.LoopFor (id, it) => (walk_iter senv ctx' it, SOME id))
           val (_, a2) = scoped senv (fn s1 =>
             let
               val s2 = (case label of SOME l => reg Label s1 l | NONE => s1)
               val s3 = (case loop_var of SOME v => reg Obj s2 v | NONE => s2)
             in (s3, walk_stmts s3 ctx' body) end)
         in a1 @ a2 end
     | A.SBlock (label, decls, stmts, handlers, _) =>
         #2 (scoped senv (fn s1 =>
           let
             val s2 = (case label of SOME l => reg Label s1 l | NONE => s1)
             val (s3, _, a1) = walk_decls NONE s2 ctx' [] decls
             val a2 = walk_stmts s3 ctx' stmts
             val a3 = maps (walk_handler s3 ctx') handlers
           in (s3, a1 @ a2 @ a3) end))
     | A.SExit (l, c, _) => optl we l @ optl we c
     | A.SReturn (eo, _) => optl we eo
     | A.SRaise (e, m, _) => optl we e @ optl we m
     | A.SPragma (_, as1, _) => maps (walk_assoc false senv ctx') as1)
  end

(* The declarations of a declarative region, one after the other; "specs" are
   the subprograms whose specification has been seen, "qual" is the qualified
   name of the package whose declarations these are. *)
and walk_decls qual senv ctx specs decls : aenv * string list * acts =
  fold (fn d => fn (s, sp, acc) =>
          let val (s', sp', a) = walk_decl qual s ctx sp d
          in (s', sp', acc @ a) end) decls (senv, specs, [])

and walk_decl qual senv ctx specs (d : pos A.aDecl)
    : aenv * string list * acts =
  let
    val ctx' = A.Decl d :: ctx
    val here = chk senv ctx' (A.nodeInfo_of_decl d)
    val we = walk_expr senv ctx'
    val wa = walk_aspects
    fun ret (s, sp, a) = (s, sp, here @ a)
  in
    ret
    (case d of
       A.DObject (ids, _, const, od, eo, asps, _) =>
         let
           val a1 = walk_objdef senv ctx' od
           val a2 = optl we eo
           val kind = if const then Const else Obj
           val s1 = fold (fn id => fn e => reg_q qual kind e id) ids senv
         in (s1, specs, a1 @ a2 @ wa s1 ctx' asps) end
     | A.DNumber (ids, e, _) =>
         let
           val a1 = we e
           val s1 = fold (fn id => fn e => reg_q qual Const e id) ids senv
         in (s1, specs, a1) end
     | A.DException (ids, _) =>
         (fold (fn id => fn e => reg_q qual Exn e id) ids senv, specs, [])
     | A.DType (id, discrs, td, asps, _) =>
         let
           val s1 = reg_q qual Typ senv id
           val s2 = (case td of
                       A.TEnum lits =>
                         fold (fn l => fn e => reg_q qual Lit e l) lits s1
                     | _ => s1)
           val (_, a1) = scoped s2 (fn s =>
             let
               val (s3, a2) = walk_params Comp s ctx' discrs
               val a3 = walk_typedef s3 ctx' td
             in (s3, a2 @ a3) end)
         in (s2, specs, a1 @ wa s2 ctx' asps) end
     | A.DIncomplete (id, _) => (reg_q qual Typ senv id, specs, [])
     | A.DSubtype (id, sub, asps, _) =>
         let
           val a1 = walk_sub senv ctx' sub
           val s1 = reg_q qual Typ senv id
         in (s1, specs, a1 @ wa s1 ctx' asps) end
     | A.DSpec (sp, _, asps, _) =>
         let
           val (s1, specs1) = reg_subprogram qual senv specs true sp
           val (_, a1) = scoped s1 (fn s =>
             let
               val (s2, a2) = walk_spec s ctx' sp
             in (s2, a2 @ wa s2 ctx' asps) end)
         in (s1, specs1, a1) end
     | A.DNullProc (sp, asps, _) =>
         let
           val (s1, specs1) = reg_subprogram qual senv specs false sp
           val (_, a1) = scoped s1 (fn s =>
             let
               val (s2, a2) = walk_spec s ctx' sp
             in (s2, a2 @ wa s2 ctx' asps) end)
         in (s1, specs1, a1) end
     | A.DExprFun (sp, e, asps, _) =>
         let
           val (s1, specs1) = reg_subprogram qual senv specs false sp
           val (_, a1) = scoped s1 (fn s =>
             let
               val (s2, a2) = walk_spec s ctx' sp
             in (s2, a2 @ walk_expr s2 ctx' e @ wa s2 ctx' asps) end)
         in (s1, specs1, a1) end
     | A.DBody (sp, asps, decls, stmts, handlers, _) =>
         let
           val (s1, specs1) = reg_subprogram qual senv specs false sp
           val (_, a1) = scoped s1 (fn s =>
             let
               val (s2, a2) = walk_spec s ctx' sp
               val a3 = wa s2 ctx' asps
               val (s4, _, a4) = walk_decls NONE s2 ctx' [] decls
               val a5 = walk_stmts s4 ctx' stmts
               val a6 = maps (walk_handler s4 ctx') handlers
             in (s4, a2 @ a3 @ a4 @ a5 @ a6) end)
         in (s1, specs1, a1) end
     | A.DPackage (name, asps, vis, priv, _) =>
         let
           val prefix = (case name of A.ESel (e1, _, _) => we e1 | _ => [])
           val key = (case dotted name of SOME k => k | NONE => "")
           val full = (case qual of SOME q => q ^ "." ^ key | NONE => key)
           val s1 =
             (case last_ident name of
                NONE => senv
              | SOME id =>
                  let
                    val s0 = reg_q qual Pack senv id
                    val A.Ident (_, _, ni) = id
                    val kind = Pack (A.pos_of_NodeInfo ni)
                  in declare kind s0 full end)
           val (s4, a1) =
             let
               val (s3, _, a2) = walk_decls (SOME full) s1 ctx' [] vis
               val (s4, _, a3) = walk_decls (SOME full) s3 ctx' [] priv
             in (s4, a2 @ a3 @ wa s4 ctx' asps) end
           (* what the package leaves behind: its qualified names *)
           val pre = full ^ "."
           val kept = Symtab.fold
             (fn (k, v) => if String.isPrefix pre k then Symtab.update (k, v)
                           else I) (names_of s4) (names_of s1)
         in (set_names kept s1, specs, prefix @ a1) end
     | A.DPackageBody (name, asps, decls, body, _) =>
         let
           val a0 = we name
           val key = (case dotted name of SOME k => k | NONE => "")
           val full = (case qual of SOME q => q ^ "." ^ key | NONE => key)
           val (_, a1) = scoped senv (fn s =>
             let
               val (s1, subs) = open_package full s
               val (s2, _, a2) = walk_decls NONE s1 ctx' subs decls
               val a3 = wa s2 ctx' asps
               val a4 = (case body of
                           NONE => []
                         | SOME (ss, hs) =>
                             walk_stmts s2 ctx' ss
                             @ maps (walk_handler s2 ctx') hs)
             in (s2, a2 @ a3 @ a4) end)
         in (senv, specs, a0 @ a1) end
     | A.DUse (is_type, es, _) =>
         let
           val a1 = maps we es
           val s1 =
             if is_type then senv
             else fold (fn e => fn s =>
                          (case dotted e of
                             SOME k => #1 (open_package k s)
                           | NONE => s)) es senv
         in (s1, specs, a1) end
     | A.DPragma (_, as1, _) =>
         (senv, specs, maps (walk_assoc false senv ctx') as1)
     | A.DAttrDef (a, b, _) => (senv, specs, we a @ we b))
  end


fun walk_clause senv ctx cl : acts =
  (case cl of
     A.CWith (_, _, es, ni) => chk senv ctx ni @ maps (walk_expr senv ctx) es
   | A.CUse (_, es, ni) => chk senv ctx ni @ maps (walk_expr senv ctx) es)

(* A "use" clause makes the entities of the packages it names directly visible
   (a "use type" clause makes nothing visible that this pass tracks). *)
fun clause_env senv cl =
  (case cl of
     A.CUse (false, es, _) =>
       fold (fn e => fn s =>
               (case dotted e of SOME k => #1 (open_package k s) | NONE => s))
         es senv
   | _ => senv)

(* One compilation unit: what its "use" clauses made visible does not persist,
   what it declares does (a changed entry is one with another declaration
   site than before the declaration was walked). *)
fun walk_unit senv ctx (A.Unit (clauses, d, ni)) : aenv * acts =
  let
    val a0 = chk senv ctx ni
    val a1 = maps (walk_clause senv ctx) clauses
    val s1 = fold (fn cl => fn s => clause_env s cl) clauses senv
    val (s2, _, a2) = walk_decl NONE s1 ctx [] d
    val names1 = names_of s1
    val persistent = Symtab.fold
      (fn (k, v) =>
         (case Symtab.lookup names1 k of
            SOME v1 => if pos_of_kind v1 = pos_of_kind v then I
                       else Symtab.update (k, v)
          | NONE => Symtab.update (k, v)))
      (names_of s2) (names_of senv)
  in (set_names persistent senv, a0 @ a1 @ a2) end

fun analyse_and_eval0 (root : pos A.root) thy =
  let
    val aenv0 = get (Context.Theory thy)
    (* The bottom frame is always the top-level root itself, so "ctx" is never
       empty. *)
    val ctx0 = [root]
    fun drop acts = (thy, acts)
  in
    case root of
      A.Id (id as A.Ident (_, _, ni)) =>
        let val here = check_antiq aenv0 ctx0 ni
            val _ = use_name aenv0 id
        in (thy, here) end
    | A.Expr e => drop (walk_expr aenv0 ctx0 e)
    | A.Type s => drop (walk_sub aenv0 ctx0 s)
    | A.Stmt s => drop (walk_stmt aenv0 ctx0 s)
    | A.Decl d => drop (#3 (walk_decl NONE aenv0 ctx0 [] d))
    | A.Body ss => drop (walk_stmts aenv0 ctx0 ss)
    | A.Crate units =>
        let
          val (aenv1, acts) = seq (fn s => fn u => walk_unit s ctx0 u)
                                aenv0 units
        in (Context.theory_map (put aenv1) thy, acts) end
  end

fun analyse_and_eval root thy =
  Dispatched_Antiqs.with_fresh (fn () => analyse_and_eval0 root thy)

end
\<close>

subsection\<open>Some Basic Antiquotation Settings\<close>

text\<open>
  The same eight demonstration antiquotations as C11's (\<open>C11_AnaEval.thy\<close>, whose
  notes on each apply unchanged): \<open>probe_aenv\<close>, \<open>probe_ast\<close>, \<open>highlight\<close>,
  \<open>term\<close>, \<open>ML\<close>, \<open>text\<close>, \<open>definition\<close> and \<open>lemma\<close>. They are written in an
  AdaSpark comment as \<^verbatim>\<open>--@ term \<open>x + 1 = (2::nat)\<close>\<close> (or anywhere in a comment as
  \<^verbatim>\<open>@term \<open>...\<close>\<close>) and attach to the node that begins on the next token;
  \<^verbatim>\<open>@tag[navi](level)\<close> selects another node and an evaluation order exactly as in
  C11. Handlers are registered under their tag in \<open>aenv\<close>'s \<open>ada_antiq\<close> table;
  nothing here knows AdaSpark, only the \<open>root\<close> they are handed.
\<close>

declare [[ML_catch_all = true]]

ML\<open>
val AENV = Unsynchronized.ref(AEnv.empty_aenv);
val probe_aenv = let fun probe (aenv, _ , _) (_ : string * Position.T) thy =
                              (AENV := aenv; thy)
                 in  AEnv.store_antiq
                   ("probe_aenv",  AEnv.lift_theory_antiq probe) end

val ADA_AST =
  Unsynchronized.ref((AdaSpark_Ast.Crate []): (Position.T AdaSpark_Ast.root) )
val probe_ast = let fun probe (_, ast , l) (_ : string * Position.T) thy =
                              (writeln("Level: "^ Int.toString l);
                               writeln("Read : " ^ AdaSpark_Pp.pp_root ast);
                               ADA_AST := ast; thy)
                in  AEnv.store_antiq
                  ("probe_ast",  AEnv.lift_theory_antiq probe) end

val highlight = let fun probe (_, ast , _) (_ : string * Position.T) thy =
                              (Position.report (AnaEval.pos_of_root ast)
                               Markup.intensify;
                               thy)
                in  AEnv.store_antiq
                  ("highlight",  AEnv.lift_theory_antiq probe) end

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
   term is a real Isabelle error positioned in the AdaSpark source. The
   catch-all handler is needed because "Syntax.read_term" fails with "Par_Exn",
   not "ERROR". *)
val ADA_TERM_PROBE =
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
      in (ADA_TERM_PROBE := t; thy) end
  in AEnv.store_antiq ("term", AEnv.lift_theory_antiq probe) end

(* Runs its body as real ML source, so a definition written in a AdaSpark
   comment becomes a later-visible ML binding - the one handler that needs
   "Context.generic -> Context.generic" rather than "theory -> theory". *)
val ml_antiq =
  let
    fun probe (_, _, _) (body, body_pos) : Context.generic -> Context.generic =
      ML_Context.exec (fn () =>
        ML_Context.eval_source (ML_Compiler.verbose true ML_Compiler.flags)
          (body_source (body, body_pos)))
      #> Local_Theory.propagate_ml_env
  in AEnv.store_antiq ("ML", probe) end

(* Isabelle's "text" command: the body goes through the real
   "Document_Output.output_document" (inner antiquotations are checked,
   hyperlinked and hoverable); the result is stashed, not typeset, for the
   reason given in the Limitations of the C11 manual. *)
val ADA_TEXT_PROBE = Unsynchronized.ref ([] : Latex.text)
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
      in (ADA_TEXT_PROBE := latex; thy) end
  in AEnv.store_antiq ("text", AEnv.lift_theory_antiq probe) end

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
  in AEnv.store_antiq ("definition", AEnv.lift_theory_antiq probe) end

(* A statement plus one terminal "by" proof, actually proved - proof-carrying
   code: e.g. a property of a VAL abbreviation's value, discharged right where
   the AdaSpark text that motivates it lives. *)
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
  in AEnv.store_antiq ("lemma", AEnv.lift_theory_antiq probe) end
\<close>

setup\<open>probe_aenv\<close>
setup\<open>probe_ast\<close>
setup\<open>highlight\<close>
setup\<open>term_antiq\<close>
setup\<open>text_antiq\<close>
setup\<open>ml_antiq\<close>
setup\<open>definition_antiq\<close>
setup\<open>lemma_antiq\<close>
end
