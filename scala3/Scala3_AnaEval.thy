(***********************************************************************************
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
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 ***********************************************************************************)

theory Scala3_AnaEval
  imports "Scala3_Env"
begin

section\<open>Analyse and Eval\<close>

text\<open>
  \<open>analyse_and_eval\<close> is the Scala 3 counterpart of the passes of the same name of the other
  front-ends (\<^verbatim>\<open>C11_AnaEval.thy\<close>, \<^verbatim>\<open>Occam2_AnaEval.thy\<close>, whose long explanations apply here and are not
  repeated): a single, purely functional, scoped walk over a parsed \<open>root\<close>, threading \<open>senv\<close> through
  the descent, collecting every antiquotation action paired with its \<open>level\<close> instead of applying
  it, and hyperlinking every name use to its declaration. What is specific to Scala:

  \<^item> \<^bold>\<open>Two name spaces.\<close> A type (a class, trait, enum, type alias or type parameter) is looked up in
    \<open>types\<close>, a term (everything else) in \<open>terms\<close>. A \<open>case class\<close>, an \<open>enum\<close>, an \<open>object\<close> declares
    a name in both.
  \<^item> \<^bold>\<open>Scoping.\<close> A block is a scope; so are a lambda, a case clause (its pattern variables are visible
    in the guard and the body), a \<open>for\<close> comprehension (a generator's variables are visible in the
    following enumerators and the body), a method (type parameters, then each parameter clause, then
    the body), a class (type parameters, constructor parameters, the template) and a template.
    Scoping is shadow-and-restore on the two tables.
  \<^item> \<^bold>\<open>Forward references.\<close> The members of a template, and the top level of a compilation unit, are
    visible throughout (a method may call one defined further down, a \<open>val\<close> may be used by an
    earlier method); in a block only the \<^emph>\<open>methods, classes, objects and types\<close> are (local functions may
    be mutually recursive), a local \<open>val\<close> is visible only after its definition. A declaration is
    therefore registered, and its site reported, \<^emph>\<open>before\<close> the walk of the scope it belongs to.
  \<^item> \<^bold>\<open>Imports\<close> register the imported names, in both name spaces, at their selector (\<open>a\<close> in \<open>{a, b as c}\<close>;
    \<open>c\<close> for a renamed one); a use is hyperlinked to the selector. A wildcard import registers nothing.
  \<^item> \<^bold>\<open>Names that resolve nowhere are not marked.\<close> Unlike C11 and occam 2, where an undeclared name is
    underlined, a Scala name routinely comes from the standard library, a wildcard import or a
    member inherited from a parent class, none of which this pass sees; underlining them would drown
    the useful markup. A member selection \<open>e.f\<close> is not resolved either (it needs types); only \<open>e\<close> is.
  \<^item> \<^bold>\<open>The compilation unit\<close> is the one root whose names persist: after \<open>scala3\<close> has analysed a unit, its
    top-level names stay in \<open>senv\<close> for the following units, as the members of a package do.
  \<^item> \<^bold>\<open>Closest context and navigation\<close> as in C11/occam 2: expressions, types, patterns and
    definitions/imports push their own node (\<open>Expr\<close>, \<open>Type\<close>, \<open>Pat\<close>, \<open>Stat\<close>); everything else (cases,
    enumerators, parameters, parents, selectors, ...) uses \<open>hd ctx\<close>. The children of a node are, in
    source order, its sub-expressions, sub-types, sub-patterns and sub-definitions; an
    expression statement is its expression.
\<close>
ML\<open>
structure AnaEval = struct

structure A = Scala3_Ast
open SEnv

type acts = (int * (Context.generic -> Context.generic)) list

fun terms_of (mk {terms, ...} : senv) = terms
fun types_of (mk {types, ...} : senv) = types

fun set_tables (terms', types') (mk {terms = _, types = _, scala_antiq, units}) =
  mk {terms = terms', types = types', scala_antiq = scala_antiq, units = units}

(* The position a "root" itself spans: what a "type_antiq_fun" sees as its own "current term". A
   compilation unit has no single span. *)
fun pos_of_root (A.Id id) = A.pos_of_ident id
  | pos_of_root (A.Expr e) = A.pos_of_expr e
  | pos_of_root (A.Type t) = A.pos_of_type t
  | pos_of_root (A.Stat s) = A.pos_of_stat s
  | pos_of_root (A.Pat p) = A.pos_of_pat p
  | pos_of_root (A.Unit _) = Position.none

(* Exactly-once dispatch of every physical antiquotation, whatever number of AST nodes share its
   leftmost source position - the same design as in the other front-ends. The set of comments
   already dispatched belongs to one walk ("analyse_and_eval" installs a fresh one for its dynamic
   extent) and is kept per thread, so two walks running at the same time cannot see each other's. *)
structure Dispatched_Antiqs = struct
  val state : Position.T A.comment list Unsynchronized.ref Thread_Data.var = Thread_Data.var ()
  fun current () =
    (case Thread_Data.get state of
       SOME r => r
     | NONE => raise Fail "Dispatched_Antiqs: outside of analyse_and_eval")
  fun with_fresh f = Thread_Data.setmp state (SOME (Unsynchronized.ref [])) f ()
  fun already_dispatched c = member (op =) (!(current ())) c
  fun mark c = let val r = current () in r := c :: !r end
end

(* A navigation step's coarse target category, ignoring the constructor within. *)
fun category (A.Id _)   = 0
  | category (A.Expr _) = 1
  | category (A.Type _) = 2
  | category (A.Stat _) = 3
  | category (A.Pat _)  = 4
  | category (A.Unit _) = 5

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
  | select_u (navi, ctx) = (navi, ctx) (* first "r"/"d": the "(u|U)*" phase is over *)

(* The ordered list of children "r"/"d" may navigate into (see the top-of-theory note):
   sub-expressions, sub-types, sub-patterns and sub-definitions in source order; nodes without a
   "root" counterpart (parameters, clauses, parents, selectors, ...) are flattened into their
   parent's list or dropped. *)
fun stat_root s = (case s of A.SExpr e => A.Expr e | _ => A.Stat s)
fun opt_expr eo = (case eo of SOME e => [A.Expr e] | NONE => [])
fun opt_type to = (case to of SOME t => [A.Type t] | NONE => [])
fun arg_exprs a = (case a of A.AExpr e => [A.Expr e] | A.ANamed (_, e, _) => [A.Expr e])
fun annot_children (A.Annot (t, argss, _)) = A.Type t :: maps (maps arg_exprs) argss
fun parent_children (A.Parent (t, argss, _, _)) = A.Type t :: maps (maps arg_exprs) argss

fun param_children (A.Param (anns, _, _, _, t, d, _)) =
  maps annot_children anns @ [A.Type t] @ opt_expr d
fun tparam_children (A.TParam (anns, _, _, hk, A.Bounds (lo, hi), ctx, _)) =
  maps annot_children anns @ maps tparam_children hk @ opt_type lo @ opt_type hi @ map A.Type ctx
fun clause_children c = (case c of
    A.PClause (_, ps, _) => maps param_children ps
  | A.TClause (tps, _) => maps tparam_children tps)

fun case_children (A.Case (p, g, body, _)) = A.Pat p :: opt_expr g @ map stat_root body
fun enum_children en = (case en of
    A.EnGen (_, p, e, _) => [A.Pat p, A.Expr e]
  | A.EnGuard (e, _) => [A.Expr e]
  | A.EnVal (p, e, _) => [A.Pat p, A.Expr e])
fun body_children (A.TemplateBody (_, stats, _)) = map stat_root stats
fun template_children (A.Template (parents, _, body, _)) =
  maps parent_children parents @ (case body of SOME b => body_children b | NONE => [])

fun children_of_type t = (case t of
    A.TName _ => []
  | A.TSelect (t1, _, _) => [A.Type t1]
  | A.TSingleton (e, _) => [A.Expr e]
  | A.TProject (t1, _, _) => [A.Type t1]
  | A.TApply (t1, ts, _) => map A.Type (t1 :: ts)
  | A.TTuple (ts, _) => map A.Type ts
  | A.TFun (_, ts, r, _) => map A.Type (ts @ [r])
  | A.TByName (t1, _) => [A.Type t1]
  | A.TRepeated (t1, _) => [A.Type t1]
  | A.TInfix (a, _, b, _) => [A.Type a, A.Type b]
  | A.TWith (a, b, _) => [A.Type a, A.Type b]
  | A.TRefine (t1, stats, _) => opt_type t1 @ map stat_root stats
  | A.TAnnot (t1, anns, _) => A.Type t1 :: maps annot_children anns
  | A.TWild (A.Bounds (lo, hi), _) => opt_type lo @ opt_type hi
  | A.TLit _ => []
  | A.TLambda (tps, t1, _) => maps tparam_children tps @ [A.Type t1]
  | A.TPolyFun (tps, t1, _) => maps tparam_children tps @ [A.Type t1]
  | A.TMatch (t1, cases, _) =>
      A.Type t1 :: maps (fn A.TypeCase (l, r, _) => opt_type l @ [A.Type r]) cases)

fun children_of_pat p = (case p of
    A.PVar _ => []
  | A.PWild _ => []
  | A.PLit _ => []
  | A.PRef e => [A.Expr e]
  | A.PApply (f, ts, ps, _) => A.Expr f :: map A.Type ts @ map A.Pat ps
  | A.PTuple (ps, _) => map A.Pat ps
  | A.PInfix (a, _, b, _) => [A.Pat a, A.Pat b]
  | A.PAlt (ps, _) => map A.Pat ps
  | A.PBind (_, p1, _) => [A.Pat p1]
  | A.PTyped (p1, t, _) => [A.Pat p1, A.Type t]
  | A.PSplat (p1, _) => [A.Pat p1]
  | A.PGiven (t, _) => [A.Type t])

fun children_of_expr e = (case e of
    A.EIdent _ => []
  | A.ESelect (e1, _, _) => [A.Expr e1]
  | A.EThis _ => []
  | A.ESuper _ => []
  | A.ELit _ => []
  | A.EApply (f, args, _, _) => A.Expr f :: maps arg_exprs args
  | A.ETypeApply (e1, ts, _) => A.Expr e1 :: map A.Type ts
  | A.EInfix (a, _, b, _) => [A.Expr a, A.Expr b]
  | A.EPrefix (_, e1, _) => [A.Expr e1]
  | A.EPostfix (e1, _, _) => [A.Expr e1]
  | A.EAssign (a, b, _) => [A.Expr a, A.Expr b]
  | A.ETyped (e1, t, _) => [A.Expr e1, A.Type t]
  | A.EAnnotated (e1, anns, _) => A.Expr e1 :: maps annot_children anns
  | A.ESplat (e1, _) => [A.Expr e1]
  | A.ELambda (_, body, _, _) => [A.Expr body]
  | A.EBlock (stats, _) => map stat_root stats
  | A.ECases (cases, _) => maps case_children cases
  | A.EIf (c, a, b, _) => A.Expr c :: A.Expr a :: opt_expr b
  | A.EWhile (c, b, _) => [A.Expr c, A.Expr b]
  | A.ETry (b, h, f, _) => A.Expr b :: opt_expr h @ opt_expr f
  | A.EThrow (e1, _) => [A.Expr e1]
  | A.EReturn (e1, _) => opt_expr e1
  | A.EFor (enums, _, body, _) => maps enum_children enums @ [A.Expr body]
  | A.EMatch (e1, cases, _) => A.Expr e1 :: maps case_children cases
  | A.ENew (parents, body, _) =>
      maps parent_children parents @ (case body of SOME b => body_children b | NONE => [])
  | A.ETuple (es, _) => map A.Expr es
  | A.EParen (e1, _) => [A.Expr e1]
  | A.EPlaceholder _ => [])

fun children_of_def d = (case d of
    A.DVal (anns, _, _, pats, t, rhs, _) => maps annot_children anns @ map A.Pat pats @ opt_type t @ opt_expr rhs
  | A.DDef (anns, _, _, clauses, t, rhs, _) =>
      maps annot_children anns @ maps clause_children clauses @ opt_type t @ opt_expr rhs
  | A.DType (anns, _, _, clauses, A.Bounds (lo, hi), rhs, _) =>
      maps annot_children anns @ maps clause_children clauses @ opt_type lo @ opt_type hi @ opt_type rhs
  | A.DClass (anns, _, _, _, tps, _, clauses, tmpl, _) =>
      maps annot_children anns @ maps tparam_children tps @ maps clause_children clauses @ template_children tmpl
  | A.DGiven (anns, _, _, clauses, t, rhs, body, parents, _) =>
      maps annot_children anns @ maps clause_children clauses @ [A.Type t] @ opt_expr rhs @
      (case body of SOME b => body_children b | NONE => []) @ maps parent_children parents
  | A.DExtension (clauses, stats, _) => maps clause_children clauses @ map stat_root stats
  | A.DEnumCase (anns, _, _, tps, clauses, parents, _) =>
      maps annot_children anns @ maps tparam_children tps @ maps clause_children clauses @ maps parent_children parents
  | A.DPackage (_, stats, _) => (case stats of SOME ss => map stat_root ss | NONE => []))

fun children_of_stat s = (case s of
    A.SExpr e => children_of_expr e
  | A.SImport _ => []
  | A.SDef d => children_of_def d)

fun children_of _ (A.Expr e) = children_of_expr e
  | children_of _ (A.Type t) = children_of_type t
  | children_of _ (A.Pat p) = children_of_pat p
  | children_of _ (A.Stat s) = children_of_stat s
  | children_of _ (A.Unit stats) = map stat_root stats
  | children_of antiq_pos (A.Id _) =
      error ("select_ast: an identifier is a leaf, no \"r\"/\"d\" children" ^ Position.here antiq_pos)

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
  | select_rd (antiq_pos, navi as A.down :: _, node) = select_count_r (antiq_pos, 1, navi, node)
  | select_rd (antiq_pos, A.right :: rest, node) = select_count_r (antiq_pos, 1, rest, node)
  | select_rd (antiq_pos, A.up :: _, _) =
      error ("select_ast: \"u\" after \"r\"/\"d\"" ^ Position.here antiq_pos)
  | select_rd (antiq_pos, A.Up :: _, _) =
      error ("select_ast: \"U\" after \"r\"/\"d\"" ^ Position.here antiq_pos)
and select_count_r (antiq_pos, n, A.right :: rest, node) = select_count_r (antiq_pos, n + 1, rest, node)
  | select_count_r (antiq_pos, n, A.down :: rest, node) =
      let val cs = children_of antiq_pos node in
        if n > length cs then
          error ("select_ast: navigation index " ^ Int.toString n ^ " out of range (only " ^
                 Int.toString (length cs) ^ " navigable children here)" ^ Position.here antiq_pos)
        else select_rd (antiq_pos, rest, List.nth (cs, n - 1))
      end
  | select_count_r (antiq_pos, _, A.up :: _, _) =
      error ("select_ast: \"u\" after \"r\"" ^ Position.here antiq_pos)
  | select_count_r (antiq_pos, _, A.Up :: _, _) =
      error ("select_ast: \"U\" after \"r\"" ^ Position.here antiq_pos)
  | select_count_r (antiq_pos, _, [], _) =
      error ("select_ast: navigation string ends with a dangling \"r\", expected a final \"d\"" ^
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
   "ni"'s comment list by tag in "senv"'s "scala_antiq", instantiates it with
   (senv, select_ast tag_pos navi ctx, level), and pairs the resulting
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
   "type_antiq_fun" in Scala3_Env.thy for why the cartouche's own position now
   travels all the way to the handler instead of being discarded here - and
   the *resolved* AST node ("select_ast tag_pos navi ctx"), not the raw navi
   list: a handler is never itself responsible for interpreting "up"/"Up"/
   "right"/"down". *)
fun check_antiq senv (ctx : pos A.root list) (ni : pos A.nodeInfo)
    : (int * (Context.generic -> Context.generic)) list =
  case ni of
    A.OnlyPos _ => []
  | A.NodeInfo (cs, _) =>
      List.mapPartial
        (fn c as A.Antiquotation ({tag = (tag, tag_pos)}, navi, {level}, {cartouche = (body, body_pos)}) =>
              if Dispatched_Antiqs.already_dispatched c then NONE
              else
                let val mk {scala_antiq, ...} = senv in
                  case Symtab.lookup scala_antiq tag of
                    NONE =>
                      error ("analyse_and_eval: no antiquotation handler registered for tag " ^
                             quote tag)
                  | SOME antiq_fun =>
                      (Dispatched_Antiqs.mark c;
                       SOME (level, antiq_fun (senv, select_ast tag_pos navi ctx, level) (body, body_pos)))
                end
          | A.Raw_txt _ => NONE)
        cs


(* The full-token range a name spans, starting at "pos" (an identifier's "nodeInfo" carries a
   bare point, which would make an entity report claim a single character). *)
fun name_range (name, pos) =
  Position.range_position (Position.range (pos, Position.symbol_explode name pos))

fun report_decl kind name decl_pos =
  let val range_pos = name_range (name, decl_pos)
  in Position.report range_pos (Position.entity_markup kind (name, range_pos)) end

(* Hyperlinks a use of "name" to its declaration, if it resolves; nothing is reported if it does
   not (see the top-of-theory note). *)
fun use_in table name use_pos =
  (case Symtab.lookup table name of
     NONE => ()
   | SOME k =>
       Position.report (name_range (name, use_pos))
         (Position.entity_markup (describe_kind k) (name, name_range (name, pos_of_kind k))))

fun use_term senv (A.Ident (name, _, ni)) = use_in (terms_of senv) name (A.pos_of_NodeInfo ni)
fun use_type senv (A.Ident (name, _, ni)) = use_in (types_of senv) name (A.pos_of_NodeInfo ni)

fun reg_term mk_kind senv (A.Ident (name, _, ni)) =
  let
    val pos = A.pos_of_NodeInfo ni
    val kind = mk_kind pos
    val _ = report_decl (describe_kind kind) name pos
  in set_tables (Symtab.update (name, kind) (terms_of senv), types_of senv) senv end

fun reg_type mk_kind senv (A.Ident (name, _, ni)) =
  let
    val pos = A.pos_of_NodeInfo ni
    val kind = mk_kind pos
    val _ = report_decl (describe_kind kind) name pos
  in set_tables (terms_of senv, Symtab.update (name, kind) (types_of senv)) senv end

(* An imported name: registered in both name spaces, at its selector. *)
fun reg_import senv (id as A.Ident (name, _, ni)) =
  let
    val pos = A.pos_of_NodeInfo ni
    val kind = Import pos
    val _ = report_decl (describe_kind kind) name pos
  in set_tables (Symtab.update (name, kind) (terms_of senv), Symtab.update (name, kind) (types_of senv)) senv end

(* Runs "f" in a nested scope: both tables are restored on exit. *)
fun scoped senv f =
  let
    val (terms, types) = (terms_of senv, types_of senv)
    val (senv1, acts) = f senv
  in (set_tables (terms, types) senv1, acts) end

fun seq (f : senv -> 'a -> senv * acts) senv xs =
  fold (fn x => fn (e, acc) => let val (e', a) = f e x in (e', acc @ a) end) xs (senv, [])

fun opt f senv x = (case x of NONE => (senv, []) | SOME y => f senv y)

(* The variables a pattern binds. *)
fun pat_binders p = (case p of
    A.PVar id => [id]
  | A.PWild _ => []
  | A.PLit _ => []
  | A.PRef _ => []
  | A.PApply (_, _, ps, _) => maps pat_binders ps
  | A.PTuple (ps, _) => maps pat_binders ps
  | A.PInfix (a, _, b, _) => pat_binders a @ pat_binders b
  | A.PAlt (ps, _) => maps pat_binders ps
  | A.PBind (id, p1, _) => id :: pat_binders p1
  | A.PTyped (p1, _, _) => pat_binders p1
  | A.PSplat (p1, _) => pat_binders p1
  | A.PGiven _ => [])

fun opt_list x = (case x of SOME y => [y] | NONE => [])

(* The names a "val"/"var" defines: the variables of its patterns - but a single identifier, even an
   upper-case one ("val A = 1"), is a definition, not a stable-identifier pattern. *)
fun val_binders pats = (case pats of [A.PRef (A.EIdent id)] => [id] | _ => maps pat_binders pats)

(* A compact wrapper for the antiquotations a node carries (its "nodeInfo"). *)
fun chk senv ctx ni = check_antiq senv ctx ni

fun walk_type senv ctx (t : pos A.sType) : senv * acts =
  let
    val ctx' = A.Type t :: ctx
    val here = chk senv ctx' (A.nodeInfo_of_type t)
    fun plus (e, a) = (e, here @ a)
    fun types ts = seq (fn s => fn x => walk_type s ctx' x) senv ts
  in
    case t of
      A.TName id => (use_type senv id; (senv, here))
    | A.TSelect (t1, _, _) => plus (types [t1])
    | A.TSingleton (e, _) => plus (walk_expr senv ctx' e)
    | A.TProject (t1, _, _) => plus (types [t1])
    | A.TApply (t1, ts, _) => plus (types (t1 :: ts))
    | A.TTuple (ts, _) => plus (types ts)
    | A.TFun (_, ts, r, _) => plus (types (ts @ [r]))
    | A.TByName (t1, _) => plus (types [t1])
    | A.TRepeated (t1, _) => plus (types [t1])
    | A.TInfix (a, op_, b, _) => (use_type senv op_; plus (types [a, b]))
    | A.TWith (a, b, _) => plus (types [a, b])
    | A.TRefine (t1, stats, _) =>
        let
          val (_, a1) = opt (fn s => fn x => walk_type s ctx' x) senv t1
          val (_, a2) = scoped senv (fn s => walk_stats true s ctx' stats)
        in (senv, here @ a1 @ a2) end
    | A.TAnnot (t1, anns, _) =>
        let
          val (_, a1) = walk_type senv ctx' t1
          val (_, a2) = seq (fn s => fn x => walk_annot s ctx' x) senv anns
        in (senv, here @ a1 @ a2) end
    | A.TWild (A.Bounds (lo, hi), _) => plus (types (opt_list lo @ opt_list hi))
    | A.TLit _ => (senv, here)
    | A.TLambda (tps, t1, _) =>
        let val (_, a) = scoped senv (fn s =>
              let val (s1, a1) = walk_tparams s ctx' tps
                  val (s2, a2) = walk_type s1 ctx' t1
              in (s2, a1 @ a2) end)
        in (senv, here @ a) end
    | A.TPolyFun (tps, t1, _) =>
        let val (_, a) = scoped senv (fn s =>
              let val (s1, a1) = walk_tparams s ctx' tps
                  val (s2, a2) = walk_type s1 ctx' t1
              in (s2, a1 @ a2) end)
        in (senv, here @ a) end
    | A.TMatch (t1, cases, _) =>
        let
          val (_, a1) = walk_type senv ctx' t1
          val (_, a2) = seq (fn s => fn A.TypeCase (l, r, ni) =>
                               let
                                 val h = chk s ctx' ni
                                 val (_, a) = seq (fn s' => fn x => walk_type s' ctx' x) s (opt_list l @ [r])
                               in (s, h @ a) end) senv cases
        in (senv, here @ a1 @ a2) end
  end

and walk_annot senv ctx (A.Annot (t, argss, ni)) =
  let
    val here = chk senv ctx ni
    val (_, a1) = walk_type senv ctx t
    val (_, a2) = seq (fn s => fn args => walk_args s ctx args) senv argss
  in (senv, here @ a1 @ a2) end

and walk_args senv ctx args =
  seq (fn s => fn a =>
         (case a of
            A.AExpr e => walk_expr s ctx e
          | A.ANamed (_, e, ni) =>
              let
                val h = chk s ctx ni
                val (_, a1) = walk_expr s ctx e
              in (s, h @ a1) end)) senv args

(* Type parameters: registered one by one (a bound may mention its own parameter, or an earlier one). *)
and walk_tparams senv ctx tps =
  seq (fn s => fn (A.TParam (anns, _, id, hk, A.Bounds (lo, hi), cbs, ni)) =>
         let
           val h = chk s ctx ni
           val (_, a0) = seq (fn s' => fn x => walk_annot s' ctx x) s anns
           val s1 = reg_type Class s id
           val (_, a1) = scoped s1 (fn s' => walk_tparams s' ctx hk)
           val (_, a2) = seq (fn s' => fn x => walk_type s' ctx x) s1 (opt_list lo @ opt_list hi @ cbs)
         in (s1, h @ a0 @ a1 @ a2) end) senv tps

(* A parameter clause: each parameter's type and default are walked before its name is registered. *)
and walk_clauses senv ctx clauses =
  seq (fn s => fn c =>
         (case c of
            A.TClause (tps, ni) =>
              let
                val h = chk s ctx ni
                val (s1, a) = walk_tparams s ctx tps
              in (s1, h @ a) end
          | A.PClause (_, ps, ni) =>
              let
                val h = chk s ctx ni
                val (s1, a) =
                  seq (fn s' => fn (A.Param (anns, _, _, id, t, d, pni)) =>
                         let
                           val ph = chk s' ctx pni
                           val (_, a0) = seq (fn s'' => fn x => walk_annot s'' ctx x) s' anns
                           val (_, a1) = walk_type s' ctx t
                           val (_, a2) = opt (fn s'' => fn x => walk_expr s'' ctx x) s' d
                           val s2 = (case id of SOME i => reg_term Param s' i | NONE => s')
                         in (s2, ph @ a0 @ a1 @ a2) end) s ps
              in (s1, h @ a) end)) senv clauses

and walk_binding senv ctx (A.Binding (id, t, ni)) =
  let
    val h = chk senv ctx ni
    val (_, a1) = opt (fn s => fn x => walk_type s ctx x) senv t
    val s1 = (case id of SOME i => reg_term Param senv i | NONE => senv)
  in (s1, h @ a1) end

(* Patterns; "reg": register the binders (not for a "val" of a template, whose binders have been
   registered ahead of the walk). *)
and walk_pat reg senv ctx (p : pos A.sPat) : senv * acts =
  let
    val ctx' = A.Pat p :: ctx
    val here = chk senv ctx' (A.nodeInfo_of_pat p)
    fun plus (e, a) = (e, here @ a)
    fun pats s ps = seq (fn s' => fn x => walk_pat reg s' ctx' x) s ps
    fun types s ts = seq (fn s' => fn x => walk_type s' ctx' x) s ts
  in
    case p of
      A.PVar id => ((if reg then (reg_term Local senv id, here) else (senv, here)))
    | A.PWild _ => (senv, here)
    | A.PLit _ => (senv, here)
    | A.PRef e => plus (walk_expr senv ctx' e)
    | A.PApply (f, ts, ps, _) =>
        let
          val (_, a0) = walk_expr senv ctx' f
          val (_, a1) = types senv ts
          val (s2, a2) = pats senv ps
        in (s2, here @ a0 @ a1 @ a2) end
    | A.PTuple (ps, _) => plus (pats senv ps)
    | A.PInfix (a, op_, b, _) => (use_term senv op_; plus (pats senv [a, b]))
    | A.PAlt (ps, _) => plus (pats senv ps)
    | A.PBind (id, p1, _) =>
        let
          val s1 = if reg then reg_term Local senv id else senv
          val (s2, a) = walk_pat reg s1 ctx' p1
        in (s2, here @ a) end
    | A.PTyped (p1, t, _) =>
        let
          val (s1, a1) = walk_pat reg senv ctx' p1
          val (_, a2) = walk_type senv ctx' t
        in (s1, here @ a1 @ a2) end
    | A.PSplat (p1, _) => plus (walk_pat reg senv ctx' p1)
    | A.PGiven (t, _) => plus (walk_type senv ctx' t)
  end

and walk_exprs senv ctx es = seq (fn s => fn e => walk_expr s ctx e) senv es

(* Always pushes its own node. *)
and walk_expr senv ctx (e : pos A.sExpr) : senv * acts =
  let
    val ctx' = A.Expr e :: ctx
    val here = chk senv ctx' (A.nodeInfo_of_expr e)
    fun plus (s, a) = (s, here @ a)
    fun one e1 = walk_exprs senv ctx' [e1]
    (* a sub-walk in its own scope: the senv the node returns is the one it was given *)
    fun inner f = let val (_, a) = scoped senv f in (senv, here @ a) end
  in
    case e of
      A.EIdent id => (use_term senv id; (senv, here))
    | A.ESelect (e1, _, _) => (case one e1 of (_, a) => (senv, here @ a))
    | A.EThis _ => (senv, here)
    | A.ESuper _ => (senv, here)
    | A.ELit _ => (senv, here)
    | A.EApply (f, args, _, _) =>
        let
          val (_, a1) = walk_expr senv ctx' f
          val (_, a2) = walk_args senv ctx' args
        in (senv, here @ a1 @ a2) end
    | A.ETypeApply (e1, ts, _) =>
        let
          val (_, a1) = walk_expr senv ctx' e1
          val (_, a2) = seq (fn s => fn x => walk_type s ctx' x) senv ts
        in (senv, here @ a1 @ a2) end
    | A.EInfix (a, op_, b, _) => (use_term senv op_; (case walk_exprs senv ctx' [a, b] of (_, x) => (senv, here @ x)))
    | A.EPrefix (_, e1, _) => (case one e1 of (_, a) => (senv, here @ a))
    | A.EPostfix (e1, _, _) => (case one e1 of (_, a) => (senv, here @ a))
    | A.EAssign (a, b, _) => (case walk_exprs senv ctx' [a, b] of (_, x) => (senv, here @ x))
    | A.ETyped (e1, t, _) =>
        let
          val (_, a1) = walk_expr senv ctx' e1
          val (_, a2) = walk_type senv ctx' t
        in (senv, here @ a1 @ a2) end
    | A.EAnnotated (e1, anns, _) =>
        let
          val (_, a1) = walk_expr senv ctx' e1
          val (_, a2) = seq (fn s => fn x => walk_annot s ctx' x) senv anns
        in (senv, here @ a1 @ a2) end
    | A.ESplat (e1, _) => (case one e1 of (_, a) => (senv, here @ a))
    | A.ELambda (bs, body, _, _) =>
        inner (fn s =>
          let
            val (s1, a1) = seq (fn s' => fn b => walk_binding s' ctx' b) s bs
            val (s2, a2) = walk_expr s1 ctx' body
          in (s2, a1 @ a2) end)
    | A.EBlock (stats, _) => inner (fn s => walk_stats false s ctx' stats)
    | A.ECases (cases, _) => (case seq (fn s => fn c => walk_case s ctx' c) senv cases of (_, a) => (senv, here @ a))
    | A.EIf (c, a, b, _) => (case walk_exprs senv ctx' (c :: a :: opt_list b) of (_, x) => (senv, here @ x))
    | A.EWhile (c, b, _) => (case walk_exprs senv ctx' [c, b] of (_, x) => (senv, here @ x))
    | A.ETry (b, h, f, _) => (case walk_exprs senv ctx' (b :: opt_list h @ opt_list f) of (_, x) => (senv, here @ x))
    | A.EThrow (e1, _) => (case one e1 of (_, a) => (senv, here @ a))
    | A.EReturn (e1, _) => (case walk_exprs senv ctx' (opt_list e1) of (_, a) => (senv, here @ a))
    | A.EFor (enums, _, body, _) =>
        inner (fn s =>
          let
            val (s1, a1) = seq (fn s' => fn en => walk_enum s' ctx' en) s enums
            val (s2, a2) = walk_expr s1 ctx' body
          in (s2, a1 @ a2) end)
    | A.EMatch (e1, cases, _) =>
        let
          val (_, a1) = walk_expr senv ctx' e1
          val (_, a2) = seq (fn s => fn c => walk_case s ctx' c) senv cases
        in (senv, here @ a1 @ a2) end
    | A.ENew (parents, body, _) =>
        let
          val (_, a1) = seq (fn s => fn p => walk_parent s ctx' p) senv parents
          val (_, a2) = opt (fn s => fn b => walk_template_body s ctx' b) senv body
        in (senv, here @ a1 @ a2) end
    | A.ETuple (es, _) => (case walk_exprs senv ctx' es of (_, a) => (senv, here @ a))
    | A.EParen (e1, _) => (case one e1 of (_, a) => (senv, here @ a))
    | A.EPlaceholder _ => (senv, here)
  end

(* A case clause: its pattern variables are visible in the guard and the body. *)
and walk_case senv ctx (A.Case (p, g, body, ni)) =
  let
    val here = chk senv ctx ni
    val (_, a) = scoped senv (fn s =>
      let
        val (s1, a1) = walk_pat true s ctx p
        val (s2, a2) = opt (fn s' => fn x => walk_expr s' ctx x) s1 g
        val (s3, a3) = walk_stats false s2 ctx body
      in (s3, a1 @ a2 @ a3) end)
  in (senv, here @ a) end

(* An enumerator of a comprehension: the generator's right-hand side is walked before its
   pattern variables are registered; they stay visible for the following enumerators. *)
and walk_enum senv ctx en =
  (case en of
     A.EnGen (_, p, e, ni) =>
       let
         val h = chk senv ctx ni
         val (_, a1) = walk_expr senv ctx e
         val (s2, a2) = walk_pat true senv ctx p
       in (s2, h @ a1 @ a2) end
   | A.EnGuard (e, ni) =>
       let
         val h = chk senv ctx ni
         val (_, a1) = walk_expr senv ctx e
       in (senv, h @ a1) end
   | A.EnVal (p, e, ni) =>
       let
         val h = chk senv ctx ni
         val (_, a1) = walk_expr senv ctx e
         val (s2, a2) = walk_pat true senv ctx p
       in (s2, h @ a1 @ a2) end)

and walk_parent senv ctx (A.Parent (t, argss, _, ni)) =
  let
    val h = chk senv ctx ni
    val (_, a1) = walk_type senv ctx t
    val (_, a2) = seq (fn s => fn args => walk_args s ctx args) senv argss
  in (senv, h @ a1 @ a2) end

(* A template body: its members are visible throughout it. *)
and walk_template_body senv ctx (A.TemplateBody (self, stats, ni)) =
  let
    val h = chk senv ctx ni
    val (_, a) = scoped senv (fn s =>
      let
        val (s1, a1) =
          (case self of
             NONE => (s, [])
           | SOME (A.Self (id, t, sni)) =>
               let
                 val sh = chk s ctx sni
                 val (_, at) = opt (fn s' => fn x => walk_type s' ctx x) s t
               in (reg_term Param s id, sh @ at) end)
        val (s2, a2) = walk_stats true s1 ctx stats
      in (s2, a1 @ a2) end)
  in (senv, h @ a) end

and walk_template senv ctx (A.Template (parents, derives, body, ni)) =
  let
    val h = chk senv ctx ni
    val (_, a1) = seq (fn s => fn p => walk_parent s ctx p) senv parents
    val _ = List.app (use_type senv) derives
    val (_, a2) = opt (fn s => fn b => walk_template_body s ctx b) senv body
  in (senv, h @ a1 @ a2) end

(* The declarations of a statement list that are visible before their definition: the methods,
   classes, objects, types, enum cases and named givens; in a template or at the top level
   ("members") also the values and variables. *)
and predeclare members stat senv =
  (case stat of
     A.SDef d =>
       (case d of
          A.DDef (_, _, id, _, _, _, _) => if A.ident_name id = "this" then senv else reg_term Def senv id
        | A.DClass (_, _, kind, id, _, _, _, _, _) =>
            let val s1 = reg_type Class senv id
            in if member (op =) [A.KObject, A.KCaseObject, A.KCaseClass, A.KEnum, A.KPackageObject] kind
               then reg_term Object s1 id else s1 end
        | A.DType (_, _, id, _, _, _, _) => reg_type Class senv id
        | A.DGiven (_, _, SOME id, _, _, _, _, _, _) => reg_term Given senv id
        | A.DEnumCase (_, _, ids, _, _, _, _) =>
            fold (fn id => fn s => reg_type Class (reg_term Enum_case s id) id) ids senv
        | A.DVal (_, _, isvar, pats, _, _, _) =>
            if members
            then fold (fn id => fn s => reg_term (if isvar then Var else Val) s id) (val_binders pats) senv
            else senv
        | _ => senv)
   | _ => senv)

and walk_stats members senv ctx stats =
  let val senv1 = fold (predeclare members) stats senv
  in seq (fn s => fn st => walk_stat members s ctx st) senv1 stats end

and walk_stat members senv ctx (s : pos A.sStat) : senv * acts =
  (case s of
     A.SExpr e => walk_expr senv ctx e
   | A.SImport (_, imps, ni) =>
       let
         val ctx' = A.Stat s :: ctx
         val here = chk senv ctx' ni
         val (s1, a) =
           seq (fn s' => fn (A.ImportExpr (path, sels, ini)) =>
                  let
                    val ih = chk s' ctx' ini
                    val (_, a0) = walk_expr s' ctx' path
                    val (s2, a1) =
                      seq (fn s'' => fn sel =>
                             (case sel of
                                A.SelName (id, rename, sni) =>
                                  (chk s'' ctx' sni, reg_import s'' (case rename of SOME r => r | NONE => id))
                                  |> (fn (h, e) => (e, h))
                              | A.SelWild sni => (s'', chk s'' ctx' sni)
                              | A.SelGiven (t, sni) =>
                                  let
                                    val h = chk s'' ctx' sni
                                    val (_, at) = opt (fn x => fn y => walk_type x ctx' y) s'' t
                                  in (s'', h @ at) end)) s' sels
                  in (s2, ih @ a0 @ a1) end) senv imps
       in (s1, here @ a) end
   | A.SDef d =>
       let
         val ctx' = A.Stat s :: ctx
         val here = chk senv ctx' (A.nodeInfo_of_def d)
         val (s1, a) = walk_def members senv ctx' d
       in (s1, here @ a) end)

and walk_def members senv ctx (d : pos A.sDef) : senv * acts =
  let
    fun annots anns = seq (fn s => fn x => walk_annot s ctx x) senv anns
  in
    case d of
      A.DVal (anns, _, isvar, pats, t, rhs, _) =>
        let
          val (_, a0) = annots anns
          val (_, a1) = opt (fn s => fn x => walk_type s ctx x) senv t
          val (_, a2) = opt (fn s => fn x => walk_expr s ctx x) senv rhs
          (* in a block the binders come into scope only now; in a template they were registered ahead *)
          val (s3, a3) =
            (case pats of
               [A.PRef (A.EIdent id)] => ((if members then senv else reg_term (if isvar then Var else Val) senv id), [])
             | _ => seq (fn s => fn p => walk_pat (not members) s ctx p) senv pats)
        in (s3, a0 @ a1 @ a2 @ a3) end
    | A.DDef (anns, _, _, clauses, t, rhs, _) =>
        let
          val (_, a0) = annots anns
          val (_, a) = scoped senv (fn s =>
            let
              val (s1, a1) = walk_clauses s ctx clauses
              val (_, a2) = opt (fn s' => fn x => walk_type s' ctx x) s1 t
              val (_, a3) = opt (fn s' => fn x => walk_expr s' ctx x) s1 rhs
            in (s1, a1 @ a2 @ a3) end)
        in (senv, a0 @ a) end
    | A.DType (anns, _, _, clauses, A.Bounds (lo, hi), rhs, _) =>
        let
          val (_, a0) = annots anns
          val (_, a) = scoped senv (fn s =>
            let
              val (s1, a1) = walk_clauses s ctx clauses
              val (_, a2) = seq (fn s' => fn x => walk_type s' ctx x) s1 (opt_list lo @ opt_list hi @ opt_list rhs)
            in (s1, a1 @ a2) end)
        in (senv, a0 @ a) end
    | A.DClass (anns, _, _, _, tps, _, clauses, tmpl, _) =>
        let
          val (_, a0) = annots anns
          val (_, a) = scoped senv (fn s =>
            let
              val (s1, a1) = walk_tparams s ctx tps
              val (s2, a2) = walk_clauses s1 ctx clauses
              val (_, a3) = walk_template s2 ctx tmpl
            in (s2, a1 @ a2 @ a3) end)
        in (senv, a0 @ a) end
    | A.DGiven (anns, _, _, clauses, t, rhs, body, parents, _) =>
        let
          val (_, a0) = annots anns
          val (_, a) = scoped senv (fn s =>
            let
              val (s1, a1) = walk_clauses s ctx clauses
              val (_, a2) = walk_type s1 ctx t
              val (_, a3) = opt (fn s' => fn x => walk_expr s' ctx x) s1 rhs
              val (_, a4) = opt (fn s' => fn x => walk_template_body s' ctx x) s1 body
              val (_, a5) = seq (fn s' => fn x => walk_parent s' ctx x) s1 parents
            in (s1, a1 @ a2 @ a3 @ a4 @ a5) end)
        in (senv, a0 @ a) end
    | A.DExtension (clauses, stats, _) =>
        let val (_, a) = scoped senv (fn s =>
              let
                val (s1, a1) = walk_clauses s ctx clauses
                val (s2, a2) = walk_stats true s1 ctx stats
              in (s2, a1 @ a2) end)
        in (senv, a) end
    | A.DEnumCase (anns, _, _, tps, clauses, parents, _) =>
        let
          val (_, a0) = annots anns
          val (_, a) = scoped senv (fn s =>
            let
              val (s1, a1) = walk_tparams s ctx tps
              val (s2, a2) = walk_clauses s1 ctx clauses
              val (_, a3) = seq (fn s' => fn x => walk_parent s' ctx x) s2 parents
            in (s2, a1 @ a2 @ a3) end)
        in (senv, a0 @ a) end
    | A.DPackage (_, stats, _) =>
        (case stats of
           NONE => (senv, [])
         | SOME ss => let val (_, a) = scoped senv (fn s => walk_stats true s ctx ss) in (senv, a) end)
  end

(* A block-local "val" is visible only after its definition: "walk_def" registers its binders in a
   block (see its DVal case), via the pattern walk. *)

fun analyse_and_eval0 (root : pos A.root) thy =
  let
    val senv0 = get (Context.Theory thy)
    (* The bottom frame is always the top-level root itself, so "ctx" is never empty. *)
    val ctx0 = [root]
    fun finish (senv1, acts) = (Context.theory_map (put senv1) thy, acts)
    fun drop (_, acts) = (thy, acts)
  in
    case root of
      A.Id (id as A.Ident (_, _, ni)) =>
        let val here = check_antiq senv0 ctx0 ni
            val _ = use_term senv0 id
        in (thy, here) end
    | A.Expr e => drop (walk_expr senv0 ctx0 e)
    | A.Type t => drop (walk_type senv0 ctx0 t)
    | A.Stat s => drop (walk_stat false senv0 ctx0 s)
    | A.Pat p => drop (walk_pat false senv0 ctx0 p)
    | A.Unit stats => finish (walk_stats true senv0 ctx0 stats)
  end

fun analyse_and_eval root thy =
  Dispatched_Antiqs.with_fresh (fn () => analyse_and_eval0 root thy)

end
\<close>

subsection\<open>Some Basic Antiquotation Settings\<close>

text\<open>
  The same eight demonstration antiquotations as C11's (\<open>C11_AnaEval.thy\<close>, whose notes on
  each apply unchanged): \<open>probe_senv\<close>, \<open>probe_ast\<close>, \<open>highlight\<close>, \<open>term\<close>, \<open>ML\<close>, \<open>text\<close>,
  \<open>definition\<close> and \<open>lemma\<close>. They are written in a Scala comment as
  \<^verbatim>\<open>//@ term \<open>x + 1 = (2::nat)\<close>\<close> (or in a \<^verbatim>\<open>/*@ ... */\<close> comment, or anywhere in a comment as
  \<^verbatim>\<open>@term \<open>...\<close>\<close>) and attach to the node that begins on the next token; \<^verbatim>\<open>@tag[navi](level)\<close> selects another node and an
  evaluation order exactly as in C11. Handlers are registered under their tag in
  \<open>senv\<close>'s \<open>scala_antiq\<close> table; nothing here knows Scala, only the \<open>root\<close> they are
  handed.
\<close>

declare [[ML_catch_all = true]]

ML\<open>
val OENV = Unsynchronized.ref(SEnv.empty_senv);
val probe_senv = let fun probe (senv, _ , _) (_ : string * Position.T) thy =
                              (OENV := senv; thy)
                 in  SEnv.store_antiq ("probe_senv",  SEnv.lift_theory_antiq probe) end

val SCALA_AST = Unsynchronized.ref((Scala3_Ast.Unit []): (Position.T Scala3_Ast.root) )
val probe_ast = let fun probe (_, ast , l) (_ : string * Position.T) thy =
                              (writeln("Level: "^ Int.toString l);
                               writeln("Read : " ^ Scala3_Pp.pp_root ast);
                               SCALA_AST := ast; thy)
                in  SEnv.store_antiq ("probe_ast",  SEnv.lift_theory_antiq probe) end

val highlight = let fun probe (_, ast , _) (_ : string * Position.T) thy =
                              (Position.report (AnaEval.pos_of_root ast) Markup.intensify;
                               thy)
                in  SEnv.store_antiq ("highlight",  SEnv.lift_theory_antiq probe) end

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
   term is a real Isabelle error positioned in the Scala source. The catch-all
   handler is needed because "Syntax.read_term" fails with "Par_Exn", not
   "ERROR". *)
val SCALA_TERM_PROBE = Unsynchronized.ref (Free ("dummy_term_probe", dummyT) : term)
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
      in (SCALA_TERM_PROBE := t; thy) end
  in SEnv.store_antiq ("term", SEnv.lift_theory_antiq probe) end

(* Runs its body as real ML source, so a definition written in a Scala
   comment becomes a later-visible ML binding - the one handler that needs
   "Context.generic -> Context.generic" rather than "theory -> theory". *)
val ml_antiq =
  let
    fun probe (_, _, _) (body, body_pos) : Context.generic -> Context.generic =
      ML_Context.exec (fn () =>
        ML_Context.eval_source (ML_Compiler.verbose true ML_Compiler.flags)
          (body_source (body, body_pos)))
      #> Local_Theory.propagate_ml_env
  in SEnv.store_antiq ("ML", probe) end

(* Isabelle's "text" command: the body goes through the real
   "Document_Output.output_document" (inner antiquotations are checked,
   hyperlinked and hoverable); the result is stashed, not typeset, for the
   reason given in the Limitations of the C11 manual. *)
val SCALA_TEXT_PROBE = Unsynchronized.ref ([] : Latex.text)
val text_antiq =
  let
    fun probe (_, _, _) (body, body_pos) thy =
      let
        val ctxt = Proof_Context.init_global thy
        val source = body_source (body, body_pos)
        val _ = Context_Position.reports ctxt (Document_Output.document_reports source)
        val latex = Document_Output.output_document ctxt {markdown = true} source
      in (SCALA_TEXT_PROBE := latex; thy) end
  in SEnv.store_antiq ("text", SEnv.lift_theory_antiq probe) end

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
          Scan.option Parse_Spec.constdecl -- (Parse_Spec.opt_thm_name ":" -- Parse.prop) --
            Parse_Spec.if_assumes -- Parse.for_fixes
        val (((decl, spec), prems), params) =
          Parse.read_embedded ctxt keywords parser source
          handle exn =>
            if Exn.is_interrupt exn then Exn.reraise exn
            else error ("definition antiquotation: " ^ Runtime.exn_message exn ^
                         Position.here (AnaEval.pos_of_root ast))
        val lthy' =
          #2 (Specification.definition_cmd {verbose = false} decl params prems spec
                (Named_Target.theory_init thy))
      in Local_Theory.exit_global lthy' end
  in SEnv.store_antiq ("definition", SEnv.lift_theory_antiq probe) end

(* A statement plus one terminal "by" proof, actually proved - proof-carrying
   code: e.g. a property of a VAL abbreviation's value, discharged right where
   the Scala text that motivates it lives. *)
val lemma_antiq =
  let
    val short_statement =
      Parse_Spec.statement -- Parse_Spec.if_statement -- Parse.for_fixes
        >> (fn ((shows, assumes), fixes) =>
          (Binding.empty_atts, [Element.Fixes fixes, Element.Assumes assumes],
           Element.Shows shows))
    val parser =
      short_statement -- (Parse.$$$ "by" |-- Method.parse -- Scan.option Method.parse)
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
          (Specification.theorem_cmd {verbose = false, long = false, kind = Thm.theoremK}
             NONE (K I) binding [] elems concl
             (Named_Target.theory_init thy)
           |> tap (fn _ => (Method.report m1; Option.map Method.report m2 |> ignore))
           |> Proof.global_terminal_proof (m1, m2))
          handle exn => fail exn
      in Local_Theory.exit_global lthy' end
  in SEnv.store_antiq ("lemma", SEnv.lift_theory_antiq probe) end
\<close>

setup\<open>probe_senv\<close>
setup\<open>probe_ast\<close>
setup\<open>highlight\<close>
setup\<open>term_antiq\<close>
setup\<open>text_antiq\<close>
setup\<open>ml_antiq\<close>
setup\<open>definition_antiq\<close>
setup\<open>lemma_antiq\<close>
end
