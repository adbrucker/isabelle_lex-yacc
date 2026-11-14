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


theory MicroRust_AnaEval
  imports "MicroRust_Env"
begin

section\<open>Analyse and Eval\<close>

text\<open>
  \<open>analyse_and_eval\<close> is the MicroRust counterpart of the passes of the same name
  of the other front-ends (\<^verbatim>\<open>C11_AnaEval.thy\<close>, \<^verbatim>\<open>Occam2_AnaEval.thy\<close>,
  \<^verbatim>\<open>Scala3_AnaEval.thy\<close>, whose long explanations apply here and are not
  repeated): a single, purely functional, scoped walk over a parsed \<open>root\<close>,
  threading \<open>renv\<close> through the descent, collecting every antiquotation action
  paired with its \<open>level\<close> instead of applying it, and hyperlinking every name
  use to its declaration. What is specific to Rust:

  \<^item> \<^bold>\<open>Two name spaces.\<close> A type (a struct, enum, trait, type alias, module or
    generic parameter) is looked up in \<open>types\<close>, a value (a function, constant,
    static, variable, parameter) in \<open>terms\<close>. A tuple or unit struct declares a
    name in both. In an expression a lone name is looked up among the values
    first; the first segment of a longer path (\<open>Vec::new\<close>, \<open>m::f\<close>, \<open>E::A\<close>) among
    the types first. Later segments are not resolved (that would need types and
    modules).
  \<^item> \<^bold>\<open>Scoping.\<close> A function (generic parameters, then the parameters, then the
    body), a block, a closure, a match arm (its pattern variables are visible in
    the guard and the body), \<open>if let\<close> and \<open>while let\<close> (the variables scope over
    the body only, not the \<open>else\<close> branch), \<open>for\<close> (over the loop body), a module,
    an \<open>impl\<close> and a \<open>trait\<close> are scopes. Scoping is shadow-and-restore on the two
    tables (the environment is a value, so a scope simply does not hand its
    extension back).
  \<^item> \<^bold>\<open>Forward references.\<close> The items of a module (and of a source file, and of a
    block) are visible throughout it: a function may call one defined further
    down. A \<open>let\<close> is visible only after its statement, and its initializer does
    not see the variables it binds.
  \<^item> \<^bold>\<open>Patterns.\<close> A lone name in a pattern is a binder if it starts with a
    lower-case letter or \<open>_\<close> (or is marked \<open>mut\<close>, or has a sub-pattern \<open>x @ p\<close>);
    otherwise it is a use of a constant, unit struct or variant - Rust's naming
    convention.
  \<^item> \<^bold>\<open>Imports\<close> register the imported names, in both name spaces, at their path
    segment (the alias for a renamed one); a use is hyperlinked to it. A glob
    import registers nothing. The members of an \<open>impl\<close> or \<open>trait\<close> are not
    entered into the environment, but their declaration sites are reported.
  \<^item> \<^bold>\<open>Names that resolve nowhere are not marked.\<close> A Rust name routinely comes from
    the prelude, a glob import or the standard library, none of which this pass
    sees; underlining them would drown the useful markup. Field and method names
    (\<open>e.f\<close>, \<open>e.m()\<close>) are not resolved either (that needs types).
  \<^item> \<^bold>\<open>The source file\<close> (\<open>Crate\<close>) is the one root whose names persist: after
    \<open>microrust\<close> has analysed a file, its top-level names stay in \<open>renv\<close> for the
    following units.
  \<^item> \<^bold>\<open>Closest context and navigation\<close> as in the other front-ends: expressions,
    types, patterns, statements (other than expression statements, which are
    their expression) and items push their own node (\<open>Expr\<close>, \<open>Type\<close>, \<open>Pat\<close>,
    \<open>Stmt\<close>, \<open>Item\<close>); everything else (blocks, arms, parameters, fields, generic
    parameters, ...) uses \<open>hd ctx\<close>. The children of a node are, in source order,
    its sub-expressions, sub-types, sub-patterns, statements and items; blocks
    are flattened into their parent.

\<close>
ML\<open>
structure AnaEval = struct

structure A = MicroRust_Ast
open REnv

type acts = (int * (Context.generic -> Context.generic)) list

fun terms_of (mk {terms, ...} : renv) = terms
fun types_of (mk {types, ...} : renv) = types

fun set_tables (terms', types') (mk {terms = _, types = _, rust_antiq, units}) =
  mk {terms = terms', types = types', rust_antiq = rust_antiq, units = units}

(* The position a "root" itself spans: what a "type_antiq_fun" sees as its own
   "current term". A source file has no single span. *)
fun pos_of_root (A.Id id) = A.pos_of_ident id
  | pos_of_root (A.Expr e) = A.pos_of_expr e
  | pos_of_root (A.Type t) = A.pos_of_type t
  | pos_of_root (A.Pat p) = A.pos_of_pat p
  | pos_of_root (A.Stmt s) = A.pos_of_stmt s
  | pos_of_root (A.Item it) = A.pos_of_item it
  | pos_of_root (A.Body b) = A.pos_of_block b
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
  | category (A.Item _)  = 4
  | category (A.Pat _)   = 5
  | category (A.Body _)  = 6
  | category (A.Crate _) = 7

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

(* The ordered list of children "r"/"d" may navigate into (see the top-of-theory
   note): sub-expressions, sub-types, sub-patterns, statements and items in
   source order; nodes without a "root" counterpart (blocks, arms, parameters,
   fields, generic parameters, ...) are flattened into their parent's list or
   dropped. *)
fun opt_expr eo = (case eo of SOME e => [A.Expr e] | NONE => [])
fun opt_type to = (case to of SOME t => [A.Type t] | NONE => [])
fun opt_pat po = (case po of SOME p => [A.Pat p] | NONE => [])

fun stmt_root s =
  (case s of A.SExpr (e, _, _) => A.Expr e | A.SItem it => A.Item it | _ =>
   A.Stmt s)

fun block_children (A.Block (stmts, tail, _)) = map stmt_root stmts
  @ opt_expr tail
fun opt_block_children bo = (case bo of SOME b => block_children b | NONE => [])

fun garg_children g = (case g of
    A.GType t => [A.Type t] | A.GConst e => [A.Expr e] | A.GBind (_, t) =>
      [A.Type t]
  | A.GLifetime _ => [])
fun gargs_children ga =
  (case ga of NONE => [] | SOME (A.GArgs (_, args)) => maps garg_children args)
fun path_children (A.Path (qself, _, segs, _)) =
  (case qself of
     NONE => []
   | SOME (t, tr) =>
     A.Type t :: (case tr of SOME p => path_children p | NONE => [])) @
  maps (fn A.Seg (_, ga, _) => gargs_children ga) segs

fun bound_children b =
  (case b of A.BTrait (_, p, _) => path_children p | A.BLifetime _ => [])
fun gparam_children g = (case g of
    A.GPLifetime _ => []
  | A.GPType (_, bs, def, _) => maps bound_children bs @ opt_type def
  | A.GPConst (_, t, _) => [A.Type t])
fun where_children w = (case w of
    A.WType (t, bs, _) => A.Type t :: maps bound_children bs
  | A.WLifetime _ => [])
fun fnparam_children p = (case p of
    A.PSelf (_, _, _, t, _) => opt_type t
  | A.PParam (_, pat, t, _) => [A.Pat pat, A.Type t])
fun fielddef_children (A.FieldDef (_, _, _, t, _)) = [A.Type t]
fun fields_children fs = (case fs of
    A.FUnit => [] | A.FNamed fds =>
      maps fielddef_children fds | A.FTuple fds => maps fielddef_children fds)
fun variant_children (A.Variant (_, _, fs, disc, _)) = fields_children fs
  @ opt_expr disc

fun cond_children c =
  (case c of A.CExpr e => [A.Expr e] | A.CLet (p, e, _) => [A.Pat p, A.Expr e])
fun arm_children (A.Arm (_, p, g, body, _)) = A.Pat p :: opt_expr g
  @ [A.Expr body]
fun cparam_children (A.CParam (p, t, _)) = A.Pat p :: opt_type t
fun fieldinit_children (A.FieldInit (_, eo, _)) = opt_expr eo

fun children_of_type t = (case t of
    A.TPath p => path_children p
  | A.TRef (_, _, t1, _) => [A.Type t1]
  | A.TPtr (_, t1, _) => [A.Type t1]
  | A.TTuple (ts, _) => map A.Type ts
  | A.TSlice (t1, _) => [A.Type t1]
  | A.TArray (t1, e, _) => [A.Type t1, A.Expr e]
  | A.TInfer _ => []
  | A.TNever _ => []
  | A.TFn (ts, r, _) => map A.Type ts @ opt_type r
  | A.TImpl (bs, _) => maps bound_children bs
  | A.TDyn (bs, _) => maps bound_children bs
  | A.THol _ => [])

fun children_of_pat p = (case p of
    A.PWild _ => [] | A.PRest _ => [] | A.PHol _ => [] | A.PLit _ => []
  | A.PIdent (_, _, _, sub, _) => opt_pat sub
  | A.PRange (lo, hi, _, _) => opt_pat lo @ opt_pat hi
  | A.PPath pa => path_children pa
  | A.PTupleStruct (pa, ps, _) => path_children pa @ map A.Pat ps
  | A.PStruct (pa, fs, _, _) =>
      path_children pa @ maps (fn A.FieldPat (_, po, _) => opt_pat po) fs
  | A.PTuple (ps, _) => map A.Pat ps
  | A.PSlice (ps, _) => map A.Pat ps
  | A.PRef (_, p1, _) => [A.Pat p1]
  | A.PAlt (ps, _) => map A.Pat ps
  | A.PParen (p1, _) => [A.Pat p1]
  | A.PMut (p1, _) => [A.Pat p1])

fun children_of_expr e = (case e of
    A.ELit _ => [] | A.EHol _ => [] | A.EEps _ => [] | A.ELogLit _ =>
      [] | A.EYield _ => []
  | A.EContinue _ => []
  | A.EPath p => path_children p
  | A.EUnary (_, e1, _) => [A.Expr e1]
  | A.EBinary (_, a, b, _) => [A.Expr a, A.Expr b]
  | A.EAssign (_, a, b, _) => [A.Expr a, A.Expr b]
  | A.ECast (e1, t, _) => [A.Expr e1, A.Type t]
  | A.ETry (e1, _) => [A.Expr e1]
  | A.ECall (f, args, _) => A.Expr f :: map A.Expr args
  | A.EMethod (r, _, ga, args, _) =>
    A.Expr r :: gargs_children ga @ map A.Expr args
  | A.EField (e1, _, _) => [A.Expr e1]
  | A.ETupIdx (e1, _, _) => [A.Expr e1]
  | A.EIndex (a, b, _) => [A.Expr a, A.Expr b]
  | A.ERange (lo, hi, _, _) => opt_expr lo @ opt_expr hi
  | A.ETuple (es, _) => map A.Expr es
  | A.EParen (e1, _) => [A.Expr e1]
  | A.EArray (es, _) => map A.Expr es
  | A.ERepeat (a, b, _) => [A.Expr a, A.Expr b]
  | A.EStruct (p, fs, base, _) =>
    path_children p @ maps fieldinit_children fs @ opt_expr base
  | A.EBlock (_, b, _) => block_children b
  | A.EUnsafe (b, _) => block_children b
  | A.ESeq (b, _) => block_children b
  | A.EIf (c, b, els, _) => cond_children c @ block_children b @ opt_expr els
  | A.EWhile (_, c, b, _) => cond_children c @ block_children b
  | A.ELoop (_, b, _) => block_children b
  | A.EFor (_, p, it, b, _) => [A.Pat p, A.Expr it] @ block_children b
  | A.EMatch (s, arms, _) => A.Expr s :: maps arm_children arms
  | A.EClosure (_, ps, ret, body, _) =>
    maps cparam_children ps @ opt_type ret @ [A.Expr body]
  | A.EReturn (eo, _) => opt_expr eo
  | A.EBreak (_, eo, _) => opt_expr eo
  | A.ELog (a, b, _) => [A.Expr a, A.Expr b]
  | A.EMacro (p, _, args, _) => path_children p @ map A.Expr args
  | A.EMacroRepeat (p, a, b, _) => path_children p @ [A.Expr a, A.Expr b]
  | A.EMatches (e1, p, _) => [A.Expr e1, A.Pat p]
  | A.EAttr (_, e1, _) => [A.Expr e1])

fun children_of_stmt s = (case s of
    A.SLet (_, p, t, init, els, _) =>
      A.Pat p :: opt_type t @ opt_expr init @ opt_block_children els
  | A.SExpr (e, _, _) => [A.Expr e]
  | A.SItem it => [A.Item it]
  | A.SEmpty _ => [])

fun children_of_item (A.MkItem (_, _, kind, _)) = (case kind of
    A.IFn (_, _, gps, params, ret, wh, body) =>
      maps gparam_children gps @ maps fnparam_children params @ opt_type ret
        @ maps where_children wh @
      opt_block_children body
  | A.IStruct (_, gps, wh, fs) =>
    maps gparam_children gps @ maps where_children wh @ fields_children fs
  | A.IEnum (_, gps, wh, vs) =>
    maps gparam_children gps @ maps where_children wh @ maps variant_children vs
  | A.IImpl (_, gps, tr, t, wh, items) =>
      maps gparam_children gps
        @ (case tr of SOME p => path_children p | NONE => []) @ [A.Type t] @
      maps where_children wh @ map A.Item items
  | A.ITrait (_, _, gps, sups, wh, items) =>
      maps gparam_children gps @ maps bound_children sups
        @ maps where_children wh @ map A.Item items
  | A.IConst (_, t, e) => A.Type t :: opt_expr e
  | A.IStatic (_, _, t, e) => A.Type t :: opt_expr e
  | A.ITypeAlias (_, gps, bs, t) =>
    maps gparam_children gps @ maps bound_children bs @ opt_type t
  | A.IUse _ => []
  | A.IMod (_, items) => (case items of SOME is => map A.Item is | NONE => []))

fun children_of _ (A.Expr e) = children_of_expr e
  | children_of _ (A.Type t) = children_of_type t
  | children_of _ (A.Pat p) = children_of_pat p
  | children_of _ (A.Stmt s) = children_of_stmt s
  | children_of _ (A.Item it) = children_of_item it
  | children_of _ (A.Body b) = block_children b
  | children_of _ (A.Crate items) = map A.Item items
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
      error ("select_ast: navigation string ends with a dangling \"r\", " ^
             "expected a final \"d\"" ^ Position.here antiq_pos)

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
   "ni"'s comment list by tag in "renv"'s "rust_antiq", instantiates it with
   (renv, select_ast tag_pos navi ctx, level), and pairs the resulting
   "Context.generic -> Context.generic" with its level - "select_ast" (and so
   "children_of", which can "error") is only forced when an "Antiquotation"
   genuinely needs it, never for an ordinary "Raw_txt" or an empty comment list.
   "tag_pos" (the antiquotation's own tag position, previously discarded here)
   is passed through purely so a "select_ast" navigation error can be reported
   at "@tag[navi] ..." itself rather than at whatever AST node the failed
   navigation happened to reach - see the note on "select_rd". An
   "Antiquotation" already dispatched earlier in this same walk (see
   "Dispatched_Antiqs" above) is silently skipped the second (or third, ...)
   time some other node sharing its position reaches it - whichever node the
   walk reaches *first* (which, since every "walk_*" checks its own
   antiquotations before recursing into its children, is always the outermost of
   any nodes genuinely tied at one position) is the one that wins. The handler
   receives "(body, body_pos)", not just "body" - see "type_antiq_fun" in
   MicroRust_Env.thy for why the cartouche's own position now travels all the
   way to the handler instead of being discarded here - and the *resolved* AST
   node ("select_ast tag_pos navi ctx"), not the raw navi list: a handler is
   never itself responsible for interpreting "up"/"Up"/ "right"/"down". *)
fun check_antiq renv (ctx : pos A.root list) (ni : pos A.nodeInfo)
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
                let val mk {rust_antiq, ...} = renv in
                  case Symtab.lookup rust_antiq tag of
                    NONE =>
                      error ("analyse_and_eval: no antiquotation handler " ^
                             "registered for tag " ^ quote tag)
                  | SOME antiq_fun =>
                      (Dispatched_Antiqs.mark c;
                       SOME (level,
                             antiq_fun
                               (renv, select_ast tag_pos navi ctx, level)
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

(* Hyperlinks a use of "name" to its declaration, if it resolves; nothing is
   reported if it does not (see the top-of-theory note). *)
fun use_in table name use_pos =
  (case Symtab.lookup table name of
     NONE => ()
   | SOME k =>
       Position.report (name_range (name, use_pos))
         (Position.entity_markup (describe_kind k)
          (name, name_range (name, pos_of_kind k))))

fun use_term renv (A.Ident (name, _, ni)) =
  use_in (terms_of renv) name (A.pos_of_NodeInfo ni)
fun use_type renv (A.Ident (name, _, ni)) =
  use_in (types_of renv) name (A.pos_of_NodeInfo ni)

fun reg_term mk_kind renv (A.Ident (name, _, ni)) =
  let
    val pos = A.pos_of_NodeInfo ni
    val kind = mk_kind pos
    val _ = report_decl (describe_kind kind) name pos
  in set_tables (Symtab.update (name, kind) (terms_of renv), types_of renv)
    renv end

fun reg_type mk_kind renv (A.Ident (name, _, ni)) =
  let
    val pos = A.pos_of_NodeInfo ni
    val kind = mk_kind pos
    val _ = report_decl (describe_kind kind) name pos
  in set_tables (terms_of renv, Symtab.update (name, kind) (types_of renv))
    renv end

(* An imported name: registered in both name spaces, at its selector. *)
fun reg_import renv (id as A.Ident (name, _, ni)) =
  let
    val pos = A.pos_of_NodeInfo ni
    val kind = Import pos
    val _ = report_decl (describe_kind kind) name pos
  in set_tables
    (Symtab.update (name, kind) (terms_of renv),
     Symtab.update (name, kind) (types_of renv)) renv end

(* Runs "f" in a nested scope: both tables are restored on exit. *)
fun scoped renv f =
  let
    val (terms, types) = (terms_of renv, types_of renv)
    val (renv1, acts) = f renv
  in (set_tables (terms, types) renv1, acts) end

fun seq (f : renv -> 'a -> renv * acts) renv xs =
  fold (fn x => fn (e, acc) => let val (e', a) = f e x in (e', acc @ a) end) xs
    (renv, [])

fun opt f renv x = (case x of NONE => (renv, []) | SOME y => f renv y)

fun opt_list x = (case x of SOME y => [y] | NONE => [])

(* A compact wrapper for the antiquotations a node carries (its "nodeInfo"). *)
fun chk renv ctx ni = check_antiq renv ctx ni

(* A name starting with a lower-case letter or "_" in a pattern is a binder;
   Rust's naming convention (enforced by a lint) makes everything else a
   constant, a unit struct or a variant. *)
fun is_binder_name s = s <> ""
  andalso (let val c = String.sub (s, 0) in Char.isLower c orelse c = #"_" end)

val keyword_names = ["self", "Self", "super", "crate"]

datatype order = Term_first | Type_first

(* Hyperlinks the use of a name to its declaration, trying the name space the
   position makes more likely first. *)
fun use_name senv order (A.Ident (name, _, ni)) =
  if member (op =) keyword_names name then ()
  else
    let
      val tables =
        (case order of
           Term_first => [terms_of senv, types_of senv]
         | Type_first => [types_of senv, terms_of senv])
    in
      (case List.find (fn t => Symtab.defined t name) tables of
         SOME t => use_in t name (A.pos_of_NodeInfo ni)
       | NONE => ())
    end

(* A name entered into the second name space without a second declaration site
   (a tuple or unit struct is a type and a value). *)
fun alias_term mk_kind senv (A.Ident (name, _, ni)) =
  set_tables
    (Symtab.update (name, mk_kind (A.pos_of_NodeInfo ni)) (terms_of senv),
     types_of senv) senv

fun decl_only mk_kind (A.Ident (name, _, ni)) =
  let val pos = A.pos_of_NodeInfo ni
  in report_decl (describe_kind (mk_kind pos)) name pos end

fun optl f x = (case x of NONE => [] | SOME y => f y)

fun use_names u = (case u of
    A.UName (path, alias, _) =>
      (case alias of SOME a => [a] | NONE => [List.last path])
  | A.UGlob _ => []
  | A.UGroup (_, us, _) => maps use_names us)

(* The names an item declares, visible throughout the scope it belongs to
   (forward references). *)
fun predeclare senv (A.MkItem (_, _, kind, _)) =
  (case kind of
     A.IFn (_, name, _, _, _, _, _) => reg_term Fn senv name
   | A.IStruct (name, _, _, fs) =>
       let val s1 = reg_type Struct senv name
       in (case fs of A.FNamed _ => s1 | _ => alias_term Struct s1 name) end
   | A.IEnum (name, _, _, _) => reg_type Enum senv name
   | A.IImpl _ => senv
   | A.ITrait (_, name, _, _, _, _) => reg_type Trait senv name
   | A.IConst (name, _, _) => reg_term Const senv name
   | A.IStatic (_, name, _, _) => reg_term Static senv name
   | A.ITypeAlias (name, _, _, _) => reg_type Alias senv name
   | A.IUse u =>
       fold (fn id => fn s =>
             if A.ident_name id = "self" then s
               else reg_import s id) (use_names u) senv
   | A.IMod (name, _) => reg_type Mod senv name)

fun predeclare_items senv items =
  fold (fn it => fn s => predeclare s it) items senv

fun walk_path order senv ctx (A.Path (qself, global, segs, _)) : acts =
  let
    val a1 = (case qself of
                NONE => []
              | SOME (t, tr) =>
                walk_type senv ctx t @ optl (walk_path Type_first senv ctx) tr)
    val _ =
      if global orelse is_some qself then ()
      else (case segs of
              A.Seg (id, _, _) :: _ =>
                use_name senv (if length segs > 1 then Type_first else order) id
            | [] => ())
    val a2 = maps (fn A.Seg (_, ga, _) => walk_gargs senv ctx ga) segs
  in a1 @ a2 end

and walk_gargs senv ctx ga : acts =
  (case ga of
     NONE => []
   | SOME (A.GArgs (_, args)) =>
       maps (fn g => (case g of
                        A.GType t => walk_type senv ctx t
                      | A.GConst e => walk_expr senv ctx e
                      | A.GBind (_, t) => walk_type senv ctx t
                      | A.GLifetime _ => [])) args)

and walk_bound senv ctx b : acts =
  (case b of A.BTrait (_, p, _) =>
   walk_path Type_first senv ctx p | A.BLifetime _ => [])

and walk_type senv ctx (t : pos A.rType) : acts =
  let
    val ctx' = A.Type t :: ctx
    val here = chk senv ctx' (A.nodeInfo_of_type t)
    val w = walk_type senv ctx'
  in
    here @
    (case t of
       A.TPath p => walk_path Type_first senv ctx' p
     | A.TRef (_, _, t1, _) => w t1
     | A.TPtr (_, t1, _) => w t1
     | A.TTuple (ts, _) => maps w ts
     | A.TSlice (t1, _) => w t1
     | A.TArray (t1, e, _) => w t1 @ walk_expr senv ctx' e
     | A.TInfer _ => []
     | A.TNever _ => []
     | A.THol _ => []
     | A.TFn (ts, r, _) => maps w ts @ optl w r
     | A.TImpl (bs, _) => maps (walk_bound senv ctx') bs
     | A.TDyn (bs, _) => maps (walk_bound senv ctx') bs)
  end

(* A pattern binds its variables (kind "mk_kind") into the environment it
   returns. *)
and walk_pat mk_kind senv ctx (p : pos A.rPat) : renv * acts =
  let
    val ctx' = A.Pat p :: ctx
    val here = chk senv ctx' (A.nodeInfo_of_pat p)
    fun many s ps = seq (fn s' => fn p1 => walk_pat mk_kind s' ctx' p1) s ps
    val (senv', acts) =
      (case p of
         A.PWild _ => (senv, [])
       | A.PRest _ => (senv, [])
       | A.PHol _ => (senv, [])
       | A.PLit _ => (senv, [])
       | A.PIdent (r, m, id, sub, _) =>
           let
             val s1 =
               if r orelse m orelse is_some sub
                 orelse is_binder_name (A.ident_name id)
               then reg_term mk_kind senv id
               else (use_name senv Term_first id; senv)
           in (case sub of SOME p1 => walk_pat mk_kind s1 ctx' p1 | NONE =>
               (s1, [])) end
       | A.PRange (lo, hi, _, _) => many senv (opt_list lo @ opt_list hi)
       | A.PPath pa => (senv, walk_path Term_first senv ctx' pa)
       | A.PTupleStruct (pa, ps, _) =>
           let
             val a1 = walk_path Term_first senv ctx' pa
             val (s2, a2) = many senv ps
           in (s2, a1 @ a2) end
       | A.PStruct (pa, fs, _, _) =>
           let
             val a1 = walk_path Type_first senv ctx' pa
             val (s2, a2) =
               seq (fn s => fn (A.FieldPat (id, po, _)) =>
                      (case po of
                         NONE => (reg_term mk_kind s id, [])
                       | SOME p1 => walk_pat mk_kind s ctx' p1)) senv fs
           in (s2, a1 @ a2) end
       | A.PTuple (ps, _) => many senv ps
       | A.PSlice (ps, _) => many senv ps
       | A.PRef (_, p1, _) => walk_pat mk_kind senv ctx' p1
       | A.PAlt (ps, _) => many senv ps
       | A.PParen (p1, _) => walk_pat mk_kind senv ctx' p1
       | A.PMut (p1, _) => walk_pat mk_kind senv ctx' p1)
  in (senv', here @ acts) end

and walk_cond senv ctx c : renv * acts =
  (case c of
     A.CExpr e => (senv, walk_expr senv ctx e)
   | A.CLet (p, e, ni) =>
       let
         val a0 = chk senv ctx ni
         val a1 = walk_expr senv ctx e
         val (s1, a2) = walk_pat Local senv ctx p
       in (s1, a0 @ a1 @ a2) end)

and walk_expr senv ctx (e : pos A.rExpr) : acts =
  let
    val ctx' = A.Expr e :: ctx
    val here = chk senv ctx' (A.nodeInfo_of_expr e)
    val w = walk_expr senv ctx'
  in
    here @
    (case e of
       A.ELit _ => []
     | A.EHol _ => []
     | A.EEps _ => []
     | A.ELogLit _ => []
     | A.EYield _ => []
     | A.EContinue _ => []
     | A.EPath p => walk_path Term_first senv ctx' p
     | A.EUnary (_, e1, _) => w e1
     | A.EBinary (_, a, b, _) => w a @ w b
     | A.EAssign (_, a, b, _) => w a @ w b
     | A.ECast (e1, t, _) => w e1 @ walk_type senv ctx' t
     | A.ETry (e1, _) => w e1
     | A.ECall (f, args, _) => w f @ maps w args
     | A.EMethod (r, _, ga, args, _) =>
       w r @ walk_gargs senv ctx' ga @ maps w args
     | A.EField (e1, _, _) => w e1
     | A.ETupIdx (e1, _, _) => w e1
     | A.EIndex (a, b, _) => w a @ w b
     | A.ERange (lo, hi, _, _) => optl w lo @ optl w hi
     | A.ETuple (es, _) => maps w es
     | A.EParen (e1, _) => w e1
     | A.EArray (es, _) => maps w es
     | A.ERepeat (a, b, _) => w a @ w b
     | A.EStruct (p, fs, base, _) =>
         walk_path Type_first senv ctx' p @
         maps (fn A.FieldInit (id, eo, ni) =>
                 chk senv ctx' ni
                   @ (case eo of SOME e1 => w e1 | NONE =>
                      (use_name senv Term_first id; []))) fs @
         optl w base
     | A.EBlock (_, b, _) => walk_block senv ctx' b
     | A.EUnsafe (b, _) => walk_block senv ctx' b
     | A.ESeq (b, _) => walk_block senv ctx' b
     | A.EIf (c, b, els, _) =>
         let val (s1, a1) = walk_cond senv ctx' c
         in a1 @ walk_block s1 ctx' b @ optl w els end
     | A.EWhile (_, c, b, _) =>
         let val (s1, a1) = walk_cond senv ctx' c
         in a1 @ walk_block s1 ctx' b end
     | A.ELoop (_, b, _) => walk_block senv ctx' b
     | A.EFor (_, p, it, b, _) =>
         let
           val a1 = w it
           val (s1, a2) = walk_pat Local senv ctx' p
         in a1 @ a2 @ walk_block s1 ctx' b end
     | A.EMatch (s, arms, _) => w s @ maps (walk_arm senv ctx') arms
     | A.EClosure (_, ps, ret, body, _) =>
         let
           val (s1, a1) =
             seq (fn s => fn (A.CParam (p, t, ni)) =>
                    let
                      val a0 = chk s ctx' ni
                      val (s1, a1) = walk_pat Local s ctx' p
                      val a2 = optl (walk_type s ctx') t
                    in (s1, a0 @ a1 @ a2) end) senv ps
           val a3 = optl (walk_type senv ctx') ret
         in a1 @ a3 @ walk_expr s1 ctx' body end
     | A.EReturn (eo, _) => optl w eo
     | A.EBreak (_, eo, _) => optl w eo
     | A.ELog (a, b, _) => w a @ w b
     | A.EMacro (p, _, args, _) =>
       walk_path Term_first senv ctx' p @ maps w args
     | A.EMacroRepeat (p, a, b, _) =>
       walk_path Term_first senv ctx' p @ w a @ w b
     | A.EMatches (e1, p, _) => w e1 @ #2 (walk_pat Local senv ctx' p)
     | A.EAttr (_, e1, _) => w e1)
  end

and walk_arm senv ctx (A.Arm (_, p, g, body, ni)) : acts =
  let
    val a0 = chk senv ctx ni
    val (s1, a1) = walk_pat Local senv ctx p
  in a0 @ a1 @ optl (walk_expr s1 ctx) g @ walk_expr s1 ctx body end

(* A block is a scope: its items are visible throughout (local functions may be
   mutually recursive), a "let" only after its statement. *)
and walk_block senv ctx (A.Block (stmts, tail, ni)) : acts =
  let
    val a0 = chk senv ctx ni
    val items = List.mapPartial (fn A.SItem it => SOME it | _ => NONE) stmts
    val s0 = predeclare_items senv items
    val (s1, a1) = seq (fn s => fn st => walk_stmt s ctx st) s0 stmts
  in a0 @ a1 @ optl (walk_expr s1 ctx) tail end

and walk_stmt senv ctx (s : pos A.rStmt) : renv * acts =
  (case s of
     A.SLet (_, p, t, init, els, ni) =>
       let
         val ctx' = A.Stmt s :: ctx
         val here = chk senv ctx' ni
         val a1 = optl (walk_type senv ctx') t
         val a2 = optl (walk_expr senv ctx') init
         val a3 = optl (walk_block senv ctx') els
         val (s1, a4) = walk_pat Local senv ctx' p
       in (s1, here @ a1 @ a2 @ a3 @ a4) end
   | A.SExpr (e, _, _) => (senv, walk_expr senv ctx e)
   | A.SItem it => (senv, walk_item senv ctx it)
   | A.SEmpty _ => (senv, []))

(* The generic parameters are in scope in the rest of the item. *)
and walk_gparams senv ctx gps : renv * acts =
  let
    val s1 =
      fold (fn g => fn s =>
              (case g of
                 A.GPType (id, _, _, _) => reg_type Tparam s id
               | A.GPConst (id, _, _) => reg_term Tparam s id
               | A.GPLifetime _ => s)) gps senv
    val acts =
      maps (fn g =>
              (case g of
                 A.GPType (_, bs, def, ni) =>
                   chk s1 ctx ni @ maps (walk_bound s1 ctx) bs
                     @ optl (walk_type s1 ctx) def
               | A.GPConst (_, t, ni) => chk s1 ctx ni @ walk_type s1 ctx t
               | A.GPLifetime (_, _, ni) => chk s1 ctx ni)) gps
  in (s1, acts) end

and walk_where senv ctx w : acts =
  (case w of
     A.WType (t, bs, ni) =>
       chk senv ctx ni @ walk_type senv ctx t @ maps (walk_bound senv ctx) bs
   | A.WLifetime (_, _, ni) => chk senv ctx ni)

and walk_fields senv ctx fs : acts =
  (case fs of
     A.FUnit => []
   | A.FNamed fds => maps (walk_fielddef senv ctx) fds
   | A.FTuple fds => maps (walk_fielddef senv ctx) fds)

and walk_fielddef senv ctx (A.FieldDef (_, _, name, t, ni)) : acts =
  chk senv ctx ni
    @ (case name of SOME id => (decl_only Local id; []) | NONE => [])
      @ walk_type senv ctx t

and walk_fnparam senv ctx p : renv * acts =
  (case p of
     A.PSelf (_, _, _, t, ni) =>
       (senv, chk senv ctx ni @ optl (walk_type senv ctx) t)
   | A.PParam (_, pat, t, ni) =>
       let
         val a0 = chk senv ctx ni
         val a1 = walk_type senv ctx t
         val (s1, a2) = walk_pat Param senv ctx pat
       in (s1, a0 @ a1 @ a2) end)

and walk_items senv ctx items : renv * acts =
  let val s1 = predeclare_items senv items
  in (s1, maps (walk_item s1 ctx) items) end

(* An associated item (of an "impl" or a "trait") declares no name in the
   environment, but its declaration site is reported. *)
and walk_assoc senv ctx (it as A.MkItem (_, _, kind, _)) : acts =
  let
    val _ = (case kind of
               A.IFn (_, name, _, _, _, _, _) => decl_only Fn name
             | A.IConst (name, _, _) => decl_only Const name
             | A.ITypeAlias (name, _, _, _) => decl_only Alias name
             | _ => ())
  in walk_item senv ctx it end

and walk_item senv ctx (it as A.MkItem (_, _, kind, ni)) : acts =
  let
    val ctx' = A.Item it :: ctx
    val here = chk senv ctx' ni
  in
    here @
    (case kind of
       A.IFn (_, _, gps, params, ret, wh, body) =>
         let
           val (s1, a1) = walk_gparams senv ctx' gps
           val (s2, a2) = seq (fn s => fn p => walk_fnparam s ctx' p) s1 params
           val a3 = optl (walk_type s2 ctx') ret
           val a4 = maps (walk_where s2 ctx') wh
           val a5 = optl (walk_block s2 ctx') body
         in a1 @ a2 @ a3 @ a4 @ a5 end
     | A.IStruct (_, gps, wh, fs) =>
         let
           val (s1, a1) = walk_gparams senv ctx' gps
         in a1 @ maps (walk_where s1 ctx') wh @ walk_fields s1 ctx' fs end
     | A.IEnum (_, gps, wh, vs) =>
         let
           val (s1, a1) = walk_gparams senv ctx' gps
           val a2 = maps (walk_where s1 ctx') wh
           val a3 =
             maps (fn A.Variant (_, id, fs, disc, vni) =>
                     (decl_only Variant id;
                      chk s1 ctx' vni @ walk_fields s1 ctx' fs
                        @ optl (walk_expr s1 ctx') disc)) vs
         in a1 @ a2 @ a3 end
     | A.IImpl (_, gps, tr, t, wh, items) =>
         let
           val (s1, a1) = walk_gparams senv ctx' gps
           val a2 = optl (walk_path Type_first s1 ctx') tr
           val a3 = walk_type s1 ctx' t
           val a4 = maps (walk_where s1 ctx') wh
           val a5 = maps (walk_assoc s1 ctx') items
         in a1 @ a2 @ a3 @ a4 @ a5 end
     | A.ITrait (_, _, gps, sups, wh, items) =>
         let
           val (s1, a1) = walk_gparams senv ctx' gps
           val a2 = maps (walk_bound s1 ctx') sups
           val a3 = maps (walk_where s1 ctx') wh
           val a4 = maps (walk_assoc s1 ctx') items
         in a1 @ a2 @ a3 @ a4 end
     | A.IConst (_, t, e) =>
       walk_type senv ctx' t @ optl (walk_expr senv ctx') e
     | A.IStatic (_, _, t, e) =>
       walk_type senv ctx' t @ optl (walk_expr senv ctx') e
     | A.ITypeAlias (_, gps, bs, t) =>
         let val (s1, a1) = walk_gparams senv ctx' gps
         in a1 @ maps (walk_bound s1 ctx') bs @ optl (walk_type s1 ctx') t end
     | A.IUse _ => []
     | A.IMod (_, items) =>
         (case items of
            NONE => []
          | SOME is => #2 (walk_items senv ctx' is)))
  end

fun analyse_and_eval0 (root : pos A.root) thy =
  let
    val renv0 = get (Context.Theory thy)
    (* The bottom frame is always the top-level root itself, so "ctx" is never
       empty. *)
    val ctx0 = [root]
    fun finish (renv1, acts) = (Context.theory_map (put renv1) thy, acts)
    fun drop acts = (thy, acts)
  in
    case root of
      A.Id (id as A.Ident (_, _, ni)) =>
        let val here = check_antiq renv0 ctx0 ni
            val _ = use_name renv0 Term_first id
        in (thy, here) end
    | A.Expr e => drop (walk_expr renv0 ctx0 e)
    | A.Type t => drop (walk_type renv0 ctx0 t)
    | A.Pat p => drop (#2 (walk_pat Local renv0 ctx0 p))
    | A.Stmt s => drop (#2 (walk_stmt renv0 ctx0 s))
    | A.Item it => drop (walk_item (predeclare renv0 it) ctx0 it)
    | A.Body b => drop (walk_block renv0 ctx0 b)
    | A.Crate items => finish (walk_items renv0 ctx0 items)
  end

fun analyse_and_eval root thy =
  Dispatched_Antiqs.with_fresh (fn () => analyse_and_eval0 root thy)

end
\<close>

subsection\<open>Some Basic Antiquotation Settings\<close>

text\<open>
  The same eight demonstration antiquotations as C11's (\<open>C11_AnaEval.thy\<close>, whose
  notes on each apply unchanged): \<open>probe_renv\<close>, \<open>probe_ast\<close>, \<open>highlight\<close>,
  \<open>term\<close>, \<open>ML\<close>, \<open>text\<close>, \<open>definition\<close> and \<open>lemma\<close>. They are written in a
  MicroRust comment as \<^verbatim>\<open>//@ term \<open>x + 1 = (2::nat)\<close>\<close> (or in a \<^verbatim>\<open>/*@ ... */\<close>
  comment, or anywhere in a comment as \<^verbatim>\<open>@term \<open>...\<close>\<close>) and attach to the node
  that begins on the next token; \<^verbatim>\<open>@tag[navi](level)\<close> selects another node and an
  evaluation order exactly as in C11. Handlers are registered under their tag in
  \<open>renv\<close>'s \<open>rust_antiq\<close> table; nothing here knows MicroRust, only the \<open>root\<close>
  they are handed.
\<close>

declare [[ML_catch_all = true]]

ML\<open>
val RENV = Unsynchronized.ref(REnv.empty_renv);
val probe_renv = let fun probe (renv, _ , _) (_ : string * Position.T) thy =
                              (RENV := renv; thy)
                 in  REnv.store_antiq
                   ("probe_renv",  REnv.lift_theory_antiq probe) end

val RUST_AST =
  Unsynchronized.ref((MicroRust_Ast.Crate []): (Position.T MicroRust_Ast.root) )
val probe_ast = let fun probe (_, ast , l) (_ : string * Position.T) thy =
                              (writeln("Level: "^ Int.toString l);
                               writeln("Read : " ^ MicroRust_Pp.pp_root ast);
                               RUST_AST := ast; thy)
                in  REnv.store_antiq
                  ("probe_ast",  REnv.lift_theory_antiq probe) end

val highlight = let fun probe (_, ast , _) (_ : string * Position.T) thy =
                              (Position.report (AnaEval.pos_of_root ast)
                               Markup.intensify;
                               thy)
                in  REnv.store_antiq
                  ("highlight",  REnv.lift_theory_antiq probe) end

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
   term is a real Isabelle error positioned in the MicroRust source. The
   catch-all handler is needed because "Syntax.read_term" fails with "Par_Exn",
   not "ERROR". *)
val RUST_TERM_PROBE =
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
      in (RUST_TERM_PROBE := t; thy) end
  in REnv.store_antiq ("term", REnv.lift_theory_antiq probe) end

(* Runs its body as real ML source, so a definition written in a MicroRust
   comment becomes a later-visible ML binding - the one handler that needs
   "Context.generic -> Context.generic" rather than "theory -> theory". *)
val ml_antiq =
  let
    fun probe (_, _, _) (body, body_pos) : Context.generic -> Context.generic =
      ML_Context.exec (fn () =>
        ML_Context.eval_source (ML_Compiler.verbose true ML_Compiler.flags)
          (body_source (body, body_pos)))
      #> Local_Theory.propagate_ml_env
  in REnv.store_antiq ("ML", probe) end

(* Isabelle's "text" command: the body goes through the real
   "Document_Output.output_document" (inner antiquotations are checked,
   hyperlinked and hoverable); the result is stashed, not typeset, for the
   reason given in the Limitations of the C11 manual. *)
val RUST_TEXT_PROBE = Unsynchronized.ref ([] : Latex.text)
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
      in (RUST_TEXT_PROBE := latex; thy) end
  in REnv.store_antiq ("text", REnv.lift_theory_antiq probe) end

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
  in REnv.store_antiq ("definition", REnv.lift_theory_antiq probe) end

(* A statement plus one terminal "by" proof, actually proved - proof-carrying
   code: e.g. a property of a VAL abbreviation's value, discharged right where
   the MicroRust text that motivates it lives. *)
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
  in REnv.store_antiq ("lemma", REnv.lift_theory_antiq probe) end
\<close>

setup\<open>probe_renv\<close>
setup\<open>probe_ast\<close>
setup\<open>highlight\<close>
setup\<open>term_antiq\<close>
setup\<open>text_antiq\<close>
setup\<open>ml_antiq\<close>
setup\<open>definition_antiq\<close>
setup\<open>lemma_antiq\<close>
end
