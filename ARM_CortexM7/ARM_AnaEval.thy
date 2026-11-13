(******************************************************************************
 * Copyright (c) University of Paris-Saclay
 *
 * All rights reserved.
 *
 * Authors: Burkhart Wolff, Claude Sonnet 5.5
 *
 * This is an LLM-generated replication of the Isabelle/C version 2 design to
 * the programming language Java (language version 25). It provides an efficient
 * parser for Java, deeply integrated into the Isabelle/PIDE document model,
 * allowing external files as well as in-theory code-snippets which are
 * transparent to the underlying theory. It provides an API for the generated
 * AST’s, and an API to hook up semantic backends that compile these AST’s to
 * theory extensions in Isabelle/HOL. Members of the family come with a
 * Java-specific antiquotation mechanism allowing programmable links to the
 * semantic backends as necessary for support of program-annotations with HOL
 * formulas.
 *
 * This session is part of the Isabelle Programming Language Toolkit
 * (Isabelle/PLTk). The generation has been done with Claude Sonnet 5.5; while
 * the replicants come with a detailed (generated) test-suite for Java, I
 * expect that human users might find errors or inconsistencies; experience
 * reports and comments are therefore welcomed. The concrete and abstract
 * syntax, being generated from Isabelle/LexYacc specifications, should be easy
 * to modify and adapt.
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


theory ARM_AnaEval
  imports "ARM_Env" "ARM_Parser"
begin

section\<open>The ARM Analysis: Scoping, Hyperlinking, Antiquotation Dispatch\<close>

text\<open>
  \<^verbatim>\<open>AnaEval\<close> is the assembler counterpart of the analysis of the other front-ends: a single,
  purely functional walk over a parsed root that fills the environment \<open>armenv\<close> as it goes, reports
  every declaration and every resolved use as Isabelle entity markup (so that hovering and
  click-through work in jEdit), and collects the antiquotations of the comments as actions that
  are run in the order of their levels. Its pieces:

  \<^item> \<^bold>\<open>Symbols.\<close> The labels (\<open>start:\<close>) and the symbols that \<open>=\<close>, \<open>.set\<close>, \<open>.equ\<close>, \<open>.equiv\<close>,
    \<open>.thumb_set\<close> and \<open>.comm\<close> define are visible in the whole unit, before and after their
    definition: they are entered before the walk. A symbol that is defined more than once
    (\<open>.set\<close> may redefine) is linked to its first definition until the walk reaches the next one.
  \<^item> \<^bold>\<open>Numeric labels.\<close> \<open>1:\<close> may be defined many times; \<open>1b\<close> refers to the nearest definition
    before and \<open>1f\<close> to the nearest after, by position in the text.
  \<^item> \<^bold>\<open>Register aliases and macros\<close> are visible from their definition on, in the order of the
    text, and end at \<open>.unreq\<close> and \<open>.purgem\<close>. A macro hides the instruction of its name (the call
    of a macro is hyperlinked to the macro, and its keyword arguments \<open>name=value\<close> to the
    parameters).
  \<^item> \<^bold>\<open>Macro parameters.\<close> In the body of a macro (and of \<open>.irp\<close>, \<open>.irpc\<close>) \<^verbatim>\<open>\name\<close> refers to a
    parameter, wherever it stands in a word: \<^verbatim>\<open>mov r\n, #\v\<close>, \<^verbatim>\<open>\name\():\<close>. A name that contains
    such a reference is a template and declares and resolves nothing else.
  \<^item> \<^bold>\<open>The top level persists.\<close> After \<open>arm\<close> has analysed a file (or \<open>arm_stmt\<close> some statements),
    the symbols, aliases and macros it defines at the top level stay in \<open>armenv\<close> for the
    following commands, as the files of a program do for each other. A macro body does not leave
    anything behind.
  \<^item> \<^bold>\<open>Closest context and navigation\<close> as in the other front-ends: expressions, operands and
    statements push their own node (\<open>Expr\<close>, \<open>Operand\<close>, \<open>Stmt\<close>); everything else (parameters of
    macros, branches of a conditional) uses \<open>hd ctx\<close>. The children of a node are, in source
    order, its operands, expressions and statements; the bodies of blocks are flattened into the
    children of the block.

  A name that resolves nowhere is \<^emph>\<open>not\<close> marked as an error: in assembly it very often comes from
  another file or from the linker script.
\<close>

ML\<open>
structure AnaEval = struct

structure A = ARM_Ast
open ARMEnv

type acts = (int * (Context.generic -> Context.generic)) list

fun names_of (mk {names, ...} : armenv) = names
fun macros_of (mk {macros, ...} : armenv) = macros
fun locals_of (mk {locals, ...} : armenv) = locals

fun set_names names' (mk {names = _, macros, locals, arm_antiq, units}) =
  mk {names = names', macros = macros, locals = locals, arm_antiq = arm_antiq, units = units}
fun set_macros macros' (mk {names, macros = _, locals, arm_antiq, units}) =
  mk {names = names, macros = macros', locals = locals, arm_antiq = arm_antiq, units = units}
fun set_locals locals' (mk {names, macros, locals = _, arm_antiq, units}) =
  mk {names = names, macros = macros, locals = locals', arm_antiq = arm_antiq, units = units}

(* The position a "root" itself spans: what a "type_antiq_fun" sees as its own "current term". A
   file has no single span but its own. *)
fun pos_of_root (A.Id id) = A.pos_of_ident id
  | pos_of_root (A.Expr e) = A.pos_of_expr e
  | pos_of_root (A.Operand o1) = A.pos_of_operand o1
  | pos_of_root (A.Stmts (s :: _)) = A.pos_of_stmt s
  | pos_of_root (A.Stmts []) = Position.none
  | pos_of_root (A.Source (A.File (_, ni))) = A.pos_of_NodeInfo ni
  | pos_of_root (A.Stmt s) = A.pos_of_stmt s

(* Exactly-once dispatch of every physical antiquotation, whatever number of AST nodes share its
   leftmost source position - the same design as in the other front-ends. The set of comments
   already dispatched belongs to one walk ("analyse_and_eval" installs a fresh one for its dynamic
   extent) and is kept per thread, so two walks running at the same time cannot see each
   other's. *)
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


(* A navigation step's coarse target category, ignoring the constructor within. *)
fun category (A.Id _)      = 0
  | category (A.Expr _)    = 1
  | category (A.Operand _) = 2
  | category (A.Stmt _)    = 3
  | category (A.Stmts _)   = 4
  | category (A.Source _)  = 5

fun run_length (ctx as top :: _) =
      let
        val cat = category top
        fun count (x :: xs) = if category x = cat then 1 + count xs else 0
          | count [] = 0
      in count ctx end

(* Resolves the "(u|U)*" prefix of a navigation string against "ctx", returning the unconsumed
   "(r|d)*" suffix together with the resulting stack. The four rules are those of the other
   front-ends:

   \<^item> Rule 1: a lone, final "u" is a no-op.
   \<^item> Rule 2: a non-final "u" pops exactly one frame, unless "ctx" is a singleton, in which case it
     is a no-op.
   \<^item> Rule 3: "U" on a same-category run of length > 1 collapses the run down to its single
     outermost member and continues; it does not also pop that member.
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


(* The ordered list of children "r"/"d" may navigate into: sub-expressions, operands and
   statements in source order; the parameters of a macro are flattened away (their default values
   are children of the macro), the directives that structure the text contribute their operands
   and the statements of their bodies. *)
fun exprs es = map A.Expr es
fun operands os = map A.Operand os

fun children_of_expr e = (case e of
    A.ENum _ => [] | A.EFloat _ => [] | A.EChar _ => [] | A.EString _ => [] | A.ESym _ => []
  | A.EReg _ => [] | A.EDot _ => [] | A.ELocal _ => []
  | A.EReloc (e1, _, _) => [A.Expr e1]
  | A.EPart (_, e1, _) => [A.Expr e1]
  | A.EUnary (_, e1, _) => [A.Expr e1]
  | A.EBinary (_, a, b, _) => [A.Expr a, A.Expr b]
  | A.EParen (e1, _) => [A.Expr e1])

fun children_of_operand o1 = (case o1 of
    A.OExpr e => [A.Expr e]
  | A.OReg _ => []
  | A.OImm (e, _) => [A.Expr e]
  | A.OShift (_, _, arg, _) => (case arg of SOME a => [A.Operand a] | NONE => [])
  | A.OLiteral (e, _) => [A.Expr e]
  | A.OMem (os, _, _) => operands os
  | A.OAlign _ => []
  | A.OList (os, _, _) => operands os
  | A.ORange (a, b, _) => [A.Operand a, A.Operand b]
  | A.OPercent _ => []
  | A.OKeyword (_, e, _) => [A.Expr e]
  | A.ORaw _ => []
  | A.OScalar (_, _, e, _) => [A.Expr e])

fun mparam_children (A.MParam (_, _, d, _, _)) = (case d of SOME e => [A.Expr e] | NONE => [])

fun children_of_stmt s = (case s of
    A.SLabel _ => []
  | A.SInsn (A.Insn (_, os, _)) => operands os
  | A.SDir (_, os, _) => operands os
  | A.SAssign (_, e, _) => [A.Expr e]
  | A.SReq (_, o1, _) => [A.Operand o1]
  | A.SCall (_, os, _) => operands os
  | A.SMacro (_, ps, body, _) => maps mparam_children ps @ map A.Stmt body
  | A.SCond (brs, els, _) =>
      maps (fn A.Branch (_, os, body, _) => operands os @ map A.Stmt body) brs
      @ (case els of SOME b => map A.Stmt b | NONE => [])
  | A.SRep (_, os, body, _) => operands os @ map A.Stmt body
  | A.SExitm _ => [])

fun children_of _ (A.Expr e) = children_of_expr e
  | children_of _ (A.Operand o1) = children_of_operand o1
  | children_of _ (A.Stmt s) = children_of_stmt s
  | children_of _ (A.Stmts ss) = map A.Stmt ss
  | children_of _ (A.Source (A.File (ss, _))) = map A.Stmt ss
  | children_of antiq_pos (A.Id _) =
      error ("select_ast: an identifier is a leaf, no \"r\"/\"d\" children"
             ^ Position.here antiq_pos)

(* Resolves the "(r|d)*" suffix against a single "node" (the result of "select_u"'s ascent
   phase): "r" advances a 1-based cursor rightward among "children_of node"; "d" descends into
   the child the cursor currently points at (cursor 1, i.e. "d" alone, if no "r" preceded it) and
   continues processing the remaining navigation string against *that* child. No
   wrapping/saturation - a cursor beyond the children list's length is a hard "error", and a "d"
   with no children to descend into likewise.

   Every "error" here reports "antiq_pos" - the antiquotation's own tag position, which is the
   closest thing available to "where the string was written" and what a user actually needs to
   jump to. *)
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

(* Maps an antiquotation's own "navi list" together with the closest-surrounding-context stack to
   the single concrete AST node the antiquotation refers to: first the "(u|U)*" prefix against
   the whole stack ("select_u"), then the "(r|d)*" suffix against whatever that leaves on top
   ("select_rd"). An empty navi list is the identity. *)
fun select_ast antiq_pos navi ctx =
  let val (rd, ctx') = select_u (navi, ctx)
  in select_rd (antiq_pos, rd, hd ctx') end

(* The shared antiquotation-dispatch helper: looks up every "Antiquotation" in "ni"'s comment
   list by tag in "armenv"'s "arm_antiq", instantiates it with (armenv, select_ast tag_pos navi ctx,
   level), and pairs the resulting "Context.generic -> Context.generic" with its level -
   "select_ast" (and so "children_of", which can "error") is only forced when an "Antiquotation"
   genuinely needs it. "tag_pos" is passed through purely so that a navigation error is reported
   at "@tag[navi] ..." itself. An "Antiquotation" already dispatched earlier in this same walk
   (see "Dispatched_Antiqs") is silently skipped the second time some other node sharing its
   position reaches it: the walk reaches the outermost of any nodes tied at one position first,
   since every "walk_*" checks its own antiquotations before recursing. The handler receives
   "(body, body_pos)" and the *resolved* AST node, never the raw navi list. *)
fun check_antiq armenv (ctx : pos A.root list) (ni : pos A.nodeInfo)
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
                let val mk {arm_antiq, ...} = armenv in
                  case Symtab.lookup arm_antiq tag of
                    NONE =>
                      error ("analyse_and_eval: no antiquotation handler " ^
                             "registered for tag " ^ quote tag)
                  | SOME antiq_fun =>
                      (Dispatched_Antiqs.mark c;
                       SOME (level,
                             antiq_fun
                               (armenv, select_ast tag_pos navi ctx, level)
                                 (body, body_pos)))
                end
          | A.Raw_txt _ => NONE)
        cs


(* --- names ---------------------------------------------------------------------------------- *)

(* the keys of the table of names, one prefix per namespace; the symbols and labels have none *)
fun skey n = n
fun rkey n = "reg:" ^ n
fun mkey n = "macro:" ^ n
fun pkey n = "param:" ^ n

fun ident_name_of (A.Ident (n, _, _)) = n
fun ident_pos (A.Ident (_, _, ni)) = A.pos_of_NodeInfo ni

(* The full-token range a name spans, starting at "pos" (an identifier's "nodeInfo" carries a bare
   point, which would make an entity report claim a single character). *)
fun name_range (name, pos) =
  Position.range_position
    (Position.range (pos, Position.symbol_explode name pos))

fun report_decl kind name decl_pos =
  let val range_pos = name_range (name, decl_pos)
  in Position.report range_pos (Position.entity_markup kind (name, range_pos)) end

(* a use of a name that is written differently from its declaration ("1b" for "1:") *)
fun report_use2 kind (use_name, use_pos) (decl_name, decl_pos) =
  Position.report (name_range (use_name, use_pos))
    (Position.entity_markup kind (decl_name, name_range (decl_name, decl_pos)))

fun report_use kind name use_pos decl_pos = report_use2 kind (name, use_pos) (name, decl_pos)

(* a name written with a reference to a macro parameter is a template, not a name *)
fun has_ref s = String.isSubstring "\\" s

fun put_name key kind env = set_names (Symtab.update (key, kind) (names_of env)) env
fun del_name key env = set_names (Symtab.delete_safe key (names_of env)) env

(* Declares a name, reporting its declaration site. A template declares nothing. *)
fun declare keyf mk_kind env (A.Ident (name, _, ni)) =
  if has_ref name then env
  else
    let
      val pos = A.pos_of_NodeInfo ni
      val kind = mk_kind pos
      val _ = report_decl (describe_kind kind) name pos
    in put_name (keyf name) kind env end

(* the same, without a report (the names that may be used before their definition) *)
fun predeclare_name keyf mk_kind env (A.Ident (name, _, ni)) =
  if has_ref name then env else put_name (keyf name) (mk_kind (A.pos_of_NodeInfo ni)) env

fun use_key env key name use_pos =
  (case Symtab.lookup (names_of env) key of
     NONE => ()
   | SOME k => report_use (describe_kind k) name use_pos (pos_of_kind k))

(* The references to the parameters of a macro in a word, "\name": linked to the parameter. *)
fun refs_in env (text, pos) : unit =
  let
    fun is_id c = Char.isAlphaNum c orelse c = #"_"
    val n = String.size text
    fun ident_end k = if k < n andalso is_id (String.sub (text, k)) then ident_end (k + 1) else k
    fun go i =
      if i >= n then ()
      else if String.sub (text, i) = #"\\" andalso i + 1 < n
              andalso (Char.isAlpha (String.sub (text, i + 1))
                       orelse String.sub (text, i + 1) = #"_")
      then
        let
          val j = ident_end (i + 1)
          val name = String.substring (text, i + 1, j - i - 1)
          val use_pos = Position.symbol_explode (String.substring (text, 0, i + 1)) pos
          val _ = use_key env (pkey name) name use_pos
        in go j end
      else go (i + 1)
  in go 0 end

fun lower s = String.map Char.toLower s

(* the alias of a register: by the spelling, else in either case *)
fun alias_key env name =
  find_first (fn k => Symtab.defined (names_of env) k) [rkey name, rkey (lower name)]

(* A reference "1b" or "1f" to a numeric label: the nearest definition before or after. *)
fun use_local env text use_pos =
  let
    val n = String.size text
    val num = String.substring (text, 0, n - 1)
    val backward = (Char.toLower (String.sub (text, n - 1)) = #"b")
    val here = Position.offset_of use_pos
    val defs = filter (fn (m, _) => m = num) (locals_of env)
    fun off p = the_default 0 (Position.offset_of p)
    val cands =
      (case here of
         NONE => []
       | SOME h =>
           if backward then rev (filter (fn (_, p) => off p < h) defs)
           else filter (fn (_, p) => off p > h) defs)
  in
    (case cands of
       (_, p) :: _ => report_use2 "ARM label" (text, use_pos) (num, p)
     | [] => ())
  end

(* a symbol in an expression: a register alias, else a symbol or a label *)
fun use_sym env (A.Ident (name, _, ni)) =
  let val pos = A.pos_of_NodeInfo ni
  in
    refs_in env (name, pos);
    if has_ref name then ()
    else
      (case alias_key env name of
         SOME k => use_key env k name pos
       | NONE => use_key env (skey name) name pos)
  end

fun optl f x = (case x of NONE => [] | SOME y => f y)

(* A compact wrapper for the antiquotations a node carries (its "nodeInfo"). *)
fun chk env ctx ni = check_antiq env ctx ni

(* --- walking the tree ----------------------------------------------------------------------- *)

fun walk_expr env ctx (e : pos A.expr) : acts =
  let
    val ctx' = A.Expr e :: ctx
    val here = chk env ctx' (A.nodeInfo_of_expr e)
    val w = walk_expr env ctx'
  in
    here @
    (case e of
       A.ENum _ => []
     | A.EFloat _ => []
     | A.EChar (s, ni) => (refs_in env (s, A.pos_of_NodeInfo ni); [])
     | A.EString (s, ni) => (refs_in env (s, A.pos_of_NodeInfo ni); [])
     | A.ESym id => (use_sym env id; [])
     | A.EReg (_, s, ni) => (refs_in env (s, A.pos_of_NodeInfo ni); [])
     | A.EDot _ => []
     | A.ELocal (s, ni) => (use_local env s (A.pos_of_NodeInfo ni); [])
     | A.EReloc (e1, _, _) => w e1
     | A.EPart (_, e1, _) => w e1
     | A.EUnary (_, e1, _) => w e1
     | A.EBinary (_, a, b, _) => w a @ w b
     | A.EParen (e1, _) => w e1)
  end

fun walk_operand env ctx (o1 : pos A.operand) : acts =
  let
    val ctx' = A.Operand o1 :: ctx
    val here = chk env ctx' (A.nodeInfo_of_operand o1)
    val w = walk_operand env ctx'
    val we = walk_expr env ctx'
  in
    here @
    (case o1 of
       A.OExpr e => walk_expr env ctx e
     | A.OReg (r, s, _, ni) =>
         let val pos = A.pos_of_NodeInfo ni
         in
           refs_in env (s, pos);
           (case r of
              A.Special _ => (case alias_key env s of SOME k => use_key env k s pos | NONE => ())
            | _ => ());
           []
         end
     | A.OImm (e, _) => we e
     | A.OShift (_, _, arg, _) => optl w arg
     | A.OLiteral (e, _) => we e
     | A.OMem (os, _, _) => maps w os
     | A.OAlign _ => []
     | A.OList (os, _, _) => maps w os
     | A.ORange (a, b, _) => w a @ w b
     | A.OPercent _ => []
     | A.OKeyword (_, e, _) => we e
     | A.ORaw _ => []
     | A.OScalar (_, s, e, ni) => (refs_in env (s, A.pos_of_NodeInfo ni); we e))
  end

(* the numeric labels of a list of statements, in the order of the text, bodies of macros and
   loops included *)
fun collect_locals (ss : pos A.stmt list) : (string * pos) list =
  maps (fn s =>
          (case s of
             A.SLabel (A.LNum (n, ni), _) => [(n, A.pos_of_NodeInfo ni)]
           | A.SMacro (_, _, body, _) => collect_locals body
           | A.SCond (brs, els, _) =>
               maps (fn A.Branch (_, _, body, _) => collect_locals body) brs
               @ (case els of SOME b => collect_locals b | NONE => [])
           | A.SRep (_, _, body, _) => collect_locals body
           | _ => [])) ss

(* the directives that define a symbol by their first operand *)
val defining_directives =
  [".set", ".equ", ".equiv", ".eqv", ".thumb_set", ".comm", ".lcomm", ".common"]

fun is_defining name = List.exists (fn d => d = lower name) defining_directives

fun first_symbol (ops : pos A.operand list) : pos A.ident option =
  (case ops of
     A.OExpr (A.ESym id) :: _ => SOME id
   | _ => NONE)

(* The symbols of a list of statements that may be used before they are defined: the labels, and
   the first definition of a symbol. The bodies of macros are templates and not looked into. *)
fun predeclare env (ss : pos A.stmt list) : armenv =
  fold (fn s => fn e =>
          (case s of
             A.SLabel (A.LName id, _) => predeclare_name skey Label e id
           | A.SAssign (id, _, _) =>
               if Symtab.defined (names_of e) (skey (ident_name_of id)) then e
               else predeclare_name skey Symbol e id
           | A.SDir (A.Ident (d, _, _), ops, _) =>
               if is_defining d
               then (case first_symbol ops of
                       SOME id => if Symtab.defined (names_of e) (skey (ident_name_of id)) then e
                                  else predeclare_name skey Symbol e id
                     | NONE => e)
               else e
           | A.SCond (brs, els, _) =>
               let
                 val e1 = fold (fn A.Branch (_, _, body, _) => fn x => predeclare x body) brs e
               in (case els of SOME b => predeclare e1 b | NONE => e1) end
           | A.SRep (_, _, body, _) => predeclare e body
           | _ => e)) ss env

(* the arguments of a macro call: the keyword arguments name parameters of the macro *)
fun walk_call_args env ctx macro_name (ops : pos A.operand list) : acts =
  let
    val params = the_default [] (Symtab.lookup (macros_of env) macro_name)
    fun one o1 =
      (case o1 of
         A.OKeyword (A.Ident (n, _, ni), e, oni) =>
           let
             val ctx' = A.Operand o1 :: ctx
             val _ = (case AList.lookup (op =) params n of
                        SOME decl => report_use "ARM macro parameter" n (A.pos_of_NodeInfo ni) decl
                      | NONE => ())
           in chk env ctx' oni @ walk_expr env ctx' e end
       | _ => walk_operand env ctx o1)
  in maps one ops end

fun walk_ops env ctx ops = maps (walk_operand env ctx) ops

fun walk_stmt env ctx (s : pos A.stmt) : armenv * acts =
  let
    val ctx' = A.Stmt s :: ctx
    val here = chk env ctx' (A.nodeInfo_of_stmt s)
    fun ret (e, a) = (e, here @ a)
    fun call_or_ops name pos ops =
      (case Symtab.lookup (names_of env) (mkey name) of
         SOME (Macro dpos) =>
           (report_use "ARM macro" name pos dpos; walk_call_args env ctx' name ops)
       | _ => walk_ops env ctx' ops)
  in
    (case s of
       A.SLabel (A.LName id, _) =>
         (refs_in env (ident_name_of id, ident_pos id); ret (declare skey Label env id, []))
     | A.SLabel (A.LNum (n, ni), _) =>
         (report_decl "ARM label" n (A.pos_of_NodeInfo ni); ret (env, []))
     | A.SInsn (A.Insn ({text, ...}, ops, ni)) =>
         let val pos = A.pos_of_NodeInfo ni
         in refs_in env (text, pos); ret (env, call_or_ops text pos ops) end
     | A.SCall (id as A.Ident (name, _, _), ops, _) =>
         (refs_in env (name, ident_pos id); ret (env, call_or_ops name (ident_pos id) ops))
     | A.SDir (id as A.Ident (name, _, _), ops, _) =>
         let
           val _ = refs_in env (name, ident_pos id)
           val lname = lower name
         in
           if is_defining name
           then
             (case ops of
                A.OExpr (A.ESym sid) :: rest =>
                  let
                    val acts = maps (walk_operand env ctx') rest
                    val env1 = declare skey Symbol env sid
                  in ret (env1, acts) end
              | _ => ret (env, walk_ops env ctx' ops))
           else if lname = ".unreq"
           then
             (case ops of
                A.OExpr (A.ESym sid) :: _ =>
                  let
                    val acts = walk_ops env ctx' ops
                    val env1 = (case alias_key env (ident_name_of sid) of
                                  SOME k => del_name k env | NONE => env)
                  in ret (env1, acts) end
              | _ => ret (env, walk_ops env ctx' ops))
           else if lname = ".purgem"
           then
             (case ops of
                A.OExpr (A.ESym sid) :: _ =>
                  let
                    val n = ident_name_of sid
                    val _ = use_key env (mkey n) n (ident_pos sid)
                    val acts = walk_ops env ctx' ops
                  in ret (del_name (mkey n) env, acts) end
              | _ => ret (env, walk_ops env ctx' ops))
           else ret (env, walk_ops env ctx' ops)
         end
     | A.SAssign (id, e, _) =>
         let val acts = walk_expr env ctx' e
         in ret (declare skey Symbol env id, acts) end
     | A.SReq (id, o1, _) =>
         let val acts = walk_operand env ctx' o1
         in ret (declare rkey Alias env id, acts) end
     | A.SMacro (id, ps, body, _) =>
         let
           val name = ident_name_of id
           val dacts =
             maps (fn A.MParam (_, _, d, _, pni) =>
                     chk env ctx' pni @ (case d of SOME e => walk_expr env ctx' e | NONE => [])) ps
           val env1 = declare mkey Macro env id
           val pdecls = map (fn A.MParam (A.Ident (n, _, ni), _, _, _, _) =>
                               (n, A.pos_of_NodeInfo ni)) ps
           val env2 = set_macros (Symtab.update (name, pdecls) (macros_of env1)) env1
           (* the body: the parameters are declared, the labels may be used before they are
              defined; nothing of it survives the macro *)
           val inner0 =
             fold (fn A.MParam (pid, _, _, _, _) => fn e => declare pkey Param e pid) ps env2
           val inner1 = predeclare inner0 body
           val (_, bacts) = walk_stmts inner1 ctx' body
         in ret (env2, dacts @ bacts) end
     | A.SCond (brs, els, _) =>
         let
           val (env1, acts1) =
             fold (fn A.Branch (d, ops, body, bni) => fn (e, acc) =>
                     let
                       val ctx'' = ctx'
                       val bacts = chk e ctx'' bni
                       val oacts = walk_ops e ctx'' ops
                       val (e1, sacts) = walk_stmts e ctx'' body
                     in (e1, acc @ bacts @ oacts @ sacts) end) brs (env, [])
           val (env2, acts2) = (case els of SOME b => walk_stmts env1 ctx' b | NONE => (env1, []))
         in ret (env2, acts1 @ acts2) end
     | A.SRep (A.Ident (d, _, _), ops, body, _) =>
         let
           val ld = lower d
           (* ".irp var, items" and ".irpc var, chars" declare the variable for the body *)
           val (var, rest) =
             if ld = ".irp" orelse ld = ".irpc"
             then (case ops of A.OExpr (A.ESym v) :: r => (SOME v, r) | _ => (NONE, ops))
             else (NONE, ops)
           val oacts = walk_ops env ctx' rest
           val inner = (case var of SOME v => declare pkey Param env v | NONE => env)
           val (env1, bacts) = walk_stmts inner ctx' body
           (* the loop variable is not visible after the loop *)
           val env2 = (case var of
                         SOME (A.Ident (n, _, _)) =>
                           (case Symtab.lookup (names_of env) (pkey n) of
                              SOME k => put_name (pkey n) k env1
                            | NONE => del_name (pkey n) env1)
                       | NONE => env1)
         in ret (env2, oacts @ bacts) end
     | A.SExitm _ => ret (env, []))
  end

and walk_stmts env ctx (ss : pos A.stmt list) : armenv * acts =
  fold (fn s => fn (e, acc) => let val (e1, a) = walk_stmt e ctx s in (e1, acc @ a) end)
    ss (env, [])

(* --- files and fragments --------------------------------------------------------------------- *)

(* a list of statements: the numeric labels and the symbols are known beforehand; the names it
   declares at the top level stay in the environment *)
fun walk_unit env ctx (ss : pos A.stmt list) : armenv * acts =
  let
    val env0 = set_locals (collect_locals ss) env
    val env1 = predeclare env0 ss
    val (env2, acts) = walk_stmts env1 ctx ss
  in (set_locals [] env2, acts) end

fun analyse_and_eval0 (root : pos A.root) thy =
  let
    val env0 = get (Context.Theory thy)
    (* The bottom frame is always the top-level root itself, so "ctx" is never empty. *)
    val ctx0 = [root]
    fun drop acts = (thy, acts)
    fun persist (env1, acts) = (Context.theory_map (put env1) thy, acts)
  in
    case root of
      A.Id (id as A.Ident (_, _, ni)) =>
        let val here = check_antiq env0 ctx0 ni
            val _ = use_sym env0 id
        in (thy, here) end
    | A.Expr e => drop (walk_expr env0 ctx0 e)
    | A.Operand o1 => drop (walk_operand env0 ctx0 o1)
    | A.Stmts ss => persist (walk_unit env0 ctx0 ss)
    | A.Stmt s => drop (#2 (walk_stmt env0 ctx0 s))
    | A.Source (A.File (ss, ni)) =>
        let
          val here = check_antiq env0 ctx0 ni
          val (env1, acts) = walk_unit env0 ctx0 ss
        in persist (env1, here @ acts) end
  end

fun analyse_and_eval root thy =
  Dispatched_Antiqs.with_fresh (fn () => analyse_and_eval0 root thy)

end
\<close>

subsection\<open>Some Basic Antiquotation Settings\<close>

text\<open>
  The same eight demonstration antiquotations as C11's (\<open>C11_AnaEval.thy\<close>, whose
  notes on each apply unchanged): \<open>probe_armenv\<close>, \<open>probe_ast\<close>, \<open>highlight\<close>,
  \<open>term\<close>, \<open>ML\<close>, \<open>text\<close>, \<open>definition\<close> and \<open>lemma\<close>. They are written in a
  comment as \<^verbatim>\<open>//@ term \<open>x + 1 = (2::nat)\<close>\<close> (or anywhere in a comment as
  \<^verbatim>\<open>@term \<open>...\<close>\<close>) and attach to the node that begins on the next token;
  \<^verbatim>\<open>@tag[navi](level)\<close> selects another node and an evaluation order exactly as in
  C11. Handlers are registered under their tag in \<open>armenv\<close>'s \<open>arm_antiq\<close> table;
  nothing here knows ARM, only the \<open>root\<close> they are handed.
\<close>

declare [[ML_catch_all = true]]

ML\<open>
val ARMENV = Unsynchronized.ref(ARMEnv.empty_armenv);
val probe_armenv = let fun probe (armenv, _ , _) (_ : string * Position.T) thy =
                              (ARMENV := armenv; thy)
                 in  ARMEnv.store_antiq
                   ("probe_armenv",  ARMEnv.lift_theory_antiq probe) end

val ARM_AST =
  Unsynchronized.ref((ARM_Ast.Stmts []): (Position.T ARM_Ast.root) )
val probe_ast = let fun probe (_, ast , l) (_ : string * Position.T) thy =
                              (writeln("Level: "^ Int.toString l);
                               writeln("Read : " ^ ARM_Pp.pp_root ast);
                               ARM_AST := ast; thy)
                in  ARMEnv.store_antiq
                  ("probe_ast",  ARMEnv.lift_theory_antiq probe) end

val highlight = let fun probe (_, ast , _) (_ : string * Position.T) thy =
                              (Position.report (AnaEval.pos_of_root ast)
                               Markup.intensify;
                               thy)
                in  ARMEnv.store_antiq
                  ("highlight",  ARMEnv.lift_theory_antiq probe) end

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
   term is a real Isabelle error positioned in the ARM source. The
   catch-all handler is needed because "Syntax.read_term" fails with "Par_Exn",
   not "ERROR". *)
val ARM_TERM_PROBE =
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
      in (ARM_TERM_PROBE := t; thy) end
  in ARMEnv.store_antiq ("term", ARMEnv.lift_theory_antiq probe) end

(* Runs its body as real ML source, so a definition written in an assembly
   comment becomes a later-visible ML binding - the one handler that needs
   "Context.generic -> Context.generic" rather than "theory -> theory". *)
val ml_antiq =
  let
    fun probe (_, _, _) (body, body_pos) : Context.generic -> Context.generic =
      ML_Context.exec (fn () =>
        ML_Context.eval_source (ML_Compiler.verbose true ML_Compiler.flags)
          (body_source (body, body_pos)))
      #> Local_Theory.propagate_ml_env
  in ARMEnv.store_antiq ("ML", probe) end

(* Isabelle's "text" command: the body goes through the real
   "Document_Output.output_document" (inner antiquotations are checked,
   hyperlinked and hoverable); the result is stashed, not typeset, for the
   reason given in the Limitations of the C11 manual. *)
val ARM_TEXT_PROBE = Unsynchronized.ref ([] : Latex.text)
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
      in (ARM_TEXT_PROBE := latex; thy) end
  in ARMEnv.store_antiq ("text", ARMEnv.lift_theory_antiq probe) end

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
  in ARMEnv.store_antiq ("definition", ARMEnv.lift_theory_antiq probe) end

(* A statement plus one terminal "by" proof, actually proved - proof-carrying
   code: e.g. a property of a VAL abbreviation's value, discharged right where
   the ARM text that motivates it lives. *)
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
  in ARMEnv.store_antiq ("lemma", ARMEnv.lift_theory_antiq probe) end
\<close>

setup\<open>probe_armenv\<close>
setup\<open>probe_ast\<close>
setup\<open>highlight\<close>
setup\<open>term_antiq\<close>
setup\<open>text_antiq\<close>
setup\<open>ml_antiq\<close>
setup\<open>definition_antiq\<close>
setup\<open>lemma_antiq\<close>
end
