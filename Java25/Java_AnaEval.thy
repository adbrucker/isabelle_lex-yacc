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

theory Java_AnaEval
  imports "Java_Env" "Java_Parser"
begin

section\<open>Analyse and Eval\<close>

text\<open>
  \<open>analyse_and_eval\<close> is the Java counterpart of the passes of the same name of the other
  front-ends (\<^verbatim>\<open>C11_AnaEval.thy\<close>, \<^verbatim>\<open>Occam2_AnaEval.thy\<close>, \<^verbatim>\<open>Scala3_AnaEval.thy\<close>,
  \<^verbatim>\<open>MicroRust_AnaEval.thy\<close>, \<^verbatim>\<open>AdaSpark_AnaEval.thy\<close>, \<^verbatim>\<open>Go_AnaEval.thy\<close>, whose long
  explanations apply here and are not repeated): a single, purely functional, scoped walk over
  a parsed \<open>root\<close>, threading \<open>jenv\<close> through the descent, collecting every antiquotation action
  paired with its \<open>level\<close> instead of applying it, and hyperlinking every name use to its
  declaration. What is specific to Java:

  \<^item> \<^bold>\<open>Several name spaces, case sensitive.\<close> A variable (a local variable, a parameter, a
    field, an enum constant), a type (a class, an interface, an enum, a record, an annotation
    interface, a type parameter, an imported type), a package and a label are different things
    even if they are spelled alike, and so are the methods, which are overloaded. A simple name
    in an expression is a variable if one is in scope, else a type, else a package (JLS 6.4.2);
    a name in a type position is a type.
  \<^item> \<^bold>\<open>Scoping.\<close> The members of a class (its fields, methods and member types, the constants
    of an enum, the components of a record) are in scope throughout the class body, whatever
    the order, and in the classes nested in it; a declaration of a method named \<open>n\<close> hides all the
    methods \<open>n\<close> of the enclosing classes, whatever its signature (JLS 6.4.1). A local variable
    is in scope from its declaration, which includes its own initializer, to the end of the
    block; a parameter in the whole method, constructor or lambda; the variable of a \<open>for\<close> in the
    statement, a resource in the rest of the resource list and the block, a catch parameter in
    its block. The scope of a type parameter is the declaration it belongs to.
  \<^item> \<^bold>\<open>Pattern variables follow the flow\<close> (JLS 6.3.1): \<open>e instanceof T v\<close> introduces \<open>v\<close> when it is
    true, \<open>!e\<close> turns what \<open>e\<close> introduces when true into what it introduces when false, \<open>a && b\<close>
    sees what \<open>a\<close> introduces when true in \<open>b\<close>, \<open>a || b\<close> what it introduces when false, \<open>c ? x : y\<close>
    sees what \<open>c\<close> introduces when true in \<open>x\<close>, when false in \<open>y\<close>; \<open>if (c) S\<close> sees the former in
    \<open>S\<close>, and the variables that \<open>c\<close> introduces when false are in scope after the \<open>if\<close> if \<open>S\<close> cannot
    complete normally (\<open>if (!(o instanceof T t)) return; ... t ...\<close>); likewise for the loops and
    for the labels of a \<open>switch\<close> with patterns, whose variables are in scope in the guard and the
    rule or group.
  \<^item> \<^bold>\<open>Methods are linked when the choice is certain.\<close> A call \<open>m(a, b)\<close> without a receiver is
    hyperlinked to the method \<open>m\<close> of the innermost class that has a method of that name if the
    arity leaves just one candidate (a variable-arity method takes what it can); with several
    candidates, which only the types of the arguments can tell, nothing is linked. A name that
    resolves nowhere is \<^emph>\<open>not\<close> marked: in Java it very often comes from an inherited member, an
    on-demand import or the platform, and underlining it would drown the useful markup.
  \<^item> \<^bold>\<open>Imports\<close> declare the simple name of an imported type - the last element of the path - at
    that element (\<open>import java.util.List;\<close>), and a static import declares the name of a variable
    and of a method; a use is hyperlinked to the import. On-demand imports declare nothing.
  \<^item> \<^bold>\<open>The top level persists.\<close> After \<open>java\<close> has analysed a compilation unit (or \<open>java_decl\<close> some
    declarations), the types, the imports and (in a compact unit) the fields and methods it
    declares at the top level stay in \<open>jenv\<close> for the following commands, as the files of a package
    do for each other; a block does not leave anything behind.
  \<^item> \<^bold>\<open>Closest context and navigation\<close> as in the other front-ends: expressions, types, statements
    and declarations push their own node (\<open>Expr\<close>, \<open>Type\<close>, \<open>Stmt\<close>, \<open>Decl\<close>); everything else
    (parameters, annotations, switch labels, ...) uses \<open>hd ctx\<close>. The children of a node are, in
    source order, its sub-expressions, types, statements and declarations; blocks are flattened
    into their parent.
\<close>
ML\<open>
structure AnaEval = struct

structure A = Java_Ast
open JEnv

type acts = (int * (Context.generic -> Context.generic)) list

fun names_of (mk {names, ...} : jenv) = names
fun meths_of (mk {meths, ...} : jenv) = meths

(* The scope of a name: the two tables are always set together. *)
fun set_scope (names', meths') (mk {names = _, meths = _, java_antiq, units}) =
  mk {names = names', meths = meths', java_antiq = java_antiq, units = units}

(* The position a "root" itself spans: what a "type_antiq_fun" sees as its own "current term". A
   compilation unit has no single span. *)
fun pos_of_root (A.Id id) = A.pos_of_ident id
  | pos_of_root (A.Expr e) = A.pos_of_expr e
  | pos_of_root (A.Type t) = A.pos_of_type t
  | pos_of_root (A.Stmts (s :: _)) = A.pos_of_stmt s
  | pos_of_root (A.Stmts []) = Position.none
  | pos_of_root (A.Decls (d :: _)) = A.pos_of_decl d
  | pos_of_root (A.Decls []) = Position.none
  | pos_of_root (A.Source (A.Unit (_, _, _, ni))) = A.pos_of_NodeInfo ni
  | pos_of_root (A.Stmt s) = A.pos_of_stmt s
  | pos_of_root (A.Decl d) = A.pos_of_decl d

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
fun category (A.Id _)     = 0
  | category (A.Expr _)   = 1
  | category (A.Type _)   = 2
  | category (A.Stmt _)   = 3
  | category (A.Decl _)   = 4
  | category (A.Stmts _)  = 5
  | category (A.Decls _)  = 6
  | category (A.Source _) = 7

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


(* The ordered list of children "r"/"d" may navigate into (see the top-of-theory note):
   sub-expressions, types, statements and declarations in source order; nodes without a "root"
   counterpart (parameters, annotations, switch labels, ...) are flattened into their parent's
   list or dropped. *)
fun opt_expr eo = (case eo of SOME e => [A.Expr e] | NONE => [])
fun opt_stmt so = (case so of SOME s => [A.Stmt s] | NONE => [])
fun exprs es = map A.Expr es
fun types ts = map A.Type ts

fun block_children (A.Block (stmts, _)) = map A.Stmt stmts

fun targs_children (A.TArgs (args, _)) =
  maps (fn A.TAType t => [A.Type t]
         | A.TAWild (_, b, _) => (case b of SOME (_, t) => [A.Type t] | NONE => [])) args

fun opt_targs ta = (case ta of SOME a => targs_children a | NONE => [])

fun children_of_type t = (case t of
    A.TPrim _ => []
  | A.TVar _ => []
  | A.TClass (_, segs, _) => maps (fn A.TSeg (_, ta) => opt_targs ta) segs
  | A.TArray (e, _, _) => [A.Type e])

fun param_children (A.Param (_, t, _, _, _, _)) = [A.Type t]

fun pattern_children p = (case p of
    A.PType (_, t, _, _) => [A.Type t]
  | A.PRecord (t, ps, _) => A.Type t :: maps pattern_children ps
  | A.PAny _ => [])

fun label_children l = (case l of
    A.LDefault _ => []
  | A.LCase (items, g, _) =>
      maps (fn A.CIExpr e => [A.Expr e] | A.CIPattern p => pattern_children p | A.CIDefault => [])
        items @ opt_expr g)

fun swcase_children c = (case c of
    A.SwRule (l, body, _) =>
      label_children l
      @ (case body of
           A.RBExpr e => [A.Expr e]
         | A.RBBlock b => block_children b
         | A.RBThrow s => [A.Stmt s])
  | A.SwGroup (ls, ss, _) => maps label_children ls @ map A.Stmt ss)

fun children_of_expr e = (case e of
    A.ELit _ => []
  | A.EName _ => []
  | A.EThis _ => []
  | A.ESuper _ => []
  | A.EField (e1, _, _) => [A.Expr e1]
  | A.EQualThis (e1, _) => [A.Expr e1]
  | A.EQualSuper (e1, _) => [A.Expr e1]
  | A.EParen (e1, _) => [A.Expr e1]
  | A.EIndex (a, i, _) => [A.Expr a, A.Expr i]
  | A.ECall (r, ta, _, args, _) => opt_expr r @ opt_targs ta @ exprs args
  | A.ENew (o1, t, args, body, _) =>
      opt_expr o1 @ [A.Type t] @ exprs args @ (case body of SOME ms => map A.Decl ms | NONE => [])
  | A.ENewArray (t, des, _, init, _) => A.Type t :: exprs des @ opt_expr init
  | A.EArrayInit (es, _, _) => exprs es
  | A.EClassLit (t, _) => [A.Type t]
  | A.EMethodRef (tg, ta, _, _) =>
      (case tg of A.MRExpr e1 => [A.Expr e1] | A.MRType t => [A.Type t]) @ opt_targs ta
  | A.ELambda (ps, _, body, _) =>
      maps (fn A.LPInfer _ => [] | A.LPTyped p => param_children p) ps
      @ (case body of A.LBExpr e1 => [A.Expr e1] | A.LBBlock b => block_children b)
  | A.EUnary (_, e1, _) => [A.Expr e1]
  | A.EBinary (_, a, b, _) => [A.Expr a, A.Expr b]
  | A.EAssign (a, _, b, _) => [A.Expr a, A.Expr b]
  | A.ECond (a, b, c, _) => [A.Expr a, A.Expr b, A.Expr c]
  | A.ECast (ts, e1, _) => types ts @ [A.Expr e1]
  | A.EInstanceof (e1, p, _) => A.Expr e1 :: pattern_children p
  | A.ESwitch (e1, cs, _) => A.Expr e1 :: maps swcase_children cs)

fun vardecl_children (A.VarDecl (_, _, init, _)) = opt_expr init

fun localvar_children (A.LocalVar (_, t, vds, _)) = A.Type t :: maps vardecl_children vds

fun resource_children r = (case r of
    A.RDecl lv => localvar_children lv
  | A.RExpr e => [A.Expr e])

fun catch_children (A.Catch (_, ts, _, b, _)) = types ts @ block_children b

fun children_of_stmt s = (case s of
    A.SBlock b => block_children b
  | A.SLocal lv => localvar_children lv
  | A.SClassDecl d => [A.Decl d]
  | A.SEmpty _ => []
  | A.SExpr (e, _) => [A.Expr e]
  | A.SLabeled (_, s1, _) => [A.Stmt s1]
  | A.SIf (c, t, e, _) => A.Expr c :: A.Stmt t :: opt_stmt e
  | A.SWhile (c, b, _) => [A.Expr c, A.Stmt b]
  | A.SDo (b, c, _) => [A.Stmt b, A.Expr c]
  | A.SFor (init, c, upd, b, _) =>
      (case init of
         NONE => []
       | SOME (A.FIVars lv) => localvar_children lv
       | SOME (A.FIExprs es) => exprs es)
      @ opt_expr c @ exprs upd @ [A.Stmt b]
  | A.SForEach (_, t, _, e, b, _) => [A.Type t, A.Expr e, A.Stmt b]
  | A.SBreak _ => []
  | A.SContinue _ => []
  | A.SReturn (e, _) => opt_expr e
  | A.SThrow (e, _) => [A.Expr e]
  | A.SYield (e, _) => [A.Expr e]
  | A.SAssert (c, m, _) => A.Expr c :: opt_expr m
  | A.SSync (e, b, _) => A.Expr e :: block_children b
  | A.STry (res, _, b, cs, f, _) =>
      maps resource_children res @ block_children b @ maps catch_children cs
      @ (case f of SOME fb => block_children fb | NONE => [])
  | A.SSwitch (e, cs, _) => A.Expr e :: maps swcase_children cs
  | A.SCtorCall (q, ta, _, args, _) => opt_expr q @ opt_targs ta @ exprs args)

fun tparam_children (A.TParam (_, _, bounds, _)) = types bounds

fun enumconst_children (A.EnumConst (_, _, args, body, _)) =
  (case args of SOME es => exprs es | NONE => [])
  @ (case body of SOME ms => map A.Decl ms | NONE => [])

fun children_of_decl d = (case d of
    A.DClass (_, _, tps, ext, impl, perm, body, _) =>
      maps tparam_children tps @ (case ext of SOME t => [A.Type t] | NONE => [])
      @ types impl @ types perm @ map A.Decl body
  | A.DInterface (_, _, tps, ext, perm, body, _) =>
      maps tparam_children tps @ types ext @ types perm @ map A.Decl body
  | A.DEnum (_, _, impl, consts, _, body, _) =>
      types impl @ maps enumconst_children consts @ map A.Decl body
  | A.DRecord (_, _, tps, comps, impl, body, _) =>
      maps tparam_children tps @ maps param_children comps @ types impl @ map A.Decl body
  | A.DAnnotType (_, _, body, _) => map A.Decl body
  | A.DField (_, t, vds, _) => A.Type t :: maps vardecl_children vds
  | A.DMethod (_, tps, res, _, ps, _, thr, body, _, _) =>
      maps tparam_children tps @ [A.Type res] @ maps param_children ps @ types thr
      @ (case body of SOME b => block_children b | NONE => [])
  | A.DCtor (_, tps, _, ps, thr, b, _) =>
      maps tparam_children tps @ maps param_children ps @ types thr @ block_children b
  | A.DCompact (_, _, b, _) => block_children b
  | A.DInit (_, b, _) => block_children b
  | A.DEmpty _ => [])

fun children_of _ (A.Expr e) = children_of_expr e
  | children_of _ (A.Type t) = children_of_type t
  | children_of _ (A.Stmt s) = children_of_stmt s
  | children_of _ (A.Decl d) = children_of_decl d
  | children_of _ (A.Stmts ss) = map A.Stmt ss
  | children_of _ (A.Decls ds) = map A.Decl ds
  | children_of _ (A.Source (A.Unit (_, _, body, _))) =
      (case body of A.Types ds => map A.Decl ds | A.Module _ => [])
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
   list by tag in "jenv"'s "java_antiq", instantiates it with (jenv, select_ast tag_pos navi ctx,
   level), and pairs the resulting "Context.generic -> Context.generic" with its level -
   "select_ast" (and so "children_of", which can "error") is only forced when an "Antiquotation"
   genuinely needs it. "tag_pos" is passed through purely so that a navigation error is reported
   at "@tag[navi] ..." itself. An "Antiquotation" already dispatched earlier in this same walk
   (see "Dispatched_Antiqs") is silently skipped the second time some other node sharing its
   position reaches it: the walk reaches the outermost of any nodes tied at one position first,
   since every "walk_*" checks its own antiquotations before recursing. The handler receives
   "(body, body_pos)" and the *resolved* AST node, never the raw navi list. *)
fun check_antiq jenv (ctx : pos A.root list) (ni : pos A.nodeInfo)
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
                let val mk {java_antiq, ...} = jenv in
                  case Symtab.lookup java_antiq tag of
                    NONE =>
                      error ("analyse_and_eval: no antiquotation handler " ^
                             "registered for tag " ^ quote tag)
                  | SOME antiq_fun =>
                      (Dispatched_Antiqs.mark c;
                       SOME (level,
                             antiq_fun
                               (jenv, select_ast tag_pos navi ctx, level)
                                 (body, body_pos)))
                end
          | A.Raw_txt _ => NONE)
        cs

(* --- names ---------------------------------------------------------------------------------- *)

(* the keys of the table of names, one prefix per name space *)
fun vkey n = n
fun tkey n = "type:" ^ n
fun pkey n = "pkg:" ^ n
fun lkey n = "label:" ^ n

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

fun report_use kind name use_pos decl_pos =
  Position.report (name_range (name, use_pos))
    (Position.entity_markup kind (name, name_range (name, decl_pos)))

(* Hyperlinks a use of "name" to the declaration registered under "key", if there is one; nothing
   is reported otherwise (see the top-of-theory note). *)
fun use_key jenv key name use_pos =
  (case Symtab.lookup (names_of jenv) key of
     NONE => ()
   | SOME k => report_use (describe_kind k) name use_pos (pos_of_kind k))

(* A simple name in an expression: a variable, else a type, else a package (JLS 6.4.2). *)
fun use_expr_name jenv (A.Ident (name, _, ni)) =
  if name = "_" then ()
  else
    let
      val pos = A.pos_of_NodeInfo ni
      val tab = names_of jenv
    in
      if Symtab.defined tab (vkey name) then use_key jenv (vkey name) name pos
      else if Symtab.defined tab (tkey name) then use_key jenv (tkey name) name pos
      else use_key jenv (pkey name) name pos
    end

(* The first name of a type: a type, else the first element of a package name *)
fun use_type_name jenv (A.Ident (name, _, ni)) =
  let
    val pos = A.pos_of_NodeInfo ni
    val tab = names_of jenv
  in
    if Symtab.defined tab (tkey name) then use_key jenv (tkey name) name pos
    else use_key jenv (pkey name) name pos
  end

fun use_label jenv lbl =
  (case lbl of
     NONE => ()
   | SOME (A.Ident (name, _, ni)) => use_key jenv (lkey name) name (A.pos_of_NodeInfo ni))

(* A call "m(args)" without a receiver: linked to the one method of that name that the number of
   arguments leaves, if there is one. *)
fun use_method jenv (A.Ident (name, _, ni)) nargs =
  (case Symtab.lookup (meths_of jenv) name of
     NONE => ()
   | SOME ds =>
       let
         fun fits (MD {arity, varargs, ...}) =
           if varargs then nargs >= arity - 1 else nargs = arity
       in
         (case filter fits ds of
            [MD {pos, ...}] => report_use "Java method" name (A.pos_of_NodeInfo ni) pos
          | _ => ())
       end)

fun put_name key kind jenv = set_scope (Symtab.update (key, kind) (names_of jenv),
  meths_of jenv) jenv

(* Declares a name, reporting its declaration site. The blank identifier declares nothing. *)
fun reg_with keyf mk_kind jenv (A.Ident (name, _, ni)) =
  if name = "_" then jenv
  else
    let
      val pos = A.pos_of_NodeInfo ni
      val kind = mk_kind pos
      val _ = report_decl (describe_kind kind) name pos
    in put_name (keyf name) kind jenv end

fun reg_v mk_kind jenv id = reg_with vkey mk_kind jenv id
fun reg_t mk_kind jenv id = reg_with tkey mk_kind jenv id

(* A declaration whose site is only reported, not entered (a constructor, a label of a pattern). *)
fun decl_only mk_kind (A.Ident (name, _, ni)) =
  if name = "_" then ()
  else
    let val pos = A.pos_of_NodeInfo ni
    in report_decl (describe_kind (mk_kind pos)) name pos end

(* Methods: the declarations of a class replace, name by name, those of the enclosing classes. *)
fun add_meths jenv (ms : (string * mdecl) list) =
  let
    val ns = distinct (op =) (map #1 ms)
    val meths' =
      fold (fn n => Symtab.update (n, map #2 (filter (fn (m, _) => m = n) ms))) ns (meths_of jenv)
  in set_scope (names_of jenv, meths') jenv end

(* Runs "f" in a nested scope: the tables are restored on exit. *)
fun scoped jenv f =
  let
    val scope = (names_of jenv, meths_of jenv)
    val (jenv1, acts) = f jenv
  in (set_scope scope jenv1, acts) end

fun optl f x = (case x of NONE => [] | SOME y => f y)

(* A compact wrapper for the antiquotations a node carries (its "nodeInfo"). *)
fun chk jenv ctx ni = check_antiq jenv ctx ni

(* The pattern variables a condition introduces when it is true / false. *)
type binds = (string * ident_kind) list

fun add_binds jenv (bs : binds) = fold (fn (n, k) => fn g => put_name (vkey n) k g) bs jenv

(* a name that a pattern introduced leaves the scope again *)
fun remove_binds old jenv (bs : binds) =
  fold (fn (n, _) => fn g =>
          let
            val key = vkey n
            val tab = names_of g
            val tab' = (case Symtab.lookup (names_of old) key of
                          SOME k => Symtab.update (key, k) tab
                        | NONE => Symtab.delete_safe key tab)
          in set_scope (tab', meths_of g) g end) bs jenv

(* --- can a statement complete normally? (JLS 14.22, in the cases that matter here) ------- *)

fun has_break (s : pos A.jStmt) : bool =
  (case s of
     A.SBreak _ => true
   | A.SBlock (A.Block (ss, _)) => exists has_break ss
   | A.SLabeled (_, s1, _) => has_break s1
   | A.SIf (_, t, e, _) => has_break t orelse (case e of SOME e1 => has_break e1 | NONE => false)
   | A.SWhile (_, b, _) => has_break b
   | A.SDo (b, _, _) => has_break b
   | A.SFor (_, _, _, b, _) => has_break b
   | A.SForEach (_, _, _, _, b, _) => has_break b
   | A.SSync (_, A.Block (ss, _), _) => exists has_break ss
   | A.STry (_, _, A.Block (ss, _), cs, f, _) =>
       exists has_break ss orelse exists (fn A.Catch (_, _, _, A.Block (cs1, _),
         _) => exists has_break cs1) cs
       orelse (case f of SOME (A.Block (fs, _)) => exists has_break fs | NONE => false)
   | A.SSwitch (_, cases, _) =>
       exists (fn A.SwRule (_, A.RBBlock (A.Block (ss, _)), _) => exists has_break ss
                | A.SwRule _ => false
                | A.SwGroup (_, ss, _) => exists has_break ss) cases
   | _ => false)

fun can_complete (s : pos A.jStmt) : bool =
  (case s of
     A.SReturn _ => false
   | A.SThrow _ => false
   | A.SBreak _ => false
   | A.SContinue _ => false
   | A.SYield _ => false
   | A.SBlock (A.Block (ss, _)) => forall can_complete ss
   | A.SLabeled (_, s1, _) => can_complete s1
   | A.SIf (_, t, SOME e, _) => can_complete t orelse can_complete e
   | A.SSync (_, A.Block (ss, _), _) => forall can_complete ss
   | _ => true)

(* --- the walk --------------------------------------------------------------------------------- *)

fun mod_kw_is ms kw = exists (fn A.MKw (s, _) => s = kw | A.MAnnot _ => false) ms

fun is_receiver (A.Ident (n, _, _)) = n = "this" orelse String.isSuffix ".this" n

fun walk_annot senv ctx (A.Annot (name, args, ni)) : acts =
  let
    val here = chk senv ctx ni
    val _ = (case name of id :: _ => use_type_name senv id | [] => ())
  in
    here @
    (case args of
       A.NoArgs => []
     | A.Single v => walk_elemval senv ctx v
     | A.Pairs ps => maps (fn (_, v) => walk_elemval senv ctx v) ps)
  end

and walk_elemval senv ctx v : acts =
  (case v of
     A.EVExpr e => #1 (walk_e senv ctx e)
   | A.EVArray (vs, _, ni1) => chk senv ctx ni1 @ maps (walk_elemval senv ctx) vs
   | A.EVAnnot a => walk_annot senv ctx a)

and walk_annots senv ctx al : acts = maps (walk_annot senv ctx) al

and walk_mods senv ctx ms : acts =
  maps (fn A.MKw _ => [] | A.MAnnot a => walk_annot senv ctx a) ms

and walk_type senv ctx (t : pos A.jType) : acts =
  let
    val ctx' = A.Type t :: ctx
    val here = chk senv ctx' (A.nodeInfo_of_type t)
  in
    here @
    (case t of
       A.TPrim (al, _, _) => walk_annots senv ctx' al
     | A.TClass (al, segs, _) =>
         let
           val _ = (case segs of A.TSeg (id, _) :: _ => use_type_name senv id | [] => ())
         in
           walk_annots senv ctx' al
           @ maps (fn A.TSeg (_, ta) => optl (walk_targs senv ctx') ta) segs
         end
     | A.TArray (e, ds, _) => walk_type senv ctx' e @ maps (walk_dim senv ctx') ds
     | A.TVar _ => [])
  end

and walk_dim senv ctx (A.Dim (al, ni)) : acts = chk senv ctx ni @ walk_annots senv ctx al

and walk_targs senv ctx (A.TArgs (args, ni)) : acts =
  chk senv ctx ni
  @ maps (fn A.TAType t => walk_type senv ctx t
           | A.TAWild (al, b, ni1) =>
               chk senv ctx ni1 @ walk_annots senv ctx al
               @ (case b of SOME (_, t) => walk_type senv ctx t | NONE => [])) args

(* expressions: the actions, and the pattern variables introduced when it is true / false *)
and walk_e senv ctx (e : pos A.jExpr) : acts * binds * binds =
  let
    val ctx' = A.Expr e :: ctx
    val here = chk senv ctx' (A.nodeInfo_of_expr e)
    fun plain acts = (here @ acts, [], [])
    fun seq es = maps (fn x => #1 (walk_e senv ctx' x)) es
  in
    (case e of
       A.ELit _ => plain []
     | A.EName id => (use_expr_name senv id; plain [])
     | A.EField (e1, _, _) => plain (seq [e1])
     | A.EThis _ => plain []
     | A.ESuper _ => plain []
     | A.EQualThis (e1, _) => plain (seq [e1])
     | A.EQualSuper (e1, _) => plain (seq [e1])
     | A.EParen (e1, _) =>
         let val (a, t, f) = walk_e senv ctx' e1 in (here @ a, t, f) end
     | A.EIndex (a, i, _) => plain (seq [a, i])
     | A.ECall (recv, ta, id, args, _) =>
         let
           val ra = (case recv of
                       SOME r => seq [r]
                     | NONE => (use_method senv id (length args); []))
         in plain (ra @ optl (walk_targs senv ctx') ta @ seq args) end
     | A.ENew (outer, t, args, body, _) =>
         plain (optl (fn o1 => seq [o1]) outer @ walk_type senv ctx' t @ seq args
                @ optl (walk_members senv ctx') body)
     | A.ENewArray (t, des, ds, init, _) =>
         plain (walk_type senv ctx' t @ seq des @ maps (walk_dim senv ctx') ds
                @ optl (fn i => seq [i]) init)
     | A.EArrayInit (es, _, _) => plain (seq es)
     | A.EClassLit (t, _) => plain (walk_type senv ctx' t)
     | A.EMethodRef (tg, ta, _, _) =>
         plain ((case tg of A.MRExpr e1 => seq [e1] | A.MRType t => walk_type senv ctx' t)
                @ optl (walk_targs senv ctx') ta)
     | A.ELambda (ps, _, body, _) =>
         let
           val (_, acts) = scoped senv (fn s =>
             let
               val (s1, pacts) = walk_lparams s ctx' ps
               val bacts = (case body of
                              A.LBExpr e1 => #1 (walk_e s1 ctx' e1)
                            | A.LBBlock b => walk_block s1 ctx' b)
             in (s1, pacts @ bacts) end)
         in plain acts end
     | A.EUnary (A.UNot, e1, _) =>
         let val (a, t, f) = walk_e senv ctx' e1 in (here @ a, f, t) end
     | A.EUnary (_, e1, _) => plain (seq [e1])
     | A.EBinary (A.LAnd, a, b, _) =>
         let
           val (a1, ta, _) = walk_e senv ctx' a
           val (b1, tb, _) = walk_e (add_binds senv ta) ctx' b
         in (here @ a1 @ b1, ta @ tb, []) end
     | A.EBinary (A.LOr, a, b, _) =>
         let
           val (a1, _, fa) = walk_e senv ctx' a
           val (b1, _, fb) = walk_e (add_binds senv fa) ctx' b
         in (here @ a1 @ b1, [], fa @ fb) end
     | A.EBinary (_, a, b, _) => plain (seq [a, b])
     | A.EAssign (l, _, r, _) => plain (seq [l, r])
     | A.ECond (c, a, b, _) =>
         let
           val (c1, tc, fc) = walk_e senv ctx' c
           val (a1, _, _) = walk_e (add_binds senv tc) ctx' a
           val (b1, _, _) = walk_e (add_binds senv fc) ctx' b
         in plain (c1 @ a1 @ b1) end
     | A.ECast (ts, e1, _) => plain (maps (walk_type senv ctx') ts @ seq [e1])
     | A.EInstanceof (e1, p, _) =>
         let
           val (a1, _, _) = walk_e senv ctx' e1
           val (pacts, bs) = walk_pattern senv ctx' p
         in (here @ a1 @ pacts, bs, []) end
     | A.ESwitch (e1, cases, _) => plain (seq [e1] @ walk_cases senv ctx' cases))
  end

and walk_pattern senv ctx (p : pos A.jPattern) : acts * binds =
  let val here = chk senv ctx (A.nodeInfo_of_pattern p)
  in
    (case p of
       A.PType (ms, t, idopt, _) =>
         let
           val acts = walk_mods senv ctx ms @ walk_type senv ctx t
           val bs = (case idopt of
                       SOME (id as A.Ident (name, _, ni)) =>
                         if name = "_" then []
                         else
                           let val pos = A.pos_of_NodeInfo ni
                           in (decl_only Var id; [(name, Var pos)]) end
                     | NONE => [])
         in (here @ acts, bs) end
     | A.PRecord (t, ps, _) =>
         let
           val tacts = walk_type senv ctx t
           val rs = map (walk_pattern senv ctx) ps
         in (here @ tacts @ maps #1 rs, maps #2 rs) end
     | A.PAny _ => (here, []))
  end

(* one switch label: its actions, the variables its patterns (and its guard) introduce *)
and walk_label senv ctx (l : pos A.jLabel) : acts * binds =
  (case l of
     A.LDefault ni => (chk senv ctx ni, [])
   | A.LCase (items, guard, ni) =>
       let
         val here = chk senv ctx ni
         val rs = map (fn A.CIExpr e => (#1 (walk_e senv ctx e), [])
                        | A.CIPattern p => walk_pattern senv ctx p
                        | A.CIDefault => ([], [])) items
         val bs = maps #2 rs
         val senv' = add_binds senv bs
         val (gacts, gt) = (case guard of
                              SOME g => let val (a, t, _) = walk_e senv' ctx g in (a, t) end
                            | NONE => ([], []))
       in (here @ maps #1 rs @ gacts, bs @ gt) end)

and walk_cases senv ctx cases : acts =
  let
    fun go _ [] = []
      | go env (c :: rest) =
          (case c of
             A.SwRule (l, body, ni) =>
               let
                 val here = chk env ctx ni
                 val (lacts, bs) = walk_label env ctx l
                 val env_l = add_binds env bs
                 val bacts =
                   (case body of
                      A.RBExpr e1 => #1 (walk_e env_l ctx e1)
                    | A.RBBlock b => walk_block env_l ctx b
                    | A.RBThrow s => #2 (walk_stmt env_l ctx s))
               in here @ lacts @ bacts @ go env rest end
           | A.SwGroup (ls, stmts, ni) =>
               let
                 val here = chk env ctx ni
                 val (lacts, bs) =
                   fold (fn l => fn (a, b) =>
                           let val (a1, b1) = walk_label (add_binds env b) ctx l in (a @ a1,
                             b @ b1) end)
                     ls ([], [])
                 val (env', sacts) = walk_stmts (add_binds env bs) ctx stmts
                 (* the pattern variables end with the group; the locals stay for the next one *)
                 val env'' = remove_binds env env' bs
               in here @ lacts @ sacts @ go env'' rest end)
  in #2 (scoped senv (fn s => (s, go s cases))) end

and walk_lparams senv ctx ps : jenv * acts =
  fold (fn p => fn (s, acc) =>
          (case p of
             A.LPInfer id => (reg_v Param s id, acc)
           | A.LPTyped pr => let val (s1, a) = walk_param s ctx pr in (s1, acc @ a) end))
    ps (senv, [])

and walk_param senv ctx (A.Param (ms, t, _, id, ds, ni)) : jenv * acts =
  let
    val acts = chk senv ctx ni @ walk_mods senv ctx ms @ walk_type senv ctx t
               @ maps (walk_dim senv ctx) ds
    val senv' = if is_receiver id then senv else reg_v Param senv id
  in (senv', acts) end

and walk_params senv ctx ps : jenv * acts =
  fold (fn p => fn (s, acc) => let val (s1, a) = walk_param s ctx p in (s1, acc @ a) end)
    ps (senv, [])

and walk_block senv ctx (A.Block (stmts, ni)) : acts =
  chk senv ctx ni @ #2 (scoped senv (fn s => walk_stmts s ctx stmts))

(* a sequence of statements; the environment after it has the locals and the pattern variables
   that the statements introduce *)
and walk_stmts senv ctx stmts : jenv * acts =
  fold (fn s => fn (e, acc) => let val (e', a) = walk_stmt e ctx s in (e', acc @ a) end)
    stmts (senv, [])

and walk_localvar senv ctx (A.LocalVar (ms, t, vds, ni)) : jenv * acts =
  let
    val a0 = chk senv ctx ni @ walk_mods senv ctx ms @ walk_type senv ctx t
  in
    fold (fn A.VarDecl (id, ds, init, vni) => fn (e, acc) =>
            let
              val e1 = reg_v Var e id          (* in scope in its own initializer *)
              val a1 = chk e1 ctx vni @ maps (walk_dim e1 ctx) ds
                       @ (case init of SOME x => #1 (walk_e e1 ctx x) | NONE => [])
            in (e1, acc @ a1) end)
      vds (senv, a0)
  end

and walk_stmt senv ctx (s : pos A.jStmt) : jenv * acts =
  let
    val ctx' = A.Stmt s :: ctx
    val here = chk senv ctx' (A.nodeInfo_of_stmt s)
    fun ret (e, a) = (e, here @ a)
    fun expr e = #1 (walk_e senv ctx' e)
    (* the loop forms: body with the variables the condition introduces when true; after the loop
       those it introduces when false, unless there is a "break" *)
    fun loop_after body fc = if has_break body then senv else add_binds senv fc
  in
    (case s of
       A.SBlock b => ret (senv, walk_block senv ctx' b)
     | A.SLocal lv => ret (walk_localvar senv ctx' lv)
     | A.SClassDecl d =>
         (case d of
            A.DClass (_, id, _, _, _, _, _, _) => walk_local_class senv ctx' d id
          | A.DInterface (_, id, _, _, _, _, _) => walk_local_class senv ctx' d id
          | A.DEnum (_, id, _, _, _, _, _) => walk_local_class senv ctx' d id
          | A.DRecord (_, id, _, _, _, _, _) => walk_local_class senv ctx' d id
          | A.DAnnotType (_, id, _, _) => walk_local_class senv ctx' d id
          | _ => ret (senv, walk_decl senv ctx' d))
     | A.SEmpty _ => ret (senv, [])
     | A.SExpr (e, _) => ret (senv, expr e)
     | A.SLabeled (id, s1, _) =>
         let
           val senv1 = reg_with lkey Label senv id
           val (e1, a) = walk_stmt senv1 ctx' s1
           val key = lkey (ident_name_of id)
           val tab = (case Symtab.lookup (names_of senv) key of
                        SOME k => Symtab.update (key, k) (names_of e1)
                      | NONE => Symtab.delete_safe key (names_of e1))
         in ret (set_scope (tab, meths_of e1) e1, a) end
     | A.SIf (c, t, e, _) =>
         let
           val (ca, tc, fc) = walk_e senv ctx' c
           val (_, ta) = walk_stmt (add_binds senv tc) ctx' t
           val ea = (case e of SOME e1 => #2 (walk_stmt (add_binds senv fc) ctx' e1) | NONE => [])
           val t_ok = can_complete t
           val e_ok = (case e of SOME e1 => can_complete e1 | NONE => true)
           val intro =
             (case e of
                NONE => if t_ok then [] else fc
              | SOME _ => (if t_ok andalso not e_ok then tc else [])
                          @ (if (not t_ok) andalso e_ok then fc else []))
         in ret (add_binds senv intro, ca @ ta @ ea) end
     | A.SWhile (c, b, _) =>
         let
           val (ca, tc, fc) = walk_e senv ctx' c
           val (_, ba) = walk_stmt (add_binds senv tc) ctx' b
         in ret (loop_after b fc, ca @ ba) end
     | A.SDo (b, c, _) =>
         let
           val (_, ba) = walk_stmt senv ctx' b
           val (ca, _, fc) = walk_e senv ctx' c
         in ret (loop_after b fc, ba @ ca) end
     | A.SFor (init, c, upd, b, _) =>
         let
           val (senv1, ia) =
             (case init of
                NONE => (senv, [])
              | SOME (A.FIVars lv) => walk_localvar senv ctx' lv
              | SOME (A.FIExprs es) => (senv, maps (fn x => #1 (walk_e senv ctx' x)) es))
           val (ca, tc, fc) = (case c of SOME c1 => walk_e senv1 ctx' c1 | NONE => ([], [], []))
           val senv2 = add_binds senv1 tc
           val ua = maps (fn x => #1 (walk_e senv2 ctx' x)) upd
           val (_, ba) = walk_stmt senv2 ctx' b
         in ret (loop_after b fc, ia @ ca @ ua @ ba) end
     | A.SForEach (ms, t, id, e, b, _) =>
         let
           val ea = expr e
           val a0 = walk_mods senv ctx' ms @ walk_type senv ctx' t
           val senv1 = reg_v Var senv id
           val (_, ba) = walk_stmt senv1 ctx' b
         in ret (senv, ea @ a0 @ ba) end
     | A.SBreak (l, _) => (use_label senv l; ret (senv, []))
     | A.SContinue (l, _) => (use_label senv l; ret (senv, []))
     | A.SReturn (e, _) => ret (senv, optl expr e)
     | A.SThrow (e, _) => ret (senv, expr e)
     | A.SYield (e, _) => ret (senv, expr e)
     | A.SAssert (c, m, _) => ret (senv, expr c @ optl expr m)
     | A.SSync (e, b, _) => ret (senv, expr e @ walk_block senv ctx' b)
     | A.STry (res, _, b, cs, f, _) =>
         let
           val (renv, racts) =
             fold (fn r => fn (e1, acc) =>
                     (case r of
                        A.RDecl lv => let val (e2, a) = walk_localvar e1 ctx' lv in (e2,
                          acc @ a) end
                      | A.RExpr x => (e1, acc @ #1 (walk_e e1 ctx' x))))
               res (senv, [])
           val bacts = walk_block renv ctx' b
           fun catch_acts (A.Catch (ms, ts, id, cb, ni)) =
             #2 (scoped senv (fn s =>
               let
                 val a0 = chk s ctx' ni @ walk_mods s ctx' ms @ maps (walk_type s ctx') ts
                 val s1 = reg_v Var s id
               in (s1, a0 @ walk_block s1 ctx' cb) end))
           val facts = (case f of SOME fb => walk_block senv ctx' fb | NONE => [])
         in ret (senv, racts @ bacts @ maps catch_acts cs @ facts) end
     | A.SSwitch (e, cases, _) => ret (senv, expr e @ walk_cases senv ctx' cases)
     | A.SCtorCall (q, ta, _, args, _) =>
         ret (senv, optl expr q @ optl (walk_targs senv ctx') ta @ maps expr args))
  end

(* a local class: its name is in scope in the class and in the rest of the block *)
and walk_local_class senv ctx d id : jenv * acts =
  let
    val senv1 = reg_t Typ senv id
  in (senv1, walk_class senv1 ctx d) end

(* --- declarations ----------------------------------------------------------------------------- *)

and declare_tparams senv ctx tps : jenv * acts =
  let
    val senv1 = fold (fn A.TParam (_, id, _, _) => fn s => reg_t Tparam s id) tps senv
    val acts = maps (fn A.TParam (al, _, bounds, ni) =>
                       chk senv1 ctx ni @ walk_annots senv1 ctx al
                       @ maps (walk_type senv1 ctx) bounds)
                 tps
  in (senv1, acts) end

(* the methods, fields, types, enum constants and components that a class body declares are in
   scope in the whole body *)
and predeclare_members senv members consts comps : jenv =
  let
    val senv1 =
      fold (fn A.EnumConst (_, id, _, _, _) => fn s => reg_v EnumC s id) consts senv
    val senv2 =
      fold (fn A.Param (_, _, _, id, _, _) => fn s => reg_v Fld s id) comps senv1
    val senv3 =
      fold (fn m => fn s =>
              (case m of
                 A.DField (_, _, vds, _) =>
                   fold (fn A.VarDecl (id, _, _, _) => fn s1 => reg_v Fld s1 id) vds s
               | A.DClass (_, id, _, _, _, _, _, _) => reg_t Typ s id
               | A.DInterface (_, id, _, _, _, _, _) => reg_t Typ s id
               | A.DEnum (_, id, _, _, _, _, _) => reg_t Typ s id
               | A.DRecord (_, id, _, _, _, _, _) => reg_t Typ s id
               | A.DAnnotType (_, id, _, _) => reg_t Typ s id
               | _ => s))
        members senv2
    fun method_of m = (case m of
        A.DMethod (_, _, _, id, ps, _, _, _, _, _) =>
          let
            val ps' = filter (fn A.Param (_, _, _, pid, _, _) => not (is_receiver pid)) ps
            val va = (case rev ps' of A.Param (_, _, v, _, _, _) :: _ => v | [] => false)
            val _ = decl_only Meth id
          in [(ident_name_of id, MD {pos = ident_pos id, arity = length ps', varargs = va})] end
      | _ => [])
    (* the accessor methods of the components of a record *)
    val accessors =
      map (fn A.Param (_, _, _, id, _, _) =>
             (ident_name_of id, MD {pos = ident_pos id, arity = 0, varargs = false})) comps
    val explicit = maps method_of members
    val ms = explicit @ filter (fn (n, _) => not (exists (fn (m, _) => m = n) explicit)) accessors
  in add_meths senv3 ms end

and walk_members senv ctx (members : pos A.jDecl list) : acts =
  let val senv1 = predeclare_members senv members [] []
  in #2 (scoped senv1 (fn s => (s, maps (walk_decl s ctx) members))) end

and walk_enum_const senv ctx (A.EnumConst (al, _, args, body, ni)) : acts =
  chk senv ctx ni @ walk_annots senv ctx al
  @ optl (maps (fn x => #1 (walk_e senv ctx x))) args @ optl (walk_members senv ctx) body

(* a class, an interface, an enum, a record or an annotation interface; its name is entered by
   the caller *)
and walk_class senv ctx (d : pos A.jDecl) : acts =
  let
    val ctx' = A.Decl d :: ctx
    val here = chk senv ctx' (A.nodeInfo_of_decl d)
    val (mods, tps, htypes, consts, comps, body) =
      (case d of
         A.DClass (ms, _, tps, ext, impl, perm, body, _) =>
           (ms, tps, (case ext of SOME t => [t] | NONE => []) @ impl @ perm, [], [], body)
       | A.DInterface (ms, _, tps, ext, perm, body, _) => (ms, tps, ext @ perm, [], [], body)
       | A.DEnum (ms, _, impl, consts, _, body, _) => (ms, [], impl, consts, [], body)
       | A.DRecord (ms, _, tps, comps, impl, body, _) => (ms, tps, impl, [], comps, body)
       | A.DAnnotType (ms, _, body, _) => (ms, [], [], [], [], body)
       | _ => raise Fail "walk_class: not a class")
    val macts = walk_mods senv ctx' mods
  in
    here @ macts @
    #2 (scoped senv (fn s =>
      let
        val (s1, tpacts) = declare_tparams s ctx' tps
        val hacts = maps (walk_type s1 ctx') htypes
        val s2 = predeclare_members s1 body consts comps
        val compacts =
          maps (fn A.Param (ms, t, _, _, _, pni) =>
                  chk s2 ctx' pni @ walk_mods s2 ctx' ms @ walk_type s2 ctx' t) comps
        val cacts = maps (walk_enum_const s2 ctx') consts
        val bacts = maps (walk_decl s2 ctx') body
      in (s2, tpacts @ hacts @ compacts @ cacts @ bacts) end))
  end

(* a member of a class body (already declared by "predeclare_members"), or a class *)
and walk_decl senv ctx (d : pos A.jDecl) : acts =
  (case d of
     A.DClass _ => walk_class senv ctx d
   | A.DInterface _ => walk_class senv ctx d
   | A.DEnum _ => walk_class senv ctx d
   | A.DRecord _ => walk_class senv ctx d
   | A.DAnnotType _ => walk_class senv ctx d
   | _ =>
       let
         val ctx' = A.Decl d :: ctx
         val here = chk senv ctx' (A.nodeInfo_of_decl d)
         fun var_init (A.VarDecl (_, ds, init, vni)) =
           chk senv ctx' vni @ maps (walk_dim senv ctx') ds
           @ (case init of SOME x => #1 (walk_e senv ctx' x) | NONE => [])
       in
         here @
         (case d of
            A.DField (ms, t, vds, _) =>
              walk_mods senv ctx' ms @ walk_type senv ctx' t @ maps var_init vds
          | A.DMethod (ms, tps, res, _, ps, ds, thr, body, dflt, _) =>
              #2 (scoped senv (fn s =>
                let
                  val a0 = walk_mods s ctx' ms
                  val (s1, a1) = declare_tparams s ctx' tps
                  val a2 = walk_type s1 ctx' res
                  val (s2, a3) = walk_params s1 ctx' ps
                  val a4 = maps (walk_dim s2 ctx') ds @ maps (walk_type s2 ctx') thr
                  val a5 = (case dflt of
                              SOME v => walk_elemval s2 ctx' v
                            | NONE => [])
                  val a6 = (case body of SOME b => walk_block s2 ctx' b | NONE => [])
                in (s2, a0 @ a1 @ a2 @ a3 @ a4 @ a5 @ a6) end))
          | A.DCtor (ms, tps, id, ps, thr, b, _) =>
              #2 (scoped senv (fn s =>
                let
                  val _ = decl_only Ctor id
                  val a0 = walk_mods s ctx' ms
                  val (s1, a1) = declare_tparams s ctx' tps
                  val (s2, a2) = walk_params s1 ctx' ps
                  val a3 = maps (walk_type s2 ctx') thr
                in (s2, a0 @ a1 @ a2 @ a3 @ walk_block s2 ctx' b) end))
          | A.DCompact (ms, id, b, _) =>
              (decl_only Ctor id; walk_mods senv ctx' ms @ walk_block senv ctx' b)
          | A.DInit (_, b, _) => walk_block senv ctx' b
          | A.DEmpty _ => []
          | _ => [])
       end)

(* --- compilation units ------------------------------------------------------------------------ *)

fun walk_import senv (A.Import (kind, name, ni)) : jenv =
  (case (kind, rev name) of
     (A.ImSingle, last :: _) => reg_t Imp senv last
   | (A.ImStaticSingle, last :: _) =>
       let
         val senv1 = reg_v Imp senv last
         val n = ident_name_of last
       in add_meths senv1 [(n, MD {pos = ident_pos last, arity = 0, varargs = true})] end
   | _ => senv)

fun walk_moddir senv ctx d : acts =
  (case d of
     A.Requires (_, _, ni) => chk senv ctx ni
   | A.Exports (_, _, ni) => chk senv ctx ni
   | A.Opens (_, _, ni) => chk senv ctx ni
   | A.Uses (_, ni) => chk senv ctx ni
   | A.Provides (_, _, ni) => chk senv ctx ni)

fun walk_top senv ctx (decls : pos A.jDecl list) : jenv * acts =
  let val senv1 = predeclare_members senv decls [] []
  in (senv1, maps (walk_decl senv1 ctx) decls) end

fun analyse_and_eval0 (root : pos A.root) thy =
  let
    val jenv0 = get (Context.Theory thy)
    (* The bottom frame is always the top-level root itself, so "ctx" is never empty. *)
    val ctx0 = [root]
    fun drop acts = (thy, acts)
    fun persist (jenv1, acts) = (Context.theory_map (put jenv1) thy, acts)
  in
    case root of
      A.Id (id as A.Ident (_, _, ni)) =>
        let val here = check_antiq jenv0 ctx0 ni
            val _ = use_expr_name jenv0 id
        in (thy, here) end
    | A.Expr e => drop (#1 (walk_e jenv0 ctx0 e))
    | A.Type t => drop (walk_type jenv0 ctx0 t)
    | A.Stmts ss => drop (#2 (walk_stmts jenv0 ctx0 ss))
    | A.Stmt s => drop (#2 (walk_stmt jenv0 ctx0 s))
    | A.Decl d => drop (walk_decl jenv0 ctx0 d)
    | A.Decls ds => persist (walk_top jenv0 ctx0 ds)
    | A.Source (A.Unit (pkg, imports, body, ni)) =>
        let
          val here = check_antiq jenv0 ctx0 ni
          val pacts = (case pkg of SOME (al, _) => walk_annots jenv0 ctx0 al | NONE => [])
          val jenv1 = fold (fn i => fn s => walk_import s i) imports jenv0
          val iacts = maps (fn A.Import (_, _, ini) => chk jenv1 ctx0 ini) imports
        in
          (case body of
             A.Types ds =>
               let val (jenv2, acts) = walk_top jenv1 ctx0 ds
               in persist (jenv2, here @ pacts @ iacts @ acts) end
           | A.Module (al, _, _, dirs, mni) =>
               drop (here @ pacts @ iacts @ chk jenv1 ctx0 mni @ walk_annots jenv1 ctx0 al
                     @ maps (walk_moddir jenv1 ctx0) dirs))
        end
  end

fun analyse_and_eval root thy =
  Dispatched_Antiqs.with_fresh (fn () => analyse_and_eval0 root thy)

end
\<close>


subsection\<open>Some Basic Antiquotation Settings\<close>

text\<open>
  The same eight demonstration antiquotations as C11's (\<open>C11_AnaEval.thy\<close>, whose
  notes on each apply unchanged): \<open>probe_jenv\<close>, \<open>probe_ast\<close>, \<open>highlight\<close>,
  \<open>term\<close>, \<open>ML\<close>, \<open>text\<close>, \<open>definition\<close> and \<open>lemma\<close>. They are written in a
  Go comment as \<^verbatim>\<open>//@ term \<open>x + 1 = (2::nat)\<close>\<close> (or anywhere in a comment as
  \<^verbatim>\<open>@term \<open>...\<close>\<close>) and attach to the node that begins on the next token;
  \<^verbatim>\<open>@tag[navi](level)\<close> selects another node and an evaluation order exactly as in
  C11. Handlers are registered under their tag in \<open>jenv\<close>'s \<open>java_antiq\<close> table;
  nothing here knows Go, only the \<open>root\<close> they are handed.
\<close>

declare [[ML_catch_all = true]]

ML\<open>
val JENV = Unsynchronized.ref(JEnv.empty_jenv);
val probe_jenv = let fun probe (jenv, _ , _) (_ : string * Position.T) thy =
                              (JENV := jenv; thy)
                 in  JEnv.store_antiq
                   ("probe_jenv",  JEnv.lift_theory_antiq probe) end

val JAVA_AST =
  Unsynchronized.ref((Java_Ast.Stmts []): (Position.T Java_Ast.root) )
val probe_ast = let fun probe (_, ast , l) (_ : string * Position.T) thy =
                              (writeln("Level: "^ Int.toString l);
                               writeln("Read : " ^ Java_Pp.pp_root ast);
                               JAVA_AST := ast; thy)
                in  JEnv.store_antiq
                  ("probe_ast",  JEnv.lift_theory_antiq probe) end

val highlight = let fun probe (_, ast , _) (_ : string * Position.T) thy =
                              (Position.report (AnaEval.pos_of_root ast)
                               Markup.intensify;
                               thy)
                in  JEnv.store_antiq
                  ("highlight",  JEnv.lift_theory_antiq probe) end

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
   term is a real Isabelle error positioned in the Go source. The
   catch-all handler is needed because "Syntax.read_term" fails with "Par_Exn",
   not "ERROR". *)
val JAVA_TERM_PROBE =
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
      in (JAVA_TERM_PROBE := t; thy) end
  in JEnv.store_antiq ("term", JEnv.lift_theory_antiq probe) end

(* Runs its body as real ML source, so a definition written in a Go
   comment becomes a later-visible ML binding - the one handler that needs
   "Context.generic -> Context.generic" rather than "theory -> theory". *)
val ml_antiq =
  let
    fun probe (_, _, _) (body, body_pos) : Context.generic -> Context.generic =
      ML_Context.exec (fn () =>
        ML_Context.eval_source (ML_Compiler.verbose true ML_Compiler.flags)
          (body_source (body, body_pos)))
      #> Local_Theory.propagate_ml_env
  in JEnv.store_antiq ("ML", probe) end

(* Isabelle's "text" command: the body goes through the real
   "Document_Output.output_document" (inner antiquotations are checked,
   hyperlinked and hoverable); the result is stashed, not typeset, for the
   reason given in the Limitations of the C11 manual. *)
val JAVA_TEXT_PROBE = Unsynchronized.ref ([] : Latex.text)
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
      in (JAVA_TEXT_PROBE := latex; thy) end
  in JEnv.store_antiq ("text", JEnv.lift_theory_antiq probe) end

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
  in JEnv.store_antiq ("definition", JEnv.lift_theory_antiq probe) end

(* A statement plus one terminal "by" proof, actually proved - proof-carrying
   code: e.g. a property of a VAL abbreviation's value, discharged right where
   the Go text that motivates it lives. *)
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
  in JEnv.store_antiq ("lemma", JEnv.lift_theory_antiq probe) end
\<close>

setup\<open>probe_jenv\<close>
setup\<open>probe_ast\<close>
setup\<open>highlight\<close>
setup\<open>term_antiq\<close>
setup\<open>text_antiq\<close>
setup\<open>ml_antiq\<close>
setup\<open>definition_antiq\<close>
setup\<open>lemma_antiq\<close>
end
