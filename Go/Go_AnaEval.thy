(******************************************************************************
 * Copyright (c) University of Paris-Saclay
 *
 * All rights reserved.
 *
 * Authors: Burkhart Wolff, Claude Sonnet 5.5
 *
 * This is an LLM-generated replication of the Isabelle/C version 2 design to
 * the programming language Go (language version 1.27). It provides an efficient
 * parser for Go, deeply integrated into the Isabelle/PIDE document model,
 * allowing external files as well as in-theory code-snippets which are
 * transparent to the underlying theory. It provides an API for the generated
 * AST’s, and an API to hook up semantic backends that compile these AST’s to
 * theory extensions in Isabelle/HOL. Members of the family come with a
 * Go-specific antiquotation mechanism allowing programmable links to the
 * semantic backends as necessary for support of program-annotations with HOL
 * formulas.
 *
 * This session is part of the Isabelle Programming Language Toolkit
 * (Isabelle/PLTk). The generation has been done with Claude Sonnet 5.5; while
 * the replicants come with a detailed (generated) test-suite for Go, I
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

theory Go_AnaEval
  imports "Go_Env"
begin

section\<open>Analyse and Eval\<close>

text\<open>
  \<open>analyse_and_eval\<close> is the Go counterpart of the passes of the same name of the other
  front-ends (\<^verbatim>\<open>C11_AnaEval.thy\<close>, \<^verbatim>\<open>Occam2_AnaEval.thy\<close>, \<^verbatim>\<open>Scala3_AnaEval.thy\<close>,
  \<^verbatim>\<open>MicroRust_AnaEval.thy\<close>, \<^verbatim>\<open>AdaSpark_AnaEval.thy\<close>, whose long explanations apply here and
  are not repeated): a single, purely functional, scoped walk over a parsed \<open>root\<close>, threading
  \<open>genv\<close> through the descent, collecting every antiquotation action paired with its \<open>level\<close>
  instead of applying it, and hyperlinking every name use to its declaration. What is specific
  to Go:

  \<^item> \<^bold>\<open>One name space, case sensitive.\<close> A variable, a constant, a parameter, a type, a
    function, an imported package and a type parameter are all names of one table. Labels have
    a name space of their own.
  \<^item> \<^bold>\<open>Block scoping.\<close> A name is visible from the end of its declaration to the end of the
    innermost block; a block, a function (its parameters, results and receiver are in the
    scope of its body), the header of an \<open>if\<close>, \<open>for\<close> or \<open>switch\<close> with the statements it governs, a
    \<open>case\<close> clause and a \<open>select\<close> clause are scopes. The scope of a type parameter is its
    declaration. Scoping is shadow-and-restore on the table (the environment is a value, so a
    scope simply does not hand its extension back).
  \<^item> \<^bold>\<open>Declarations.\<close> The names declared at the top level of a package are visible
    throughout it, whatever the order (a function may call one that is defined further down);
    in a function, a declaration is visible only after itself. A type sees itself in its own
    definition. A short variable declaration \<open>a, b := f()\<close> declares the names that are new in
    the current block; the others are assigned to, which is a use. The blank identifier
    declares nothing. The variable of a type switch \<open>switch x := v.(type)\<close> is declared once, at
    the guard, and is visible in every clause.
  \<^item> \<^bold>\<open>Methods and generic receivers.\<close> The type parameters of a method are declared by its
    receiver type (\<open>func (l *List[T]) Push(x T)\<close>), and are visible in the signature and the
    body. A method is declared (its name is reported) but not entered into the table: it is
    reached by selection.
  \<^item> \<^bold>\<open>Selections are not resolved.\<close> \<open>x.f\<close> resolves \<open>x\<close>, and \<open>f\<close> if it is the name of a package
    member only in the sense that \<open>pkg\<close> is an imported package; fields and methods need types. The
    keys of a composite literal that are bare names are field names (or, in a map literal,
    variables - this pass cannot tell) and are not resolved; any other key is an expression.
  \<^item> \<^bold>\<open>Imports\<close> declare the package name - the alias, or the last element of the import path -
    at the import path; a use \<open>pkg.Name\<close> is hyperlinked to it. The standard library is not seen
    by this pass.
  \<^item> \<^bold>\<open>Names that resolve nowhere are not marked.\<close> A Go name very often comes from the universe
    block (\<open>int\<close>, \<open>len\<close>, \<open>nil\<close>), a dot import or another file of the package, none of which this
    pass sees; underlining them would drown the useful markup.
  \<^item> \<^bold>\<open>The top level persists.\<close> After \<open>go\<close> has analysed a source file (or \<open>go_decl\<close> a declaration),
    the names it declares at the top level, imports included, stay in \<open>genv\<close> for the following
    commands, as the files of a package do for each other; a block does not leave anything
    behind.
  \<^item> \<^bold>\<open>Closest context and navigation\<close> as in the other front-ends: expressions (and types, which
    are expressions), statements and declarations push their own node (\<open>Expr\<close>, \<open>Stmt\<close>, \<open>Decl\<close>);
    everything else (parameters, fields, specifications, elements, clauses) uses \<open>hd ctx\<close>. The
    children of a node are, in source order, its sub-expressions, statements and declarations;
    blocks are flattened into their parent.

\<close>
ML\<open>
structure AnaEval = struct

structure A = Go_Ast
open GEnv

type acts = (int * (Context.generic -> Context.generic)) list

fun names_of (mk {names, ...} : genv) = names

fun set_names names' (mk {names = _, go_antiq, units}) =
  mk {names = names', go_antiq = go_antiq, units = units}

(* The position a "root" itself spans: what a "type_antiq_fun" sees as its own "current term". A
   source file has no single span. *)
fun pos_of_root (A.Id id) = A.pos_of_ident id
  | pos_of_root (A.Expr e) = A.pos_of_expr e
  | pos_of_root (A.Stmts (s :: _)) = A.pos_of_stmt s
  | pos_of_root (A.Stmts []) = Position.none
  | pos_of_root (A.Decls (d :: _)) = A.pos_of_decl d
  | pos_of_root (A.Decls []) = Position.none
  | pos_of_root (A.Source (A.File (id, _, _))) = A.pos_of_ident id
  | pos_of_root (A.Stmt s) = A.pos_of_stmt s
  | pos_of_root (A.Decl d) = A.pos_of_decl d

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


(* A navigation step's coarse target category, ignoring the constructor within. *)
fun category (A.Id _)     = 0
  | category (A.Expr _)   = 1
  | category (A.Stmt _)   = 2
  | category (A.Decl _)   = 3
  | category (A.Stmts _)  = 4
  | category (A.Decls _)  = 5
  | category (A.Source _) = 6

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


(* The ordered list of children "r"/"d" may navigate into (see the top-of-theory note):
   sub-expressions, statements and declarations in source order; nodes without a "root"
   counterpart (parameters, fields, elements, clauses, specifications) are flattened into their
   parent's list or dropped. *)
fun opt_expr eo = (case eo of SOME e => [A.Expr e] | NONE => [])
fun exprs es = map A.Expr es
fun opt_stmt so = (case so of SOME s => [A.Stmt s] | NONE => [])

fun block_children (A.Block (stmts, _)) = map A.Stmt stmts

fun param_children (A.Param (_, t, _, _)) = [A.Expr t]
fun sig_children (A.Sig (ps, rs, _)) = maps param_children ps @ maps param_children rs
fun tparam_children (A.TParam (_, c, _)) = [A.Expr c]
fun field_children (A.Field (_, t, _, _)) = [A.Expr t]
fun ielem_children i = (case i of
    A.IMethod (_, sg, _) => sig_children sg
  | A.IType (e, _) => [A.Expr e])
fun element_children (A.Element (k, v, _)) = opt_expr k @ [A.Expr v]

fun children_of_expr e = (case e of
    A.EIdent _ => [] | A.EInt _ => [] | A.EFloat _ => [] | A.EImag _ => [] | A.ERune _ => []
  | A.EString _ => []
  | A.EParen (e1, _) => [A.Expr e1]
  | A.ESelector (e1, _, _) => [A.Expr e1]
  | A.EIndex (e1, args, _) => A.Expr e1 :: exprs args
  | A.ESlice (e1, a, b, c, _) => A.Expr e1 :: (opt_expr a @ opt_expr b @ opt_expr c)
  | A.ETypeAssert (e1, t, _) => A.Expr e1 :: opt_expr t
  | A.ECall (f, args, _, _) => A.Expr f :: exprs args
  | A.EStar (e1, _) => [A.Expr e1]
  | A.EUnary (_, e1, _) => [A.Expr e1]
  | A.EBinary (_, a, b, _) => [A.Expr a, A.Expr b]
  | A.ECompLit (t, elems, _) => opt_expr t @ maps element_children elems
  | A.EFuncLit (sg, body, _) => sig_children sg @ block_children body
  | A.EArrayType (n, t, _) => opt_expr n @ [A.Expr t]
  | A.EEllipsisArray (t, _) => [A.Expr t]
  | A.EMapType (k, v, _) => [A.Expr k, A.Expr v]
  | A.EChanType (_, t, _) => [A.Expr t]
  | A.EFuncType (sg, _) => sig_children sg
  | A.EStructType (fields, _) => maps field_children fields
  | A.EInterfaceType (elems, _) => maps ielem_children elems
  | A.ETilde (e1, _) => [A.Expr e1]
  | A.EUnion (es, _) => exprs es)

fun case_children (A.Case (guards, stmts, _)) =
  (case guards of SOME es => exprs es | NONE => []) @ map A.Stmt stmts

fun comm_children (A.Comm (g, stmts, _)) = opt_stmt g @ map A.Stmt stmts

fun children_of_stmt s = (case s of
    A.SEmpty _ => []
  | A.SExpr (e, _) => [A.Expr e]
  | A.SSend (c, v, _) => [A.Expr c, A.Expr v]
  | A.SIncDec (e, _, _) => [A.Expr e]
  | A.SAssign (l, _, r, _) => exprs l @ exprs r
  | A.SShortVar (l, r, _) => exprs l @ exprs r
  | A.SDecl d => [A.Decl d]
  | A.SLabeled (_, s1, _) => [A.Stmt s1]
  | A.SGo (e, _) => [A.Expr e]
  | A.SDefer (e, _) => [A.Expr e]
  | A.SReturn (es, _) => exprs es
  | A.SBreak _ => [] | A.SContinue _ => [] | A.SGoto _ => [] | A.SFallthrough _ => []
  | A.SBlock b => block_children b
  | A.SIf (init, c, thn, els, _) =>
      opt_stmt init @ [A.Expr c] @ block_children thn @ opt_stmt els
  | A.SSwitch (init, tag, cases, _) => opt_stmt init @ opt_expr tag @ maps case_children cases
  | A.STypeSwitch (init, _, e, cases, _) => opt_stmt init @ [A.Expr e] @ maps case_children cases
  | A.SSelect (comms, _) => maps comm_children comms
  | A.SFor (init, c, post, body, _) =>
      opt_stmt init @ opt_expr c @ opt_stmt post @ block_children body
  | A.SRange (k, v, _, e, body, _) => opt_expr k @ opt_expr v @ [A.Expr e] @ block_children body)

fun spec_children sp = (case sp of
    A.ConstSpec (_, t, vals, _) => opt_expr t @ exprs vals
  | A.VarSpec (_, t, vals, _) => opt_expr t @ exprs vals
  | A.TypeSpec (_, tps, _, t, _) => maps tparam_children tps @ [A.Expr t]
  | A.ImportSpec _ => [])

fun children_of_decl d = (case d of
    A.DConst (specs, _, _) => maps spec_children specs
  | A.DVar (specs, _, _) => maps spec_children specs
  | A.DType (specs, _, _) => maps spec_children specs
  | A.DImport (specs, _, _) => maps spec_children specs
  | A.DFunc (_, tps, sg, body, _) =>
      maps tparam_children tps @ sig_children sg
      @ (case body of SOME b => block_children b | NONE => [])
  | A.DMethod (recv, _, tps, sg, body, _) =>
      maps param_children recv @ maps tparam_children tps @ sig_children sg
      @ (case body of SOME b => block_children b | NONE => []))

fun children_of _ (A.Expr e) = children_of_expr e
  | children_of _ (A.Stmt s) = children_of_stmt s
  | children_of _ (A.Decl d) = children_of_decl d
  | children_of _ (A.Stmts ss) = map A.Stmt ss
  | children_of _ (A.Decls ds) = map A.Decl ds
  | children_of _ (A.Source (A.File (_, ds, _))) = map A.Decl ds
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
   "ni"'s comment list by tag in "genv"'s "go_antiq", instantiates it with
   (genv, select_ast tag_pos navi ctx, level), and pairs the resulting
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
fun check_antiq genv (ctx : pos A.root list) (ni : pos A.nodeInfo)
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
                let val mk {go_antiq, ...} = genv in
                  case Symtab.lookup go_antiq tag of
                    NONE =>
                      error ("analyse_and_eval: no antiquotation handler " ^
                             "registered for tag " ^ quote tag)
                  | SOME antiq_fun =>
                      (Dispatched_Antiqs.mark c;
                       SOME (level,
                             antiq_fun
                               (genv, select_ast tag_pos navi ctx, level)
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


(* Hyperlinks a use of "name" to the declaration registered under "key", if there is one; nothing
   is reported otherwise (see the top-of-theory note). *)
fun use_key genv key name use_pos =
  (case Symtab.lookup (names_of genv) key of
     NONE => ()
   | SOME k =>
       Position.report (name_range (name, use_pos))
         (Position.entity_markup (describe_kind k)
          (name, name_range (name, pos_of_kind k))))

fun use_name genv (A.Ident (name, _, ni)) =
  if name = "_" then () else use_key genv name name (A.pos_of_NodeInfo ni)

(* Labels have a name space of their own: the key cannot be an identifier. *)
fun label_key name = "label:" ^ name

fun use_label genv lbl =
  (case lbl of
     NONE => ()
   | SOME (A.Ident (name, _, ni)) => use_key genv (label_key name) name (A.pos_of_NodeInfo ni))

fun declare kind genv key =
  set_names (Symtab.update (key, kind) (names_of genv)) genv

(* Enters a name silently (no declaration site is reported). *)
fun enter mk_kind genv (A.Ident (name, _, ni)) =
  if name = "_" then genv else declare (mk_kind (A.pos_of_NodeInfo ni)) genv name

(* Declares a name, reporting its declaration site. The blank identifier declares nothing. *)
fun reg mk_kind genv (A.Ident (name, _, ni)) =
  if name = "_" then genv
  else
    let
      val pos = A.pos_of_NodeInfo ni
      val kind = mk_kind pos
      val _ = report_decl (describe_kind kind) name pos
    in declare kind genv name end

fun reg_label genv (A.Ident (name, _, ni)) =
  let
    val pos = A.pos_of_NodeInfo ni
    val kind = Label pos
    val _ = report_decl (describe_kind kind) name pos
  in declare kind genv (label_key name) end

(* A declaration whose name is not entered into the table (a field, a method). *)
fun decl_only mk_kind (A.Ident (name, _, ni)) =
  if name = "_" then ()
  else
    let val pos = A.pos_of_NodeInfo ni
    in report_decl (describe_kind (mk_kind pos)) name pos end

(* Runs "f" in a nested scope: the table is restored on exit. *)
fun scoped genv f =
  let
    val names = names_of genv
    val (genv1, acts) = f genv
  in (set_names names genv1, acts) end

fun optl f x = (case x of NONE => [] | SOME y => f y)

(* A compact wrapper for the antiquotations a node carries (its "nodeInfo"). *)
fun chk genv ctx ni = check_antiq genv ctx ni

fun ident_name_of (A.Ident (n, _, _)) = n

(* The name an import path declares: its last element, unless that is a major version suffix
   "v2", and without the quotes. *)
fun import_name path =
  let
    val inner = String.substring (path, 1, Int.max (size path - 2, 0))
    val parts = String.fields (fn c => c = #"/") inner
    fun is_version p = size p >= 2 andalso String.sub (p, 0) = #"v" andalso
      List.all Char.isDigit (tl (String.explode p))
  in
    (case rev parts of
       last :: prev :: _ => if is_version last then prev else last
     | [last] => last
     | [] => inner)
  end

(* An import declares the package name at the import path (or at the alias). *)
fun reg_import genv (A.ImportSpec (name, path, ni)) =
      (case name of
         SOME (id as A.Ident (n, _, _)) =>
           if n = "_" orelse n = "." then genv else reg Pkg genv id
       | NONE =>
           let
             val pos = A.pos_of_NodeInfo ni
             val pname = import_name path
             val kind = Pkg pos
             val _ = report_decl (describe_kind kind) path pos
           in declare kind genv pname end)
  | reg_import genv _ = genv

fun enter_import genv (A.ImportSpec (name, path, ni)) =
      (case name of
         SOME (id as A.Ident (n, _, _)) =>
           if n = "_" orelse n = "." then genv else enter Pkg genv id
       | NONE => declare (Pkg (A.pos_of_NodeInfo ni)) genv (import_name path))
  | enter_import genv _ = genv

(* The type parameters a method's receiver type declares: "func (l *List[T]) Push(x T)". *)
fun recv_base t = (case t of
    A.EStar (t1, _) => recv_base t1
  | A.EParen (t1, _) => recv_base t1
  | _ => t)

fun recv_targs t = (case recv_base t of
    A.EIndex (_, args, _) => List.mapPartial (fn A.EIdent id => SOME id | _ => NONE) args
  | _ => [])

fun recv_head t = (case recv_base t of A.EIndex (b, _, _) => b | _ => t)

fun walk_expr senv ctx (e : pos A.gExpr) : acts =
  let
    val ctx' = A.Expr e :: ctx
    val here = chk senv ctx' (A.nodeInfo_of_expr e)
    val w = walk_expr senv ctx'
  in
    here @
    (case e of
       A.EIdent id => (use_name senv id; [])
     | A.EInt _ => []
     | A.EFloat _ => []
     | A.EImag _ => []
     | A.ERune _ => []
     | A.EString _ => []
     | A.EParen (e1, _) => w e1
     | A.ESelector (e1, _, _) => w e1
     | A.EIndex (e1, args, _) => w e1 @ maps w args
     | A.ESlice (e1, a, b, c, _) => w e1 @ optl w a @ optl w b @ optl w c
     | A.ETypeAssert (e1, t, _) => w e1 @ optl w t
     | A.ECall (f, args, _, _) => w f @ maps w args
     | A.EStar (e1, _) => w e1
     | A.EUnary (_, e1, _) => w e1
     | A.EBinary (_, a, b, _) => w a @ w b
     | A.ECompLit (t, elems, _) => optl w t @ maps (walk_element senv ctx') elems
     | A.EFuncLit (sg, body, _) =>
         #2 (scoped senv (fn s =>
           let
             val (s1, names, a1) = walk_sig s ctx' sg
             val a2 = walk_body s1 ctx' names body
           in (s1, a1 @ a2) end))
     | A.EArrayType (n, t, _) => optl w n @ w t
     | A.EEllipsisArray (t, _) => w t
     | A.EMapType (k, v, _) => w k @ w v
     | A.EChanType (_, t, _) => w t
     | A.EFuncType (sg, _) => walk_sig_type senv ctx' sg
     | A.EStructType (fields, _) => maps (walk_field senv ctx') fields
     | A.EInterfaceType (elems, _) => maps (walk_ielem senv ctx') elems
     | A.ETilde (e1, _) => w e1
     | A.EUnion (es, _) => maps w es)
  end

(* A bare name as the key of a composite literal is a field name (or, in a map literal, a
   variable: this pass cannot tell), and is not resolved. *)
and walk_element senv ctx (A.Element (k, v, ni)) : acts =
  chk senv ctx ni
  @ (case k of
       NONE => []
     | SOME (e as A.EIdent _) => chk senv (A.Expr e :: ctx) (A.nodeInfo_of_expr e)
     | SOME e => walk_expr senv ctx e)
  @ walk_expr senv ctx v

(* The types of a parameter list, seen in the scope outside of the function. *)
and walk_param_types senv ctx ps : acts =
  maps (fn A.Param (_, t, _, ni) => chk senv ctx ni @ walk_expr senv ctx t) ps

(* A signature as a type: its parameter names are declared nowhere. *)
and walk_sig_type senv ctx (A.Sig (ps, rs, ni)) : acts =
  let
    val _ = List.app (fn A.Param (names, _, _, _) => List.app (decl_only Param) names) (ps @ rs)
  in chk senv ctx ni @ walk_param_types senv ctx ps @ walk_param_types senv ctx rs end

(* A signature of a function: the types first, then the names, which are declared in the scope of
   the body. Returns the names, which are in the outermost block of the body. *)
and walk_sig senv ctx (A.Sig (ps, rs, ni)) : genv * string list * acts =
  let
    val a1 = chk senv ctx ni @ walk_param_types senv ctx ps @ walk_param_types senv ctx rs
    val ids = maps (fn A.Param (names, _, _, _) => names) (ps @ rs)
    val senv1 = fold (fn id => fn s => reg Param s id) ids senv
    val names = filter (fn n => n <> "_") (map ident_name_of ids)
  in (senv1, names, a1) end

and walk_field senv ctx (A.Field (names, t, _, ni)) : acts =
  let val _ = List.app (decl_only Fld) names
  in chk senv ctx ni @ walk_expr senv ctx t end

and walk_ielem senv ctx ie : acts =
  (case ie of
     A.IMethod (id, sg, ni) =>
       let val _ = decl_only Meth id
       in chk senv ctx ni @ walk_sig_type senv ctx sg end
   | A.IType (e, ni) => chk senv ctx ni @ walk_expr senv ctx e)

(* Type parameters are declared first, all of them, as the constraint of one may mention another
   ("[S ~[]E, E any]"). *)
and walk_tparams senv ctx tps : genv * acts =
  let
    val senv1 =
      fold (fn A.TParam (names, _, _) => fn s => fold (fn id => fn s1 => reg Tparam s1 id) names s)
        tps senv
    val acts = maps (fn A.TParam (_, c, ni) => chk senv1 ctx ni @ walk_expr senv1 ctx c) tps
  in (senv1, acts) end

(* The statements of a block in the scope that is already open, "blk" being the names declared
   so far in that scope. *)
and walk_body senv ctx blk (A.Block (stmts, ni)) : acts =
  let val (_, _, acts) = walk_stmts senv ctx blk stmts
  in chk senv ctx ni @ acts end

and walk_block senv ctx b : acts = #2 (scoped senv (fn s => (s, walk_body s ctx [] b)))

and walk_stmts senv ctx blk stmts : genv * string list * acts =
  fold (fn s => fn (e, b, acc) =>
          let val (e', b', a) = walk_stmt e ctx b s in (e', b', acc @ a) end)
    stmts (senv, blk, [])

(* "a, b := ..." declares the names that are new in the current block; the others are assigned
   to, which is a use. *)
and define senv ctx blk lhs : genv * string list * acts =
  fold (fn e => fn (s, b, acc) =>
          let
            val ctx' = A.Expr e :: ctx
            val here = chk s ctx' (A.nodeInfo_of_expr e)
          in
            (case e of
               A.EIdent (id as A.Ident (name, _, _)) =>
                 if name = "_" then (s, b, acc @ here)
                 else if member (op =) b name then (use_name s id; (s, b, acc @ here))
                 else (reg Var s id, name :: b, acc @ here)
             | _ => (s, b, acc @ here @ walk_expr s ctx e))
          end)
    lhs (senv, blk, [])

and walk_stmt senv ctx blk (s : pos A.gStmt) : genv * string list * acts =
  let
    val ctx' = A.Stmt s :: ctx
    val here = chk senv ctx' (A.nodeInfo_of_stmt s)
    val we = walk_expr senv ctx'
    fun ret (env, b, a) = (env, b, here @ a)
    fun plain a = ret (senv, blk, a)
    fun init_of s0 i = (case i of
        SOME i1 => walk_stmt s0 ctx' [] i1
      | NONE => (s0, [], []))
  in
    (case s of
       A.SEmpty _ => plain []
     | A.SExpr (e, _) => plain (we e)
     | A.SSend (c, v, _) => plain (we c @ we v)
     | A.SIncDec (e, _, _) => plain (we e)
     | A.SAssign (l, _, r, _) => plain (maps we l @ maps we r)
     | A.SShortVar (lhs, rhs, _) =>
         let
           val a1 = maps we rhs
           val (senv1, blk1, a2) = define senv ctx' blk lhs
         in ret (senv1, blk1, a1 @ a2) end
     | A.SDecl d => ret (walk_decl senv ctx' blk d)
     | A.SLabeled (l, s1, _) =>
         let
           val senv1 = reg_label senv l
           val (senv2, blk2, a) = walk_stmt senv1 ctx' blk s1
         in ret (senv2, blk2, a) end
     | A.SGo (e, _) => plain (we e)
     | A.SDefer (e, _) => plain (we e)
     | A.SReturn (es, _) => plain (maps we es)
     | A.SBreak (l, _) => (use_label senv l; plain [])
     | A.SContinue (l, _) => (use_label senv l; plain [])
     | A.SGoto (l, _) => (use_label senv (SOME l); plain [])
     | A.SFallthrough _ => plain []
     | A.SBlock b => plain (walk_block senv ctx' b)
     | A.SIf (init, c, thn, els, _) =>
         plain (#2 (scoped senv (fn s0 =>
           let
             val (s1, _, a1) = init_of s0 init
             val a2 = walk_expr s1 ctx' c
             val a3 = walk_block s1 ctx' thn
             val a4 = (case els of SOME e => #3 (walk_stmt s1 ctx' [] e) | NONE => [])
           in (s1, a1 @ a2 @ a3 @ a4) end)))
     | A.SSwitch (init, tag, cases, _) =>
         plain (#2 (scoped senv (fn s0 =>
           let
             val (s1, _, a1) = init_of s0 init
             val a2 = optl (walk_expr s1 ctx') tag
             val a3 = maps (walk_case s1 ctx' NONE) cases
           in (s1, a1 @ a2 @ a3) end)))
     | A.STypeSwitch (init, bind, x, cases, _) =>
         plain (#2 (scoped senv (fn s0 =>
           let
             val (s1, _, a1) = init_of s0 init
             val a2 = walk_expr s1 ctx' x
             val _ = (case bind of SOME id => decl_only Var id | NONE => ())
             val a3 = maps (walk_case s1 ctx' bind) cases
           in (s1, a1 @ a2 @ a3) end)))
     | A.SSelect (comms, _) => plain (maps (walk_comm senv ctx') comms)
     | A.SFor (init, c, post, body, _) =>
         plain (#2 (scoped senv (fn s0 =>
           let
             val (s1, _, a1) = init_of s0 init
             val a2 = optl (walk_expr s1 ctx') c
             val a3 = (case post of SOME p => #3 (walk_stmt s1 ctx' [] p) | NONE => [])
             val a4 = walk_block s1 ctx' body
           in (s1, a1 @ a2 @ a3 @ a4) end)))
     | A.SRange (k, v, def, e, body, _) =>
         let
           (* the ranged-over expression is not in the scope of the loop variables *)
           val a1 = we e
           val (_, a2) = scoped senv (fn s0 =>
             let
               val ks = (case k of SOME k1 => [k1] | NONE => [])
                        @ (case v of SOME v1 => [v1] | NONE => [])
               val (s1, a3) =
                 if def then (fn (s2, _, a) => (s2, a)) (define s0 ctx' [] ks)
                 else (s0, maps we ks)
               val a4 = walk_block s1 ctx' body
             in (s1, a3 @ a4) end)
         in plain (a1 @ a2) end)
  end

(* A case clause; the variable of a type switch is declared once, at the guard, and is visible
   in every clause. *)
and walk_case senv ctx bind (A.Case (guards, stmts, ni)) : acts =
  #2 (scoped senv (fn s0 =>
    let
      val a1 = chk s0 ctx ni @ (case guards of SOME es => maps (walk_expr s0 ctx) es | NONE => [])
      val s1 = (case bind of SOME id => enter Var s0 id | NONE => s0)
      val (_, _, a2) = walk_stmts s1 ctx [] stmts
    in (s1, a1 @ a2) end))

and walk_comm senv ctx (A.Comm (g, stmts, ni)) : acts =
  #2 (scoped senv (fn s0 =>
    let
      val a0 = chk s0 ctx ni
      val (s1, _, a1) = (case g of SOME g1 => walk_stmt s0 ctx [] g1 | NONE => (s0, [], []))
      val (_, _, a2) = walk_stmts s1 ctx [] stmts
    in (s1, a0 @ a1 @ a2) end))

and walk_spec senv ctx blk spec : genv * string list * acts =
  (case spec of
     A.ConstSpec (ids, t, vals, ni) => walk_values Const senv ctx blk (ids, t, vals, ni)
   | A.VarSpec (ids, t, vals, ni) => walk_values Var senv ctx blk (ids, t, vals, ni)
   | A.TypeSpec (name, tps, _, t, ni) =>
       let
         val senv1 = reg Typ senv name
         val blk1 = if ident_name_of name = "_" then blk else ident_name_of name :: blk
         val (_, a) = scoped senv1 (fn s =>
           let
             val (s1, a1) = walk_tparams s ctx tps
             val a2 = walk_expr s1 ctx t
           in (s1, a1 @ a2) end)
       in (senv1, blk1, chk senv ctx ni @ a) end
   | A.ImportSpec (_, _, ni) => (reg_import senv spec, blk, chk senv ctx ni))

(* The values are evaluated before the names are declared. *)
and walk_values mk_kind senv ctx blk (ids, t, vals, ni) : genv * string list * acts =
  let
    val a = chk senv ctx ni @ optl (walk_expr senv ctx) t @ maps (walk_expr senv ctx) vals
    val senv1 = fold (fn id => fn s => reg mk_kind s id) ids senv
    val blk1 = filter (fn n => n <> "_") (map ident_name_of ids) @ blk
  in (senv1, blk1, a) end

and walk_specs senv ctx blk specs : genv * string list * acts =
  fold (fn sp => fn (e, b, acc) =>
          let val (e', b', a) = walk_spec e ctx b sp in (e', b', acc @ a) end)
    specs (senv, blk, [])

and walk_decl senv ctx blk (d : pos A.gDecl) : genv * string list * acts =
  let
    val ctx' = A.Decl d :: ctx
    val here = chk senv ctx' (A.nodeInfo_of_decl d)
    fun ret (e, b, a) = (e, b, here @ a)
  in
    (case d of
       A.DConst (specs, _, _) => ret (walk_specs senv ctx' blk specs)
     | A.DVar (specs, _, _) => ret (walk_specs senv ctx' blk specs)
     | A.DType (specs, _, _) => ret (walk_specs senv ctx' blk specs)
     | A.DImport (specs, _, _) => ret (walk_specs senv ctx' blk specs)
     | A.DFunc (name, tps, sg, body, _) =>
         let
           val senv1 = reg Func senv name
           val (_, a) = scoped senv1 (fn s =>
             let
               val (s1, a1) = walk_tparams s ctx' tps
               val (s2, names, a2) = walk_sig s1 ctx' sg
               val a3 = (case body of SOME b => walk_body s2 ctx' names b | NONE => [])
             in (s2, a1 @ a2 @ a3) end)
         in ret (senv1, blk, a) end
     | A.DMethod (recv, name, tps, sg, body, _) =>
         let
           val _ = decl_only Meth name
           val (_, a) = scoped senv (fn s =>
             let
               (* the receiver declares the type parameters of the type *)
               val targs = maps (fn A.Param (_, t, _, _) => recv_targs t) recv
               val s0 = fold (fn id => fn s' => reg Tparam s' id) targs s
               val a0 = maps (fn A.Param (_, t, _, ni) =>
                                chk s0 ctx' ni @ walk_expr s0 ctx' (recv_head t)) recv
               val rids = maps (fn A.Param (names, _, _, _) => names) recv
               val s1 = fold (fn id => fn s' => reg Param s' id) rids s0
               val (s2, a1) = walk_tparams s1 ctx' tps
               val (s3, names, a2) = walk_sig s2 ctx' sg
               val names' = names @ filter (fn n => n <> "_") (map ident_name_of rids)
               val a3 = (case body of SOME b => walk_body s3 ctx' names' b | NONE => [])
             in (s3, a0 @ a1 @ a2 @ a3) end)
         in ret (senv, blk, a) end)
  end

(* The names declared at the top level of a package are visible throughout it: they are entered
   before anything is walked. *)
fun predeclare senv (d : pos A.gDecl) =
  let
    fun enter_all mk_kind ids s = fold (fn id => fn s1 => enter mk_kind s1 id) ids s
    fun values mk_kind specs =
      fold (fn A.ConstSpec (ids, _, _, _) => enter_all mk_kind ids
             | A.VarSpec (ids, _, _, _) => enter_all mk_kind ids
             | A.TypeSpec (name, _, _, _, _) => (fn s => enter mk_kind s name)
             | sp => (fn s => enter_import s sp)) specs senv
  in
    (case d of
       A.DConst (specs, _, _) => values Const specs
     | A.DVar (specs, _, _) => values Var specs
     | A.DType (specs, _, _) => values Typ specs
     | A.DImport (specs, _, _) => values Pkg specs
     | A.DFunc (name, _, _, _, _) => enter Func senv name
     | A.DMethod _ => senv)
  end

fun walk_top senv ctx (decls : pos A.gDecl list) : genv * acts =
  let
    val senv1 = fold (fn d => fn s => predeclare s d) decls senv
    val (senv2, _, acts) =
      fold (fn d => fn (e, b, acc) =>
              let val (e', b', a) = walk_decl e ctx b d in (e', b', acc @ a) end)
        decls (senv1, [], [])
  in (senv2, acts) end

fun analyse_and_eval0 (root : pos A.root) thy =
  let
    val genv0 = get (Context.Theory thy)
    (* The bottom frame is always the top-level root itself, so "ctx" is never empty. *)
    val ctx0 = [root]
    fun drop acts = (thy, acts)
    fun persist (genv1, acts) = (Context.theory_map (put genv1) thy, acts)
  in
    case root of
      A.Id (id as A.Ident (_, _, ni)) =>
        let val here = check_antiq genv0 ctx0 ni
            val _ = use_name genv0 id
        in (thy, here) end
    | A.Expr e => drop (walk_expr genv0 ctx0 e)
    | A.Stmts ss => drop (#3 (walk_stmts genv0 ctx0 [] ss))
    | A.Stmt s => drop (#3 (walk_stmt genv0 ctx0 [] s))
    | A.Decl d => drop (#3 (walk_decl genv0 ctx0 [] d))
    | A.Decls ds => persist (walk_top genv0 ctx0 ds)
    | A.Source (A.File (pkg, ds, ni)) =>
        let
          val here = check_antiq genv0 ctx0 ni
          val _ = decl_only Pkg pkg
          val (genv1, acts) = walk_top genv0 ctx0 ds
        in persist (genv1, here @ acts) end
  end

fun analyse_and_eval root thy =
  Dispatched_Antiqs.with_fresh (fn () => analyse_and_eval0 root thy)

end
\<close>

subsection\<open>Some Basic Antiquotation Settings\<close>

text\<open>
  The same eight demonstration antiquotations as C11's (\<open>C11_AnaEval.thy\<close>, whose
  notes on each apply unchanged): \<open>probe_genv\<close>, \<open>probe_ast\<close>, \<open>highlight\<close>,
  \<open>term\<close>, \<open>ML\<close>, \<open>text\<close>, \<open>definition\<close> and \<open>lemma\<close>. They are written in a
  Go comment as \<^verbatim>\<open>//@ term \<open>x + 1 = (2::nat)\<close>\<close> (or anywhere in a comment as
  \<^verbatim>\<open>@term \<open>...\<close>\<close>) and attach to the node that begins on the next token;
  \<^verbatim>\<open>@tag[navi](level)\<close> selects another node and an evaluation order exactly as in
  C11. Handlers are registered under their tag in \<open>genv\<close>'s \<open>go_antiq\<close> table;
  nothing here knows Go, only the \<open>root\<close> they are handed.
\<close>

declare [[ML_catch_all = true]]

ML\<open>
val GENV = Unsynchronized.ref(GEnv.empty_genv);
val probe_genv = let fun probe (genv, _ , _) (_ : string * Position.T) thy =
                              (GENV := genv; thy)
                 in  GEnv.store_antiq
                   ("probe_genv",  GEnv.lift_theory_antiq probe) end

val GO_AST =
  Unsynchronized.ref((Go_Ast.Stmts []): (Position.T Go_Ast.root) )
val probe_ast = let fun probe (_, ast , l) (_ : string * Position.T) thy =
                              (writeln("Level: "^ Int.toString l);
                               writeln("Read : " ^ Go_Pp.pp_root ast);
                               GO_AST := ast; thy)
                in  GEnv.store_antiq
                  ("probe_ast",  GEnv.lift_theory_antiq probe) end

val highlight = let fun probe (_, ast , _) (_ : string * Position.T) thy =
                              (Position.report (AnaEval.pos_of_root ast)
                               Markup.intensify;
                               thy)
                in  GEnv.store_antiq
                  ("highlight",  GEnv.lift_theory_antiq probe) end

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
val GO_TERM_PROBE =
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
      in (GO_TERM_PROBE := t; thy) end
  in GEnv.store_antiq ("term", GEnv.lift_theory_antiq probe) end

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
  in GEnv.store_antiq ("ML", probe) end

(* Isabelle's "text" command: the body goes through the real
   "Document_Output.output_document" (inner antiquotations are checked,
   hyperlinked and hoverable); the result is stashed, not typeset, for the
   reason given in the Limitations of the C11 manual. *)
val GO_TEXT_PROBE = Unsynchronized.ref ([] : Latex.text)
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
      in (GO_TEXT_PROBE := latex; thy) end
  in GEnv.store_antiq ("text", GEnv.lift_theory_antiq probe) end

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
  in GEnv.store_antiq ("definition", GEnv.lift_theory_antiq probe) end

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
  in GEnv.store_antiq ("lemma", GEnv.lift_theory_antiq probe) end
\<close>

setup\<open>probe_genv\<close>
setup\<open>probe_ast\<close>
setup\<open>highlight\<close>
setup\<open>term_antiq\<close>
setup\<open>text_antiq\<close>
setup\<open>ml_antiq\<close>
setup\<open>definition_antiq\<close>
setup\<open>lemma_antiq\<close>
end
