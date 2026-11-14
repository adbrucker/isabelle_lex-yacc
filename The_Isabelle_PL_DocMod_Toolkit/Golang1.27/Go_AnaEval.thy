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
  imports "Go_Env" "Go_Parser"
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
  \<^item> \<^bold>\<open>Selections are resolved with types, and only when that is certain.\<close> \<open>x.f\<close> resolves \<open>x\<close>;
    \<open>f\<close> is hyperlinked to the field or method it denotes if the type of \<open>x\<close> is known well enough
    to tell, and left unmarked otherwise. The types are computed by a pure function
    \<open>type_of\<close> over the expression: the type of a name is the one it was declared with
    (\<open>var\<close>, a parameter, a result, a receiver, a constant) or the one of the value that
    defined it (\<open>:=\<close>, \<open>var x = v\<close>, a range variable, the variable of a type switch in the
    clause); a call has the result type of the signature of its callee, a conversion the type
    converted to, \<open>*p\<close>, \<open>&x\<close>, \<open><-c\<close>, \<open>a[i]\<close>, \<open>a[i:j]\<close>, \<open>x.(T)\<close>, a composite literal and a
    function literal their natural types, and the builtins \<open>len\<close>, \<open>new\<close>, \<open>make\<close>, \<open>append\<close>... what
    they are known to return. The type arguments of a call of a generic function (or of a generic
    method) are inferred: from the typed arguments by unification (a type literal meeting the
    structure of a defined type), from the core types of the constraints (\<open>S ~[]E\<close>: E is the
    element type of S), and from untyped constants by their default type; a type parameter about
    which anything is doubtful stays \<open>TUnknown\<close>. Everything else - for instance an imported
    type when no Go tree is found - is \<open>TUnknown\<close>, on which nothing is ever linked. A named type is a \<^emph>\<open>reference\<close> to its declaration
    (the position of its name), so types, fields and methods may be mutually recursive and
    declared in any order: the types, signatures and methods of a package are registered
    before anything is walked, and the types of package-level variables that are inferred are
    found in a few rounds, which also settles variables that depend on each other. The lookup
    follows the language: the pointer is dereferenced automatically, the members of an
    embedded type are promoted, the shallowest depth wins and a tie is ambiguous (no link), an
    interface has the methods of the interfaces it embeds, a type parameter those of its
    constraint, an alias those of its target, and an instantiated generic type has its type
    arguments substituted; a match is dropped if an embedded type this pass does not know
    could have provided the same name nearer. The keys of a composite literal are fields of
    its (struct) type, also in elided elements (\<open>[]T{{a: 1}}\<close>); in a map literal they are
    expressions; when the type of the literal is unknown a bare name as a key is left alone,
    as it could be either.
  \<^item> \<^bold>\<open>Imports\<close> declare the package name - the alias, or the last element of the import path -
    at the import path; a use \<open>pkg.Name\<close> is hyperlinked to it. The imported package is read from
    a Go tree if one is found (see \<open>Pkg_Store\<close>, \<open>load_package\<close> and \<open>target_string\<close> below): its
    exported members are hyperlinked to their declarations in the files of the tree, and its
    types, functions and methods are known to the type pass.
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
fun vtypes_of (mk {vtypes, ...} : genv) = vtypes
fun defs_of (mk {defs, ...} : genv) = defs
fun meths_of (mk {meths, ...} : genv) = meths

(* The scope of a name is that of its type: the two tables are always set together. *)
fun target_of (mk {target, ...} : genv) = target

fun set_scope (names', vtypes') (mk {names = _, vtypes = _, defs, meths, go_antiq, units, target}) =
  mk {names = names', vtypes = vtypes', defs = defs, meths = meths, go_antiq = go_antiq,
      units = units, target = target}

fun add_def key d (mk {names, vtypes, defs, meths, go_antiq, units, target}) =
  mk {names = names, vtypes = vtypes, defs = Symtab.update (key, d) defs, meths = meths,
      go_antiq = go_antiq, units = units, target = target}

fun add_meth key m (mk {names, vtypes, defs, meths, go_antiq, units, target}) =
  mk {names = names, vtypes = vtypes, defs = defs, meths = Symtab.update (key, m) meths,
      go_antiq = go_antiq, units = units, target = target}

fun set_vtypes vtypes' (mk {names, vtypes = _, defs, meths, go_antiq, units, target}) =
  mk {names = names, vtypes = vtypes', defs = defs, meths = meths, go_antiq = go_antiq,
      units = units, target = target}

fun set_target target' (mk {names, vtypes, defs, meths, go_antiq, units, target = _}) =
  mk {names = names, vtypes = vtypes, defs = defs, meths = meths, go_antiq = go_antiq,
      units = units, target = target'}

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

(* A name that is declared again at the very same site (the pre-pass of a package, then the walk)
   keeps its type; at another site (a shadowing declaration) it starts without one. *)
fun declare kind genv key =
  let
    val same_site =
      (case Symtab.lookup (names_of genv) key of
         SOME k => pos_of_kind k = pos_of_kind kind
       | NONE => false)
    val vts = if same_site then vtypes_of genv else Symtab.delete_safe key (vtypes_of genv)
  in set_scope (Symtab.update (key, kind) (names_of genv), vts) genv end

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
    val scope = (names_of genv, vtypes_of genv)
    val (genv1, acts) = f genv
  in (set_scope scope genv1, acts) end

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

(* The import path without its quotes. *)
fun unquote_path path = String.substring (path, 1, Int.max (size path - 2, 0))

(* The package name stands for the package: its type is the import path. *)
fun set_pkg_path name path genv =
  set_vtypes (Symtab.update (name, TPkg (unquote_path path)) (vtypes_of genv)) genv

(* An import declares the package name at the import path (or at the alias). *)
fun reg_import genv (A.ImportSpec (name, path, ni)) =
      (case name of
         SOME (id as A.Ident (n, _, _)) =>
           if n = "_" orelse n = "." then genv else set_pkg_path n path (reg Pkg genv id)
       | NONE =>
           let
             val pos = A.pos_of_NodeInfo ni
             val pname = import_name path
             val kind = Pkg pos
             val _ = report_decl (describe_kind kind) path pos
           in set_pkg_path pname path (declare kind genv pname) end)
  | reg_import genv _ = genv

fun enter_import genv (A.ImportSpec (name, path, ni)) =
      (case name of
         SOME (id as A.Ident (n, _, _)) =>
           if n = "_" orelse n = "." then genv else set_pkg_path n path (enter Pkg genv id)
       | NONE =>
           let val pname = import_name path
           in set_pkg_path pname path (declare (Pkg (A.pos_of_NodeInfo ni)) genv pname) end)
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

(* ---- Types: what the resolution of selections needs ----------------------------------------

   Everything below is pure (no report, no antiquotation) and works on the "genv" it is given, so
   it can be asked about any expression at any point of the walk. See the top-of-theory note. *)

(* ---- Packages that are imported --------------------------------------------------------------
   The packages a program imports are read from a Go tree (see "target_string" below): the source
   files of a package are parsed on first use, and their declarations are converted to types the
   first time one of them is needed. What has been loaded lives in this store, shared by all
   theories, keyed by the target (root, operating system, architecture) and the import path, so it
   is read from disk once per session. The definitions of the types of an imported package are
   found by their key, like those of the program itself (see "get_def"). *)
structure Pkg_Store = struct
  (* the package-level names, the conversion of its declarations (which also publishes the type
     definitions and methods to "defs" and "meths"), the types of its variables and constants *)
  datatype pkg = Pk of {members : ident_kind Symtab.table,
                        conv : {ftypes : ty Symtab.table} Lazy.lazy,
                        vtys : ty Symtab.table Lazy.lazy}
  val defs = Synchronized.var "Go_Pkg.defs" (Symtab.empty : tydef Symtab.table)
  val meths = Synchronized.var "Go_Pkg.meths" (Symtab.empty : methdef Symtab.table)
  val pkgs = Synchronized.var "Go_Pkg.pkgs" (Symtab.empty : pkg option Symtab.table)
  val owners = Synchronized.var "Go_Pkg.owners" (Symtab.empty : string Symtab.table)
  fun k tgt key = tgt ^ "|" ^ key
  fun def tgt key = Symtab.lookup (Synchronized.value defs) (k tgt key)
  fun meth tgt key name = Symtab.lookup (Synchronized.value meths) (k tgt (key ^ "|" ^ name))
  fun owner tgt key = Symtab.lookup (Synchronized.value owners) (k tgt key)
  (* set once the loader below is defined *)
  val load_hook : (string -> string -> pkg option) Unsynchronized.ref =
    Unsynchronized.ref (fn _ => fn _ => NONE)
  val member_hook : (genv -> string -> string -> (ident_kind * ty) option) Unsynchronized.ref =
    Unsynchronized.ref (fn _ => fn _ => fn _ => NONE)
  fun force tgt path =
    (case !load_hook tgt path of SOME (Pk {conv, ...}) => ignore (Lazy.force conv) | NONE => ())
end

(* The definition of the type declared under "key", in the program or in an imported package
   (whose conversion this forces). *)
fun get_def genv key =
  (case Symtab.lookup (defs_of genv) key of
     SOME d => SOME d
   | NONE =>
       let val tgt = target_of genv
       in
         if tgt = "" then NONE
         else
           (case Pkg_Store.def tgt key of
              SOME d => SOME d
            | NONE =>
                (case Pkg_Store.owner tgt key of
                   SOME path => (try (Pkg_Store.force tgt) path; Pkg_Store.def tgt key)
                 | NONE => NONE))
       end)

fun get_meth genv key name =
  (case Symtab.lookup (meths_of genv) (key ^ "|" ^ name) of
     SOME m => SOME m
   | NONE =>
       let val tgt = target_of genv
       in
         if tgt = "" then NONE
         else
           (case Pkg_Store.meth tgt key name of
              SOME m => SOME m
            | NONE =>
                (case Pkg_Store.owner tgt key of
                   SOME path => (try (Pkg_Store.force tgt) path; Pkg_Store.meth tgt key name)
                 | NONE => NONE))
       end)


val int_ty = TBasic "int"
val bool_ty = TBasic "bool"

val basic_type_names =
  ["bool", "byte", "complex64", "complex128", "error", "float32", "float64", "int", "int8",
   "int16", "int32", "int64", "rune", "string", "uint", "uint8", "uint16", "uint32", "uint64",
   "uintptr", "comparable"]

val integer_type_names =
  ["byte", "int", "int8", "int16", "int32", "int64", "rune", "uint", "uint8", "uint16", "uint32",
   "uint64", "uintptr"]

(* What an expression denotes: a value of a type, or a type. *)
datatype tv = Val of ty | Ty of ty

(* A name of the universe block, unless the program has declared it itself. *)
fun lookup_ident genv name : tv =
  (case Symtab.lookup (names_of genv) name of
     SOME (Typ p) => Ty (TNamed (pos_key p, []))
   | SOME (Tparam p) => Ty (TVar (pos_key p))
   | SOME (Var _) => Val (the_default TUnknown (Symtab.lookup (vtypes_of genv) name))
   | SOME (Const _) => Val (the_default TUnknown (Symtab.lookup (vtypes_of genv) name))
   | SOME (Param _) => Val (the_default TUnknown (Symtab.lookup (vtypes_of genv) name))
   | SOME (Func _) => Val (the_default TUnknown (Symtab.lookup (vtypes_of genv) name))
   | SOME (Pkg _) => Val (the_default TUnknown (Symtab.lookup (vtypes_of genv) name))
   | SOME _ => Val TUnknown
   | NONE =>
       if name = "any" then Ty (TIface ([], []))
       else if name = "byte" then Ty (TBasic "uint8")
       else if name = "rune" then Ty (TBasic "int32")
       else if member (op =) basic_type_names name then Ty (TBasic name)
       else if name = "true" orelse name = "false" then Val bool_ty
       else if name = "iota" then Val int_ty
       else Val TUnknown)

fun meth_key tkey name = tkey ^ "|" ^ name

(* Substitution of type parameters (by key). *)
fun subst (m : (string * ty) list) (t : ty) : ty =
  let
    fun s t = (case t of
        TVar k => the_default t (AList.lookup (op =) m k)
      | TNamed (k, args) => TNamed (k, map s args)
      | TPtr t1 => TPtr (s t1)
      | TSlice t1 => TSlice (s t1)
      | TArray t1 => TArray (s t1)
      | TMap (a, b) => TMap (s a, s b)
      | TChan t1 => TChan (s t1)
      | TFunc sg => TFunc (ssig sg)
      | TStruct fs => TStruct (map (fn TF (n, p, t1, e) => TF (n, p, s t1, e)) fs)
      | TIface (ms, es) => TIface (map (fn TM (n, p, sg) => TM (n, p, ssig sg)) ms, map s es)
      | TTuple ts => TTuple (map s ts)
      | TGeneric (ks, sg) => TGeneric (ks, ssig sg)
      | TTilde t1 => TTilde (s t1)
      | TUnion ts => TUnion (map s ts)
      | _ => t)
    and ssig (TSig (ps, rs, v)) = TSig (map s ps, map s rs, v)
  in if null m then t else s t end

(* The type parameters of a declaration instantiated by "args"; with the wrong number of
   arguments (an uninstantiated mention) they are unknown. *)
fun inst_map (tparams, args) =
  if length tparams = length args then tparams ~~ args else map (fn k => (k, TUnknown)) tparams

(* The structure of a type: named types and aliases are unfolded, type arguments substituted. A
   cycle (invalid Go) is cut by the fuel. *)
fun under genv fuel (t : ty) : ty =
  (case t of
     TNamed (k, args) =>
       if fuel <= 0 then TUnknown
       else
         (case get_def genv k of
            SOME (TDef {tparams, rhs, ...}) =>
              under genv (fuel - 1) (subst (inst_map (tparams, args)) rhs)
          | NONE => TUnknown)
   | _ => t)

fun strip_paren e = (case e of A.EParen (e1, _) => strip_paren e1 | _ => e)

fun embedded_id t = (case t of
    A.EStar (t1, _) => embedded_id t1
  | A.EParen (t1, _) => embedded_id t1
  | A.EIdent id => SOME id
  | A.ESelector (_, id, _) => SOME id
  | A.EIndex (b, _, _) => embedded_id b
  | _ => NONE)

(* A type expression as a type. Pure; a name that is not found (a package member, a name this
   pass does not see) gives "TUnknown". *)
fun ty_of genv (e : pos A.gExpr) : ty =
  (case e of
     A.EIdent (A.Ident (n, _, _)) => (case lookup_ident genv n of Ty t => t | Val _ => TUnknown)
   | A.EParen (e1, _) => ty_of genv e1
   | A.EStar (e1, _) => TPtr (ty_of genv e1)
   | A.EIndex (b, args, _) =>
       (case ty_of genv b of
          TNamed (k, _) => TNamed (k, map (ty_of genv) args)
        | _ => TUnknown)
   | A.EArrayType (NONE, t, _) => TSlice (ty_of genv t)
   | A.EArrayType (SOME _, t, _) => TArray (ty_of genv t)
   | A.EEllipsisArray (t, _) => TArray (ty_of genv t)
   | A.EMapType (k, v, _) => TMap (ty_of genv k, ty_of genv v)
   | A.EChanType (_, t, _) => TChan (ty_of genv t)
   | A.EFuncType (sg, _) => TFunc (ty_of_sig genv sg)
   | A.ESelector (A.EIdent (A.Ident (p, _, _)), A.Ident (n, _, _), _) =>
       (case lookup_ident genv p of
          Val (TPkg path) =>
            (case !Pkg_Store.member_hook genv path n of
               SOME (Typ tp, _) => TNamed (pos_key tp, [])
             | _ => TUnknown)
        | _ => TUnknown)
   | A.ETilde (t, _) => TTilde (ty_of genv t)
   | A.EBinary (A.Or, _, _, _) =>
       let
         fun terms t = (case t of
             A.EBinary (A.Or, a, b, _) => terms a @ terms b
           | A.EParen (a, _) => terms a
           | _ => [ty_of genv t])
       in TUnion (terms e) end
   | A.EStructType (fields, _) => TStruct (maps (ty_of_field genv) fields)
   | A.EInterfaceType (elems, _) =>
       TIface (List.mapPartial
                 (fn A.IMethod (A.Ident (n, _, ni), sg, _) =>
                       SOME (TM (n, A.pos_of_NodeInfo ni, ty_of_sig genv sg))
                   | _ => NONE) elems,
               List.mapPartial (fn A.IType (t, _) => SOME (ty_of genv t) | _ => NONE) elems)
   | _ => TUnknown)

and ty_of_sig genv (A.Sig (ps, rs, _)) : tsig =
  let
    fun one (A.Param (names, t, variadic, _)) =
      let val t0 = ty_of genv t
      in replicate (Int.max (1, length names)) (if variadic then TSlice t0 else t0) end
  in TSig (maps one ps, maps one rs, exists (fn A.Param (_, _, v, _) => v) ps) end

and ty_of_field genv (A.Field (names, t, _, _)) : tfield list =
  let val ft = ty_of genv t
  in
    if null names then
      (case embedded_id t of
         SOME (A.Ident (n, _, ni)) => [TF (n, A.pos_of_NodeInfo ni, ft, true)]
       | NONE => [])
    else map (fn A.Ident (n, _, ni) => TF (n, A.pos_of_NodeInfo ni, ft, false)) names
  end

(* The members called "name" a type has itself - its methods, the fields of a struct, the methods
   of an interface - and the types embedded in it, which provide the members of the next depth. *)
fun direct genv fuel name (t : ty) : (ident_kind * ty) list * ty list =
  if fuel <= 0 then ([], [])
  else
    (case t of
       TNamed (k, args) =>
         let
           val own =
             (case get_meth genv k name of
                SOME (MDef {pos, sg, rtvars, mtvars, ...}) =>
                  [(Meth pos,
                    (case subst (inst_map (rtvars, args)) (TFunc sg) of
                       TFunc g => if null mtvars then TFunc g else TGeneric (mtvars, g)
                     | t => t))]
              | NONE => [])
           val (ms, es) =
             (case get_def genv k of
                SOME (TDef {tparams, rhs, alias}) =>
                  let val rhs' = subst (inst_map (tparams, args)) rhs
                  in
                    if alias then direct genv (fuel - 1) name rhs'
                    else direct genv (fuel - 1) name (under genv 20 rhs')
                  end
              | NONE => ([], [TUnknown]))
         in (own @ filter (fn (Meth _, _) => own = [] | _ => true) ms, es) end
     | TStruct fs =>
         (List.mapPartial (fn TF (n, p, ft, _) => if n = name then SOME (Fld p, ft) else NONE) fs,
          List.mapPartial (fn TF (_, _, ft, emb) => if emb then SOME (deref ft) else NONE) fs)
     | TIface (ms, es) =>
         let
           val own = List.mapPartial (fn TM (n, p, sg) =>
                       if n = name then SOME (Meth p, TFunc sg) else NONE) ms
           val subs = map (fn e => direct genv (fuel - 1) name (under genv 20 e)) es
           val inh = distinct (fn ((Meth p1, _), (Meth p2, _)) => p1 = p2 | _ => false)
                       (own @ maps (fn (m, _) => filter (fn (Meth _, _) => true | _ => false) m)
                                subs)
           val unk = exists (fn e => under genv 20 e = TUnknown) es
         in (inh, if unk then [TUnknown] else []) end
     | TVar k =>
         (case get_def genv k of
            SOME (TDef {rhs, ...}) =>
              (filter (fn (Meth _, _) => true | _ => false)
                 (#1 (direct genv (fuel - 1) name (under genv 20 rhs))), [])
          | NONE => ([], []))
     | _ => ([], []))

and deref t = (case t of TPtr t1 => t1 | _ => t)

(* Field or method selection "x.name" on a value of type "t", by the rules of the language: the
   pointer is dereferenced automatically, members of an embedded type are promoted, the
   shallowest depth wins and a tie is ambiguous. The answer is given only when it is certain: an
   embedded type this pass does not know (an imported one) could provide the name at a
   shallower depth than a match that is found further down, so then there is none. *)
fun lookup_member genv name (t : ty) : (ident_kind * ty) option =
  let
    fun level ts depth seen uncertain =
      if null ts orelse depth > 16 then NONE
      else
        let
          val rs = map (direct genv 20 name) ts
          val found = maps #1 rs
        in
          (case found of
             [m] => if uncertain then NONE else SOME m
           | _ :: _ => NONE
           | [] =>
               let
                 val embeds = map deref (maps #2 rs)
                 val unk = exists (fn e => under genv 20 e = TUnknown) embeds
                 val fresh = filter (fn e => (case e of
                     TNamed (k, _) => not (member (op =) seen k)
                   | _ => true)) embeds
                 val seen' = seen @ List.mapPartial (fn TNamed (k, _) => SOME k | _ => NONE) fresh
               in level (filter (fn e => e <> TUnknown) fresh) (depth + 1) seen' (uncertain orelse unk)
               end)
        end
  in level [deref t] 0 [] false end

fun elem_of genv t =
  (case under genv 20 t of
     TSlice e => e
   | TArray e => e
   | TMap (_, v) => v
   | TPtr p => (case under genv 20 p of TArray e => e | _ => TUnknown)
   | TBasic "string" => TBasic "uint8"
   | _ => TUnknown)

fun slice_of genv t =
  (case under genv 20 t of
     TBasic "string" => t
   | TSlice _ => t
   | TArray e => TSlice e
   | TPtr p => (case under genv 20 p of TArray e => TSlice e | _ => TUnknown)
   | _ => TUnknown)

(* ---- Inference of the type arguments of a call ---------------------------------------------
   "ks" are the type parameters (keys) of the generic function called. The pass unifies the
   parameter types with the types of the typed arguments, uses the core types of the constraints
   (S ~[]E: E is what S is a slice of), then gives the type parameters that only untyped constants
   reach their default type, and uses the constraints again. It is conservative like all of the
   type pass: a type parameter about which anything is doubtful is bound to "TUnknown" (poisoned),
   and a poisoned parameter is never replaced by a default. *)

datatype acls =
    ATyped of ty      (* a typed argument *)
  | AUntyped of ty    (* an untyped constant, by its default type *)
  | ADoubt            (* a named constant, a type: typed or not, this pass cannot tell *)
  | ANil              (* nil: tells nothing *)

fun tvars_in ks (t : ty) : string list =
  let
    fun go t acc = (case t of
        TVar k => if member (op =) ks k andalso not (member (op =) acc k) then k :: acc else acc
      | TNamed (_, args) => fold go args acc
      | TPtr t1 => go t1 acc
      | TSlice t1 => go t1 acc
      | TArray t1 => go t1 acc
      | TMap (a, b) => go b (go a acc)
      | TChan t1 => go t1 acc
      | TFunc sg => gsig sg acc
      | TStruct fs => fold (fn TF (_, _, t1, _) => go t1) fs acc
      | TIface (ms, es) => fold go es (fold (fn TM (_, _, sg) => gsig sg) ms acc)
      | TTuple ts => fold go ts acc
      | TGeneric (_, sg) => gsig sg acc
      | TTilde t1 => go t1 acc
      | TUnion ts => fold go ts acc
      | _ => acc)
    and gsig (TSig (ps, rs, _)) acc = fold go rs (fold go ps acc)
  in rev (go t []) end

(* The core type of a constraint (with: is it a "~T" term), if it has a single one. *)
fun core_type genv fuel (c : ty) : (bool * ty) option =
  if fuel <= 0 then NONE
  else
    (case c of
       TTilde t => SOME (true, t)
     | TUnion [t] => core_type genv (fuel - 1) t
     | TUnion _ => NONE
     | TIface (_, es) =>
         (case List.mapPartial (core_type genv (fuel - 1)) es of [x] => SOME x | _ => NONE)
     | TNamed _ =>
         (case under genv 20 c of
            TUnknown => NONE
          | TIface (ms, es) => core_type genv (fuel - 1) (TIface (ms, es))
          | _ => SOME (false, c))
     | TBasic "comparable" => NONE
     | TBasic "error" => NONE
     | TUnknown => NONE
     | TVar _ => NONE
     | t => SOME (false, t))

(* Binds "k" to "a" in "bs"; a second, different type poisons it (a named type and a type literal
   with the same structure give the named one), and an unknown type changes nothing known. *)
fun bind_tparam genv k a bs =
  (case AList.lookup (op =) bs k of
     NONE => (k, a) :: bs
   | SOME b =>
       if b = a orelse b = TUnknown orelse a = TUnknown then bs
       else if under genv 20 b = under genv 20 a
            andalso (case (b, a) of (TNamed _, TNamed _) => false | (TNamed _, _) => true
                                  | (_, TNamed _) => true | _ => false)
       then AList.update (op =) (k, (case b of TNamed _ => b | _ => a)) bs
       else AList.update (op =) (k, TUnknown) bs)

fun poison_tparams ks p bs =
  fold (fn k => fn b => if AList.defined (op =) b k then b else (k, TUnknown) :: b)
    (tvars_in ks p) bs

(* Unification of a parameter type "p" (with type parameters "ks") with the type "a" of an
   argument; inexact like Go's: a type literal meets the structure of a defined type. *)
fun unify genv ks (p : ty) (a : ty) bs : (string * ty) list =
  let
    fun all2 f xs ys b =
      if length xs = length ys then fold (fn (x, y) => f x y) (xs ~~ ys) b
      else poison_tparams ks p b
  in
    if null (tvars_in ks p) then bs
    else
      (case p of
         TVar k => bind_tparam genv k a bs
       | _ =>
           let
             val a' = (case (p, a) of (TNamed _, _) => a | (_, TNamed _) => under genv 20 a
                                    | _ => a)
           in
             (case (p, a') of
                (TPtr x, TPtr y) => unify genv ks x y bs
              | (TSlice x, TSlice y) => unify genv ks x y bs
              | (TArray x, TArray y) => unify genv ks x y bs
              | (TChan x, TChan y) => unify genv ks x y bs
              | (TMap (k1, v1), TMap (k2, v2)) => unify genv ks v1 v2 (unify genv ks k1 k2 bs)
              | (TNamed (k1, xs), TNamed (k2, ys)) =>
                  if k1 = k2 then all2 (unify genv ks) xs ys bs else poison_tparams ks p bs
              | (TFunc (TSig (ps, rs, _)), TFunc (TSig (ps', rs', _))) =>
                  if length ps = length ps' andalso length rs = length rs'
                  then fold (fn (x, y) => unify genv ks x y) (rs ~~ rs')
                         (fold (fn (x, y) => unify genv ks x y) (ps ~~ ps') bs)
                  else poison_tparams ks p bs
              | (TStruct fs, TStruct gs) =>
                  if map (fn TF (n, _, _, _) => n) fs = map (fn TF (n, _, _, _) => n) gs
                  then fold (fn (TF (_, _, x, _), TF (_, _, y, _)) => unify genv ks x y)
                         (fs ~~ gs) bs
                  else poison_tparams ks p bs
              | _ => poison_tparams ks p bs)
           end)
  end

(* Constraint type inference: for "S ~[]E" with S known, E is what S is a slice of; with a single
   core type without "~" and S unknown, S is that type. *)
fun infer_constraints genv ks bs =
  let
    fun one k bs =
      (case get_def genv k of
         NONE => bs
       | SOME (TDef {rhs, ...}) =>
           (case core_type genv 8 rhs of
              NONE => bs
            | SOME (tilde, ct) =>
                (case AList.lookup (op =) bs k of
                   SOME TUnknown => bs
                 | SOME b =>
                     let
                       val target =
                         (case under genv 20 b of
                            TVar kk =>
                              (case get_def genv kk of
                                 SOME (TDef {rhs = c2, ...}) =>
                                   (case core_type genv 8 c2 of SOME (_, t2) => t2 | NONE => TUnknown)
                               | NONE => TUnknown)
                          | u => if tilde then u else b)
                     in unify genv ks ct target bs end
                 | NONE =>
                     if tilde then bs
                     else
                       let
                         val m = List.mapPartial
                                   (fn (k1, t) => if t = TUnknown then NONE else SOME (k1, t)) bs
                         val ct' = subst m ct
                       in if null (tvars_in ks ct') then (k, ct') :: bs else bs end)))
    fun rounds 0 bs = bs
      | rounds n bs = rounds (n - 1) (fold one ks bs)
  in rounds 3 bs end

fun untyped_rank t =
  (case t of
     TBasic "int" => 1 | TBasic "int32" => 2 | TBasic "float64" => 3 | TBasic "complex128" => 4
   | _ => 0)

(* The default type of a type parameter only untyped constants reach: the largest kind (int,
   rune, float, complex); strings and booleans must agree. *)
fun untyped_default (ts : ty list) : ty =
  (case ts of
     [] => TUnknown
   | t :: _ =>
       if forall (fn x => untyped_rank x > 0) ts then
         fold (fn x => fn m => if untyped_rank x > untyped_rank m then x else m) ts t
       else if forall (fn x => x = t) ts then t
       else TUnknown)

fun is_literal e =
  (case strip_paren e of
     A.EInt _ => true | A.EFloat _ => true | A.EImag _ => true | A.ERune _ => true
   | A.EString _ => true | _ => false)

(* The type an expression has, or the type it is. Pure, and conservative: whatever is not known is
   "TUnknown", on which nothing is ever linked. *)
fun type_of genv (e : pos A.gExpr) : tv =
  let
    fun val_of e1 = (case type_of genv e1 of Val t => t | Ty _ => TUnknown)
  in
    (case e of
       A.EIdent (A.Ident (n, _, _)) => lookup_ident genv n
     | A.EInt _ => Val int_ty
     | A.EFloat _ => Val (TBasic "float64")
     | A.EImag _ => Val (TBasic "complex128")
     | A.ERune _ => Val (TBasic "int32")
     | A.EString _ => Val (TBasic "string")
     | A.EParen (e1, _) => type_of genv e1
     | A.ESelector (e1, A.Ident (n, _, _), _) =>
         (case type_of genv e1 of
            Val (TPkg path) =>
              (case !Pkg_Store.member_hook genv path n of
                 SOME (Typ tp, _) => Ty (TNamed (pos_key tp, []))
               | SOME (_, t) => Val t
               | NONE => Val TUnknown)
          | Val t => Val (case lookup_member genv n t of SOME (_, mt) => mt | NONE => TUnknown)
          | Ty t => Val (case lookup_member genv n t of
                           SOME (Meth _, mt) => mt | _ => TUnknown))
     | A.EIndex (e1, args, _) =>
         (case type_of genv e1 of
            Ty (TNamed (k, _)) => Ty (TNamed (k, map (ty_of genv) args))
          | Ty _ => Ty TUnknown
          | Val (TGeneric (ks, sg)) =>
              let
                val n = Int.min (length ks, length args)
                val m = take n ks ~~ map (ty_of genv) (take n args)
                val sg' = (case subst m (TFunc sg) of TFunc g => g | _ => sg)
              in
                Val (if n = length ks then TFunc sg' else TGeneric (drop n ks, sg'))
              end
          | Val t => Val (elem_of genv t))
     | A.ESlice (e1, _, _, _, _) => Val (slice_of genv (val_of e1))
     | A.ETypeAssert (_, SOME t, _) => Val (ty_of genv t)
     | A.ETypeAssert (_, NONE, _) => Val TUnknown
     | A.ECall (f, args, dots, _) => call_type genv f args dots
     | A.EStar (e1, _) =>
         (case type_of genv e1 of
            Ty t => Ty (TPtr t)
          | Val t => Val (case under genv 20 t of TPtr p => p | _ => TUnknown))
     | A.EUnary (A.UAnd, e1, _) => Val (case type_of genv e1 of Val t => TPtr t | Ty _ => TUnknown)
     | A.EUnary (A.Not, _, _) => Val bool_ty
     | A.EUnary (A.URecv, e1, _) =>
         Val (case under genv 20 (val_of e1) of TChan t => t | _ => TUnknown)
     | A.EUnary (_, e1, _) => type_of genv e1
     | A.EBinary (opr, a, b, _) =>
         if member (op =) [A.Eq, A.Ne, A.Lt, A.Le, A.Gt, A.Ge, A.LAnd, A.LOr] opr then Val bool_ty
         else if member (op =) [A.Shl, A.Shr] opr then type_of genv a
         else if is_literal a then type_of genv b
         else if is_literal b then type_of genv a
         else
           let val (ta, tb) = (val_of a, val_of b)
           in Val (if ta = tb then ta else TUnknown) end
     | A.ECompLit (SOME t, _, _) => Val (ty_of genv t)
     | A.ECompLit (NONE, _, _) => Val TUnknown
     | A.EFuncLit (sg, _, _) => Val (TFunc (ty_of_sig genv sg))
     | _ => Ty (ty_of genv e))
  end

and call_type genv f args dots : tv =
  let
    fun results t =
      (case t of
         TFunc (TSig (_, [r], _)) => Val r
       | TFunc (TSig (_, [], _)) => Val TUnknown
       | TFunc (TSig (_, rs, _)) => Val (TTuple rs)
       | _ => Val TUnknown)
    val builtin =
      (case f of
         A.EIdent (A.Ident (n, _, _)) =>
           if Symtab.defined (names_of genv) n then NONE else SOME n
       | _ => NONE)
    fun first_arg () = (case args of a :: _ => type_of genv a | [] => Val TUnknown)
  in
    (case builtin of
       SOME b =>
         if member (op =) ["len", "cap", "copy"] b then Val int_ty
         else if b = "new" then
           Val (case args of t :: _ => TPtr (ty_of genv t) | [] => TUnknown)
         else if b = "make" then
           Val (case args of t :: _ => ty_of genv t | [] => TUnknown)
         else if member (op =) ["append", "min", "max"] b then first_arg ()
         else (case type_of genv f of Ty t => Val t | Val _ => Val TUnknown)
     | NONE =>
         (case type_of genv f of
            Ty t => Val t
          | Val t =>
              (case t of
                 TGeneric (ks, sg) => results (infer_call genv ks sg args dots)
               | _ => results (under genv 20 t))))
  end

and arg_class genv (e : pos A.gExpr) : acls =
  let
    fun typed () =
      (case type_of genv e of Val t => ATyped t | Ty _ => ADoubt)
  in
    (case e of
       A.EParen (e1, _) => arg_class genv e1
     | A.EInt _ => AUntyped int_ty
     | A.EFloat _ => AUntyped (TBasic "float64")
     | A.EImag _ => AUntyped (TBasic "complex128")
     | A.ERune _ => AUntyped (TBasic "int32")
     | A.EString _ => AUntyped (TBasic "string")
     | A.EIdent (A.Ident (n, _, _)) =>
         (case Symtab.lookup (names_of genv) n of
            NONE =>
              if n = "true" orelse n = "false" then AUntyped bool_ty
              else if n = "iota" then AUntyped int_ty
              else if n = "nil" then ANil
              else typed ()
          | SOME (Const _) =>
              (case Symtab.lookup (vtypes_of genv) n of
                 SOME (t as TNamed _) => ATyped t
               | _ => ADoubt)
          | SOME _ => typed ())
     | A.EUnary (A.UAnd, _, _) => typed ()
     | A.EUnary (A.URecv, _, _) => typed ()
     | A.EUnary (_, e1, _) => arg_class genv e1
     | A.EBinary (opr, a, b, _) =>
         if member (op =) [A.Eq, A.Ne, A.Lt, A.Le, A.Gt, A.Ge, A.LAnd, A.LOr] opr then
           ATyped bool_ty
         else if member (op =) [A.Shl, A.Shr] opr then arg_class genv a
         else
           (case (arg_class genv a, arg_class genv b) of
              (ATyped t, _) => ATyped t
            | (_, ATyped t) => ATyped t
            | (AUntyped x, AUntyped y) =>
                AUntyped (if untyped_rank x >= untyped_rank y then x else y)
            | _ => ADoubt)
     | _ => typed ())
  end

(* The signature of a generic function called with "args", its type parameters replaced by what
   is inferred (the others by "TUnknown"). *)
and infer_call genv ks (sg as TSig (ps, _, variadic)) args dots : ty =
  let
    val n = length ps
    val classes =
      (case map (arg_class genv) args of
         [ATyped (TTuple ts)] => map ATyped ts
       | cs => cs)
    fun param_at i =
      if variadic andalso i >= n - 1 then
        (if dots then SOME (List.last ps)
         else (case List.last ps of TSlice t => SOME t | _ => NONE))
      else if i < n then SOME (nth ps i) else NONE
    val pairs =
      if (not variadic andalso length classes <> n) orelse (variadic andalso length classes < n - 1)
      then []
      else List.mapPartial (fn (i, c) => Option.map (fn p => (p, c)) (param_at i))
             (tag_list 0 classes)
    val bs1 =
      fold (fn (p, c) => fn bs =>
              (case c of
                 ATyped t => unify genv ks p t bs
               | _ => bs)) pairs []
    val bs2 = infer_constraints genv ks bs1
    val bs3 =
      fold (fn k => fn bs =>
              if AList.defined (op =) bs k then bs
              else
                let
                  val cs = List.mapPartial (fn (TVar k', c) => if k' = k then SOME c else NONE
                                             | _ => NONE) pairs
                in
                  if null cs then bs
                  else if exists (fn ADoubt => true | _ => false) cs then (k, TUnknown) :: bs
                  else
                    (k, untyped_default (List.mapPartial (fn AUntyped t => SOME t | _ => NONE) cs))
                      :: bs
                end) ks bs2
    val bs4 = infer_constraints genv ks bs3
    val m = map (fn k => (k, the_default TUnknown (AList.lookup (op =) bs4 k))) ks
  in subst m (TFunc sg) end

fun val_ty genv e = (case type_of genv e of Val t => t | Ty _ => TUnknown)

(* The types of the names that "a, b := rhs" declares (and of "var a, b = rhs"): "n" names. *)
fun rhs_types genv n (rhs : pos A.gExpr list) : ty list =
  if length rhs = n then map (val_ty genv) rhs
  else
    (case rhs of
       [e] =>
         (case (n, strip_paren e) of
            (2, A.EIndex (m, _, _)) => [elem_of genv (val_ty genv m), bool_ty]
          | (2, A.ETypeAssert (_, SOME t, _)) => [ty_of genv t, bool_ty]
          | (2, A.EUnary (A.URecv, c, _)) =>
              [(case under genv 20 (val_ty genv c) of TChan t => t | _ => TUnknown), bool_ty]
          | _ =>
              (case val_ty genv e of
                 TTuple ts => if length ts = n then ts else replicate n TUnknown
               | _ => replicate n TUnknown))
     | _ => replicate n TUnknown)

(* The key and value types of "for k, v := range e". *)
fun range_types genv (e : pos A.gExpr) : ty * ty =
  let
    val unk = (TUnknown, TUnknown)
    val t = val_ty genv e
  in
    (case under genv 20 t of
       TSlice el => (int_ty, el)
     | TArray el => (int_ty, el)
     | TPtr p => (case under genv 20 p of TArray el => (int_ty, el) | _ => unk)
     | TMap (k, v) => (k, v)
     | TBasic "string" => (int_ty, TBasic "int32")
     | TChan el => (el, TUnknown)
     | TBasic s => if member (op =) integer_type_names s then (t, TUnknown) else unk
     | TFunc (TSig ([y], _, _)) =>
         (case under genv 20 y of
            TFunc (TSig (ps, _, _)) =>
              (case ps of
                 [a] => (a, TUnknown)
               | a :: b :: _ => (a, b)
               | [] => unk)
          | _ => unk)
     | _ => unk)
  end

(* Gives the name just declared by "id" its type, if one is known (never overwriting a known type
   with an unknown one). *)
fun set_vty genv (A.Ident (name, _, ni)) ty =
  if name = "_" orelse ty = TUnknown then genv
  else
    (case Symtab.lookup (names_of genv) name of
       SOME k =>
         if pos_of_kind k = A.pos_of_NodeInfo ni
         then set_vtypes (Symtab.update (name, ty) (vtypes_of genv)) genv
         else genv
     | NONE => genv)

fun restore_scope genv0 genv1 = set_scope (names_of genv0, vtypes_of genv0) genv1

fun id_key (A.Ident (_, _, ni)) = pos_key (A.pos_of_NodeInfo ni)

(* The type parameters of a declaration, entered silently in a scope the caller discards; the
   constraint of each is recorded under the key of the parameter. *)
fun register_tparams genv (tps : pos A.gTParam list) : genv * string list =
  let
    val genv1 =
      fold (fn A.TParam (ids, _, _) => fn g => fold (fn id => fn g1 => enter Tparam g1 id) ids g)
        tps genv
    val genv2 =
      fold (fn A.TParam (ids, c, _) => fn g =>
              let val cty = ty_of g c
              in fold (fn id => fn g1 =>
                         add_def (id_key id) (TDef {tparams = [], rhs = cty, alias = false}) g1)
                   ids g end)
        tps genv1
  in (genv2, maps (fn A.TParam (ids, _, _) => map id_key ids) tps) end

(* The declaration of a type (its name already in the table), a function or a method. These are
   idempotent and are run for the whole package before anything is walked, so that a function may
   use a type, a method or a function that is declared further down. *)
fun register_typespec genv (A.TypeSpec (name, tps, alias, t, _)) =
      let
        val (g1, tpkeys) = register_tparams genv tps
        val rhs = ty_of g1 t
        val g2 = add_def (id_key name) (TDef {tparams = tpkeys, rhs = rhs, alias = alias}) g1
      in restore_scope genv g2 end
  | register_typespec genv _ = genv

fun register_func genv (A.DFunc (name, tps, sg, _, _)) =
      let
        val (g1, tpkeys) = register_tparams genv tps
        val g = ty_of_sig g1 sg
        (* a generic function is called with its type arguments inferred (see "infer_call") *)
        val fty = if null tpkeys then TFunc g else TGeneric (tpkeys, g)
      in set_vty (restore_scope genv g1) name fty end
  | register_func genv _ = genv

fun register_method genv (A.DMethod ([A.Param (_, rt, _, _)], A.Ident (mname, _, mni), mtps, sg, _, _)) =
      if mname = "_" then genv
      else
        (case (case recv_base rt of A.EIndex (b, _, _) => b | b => b) of
           A.EIdent (A.Ident (tn, _, _)) =>
             (case Symtab.lookup (names_of genv) tn of
                SOME (Typ tp) =>
                  let
                    val targs = recv_targs rt
                    val g0 = fold (fn id => fn g => enter Tparam g id) targs genv
                    val ptr = (case strip_paren rt of A.EStar _ => true | _ => false)
                    val (g1, mtkeys) = register_tparams g0 mtps
                    val m = MDef {pos = A.pos_of_NodeInfo mni, sg = ty_of_sig g1 sg, ptr = ptr,
                                  rtvars = map id_key targs, mtvars = mtkeys}
                  in add_meth (meth_key (pos_key tp) mname) m (restore_scope genv g1) end
              | _ => genv)
         | _ => genv)
  | register_method genv _ = genv

fun register_decl genv (d : pos A.gDecl) =
  (case d of
     A.DType (specs, _, _) => fold (fn sp => fn g => register_typespec g sp) specs genv
   | A.DFunc _ => register_func genv d
   | A.DMethod _ => register_method genv d
   | _ => genv)

(* The types of the names a "var"/"const" specification declares: the written type, or those of
   the values; a constant specification that repeats its predecessor ("iota" groups) has its type
   and values. *)
fun value_types genv ids t vals : ty list =
  (case t of
     SOME te => replicate (length ids) (ty_of genv te)
   | NONE => rhs_types genv (length ids) vals)

fun effective_spec prev sp =
  (case sp of
     A.ConstSpec (ids, t, vals, _) =>
       if is_none t andalso null vals then (ids, fst prev, snd prev) else (ids, t, vals)
   | A.VarSpec (ids, t, vals, _) => (ids, t, vals)
   | _ => ([], NONE, []))

fun next_prev prev sp =
  (case sp of
     A.ConstSpec (_, t, vals, _) => if is_none t andalso null vals then prev else (t, vals)
   | _ => prev)

fun set_vtys ids tys genv = fold (fn (id, ty) => fn g => set_vty g id ty) (ids ~~ tys) genv

fun register_values genv (d : pos A.gDecl) =
  let
    fun specs sps =
      #1 (fold (fn sp => fn (g, prev) =>
                  let val (ids, t, vals) = effective_spec prev sp
                  in (set_vtys ids (value_types g ids t vals) g, next_prev prev sp) end)
            sps (genv, (NONE, [])))
  in
    (case d of
       A.DVar (sps, _, _) => specs sps
     | A.DConst (sps, _, _) => specs sps
     | _ => genv)
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

(* ---- Reading a package -----------------------------------------------------------------------
   The files of a package that count are those the Go tool would build for the target: not the
   tests, and those whose name (name_linux.go, name_windows_amd64.go) and "//go:build" line
   match the operating system and the architecture. cgo, the race detector and the experiments
   are off. *)

val known_os =
  ["aix", "android", "darwin", "dragonfly", "freebsd", "hurd", "illumos", "ios", "js", "linux",
   "nacl", "netbsd", "openbsd", "plan9", "solaris", "wasip1", "windows", "zos"]

val known_arch =
  ["386", "amd64", "amd64p32", "arm", "armbe", "arm64", "arm64be", "loong64", "mips", "mipsle",
   "mips64", "mips64le", "mips64p32", "mips64p32le", "ppc", "ppc64", "ppc64le", "riscv", "riscv64",
   "s390", "s390x", "sparc", "sparc64", "wasm"]

val unix_os =
  ["aix", "android", "darwin", "dragonfly", "freebsd", "hurd", "illumos", "ios", "linux", "netbsd",
   "openbsd", "solaris"]

val go_version = 27

fun os_matches os name =
  name = os orelse (os = "android" andalso name = "linux") orelse
  (os = "ios" andalso name = "darwin") orelse (os = "illumos" andalso name = "solaris")

fun tag_true (os, arch) tag =
  os_matches os tag orelse tag = arch orelse tag = "gc" orelse
  (tag = "unix" andalso member (op =) unix_os os) orelse
  (String.isPrefix "go1." tag andalso
   (case Int.fromString (String.extract (tag, 4, NONE)) of SOME n => n <= go_version | NONE => false))

(* The value of a "//go:build" expression: ||, &&, ! and parentheses over tags. *)
fun eval_build target (expr : string) : bool =
  let
    fun is_tag_char c = Char.isAlphaNum c orelse c = #"_" orelse c = #"."
    fun tokens cs =
      (case cs of
         [] => []
       | #"&" :: #"&" :: r => "&&" :: tokens r
       | #"|" :: #"|" :: r => "||" :: tokens r
       | c :: r =>
           if c = #"(" orelse c = #")" orelse c = #"!" then str c :: tokens r
           else if is_tag_char c then
             String.implode (take_prefix is_tag_char cs) :: tokens (drop_prefix is_tag_char cs)
           else tokens r)
    fun p_or ts =
      let val (a, ts1) = p_and ts
      in (case ts1 of "||" :: r => let val (b, ts2) = p_or r in (a orelse b, ts2) end
                    | _ => (a, ts1)) end
    and p_and ts =
      let val (a, ts1) = p_not ts
      in (case ts1 of "&&" :: r => let val (b, ts2) = p_and r in (a andalso b, ts2) end
                    | _ => (a, ts1)) end
    and p_not ts =
      (case ts of
         "!" :: r => let val (a, ts1) = p_not r in (not a, ts1) end
       | "(" :: r =>
           let val (a, ts1) = p_or r
           in (a, (case ts1 of ")" :: r' => r' | _ => ts1)) end
       | t :: r => (tag_true target t, r)
       | [] => (false, []))
  in #1 (p_or (tokens (String.explode expr))) end

(* The "//go:build" line of a file, if its header (comments before the package clause) has one. *)
fun build_line (text : string) : string option =
  let
    fun scan lines in_block =
      (case lines of
         [] => NONE
       | l :: r =>
           let val t = String.concat (String.tokens (fn c => c = #"\r") l)
               val t = String.implode (drop_prefix Char.isSpace (String.explode t))
           in
             if in_block then
               scan r (not (String.isSubstring "*/" t))
             else if t = "" then scan r false
             else if String.isPrefix "//go:build " t then
               SOME (String.extract (t, size "//go:build ", NONE))
             else if String.isPrefix "//" t then scan r false
             else if String.isPrefix "/*" t then scan r (not (String.isSubstring "*/" t))
             else NONE
           end)
  in scan (String.fields (fn c => c = #"\n") text) false end

(* The rules about the name of a file: name_$GOOS.go, name_$GOARCH.go, name_$GOOS_$GOARCH.go. *)
fun name_matches (os, arch) (fname : string) : bool =
  let
    val base = Path.implode (Path.base (Path.explode fname))
    val stem = if String.isSuffix ".go" base then String.substring (base, 0, size base - 3) else base
  in
    (case String.fields (fn c => c = #"_") stem of
       [] => true
     | _ :: [] => true
     | _ :: rest =>
         let val parts = (case rev rest of "test" :: r => r | r => r)   (* reversed *)
         in
           (case parts of
              [] => true
            | l :: more =>
                if member (op =) known_arch l then
                  (case more of
                     p :: _ => if member (op =) known_os p then os_matches os p andalso arch = l
                               else arch = l
                   | [] => arch = l)
                else if member (op =) known_os l then os_matches os l
                else true)
         end)
  end

fun is_exported name =
  size name > 0 andalso Char.isUpper (String.sub (name, 0))

val parse_ctxt = Proof_Context.init_global @{theory}

(* The parsed declarations of a source file, whose positions name the file. *)
fun parse_go_file path_str text : pos A.gDecl list option =
  let
    val pos = Position.line_file 1 path_str
    val source = Input.source false text (pos, pos)
  in
    (case try (Go_Parse.parse_quiet Go_Parse.Entry_File parse_ctxt) source of
       SOME (SOME (A.Source (A.File (_, ds, _)))) => SOME ds
     | _ => NONE)
  end

(* The directory of an import path in the Go tree: its standard library, or its vendored copies. *)
fun package_dir root path =
  let
    val elems = String.fields (fn c => c = #"/") path
    val ok = not (null elems) andalso
      forall (fn e => e <> "" andalso e <> "." andalso e <> ".." andalso
                      not (String.isSubstring "\\" e)) elems
    fun under_src prefix =
      Path.appends (Path.explode root :: Path.basic "src" :: map Path.basic (prefix @ elems))
  in
    if not ok then NONE
    else find_first File.is_dir [under_src [], under_src ["vendor"]]
  end

(* The declarations of the files of a package. *)
fun package_files (root, os, arch) path : (string * pos A.gDecl list) list =
  (case package_dir root path of
     NONE => []
   | SOME dir =>
       let
         val names = sort_strings (File.read_dir dir)
         val cand = filter (fn n => String.isSuffix ".go" n andalso not (String.isSuffix "_test.go" n)
                                    andalso not (String.isPrefix "_" n)
                                    andalso not (String.isPrefix "." n)
                                    andalso name_matches (os, arch) n) names
       in
         map_filter (fn n =>
           Option.join (try (fn () =>
             let
               val file = Path.append dir (Path.basic n)
               val text = File.read file
               val tagged =
                 (case build_line text of SOME e => eval_build (os, arch) e | NONE => true)
             in
               if tagged then Option.map (fn ds => (Path.implode file, ds))
                                         (parse_go_file (Path.implode file) text)
               else NONE
             end) ())) cand
       end)

fun split_target tgt =
  (case String.fields (fn c => c = #"\n") tgt of [r, o, a] => (r, o, a) | _ => ("", "", ""))

(* The package (not its conversion) at an import path of the target. The conversion of its
   declarations - types, functions, methods - is lazy, and so is that of the types of its
   variables and constants. *)
fun build_package tgt path : Pkg_Store.pkg option =
  let
    val target = split_target tgt
    val parsed = package_files target path
  in
    if null parsed then NONE
    else
      let
        val empty = set_target tgt empty_genv
        val is_import = (fn A.DImport _ => true | _ => false)
        val names_genv =
          fold (fn (_, ds) => fold (fn d => fn g => predeclare g d) (filter (not o is_import) ds))
            parsed empty
        val members = names_of names_genv
        val _ = Synchronized.change Pkg_Store.owners
                  (Symtab.fold (fn (_, Typ p) => Symtab.update (Pkg_Store.k tgt (pos_key p), path)
                                 | _ => I) members)
        (* the scope of a file: the names of the package, and its own imports *)
        fun file_genv ds = fold (fn d => fn g => if is_import d then predeclare g d else g) ds names_genv
        val conv = Lazy.lazy (fn () =>
          let
            val results = map (fn (_, ds) => (ds, fold (fn d => fn g => register_decl g d) ds (file_genv ds)))
                            parsed
            val _ = Synchronized.change Pkg_Store.defs
                      (fold (fn (_, g) => Symtab.fold (fn (key, d) => Symtab.update (Pkg_Store.k tgt key, d))
                                            (defs_of g)) results)
            val _ = Synchronized.change Pkg_Store.meths
                      (fold (fn (_, g) => Symtab.fold (fn (key, m) => Symtab.update (Pkg_Store.k tgt key, m))
                                            (meths_of g)) results)
            val ftypes =
              fold (fn (ds, g) => fold (fn A.DFunc (A.Ident (n, _, _), _, _, _, _) =>
                                           (case Symtab.lookup (vtypes_of g) n of
                                              SOME t => Symtab.update (n, t) | NONE => I)
                                         | _ => I) ds) results Symtab.empty
          in (results, {ftypes = ftypes}) end)
        val conv' = Lazy.lazy (fn () => #2 (Lazy.force conv))
        val vtys = Lazy.lazy (fn () =>
          let
            val (results, _) = Lazy.force conv
            fun value_ids ds = maps (fn d => (case d of
                A.DVar (sps, _, _) => maps (fn A.VarSpec (ids, _, _, _) => ids | _ => []) sps
              | A.DConst (sps, _, _) => maps (fn A.ConstSpec (ids, _, _, _) => ids | _ => []) sps
              | _ => [])) ds
          in
            fold (fn (ds, g) =>
                    let
                      val g1 = funpow 3 (fn g0 => fold (fn d => fn g' => register_values g' d) ds g0) g
                    in
                      fold (fn A.Ident (n, _, _) =>
                              (case Symtab.lookup (vtypes_of g1) n of
                                 SOME t => Symtab.update (n, t) | NONE => I)) (value_ids ds)
                    end) results Symtab.empty
          end)
      in SOME (Pkg_Store.Pk {members = members, conv = conv', vtys = vtys}) end
  end

fun load_package tgt path : Pkg_Store.pkg option =
  let val key = Pkg_Store.k tgt path
  in
    (case Symtab.lookup (Synchronized.value Pkg_Store.pkgs) key of
       SOME r => r
     | NONE =>
         let val r = Option.join (try (build_package tgt) path)
             val _ = Synchronized.change Pkg_Store.pkgs (Symtab.update (key, r))
         in r end)
  end

(* The member "n" of the package at the import path "path": its kind (with the declaration site in
   the file of the package) and its type. Only the exported members are seen. *)
fun package_member genv path n : (ident_kind * ty) option =
  let val tgt = target_of genv
  in
    if tgt = "" orelse not (is_exported n) then NONE
    else
      Option.join (try (fn () =>
        (case load_package tgt path of
           NONE => NONE
         | SOME (Pkg_Store.Pk {members, conv, vtys}) =>
             (case Symtab.lookup members n of
                NONE => NONE
              | SOME (k as Func _) =>
                  SOME (k, the_default TUnknown (Symtab.lookup (#ftypes (Lazy.force conv)) n))
              | SOME (k as Var _) =>
                  SOME (k, the_default TUnknown (Symtab.lookup (Lazy.force vtys) n))
              | SOME (k as Const _) =>
                  SOME (k, the_default TUnknown (Symtab.lookup (Lazy.force vtys) n))
              | SOME k => SOME (k, TUnknown)))) ())
  end

val _ = Pkg_Store.load_hook := load_package
val _ = Pkg_Store.member_hook := package_member

(* Where the packages are read from: the configuration of the theory, the environment of Go
   ($GOROOT, $GOOS, $GOARCH), the usual places of an installation. *)
val go_root = Attrib.setup_config_string \<^binding>\<open>go_root\<close> (K "")
val go_os = Attrib.setup_config_string \<^binding>\<open>go_os\<close> (K "")
val go_arch = Attrib.setup_config_string \<^binding>\<open>go_arch\<close> (K "")

fun target_string thy =
  let
    fun first xs = the_default "" (find_first (fn x => x <> "") xs)
    val has_src = (fn d => d <> "" andalso File.is_dir (Path.append (Path.explode d) (Path.basic "src")))
    val root =
      first [Config.get_global thy go_root, getenv "GOROOT"]
      |> (fn r => if has_src r then r
                  else the_default "" (find_first has_src
                         ["/usr/local/go", "/opt/homebrew/opt/go/libexec", "/usr/lib/go",
                          "/usr/share/go"]))
    val os = first [Config.get_global thy go_os, getenv "GOOS",
                    (case getenv "ISABELLE_PLATFORM_FAMILY" of
                       "macos" => "darwin" | "windows" => "windows" | _ => "linux")]
    val arch = first [Config.get_global thy go_arch, getenv "GOARCH",
                      if String.isPrefix "arm64" (getenv "ISABELLE_PLATFORM64") then "arm64"
                      else "amd64"]
  in if root = "" then "" else space_implode "\n" [root, os, arch] end

(* Hyperlinks the use of a member (a field or a method) at "use_pos" to its declaration. *)
fun report_member (name, use_pos) kind =
  Position.report (name_range (name, use_pos))
    (Position.entity_markup (describe_kind kind) (name, name_range (name, pos_of_kind kind)))

(* "expect" is the type a composite literal without a type (an element "{...}" of a literal) is
   given by its context. *)
fun walk_exp senv ctx expect (e : pos A.gExpr) : acts =
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
     | A.ESelector (e1, A.Ident (n, _, ini), _) =>
         let
           val a = w e1
           val found =
             (case type_of senv e1 of
                Val (TPkg path) =>
                  Option.map (fn (kind, _) => (kind, TUnknown))
                    (!Pkg_Store.member_hook senv path n)
              | Val t => lookup_member senv n t
              | Ty t => (case lookup_member senv n t of
                           SOME (m as (Meth _, _)) => SOME m | _ => NONE))
           val _ = (case found of
                      SOME (kind, _) => report_member (n, A.pos_of_NodeInfo ini) kind
                    | NONE => ())
         in a end
     | A.EIndex (e1, args, _) => w e1 @ maps w args
     | A.ESlice (e1, a, b, c, _) => w e1 @ optl w a @ optl w b @ optl w c
     | A.ETypeAssert (e1, t, _) => w e1 @ optl w t
     | A.ECall (f, args, _, _) => w f @ maps w args
     | A.EStar (e1, _) => w e1
     | A.EUnary (_, e1, _) => w e1
     | A.EBinary (_, a, b, _) => w a @ w b
     | A.ECompLit (t, elems, _) =>
         let
           val lit_ty = (case t of SOME te => ty_of senv te | NONE => deref expect)
         in optl w t @ walk_elements senv ctx' lit_ty elems end
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

and walk_expr senv ctx e : acts = walk_exp senv ctx TUnknown e

(* The elements of a composite literal of type "lit_ty". For a struct, a bare name as a key is a
   field of it, and the values have the types of the fields; for a slice, an array or a map, the
   keys and values have the element types (a map key is an expression, so a bare name is a
   variable). When the type is not known, a bare name as a key is not resolved: it could be
   either. *)
and walk_elements senv ctx lit_ty elems : acts =
  let
    val u = under senv 20 lit_ty
    fun key_ident_acts e = chk senv (A.Expr e :: ctx) (A.nodeInfo_of_expr e)
    fun elem idx (A.Element (k, v, ni)) =
      let
        val a0 = chk senv ctx ni
        val (ak, vty) =
          (case (u, k) of
             (TStruct fs, SOME (e as A.EIdent (A.Ident (n, _, kni)))) =>
               (case List.find (fn TF (fname, _, _, _) => fname = n) fs of
                  SOME (TF (_, fp, fty, _)) =>
                    (report_member (n, A.pos_of_NodeInfo kni) (Fld fp);
                     (key_ident_acts e, fty))
                | NONE => (key_ident_acts e, TUnknown))
           | (TStruct _, SOME e) => (walk_expr senv ctx e, TUnknown)
           | (TStruct fs, NONE) =>
               ([], (case try (fn i => nth fs i) idx of
                        SOME (TF (_, _, fty, _)) => fty | NONE => TUnknown))
           | (TSlice el, _) => (optl (walk_expr senv ctx) k, el)
           | (TArray el, _) => (optl (walk_expr senv ctx) k, el)
           | (TMap (kt, vt), _) => (optl (walk_exp senv ctx kt) k, vt)
           | (_, SOME (e as A.EIdent _)) => (key_ident_acts e, TUnknown)
           | (_, SOME e) => (walk_expr senv ctx e, TUnknown)
           | (_, NONE) => ([], TUnknown))
      in a0 @ ak @ walk_exp senv ctx vty v end
  in maps (uncurry elem) (tag_list 0 elems) end

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
    val senv1 =
      fold (fn A.Param (pids, t, variadic, _) => fn s =>
              let val t0 = ty_of senv t
                  val ty = if variadic then TSlice t0 else t0
              in fold (fn id => fn s1 => set_vty (reg Param s1 id) id ty) pids s end)
        (ps @ rs) senv
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
and define senv ctx blk lhs tys : genv * string list * acts =
  fold (fn (e, ty) => fn (s, b, acc) =>
          let
            val ctx' = A.Expr e :: ctx
            val here = chk s ctx' (A.nodeInfo_of_expr e)
          in
            (case e of
               A.EIdent (id as A.Ident (name, _, _)) =>
                 if name = "_" then (s, b, acc @ here)
                 else if member (op =) b name then (use_name s id; (s, b, acc @ here))
                 else (set_vty (reg Var s id) id ty, name :: b, acc @ here)
             | _ => (s, b, acc @ here @ walk_expr s ctx e))
          end)
    (lhs ~~ take (length lhs) tys) (senv, blk, [])

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
           val (senv1, blk1, a2) = define senv ctx' blk lhs (rhs_types senv (length lhs) rhs)
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
             val xty = val_ty s1 x
             val a3 = maps (walk_case s1 ctx' (Option.map (fn id => (id, xty)) bind)) cases
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
               val (kt, vt) = range_types senv e
               val (s1, a3) =
                 if def then (fn (s2, _, a) => (s2, a)) (define s0 ctx' [] ks [kt, vt])
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
      val s1 =
        (case bind of
           SOME (id, xty) =>
             let
               val cty = (case guards of
                   SOME [A.EIdent (A.Ident ("nil", _, _))] => xty
                 | SOME [g] => ty_of s0 g
                 | _ => xty)
             in set_vty (enter Var s0 id) id cty end
         | NONE => s0)
      val (_, _, a2) = walk_stmts s1 ctx [] stmts
    in (s1, a1 @ a2) end))

and walk_comm senv ctx (A.Comm (g, stmts, ni)) : acts =
  #2 (scoped senv (fn s0 =>
    let
      val a0 = chk s0 ctx ni
      val (s1, _, a1) = (case g of SOME g1 => walk_stmt s0 ctx [] g1 | NONE => (s0, [], []))
      val (_, _, a2) = walk_stmts s1 ctx [] stmts
    in (s1, a0 @ a1 @ a2) end))

and walk_spec senv ctx blk eff spec : genv * string list * acts =
  (case spec of
     A.ConstSpec (ids, t, vals, ni) => walk_values Const senv ctx blk eff (ids, t, vals, ni)
   | A.VarSpec (ids, t, vals, ni) => walk_values Var senv ctx blk eff (ids, t, vals, ni)
   | A.TypeSpec (name, tps, _, t, ni) =>
       let
         val senv1 = register_typespec (reg Typ senv name) spec
         val blk1 = if ident_name_of name = "_" then blk else ident_name_of name :: blk
         val (_, a) = scoped senv1 (fn s =>
           let
             val (s1, a1) = walk_tparams s ctx tps
             val a2 = walk_expr s1 ctx t
           in (s1, a1 @ a2) end)
       in (senv1, blk1, chk senv ctx ni @ a) end
   | A.ImportSpec (_, _, ni) => (reg_import senv spec, blk, chk senv ctx ni))

(* The values are evaluated before the names are declared. *)
and walk_values mk_kind senv ctx blk (_, et, evals) (ids, t, vals, ni)
    : genv * string list * acts =
  let
    val a = chk senv ctx ni @ optl (walk_expr senv ctx) t @ maps (walk_expr senv ctx) vals
    (* typed in the scope of the values, before the names exist *)
    val tys = value_types senv ids et evals
    val senv1 = fold (fn (id, ty) => fn s => set_vty (reg mk_kind s id) id ty) (ids ~~ tys) senv
    val blk1 = filter (fn n => n <> "_") (map ident_name_of ids) @ blk
  in (senv1, blk1, a) end

and walk_specs senv ctx blk specs : genv * string list * acts =
  #1 (fold (fn sp => fn ((e, b, acc), prev) =>
          let val (e', b', a) = walk_spec e ctx b (effective_spec prev sp) sp
          in ((e', b', acc @ a), next_prev prev sp) end)
    specs ((senv, blk, []), (NONE, [])))

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
           val senv1 = register_func (reg Func senv name) d
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
           val (_, a) = scoped (register_method senv d) (fn s =>
             let
               (* the receiver declares the type parameters of the type *)
               val targs = maps (fn A.Param (_, t, _, _) => recv_targs t) recv
               val s0 = fold (fn id => fn s' => reg Tparam s' id) targs s
               val a0 = maps (fn A.Param (_, t, _, ni) =>
                                chk s0 ctx' ni @ walk_expr s0 ctx' (recv_head t)) recv
               val rids = maps (fn A.Param (names, _, _, _) => names) recv
               val s1 =
                 fold (fn A.Param (pids, t, _, _) => fn s' =>
                         let val ty = ty_of s0 t
                         in fold (fn id => fn s'' => set_vty (reg Param s'' id) id ty) pids s' end)
                   recv s0
               val (s2, a1) = walk_tparams s1 ctx' tps
               val (s3, names, a2) = walk_sig s2 ctx' sg
               val names' = names @ filter (fn n => n <> "_") (map ident_name_of rids)
               val a3 = (case body of SOME b => walk_body s3 ctx' names' b | NONE => [])
             in (s3, a0 @ a1 @ a2 @ a3) end)
         in ret (senv, blk, a) end)
  end

fun walk_top senv ctx (decls : pos A.gDecl list) : genv * acts =
  let
    val senv0 = fold (fn d => fn s => predeclare s d) decls senv
    (* types, signatures and methods first; then the types of the variables and constants, which
       may depend on each other, in a few rounds (an initialisation cycle is invalid Go) *)
    val senv0' = fold (fn d => fn s => register_decl s d) decls senv0
    val senv1 = funpow 3 (fn s => fold (fn d => fn s1 => register_values s1 d) decls s) senv0'
    val (senv2, _, acts) =
      fold (fn d => fn (e, b, acc) =>
              let val (e', b', a) = walk_decl e ctx b d in (e', b', acc @ a) end)
        decls (senv1, [], [])
  in (senv2, acts) end

fun analyse_and_eval0 (root : pos A.root) thy =
  let
    val genv0 = set_target (target_string thy) (get (Context.Theory thy))
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
