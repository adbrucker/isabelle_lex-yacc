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
  \<^item> \<^bold>\<open>Selections and calls are resolved with types, and only when that is certain.\<close> \<open>x.f\<close> and
    \<open>x.m(a)\<close> are hyperlinked to the field or method they denote if the type of \<open>x\<close> is known well
    enough to tell, and left unmarked otherwise. The types are computed by a pure function
    \<open>type_of\<close> over the expression: the type of a name is the one it was declared with (a local
    variable, a parameter, a field, a pattern variable, a catch parameter; for \<open>var\<close> and an
    enhanced \<open>for\<close> the one of the initializer or of the array), a literal, \<open>new\<close>, a cast, \<open>this\<close>
    and an array access have their natural types, an operator the type that the numeric
    promotion gives, and a call the result type of the method it resolves to, with the type
    arguments of the receiver substituted and the type parameters of the method bound by the
    arguments that are exactly such a parameter. A class is a \<^emph>\<open>reference\<close> to its declaration (the
    position of its name), so classes, their fields and their methods may be mutually recursive
    and declared in any order: the classes of a unit - member classes, local classes and
    anonymous classes too - are registered before anything is walked. A field is found in the
    class, else in its superclass and interfaces provided they are all declared (a supertype that
    comes from nowhere that is known could have the same name) and exactly one of them has it; the
    methods of a name are those of the class and of its supertypes and of \<open>Object\<close>, an inherited
    method of the same signature being hidden. A call is linked if the types of the arguments
    leave exactly one applicable method, or one that is more specific than all the others
    (JLS 15.12.2, with subtyping answered yes, no or perhaps: an unknown type is always
    \<open>perhaps\<close>). Without a receiver the innermost enclosing class that has a method of that name
    is the one that counts (JLS 15.12.1), else a statically imported method.
    \<^bold>\<open>Lambdas, method references and switch expressions\<close> are typed from their context: the
    walk passes the type that the context expects (the parameter type of the method that a call
    resolves to, a declared variable or field, a \<open>return\<close>, a cast, an assignment) to the very
    next expression; a functional interface gives a lambda the types of its parameters, and the
    result of a lambda or of a method reference binds the type parameters of the method that takes
    it (\<open>call_info\<close>). A \<open>switch\<close> expression has the type its arms agree on.
    \<^bold>\<open>The platform\<close>: a class that the program does not declare - an imported one, one of
    \<open>java.lang\<close>, one named by its package - is read from the sources of a JDK (the theory option
    \<open>java_src\<close>: a \<open>src.zip\<close> or a directory, \<open>none\<close> for no platform; by default the
    \<open>src.zip\<close> of the JDK of Isabelle or of \<open>$JAVA_HOME\<close>). It is parsed the first time it is
    needed and its definitions, of the members that a program can see, are kept for the session
    in a store shared by all theories, under the key \<open>qn:<qualified name>\<close>; its declarations are
    the ones that uses are linked to. A name that resolves nowhere is \<^emph>\<open>not\<close> marked: in Java it
    very often comes from an inherited member or an on-demand import, and underlining it would
    drown the useful markup.
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
fun set_scope (names', meths', vtypes') (mk {names = _, meths = _, vtypes = _, defs, cur,
  java_antiq,
                                             units}) =
  mk {names = names', meths = meths', vtypes = vtypes', defs = defs, cur = cur,
      java_antiq = java_antiq, units = units}

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

(* --- types -------------------------------------------------------------------------------- *)

(* The type pass is the one of Go_AnaEval.thy, for Java: pure functions over the environment that
   say what a type name denotes ("ty_of_type"), what the type of an expression is ("type_of"),
   which member a selection denotes ("find_field", "collect_methods") and which method a call
   resolves to ("call_info"). A class is a reference to its declaration (the position key of its
   name), the classes of the units seen so far are in "defs"; a type that is not declared there -
   everything that comes from the platform - is "TUnknown", on which nothing is ever linked.
   Nothing is linked unless it is certain: an overloaded method is linked if the types of the
   arguments leave exactly one candidate, or one candidate that is more specific than all others;
   a field of a class is found in the class, else in its superclasses and interfaces provided all
   of them are known and just one of them has it.

   The classes of the platform are read from the sources of a JDK (see "Platform" below): a class
   whose key starts with "qn:" is looked up there, by its qualified name, and parsed the first time
   it is needed. *)

fun vtypes_of (mk {vtypes, ...} : jenv) = vtypes
fun defs_of (mk {defs, ...} : jenv) = defs
fun cur_of (mk {cur, ...} : jenv) = cur

fun set_cur cur' (mk {names, meths, vtypes, defs, cur = _, java_antiq, units}) =
  mk {names = names, meths = meths, vtypes = vtypes, defs = defs, cur = cur',
      java_antiq = java_antiq, units = units}

fun add_def key d (mk {names, meths, vtypes, defs, cur, java_antiq, units}) =
  mk {names = names, meths = meths, vtypes = vtypes, defs = Symtab.update (key, d) defs, cur = cur,
      java_antiq = java_antiq, units = units}

fun set_defs defs' (mk {names, meths, vtypes, defs = _, cur, java_antiq, units}) =
  mk {names = names, meths = meths, vtypes = vtypes, defs = defs', cur = cur,
      java_antiq = java_antiq, units = units}

(* --- the platform ------------------------------------------------------------------------ *)

(* The classes of the platform live in a store shared by all theories, keyed by the source they are
   read from (the "src" of an environment) and by their key "qn:<qualified name>"; the loader that
   fills it is defined with the registration of classes (see "load_hook" there). *)
structure Platform = struct
  val defs = Synchronized.var "Java_Platform.defs" (Symtab.empty : cdef Symtab.table)
  fun k src key = src ^ "|" ^ key
  fun is_qn key = String.isPrefix "qn:" key
  fun key_of qn = "qn:" ^ qn
  (* a class by its key; the top-level class of a package by name; whether a package exists *)
  val load_hook : (string -> string -> cdef option) Unsynchronized.ref =
    Unsynchronized.ref (fn _ => fn _ => NONE)
  val type_hook : (string -> string -> string -> string option) Unsynchronized.ref =
    Unsynchronized.ref (fn _ => fn _ => fn _ => NONE)
  val pkg_hook : (string -> string -> bool) Unsynchronized.ref =
    Unsynchronized.ref (fn _ => fn _ => false)
  fun def src key =
    if src = "" then NONE
    else
      (case Symtab.lookup (Synchronized.value defs) (k src key) of
         SOME d => SOME d
       | NONE => !load_hook src key)
end

(* The facts about the platform that an environment carries are entries of "vtypes" whose keys
   cannot be identifiers (they contain a colon): the source ("java:src"), the single-type imports
   ("java:imp:<name>"), the packages of the compilation unit and the on-demand imports, static
   imports, and the mark of a unit that is read from the platform ("java:platform"). A list of names
   is a type "TCls ("", [TCls (name, []), ...])". *)
fun put_vtype key t (mk {names, meths, vtypes, defs, cur, java_antiq, units}) =
  mk {names = names, meths = meths, vtypes = Symtab.update (key, t) vtypes, defs = defs,
      cur = cur, java_antiq = java_antiq, units = units}

fun src_of jenv =
  (case Symtab.lookup (vtypes_of jenv) "java:src" of SOME (TCls (s, _)) => s | _ => "")
fun set_src s jenv = put_vtype "java:src" (TCls (s, [])) jenv
fun in_platform_unit jenv = Symtab.defined (vtypes_of jenv) "java:platform"

fun names_at jenv key =
  (case Symtab.lookup (vtypes_of jenv) key of
     SOME (TCls (_, ts)) => List.mapPartial (fn TCls (n, _) => SOME n | _ => NONE) ts
   | _ => [])
fun add_name_at key n jenv =
  put_vtype key (TCls ("", map (fn x => TCls (x, [])) (names_at jenv key @ [n]))) jenv

fun def_of jenv key =
  (case Symtab.lookup (defs_of jenv) key of
     SOME d => SOME d
   | NONE => if Platform.is_qn key then Platform.def (src_of jenv) key else NONE)

val string_key = Platform.key_of "java.lang.String"
val object_key = Platform.key_of "java.lang.Object"
val string_ty = TCls (string_key, [])
val object_ty = TCls (object_key, [])

(* the key of a class declared at the position: its position, but for the classes read from the
   platform, whose registered position stands for the qualified name *)
fun class_key jenv p =
  (case Symtab.lookup (vtypes_of jenv) ("java:qn:" ^ pos_key p) of
     SOME (TCls (k, _)) => k
   | _ => pos_key p)

(* The class that a simple name denotes by an import or by the platform: a single-type import, a
   class of the package of the unit, a class of an on-demand import (a package or a class) or of
   java.lang. *)
fun import_ty jenv name : ty option =
  let
    val src = src_of jenv
    fun in_pkg p =
      if !Platform.pkg_hook src p
      then Option.map (fn qn => TCls (Platform.key_of qn, [])) (!Platform.type_hook src p name)
      else
        (case def_of jenv (Platform.key_of p) of
           SOME (CD {types, ...}) =>
             Option.map (fn (key, _) => TCls (key, [])) (AList.lookup (op =) types name)
         | NONE => NONE)
  in
    (case Symtab.lookup (vtypes_of jenv) ("java:imp:" ^ name) of
       SOME t => SOME t
     | NONE =>
         if src = "" then NONE
         else
           get_first in_pkg (names_at jenv "java:pkg" @ names_at jenv "java:demand" @ ["java.lang"]))
  end

(* a class of the platform by its qualified name *)
fun platform_class jenv qn : ty option =
  if src_of jenv = "" then NONE
  else
    (case def_of jenv (Platform.key_of qn) of
       SOME _ => SOME (TCls (Platform.key_of qn, []))
     | NONE => NONE)

fun lookup_type_name jenv name : ty =
  (case Symtab.lookup (names_of jenv) (tkey name) of
     SOME (Typ p) => TCls (class_key jenv p, [])
   | SOME (Tparam p) => TTv (pos_key p)
   | SOME (Imp _) => the_default TUnknown (import_ty jenv name)
   | SOME _ => TUnknown
   | NONE =>
       (case import_ty jenv name of
          SOME t => t
        | NONE => (case name of "String" => string_ty | "Object" => object_ty | _ => TUnknown)))

fun subst (m : (string * ty) list) (t : ty) : ty =
  (case t of
     TTv k => (case AList.lookup (op =) m k of SOME t1 => t1 | NONE => t)
   | TCls (k, args) => TCls (k, map (subst m) args)
   | TArr t1 => TArr (subst m t1)
   | _ => t)

(* a raw use of a generic class has unknown type arguments *)
fun inst_map tps args =
  if length tps = length args then tps ~~ args else map (fn k => (k, TUnknown)) tps

fun ty_of_type jenv (t : pos A.jType) : ty =
  (case t of
     A.TPrim (_, n, _) => TPrimT n
   | A.TVar _ => TUnknown
   | A.TArray (e, ds, _) => fold (fn _ => fn x => TArr x) ds (ty_of_type jenv e)
   | A.TClass (_, segs, _) =>
       let
         fun targs ta = (case ta of
             NONE => []
           | SOME (A.TArgs (args, _)) =>
               map (fn A.TAType x => ty_of_type jenv x
                     | A.TAWild (_, SOME (_, x), _) => ty_of_type jenv x
                     | A.TAWild (_, NONE, _) => TUnknown) args)
         fun with_args cur ta =
           (case cur of TCls (k, _) => TCls (k, targs ta) | _ => cur)
         fun member cur name =
           (case cur of
              TCls (k, _) =>
                (case def_of jenv k of
                   SOME (CD {types, ...}) =>
                     (case AList.lookup (op =) types name of
                        SOME (key, _) => TCls (key, [])
                      | NONE => TUnknown)
                 | NONE =>
                     if in_platform_unit jenv andalso Platform.is_qn k
                     then TCls (k ^ "." ^ name, []) else TUnknown)
            | _ => TUnknown)
       in
         (case segs of
            [] => TUnknown
          | A.TSeg (A.Ident (n, _, _), ta) :: rest =>
              let
                fun walk_members more cur =
                  fold (fn A.TSeg (A.Ident (n1, _, _), ta1) => fn c =>
                          with_args (member c n1) ta1) more cur
                (* a package name in front: the first prefix that is a class of the platform *)
                fun qualified acc more =
                  (case more of
                     [] => TUnknown
                   | A.TSeg (A.Ident (n1, _, _), ta1) :: more' =>
                       let val qn = acc ^ "." ^ n1
                       in
                         (case platform_class jenv qn of
                            SOME t => walk_members more' (with_args t ta1)
                          | NONE => qualified qn more')
                       end)
                val first = lookup_type_name jenv n
              in
                if first = TUnknown andalso src_of jenv <> "" andalso not (null rest)
                then qualified n rest
                else walk_members rest (with_args first ta)
              end)
       end)

fun supers_of jenv t =
  (case t of
     TCls (k, args) =>
       (case def_of jenv k of
          SOME (CD {tps, supers, ...}) => map (subst (inst_map tps args)) supers
        | NONE => [])
   | _ => [])

fun known_class jenv t = (case t of TCls (k, _) => is_some (def_of jenv k) | _ => false)

fun class_self jenv key =
  (case def_of jenv key of
     SOME (CD {tps, ...}) => TCls (key, map TTv tps)
   | NONE => TUnknown)

(* --- subtyping, three-valued: yes, no, perhaps ------------------------------------------------ *)

datatype tri = Y | N | M

fun tri_and a b =
  (case (a, b) of (N, _) => N | (_, N) => N | (M, _) => M | (_, M) => M | _ => Y)
fun tri_or a b =
  (case (a, b) of (Y, _) => Y | (_, Y) => Y | (M, _) => M | (_, M) => M | _ => N)

fun prim_widens a b =
  let
    val ranks = ["byte", "short", "int", "long", "float", "double"]
    fun idx x = find_index (fn y => y = x) ranks
  in
    a = b orelse
    (if a = "char" then member (op =) ["int", "long", "float", "double"] b
     else idx a >= 0 andalso idx b >= 0 andalso idx a <= idx b)
  end

(* Whether a class is certainly not a primitive type's box or supertype of one: only a class of
   the program and String are; the wrappers of the platform (Integer, Number, ...) may be. *)
fun not_boxable jenv k = k = string_key orelse (is_some (def_of jenv k) andalso not (Platform.is_qn k))

fun is_object t = (case t of TCls (k, _) => k = object_key | _ => false)

fun is_sub jenv fuel (a : ty) (b : ty) : tri =
  if a = b then Y
  else if fuel = 0 then M
  else if is_object b andalso (case a of TCls _ => true | TTv _ => true | _ => false) then Y
  else
    (case (a, b) of
       (TUnknown, _) => M
     | (_, TUnknown) => M
     | (TPrimT x, TPrimT y) => if prim_widens x y then Y else N
     | (TNull, TPrimT _) => N
     | (TNull, _) => Y
     | (TPrimT _, TCls (k, _)) => if not_boxable jenv k then N else M
     | (TPrimT _, TArr _) => N
     | (TPrimT _, _) => M
     | (TArr x, TArr y) =>
         (case (x, y) of
            (TPrimT _, _) => N
          | (_, TPrimT _) => N
          | _ => is_sub jenv (fuel - 1) x y)
     | (TArr _, TCls (k, _)) =>
         if member (op =) [object_key, Platform.key_of "java.lang.Cloneable",
                           Platform.key_of "java.io.Serializable"] k then Y
         else if is_some (def_of jenv k) then N else M
     | (TArr _, TPrimT _) => N
     | (TArr _, _) => M
     | (TCls (ka, aa), TCls (kb, ab)) =>
         if ka = kb then (if aa = ab orelse null aa orelse null ab then Y else M)
         else if not (is_some (def_of jenv ka)) then M
         else
           let val ss = supers_of jenv a
           in fold (fn s => fn r => tri_or r (is_sub jenv (fuel - 1) s b)) ss N end
     | (TCls (ka, _), TPrimT _) => if not_boxable jenv ka then N else M
     | (TCls _, TArr _) => N
     | (_, _) => M)

(* --- members ------------------------------------------------------------------------------- *)

(* The field "name" of the type "t": in the class, else in its supertypes provided they are all
   known and exactly one has it. The declaration site and the type, as seen from "t". *)
fun find_field jenv fuel (t : ty) name : (pos * ty) option =
  (case t of
     TCls (k, args) =>
       (case def_of jenv k of
          NONE => NONE
        | SOME (CD {tps, fields, supers, ...}) =>
            let val m = inst_map tps args
            in
              (case AList.lookup (op =) fields name of
                 SOME (FD {pos, ty, ...}) => SOME (pos, subst m ty)
               | NONE =>
                   if fuel = 0 then NONE
                   else
                     let
                       val ss = map (subst m) supers
                       val rs = map_filter (fn s => find_field jenv (fuel - 1) s name) ss
                       val unknown = exists (fn s => not (known_class jenv s)) ss
                     in
                       if unknown then NONE
                       else (case distinct (fn ((p1, _), (p2, _)) => p1 = p2) rs of
                               [x] => SOME x
                             | _ => NONE)
                     end)
            end)
   | _ => NONE)

(* The methods called "name" of the type "t", with the substitution of the type parameters of the
   class that declares them; a method of a subtype hides an inherited one of the same signature. *)
fun collect_methods jenv fuel (t : ty) name : (mdef * (string * ty) list) list =
  (case t of
     TCls (k, args) =>
       (case def_of jenv k of
          NONE => []
        | SOME (CD {tps, methods, supers, ...}) =>
            let
              val m = inst_map tps args
              val own = map (fn (_, md) => (md, m)) (filter (fn (n, _) => n = name) methods)
              (* every class and interface has the public methods of Object *)
              val inherited =
                if fuel = 0 then []
                else
                  maps (fn s => collect_methods jenv (fuel - 1) (subst m s) name) supers
                  @ (if k = object_key then [] else collect_methods jenv (fuel - 1) object_ty name)
              fun sg (MT {ps, ...}, mm) = map (subst mm) ps
              val own_sigs = map sg own
              fun first_of _ [] = []
                | first_of seen (c :: cs) =
                    if member (op =) seen (sg c) then first_of seen cs
                    else c :: first_of (sg c :: seen) cs
            in own @ first_of own_sigs inherited end)
   | _ => [])

fun fits_arity (MT {ps, va, ...}, _) n =
  if va then n >= length ps - 1 else n = length ps

(* the type a method expects for its i-th argument (variable arity: element type or array) *)
fun param_tys (MT {ps, va, tps, ...}, mm) n : ty list list =
  let
    fun erase t = (case t of
        TTv k => if member (op =) tps k then TUnknown else t
      | TCls (k, args) => TCls (k, map erase args)
      | TArr x => TArr (erase x)
      | _ => t)
    val ps' = map (erase o subst mm) ps
    val np = length ps'
  in
    List.tabulate (n, fn i =>
      if va andalso i >= np - 1
      then (case List.last ps' of TArr e => [e, TArr e] | x => [x])
      else [List.nth (ps', i)])
  end

(* How well the arguments fit a candidate. In the strict phase (JLS 15.12.2.2) a primitive does
   not meet a reference (no boxing) and a method of variable arity takes an array; the loose
   phase allows both. *)
fun cand_tri jenv strict c (arg_tys : ty list) : tri =
  let
    val MT {ps, va, ...} = #1 c
    val n = length arg_tys
    val pts = param_tys c n
    val pts' =
      if strict andalso va
      then (if n = length ps then take (n - 1) pts @ [[List.last (List.last pts)]] else [[]])
      else pts
    fun fit a p =
      if strict andalso (case (a, p) of
                           (TPrimT _, TCls _) => true
                         | (TPrimT _, TArr _) => true
                         | (TCls _, TPrimT _) => true
                         | _ => false)
      then N
      else is_sub jenv 8 a p
  in
    if strict andalso va andalso n <> length ps then N
    else
      fold (fn (a, alts) => fn r =>
              tri_and r (fold (fn p => fn x => tri_or x (fit a p)) alts N))
        (arg_tys ~~ pts') Y
  end

(* the method that the types of the arguments select, if it is certain: among the candidates of
   the strict phase if there are any, else among those of the loose phase *)
fun pick_method jenv (cands : (mdef * (string * ty) list) list) (arg_tys : ty list)
    : (mdef * (string * ty) list) option =
  let
    val n = length arg_tys
    val fitting = filter (fn c => fits_arity c n) cands
    fun live_of strict =
      filter (fn (_, t) => t <> N) (map (fn c => (c, cand_tri jenv strict c arg_tys)) fitting)
    val live = (case live_of true of [] => live_of false | l => l)
  in
    (case live of
       [] => NONE
     | [(c, _)] => SOME c
     | _ =>
         let
           val sure = map #1 (filter (fn (_, t) => t = Y) live)
           fun dominates (MT {ps = p1, ...}, m1) (MT {ps = p2, ...}, m2) =
             length p1 = length p2 andalso
             forall (fn (a, b) => is_sub jenv 8 (subst m1 a) (subst m2 b) = Y) (p1 ~~ p2)
           val best = filter (fn c => forall (fn (o1, _) => o1 = c orelse dominates c o1) live) sure
         in (case best of [c] => SOME c | _ => NONE) end)
  end

(* --- inference ---------------------------------------------------------------------------- *)

(* the box of a primitive type; the other types are their own *)
fun box_ty t =
  (case t of
     TPrimT p =>
       (case p of
          "int" => TCls (Platform.key_of "java.lang.Integer", [])
        | "char" => TCls (Platform.key_of "java.lang.Character", [])
        | "boolean" => TCls (Platform.key_of "java.lang.Boolean", [])
        | "byte" => TCls (Platform.key_of "java.lang.Byte", [])
        | "short" => TCls (Platform.key_of "java.lang.Short", [])
        | "long" => TCls (Platform.key_of "java.lang.Long", [])
        | "float" => TCls (Platform.key_of "java.lang.Float", [])
        | "double" => TCls (Platform.key_of "java.lang.Double", [])
        | _ => TUnknown)
   | _ => t)

(* the instance of the class "kp" that the type "a" is a subtype of, if its supertypes tell *)
fun as_super jenv fuel (a : ty) kp : ty option =
  (case a of
     TCls (ka, _) =>
       if ka = kp then SOME a
       else if fuel = 0 then NONE
       else get_first (fn s => as_super jenv (fuel - 1) s kp) (supers_of jenv a)
   | _ => NONE)

(* what the type "a" of an argument says of the type parameters "tps" in the parameter type "p" *)
fun unify jenv tps (p : ty) (a : ty) : (string * ty) list =
  (case (p, a) of
     (TTv k, _) =>
       if member (op =) tps k andalso a <> TUnknown andalso a <> TNull
       then (case box_ty a of TUnknown => [] | b => [(k, b)])
       else []
   | (TArr p1, TArr a1) => unify jenv tps p1 a1
   | (TCls (kp, pa), TCls _) =>
       (case as_super jenv 8 a kp of
          SOME (TCls (_, aa)) =>
            if length pa = length aa then maps (fn (x, y) => unify jenv tps x y) (pa ~~ aa) else []
        | _ => [])
   | _ => [])

(* one type for each type parameter: what all the bindings agree on, else unknown *)
fun combine_binds tps (binds : (string * ty) list) : (string * ty) list =
  map (fn k =>
         (k, (case map snd (filter (fn (k1, _) => k1 = k) binds) of
                [] => TUnknown
              | t :: ts => if forall (fn x => x = t) ts then t else TUnknown))) tps

fun erase_tps tps t =
  (case t of
     TTv k => if member (op =) tps k then TUnknown else t
   | TCls (k, args) => TCls (k, map (erase_tps tps) args)
   | TArr x => TArr (erase_tps tps x)
   | _ => t)

(* The parameter type of each argument of a call of the method (a variable-arity method takes
   the element type for the last arguments, or the array for a single array argument). *)
fun arg_params (MT {ps, va, ...}, mm) (arg_tys : ty list) : ty list =
  let
    val ps' = map (subst mm) ps
    val np = length ps'
    val n = length arg_tys
    fun elem_of t = (case t of TArr e => e | x => x)
  in
    List.tabulate (n, fn i =>
      if va andalso np > 0 andalso i >= np - 1
      then (if n = np andalso (case List.nth (arg_tys, i) of TArr _ => true | _ => false)
            then List.last ps' else elem_of (List.last ps'))
      else if i < np then List.nth (ps', i) else TUnknown)
  end

(* The bindings of the type parameters of the method that the types of the arguments give; a
   lambda or a method reference has no type here and says nothing. *)
fun arg_binds jenv (c as (MT {tps, ...}, _)) (arg_tys : ty list) : (string * ty) list =
  maps (fn (p, a) => unify jenv tps p a) (arg_params c arg_tys ~~ arg_tys)

(* --- functional interfaces ------------------------------------------------------------------- *)

(* the abstract methods of an interface type, with the substitution of its type parameters *)
fun abstract_methods jenv fuel (t : ty) : (string * mdef * (string * ty) list) list =
  (case t of
     TCls (k, args) =>
       (case def_of jenv k of
          NONE => []
        | SOME (CD {tps, methods, supers, ...}) =>
            let
              val m = inst_map tps args
              fun sg (MT {ps, ...}, mm) = map (subst mm) ps
              val own_sigs = map (fn (n, md) => (n, sg (md, m))) methods
              val own = List.mapPartial (fn (n, md as MT {abs, ...}) =>
                                           if abs then SOME (n, md, m) else NONE) methods
              val inherited =
                if fuel = 0 then []
                else maps (fn s => abstract_methods jenv (fuel - 1) (subst m s)) supers
              fun keep (n, md, mm) = not (member (op =) own_sigs (n, sg (md, mm)))
              fun first_of _ [] = []
                | first_of seen ((n, md, mm) :: rest) =
                    if member (op =) seen (n, sg (md, mm)) then first_of seen rest
                    else (n, md, mm) :: first_of ((n, sg (md, mm)) :: seen) rest
            in own @ first_of (map (fn (n, md, mm) => (n, sg (md, mm))) own)
                              (filter keep inherited) end)
   | _ => [])

(* The function type of a functional interface type: the parameter types and the result of its one
   abstract method (those of Object do not count). *)
fun sam_of jenv (t : ty) : (ty list * ty) option =
  (case t of
     TCls (k, _) =>
       (case def_of jenv k of
          SOME (CD {kind = "interface", ...}) =>
            let
              fun of_object (n, MT {ps, ...}, _) =
                (n = "equals" andalso length ps = 1) orelse
                (n = "hashCode" andalso null ps) orelse (n = "toString" andalso null ps)
            in
              (case filter (not o of_object) (abstract_methods jenv 8 t) of
                 [(_, MT {ps, ret, tps = [], ...}, mm)] => SOME (map (subst mm) ps, subst mm ret)
               | _ => NONE)
            end
        | _ => NONE)
   | _ => NONE)

(* whether a lambda with that many parameters can have the parameter type "pt" *)
fun lambda_arity_ok jenv (pt : ty) (a : pos A.jExpr) : bool =
  (case a of
     A.ELambda (lps, _, _, _) =>
       (case pt of
          TCls _ =>
            (case sam_of jenv pt of
               SOME (pts, _) => length pts = length lps
             | NONE => not (known_class jenv pt))
        | TUnknown => true
        | TTv _ => true
        | _ => false)
   | _ => true)

fun dims_ty_ds t ds = fold (fn _ => fn x => TArr x) ds t

(* a name bound to a type, as the parameters of a lambda are *)
fun bind_var name pos ty jenv =
  set_scope (Symtab.update (vkey name, Param pos) (names_of jenv), meths_of jenv,
             Symtab.update (vkey name, ty) (vtypes_of jenv)) jenv

(* the parameters of a lambda declared in the environment, with the types of the context for
   those that are not typed *)
fun bind_lparams jenv (lps : pos A.jLParam list) (ptys : ty list) : jenv =
  let
    val tys = if length ptys = length lps then ptys else map (K TUnknown) lps
  in
    fold (fn (lp, t) => fn j =>
            (case lp of
               A.LPInfer (A.Ident (n, _, ni)) =>
                 if n = "_" then j else bind_var n (A.pos_of_NodeInfo ni) t j
             | A.LPTyped (A.Param (_, ty, _, A.Ident (n, _, ni), ds, _)) =>
                 if n = "_" then j
                 else
                   bind_var n (A.pos_of_NodeInfo ni)
                     (case ty of A.TVar _ => t | _ => dims_ty_ds (ty_of_type j ty) ds) j))
      (lps ~~ tys) jenv
  end

(* --- the type of an expression ---------------------------------------------------------------- *)

datatype tv = Val of ty | Ty of ty | Pk

fun numeric x = member (op =) ["byte", "short", "char", "int", "long", "float", "double"] x
fun promote a b =
  if a = "double" orelse b = "double" then "double"
  else if a = "float" orelse b = "float" then "float"
  else if a = "long" orelse b = "long" then "long" else "int"
fun unary_promote a = if member (op =) ["byte", "short", "char"] a then "int" else a
fun unary_ty t = (case t of TPrimT x => TPrimT (unary_promote x) | _ => TUnknown)

fun lit_type l = (case l of
    A.LInt s =>
      TPrimT (if String.isSuffix "l" s orelse String.isSuffix "L" s then "long" else "int")
  | A.LFloat s =>
      TPrimT (if String.isSuffix "f" s orelse String.isSuffix "F" s then "float" else "double")
  | A.LChar _ => TPrimT "char"
  | A.LString _ => string_ty
  | A.LTextBlock _ => string_ty
  | A.LBool _ => TPrimT "boolean"
  | A.LNull => TNull)

(* the field of an enclosing class's supertypes that a simple name denotes *)
fun inherited_field jenv name : (pos * ty) option =
  let
    fun go [] = NONE
      | go (k :: rest) =
          (case find_field jenv 8 (class_self jenv k) name of
             SOME r => SOME r
           | NONE => go rest)
  in go (cur_of jenv) end

(* the dotted name that an expression is, if it is one *)
fun dotted (e : pos A.jExpr) : string option =
  (case e of
     A.EName (A.Ident (n, _, _)) => SOME n
   | A.EField (e1, A.Ident (n, _, _), _) => Option.map (fn p => p ^ "." ^ n) (dotted e1)
   | _ => NONE)

(* the methods named "name" that static imports bring in *)
fun static_import_methods jenv name =
  let val classes = names_at jenv ("java:sti:" ^ name) @ names_at jenv "java:stid"
  in
    maps (fn c =>
            filter (fn (MT {static, ...}, _) => static)
              (collect_methods jenv 8 (TCls (Platform.key_of c, [])) name)) classes
  end

fun type_of jenv (e : pos A.jExpr) : tv =
  (case e of
     A.ELit (l, _) => Val (lit_type l)
   | A.EName (A.Ident (name, _, _)) =>
       if Symtab.defined (names_of jenv) (vkey name)
       then Val (the_default TUnknown (Symtab.lookup (vtypes_of jenv) (vkey name)))
       else
         (case inherited_field jenv name of
            SOME (_, t) => Val t
          | NONE =>
              (case Symtab.lookup (names_of jenv) (tkey name) of
                 SOME _ => Ty (lookup_type_name jenv name)
               | NONE =>
                   (case import_ty jenv name of
                      SOME t => Ty t
                    | NONE => (case name of
                                 "String" => Ty string_ty
                               | "Object" => Ty object_ty
                               | _ => Pk))))
   | A.EThis _ =>
       (case cur_of jenv of k :: _ => Val (class_self jenv k) | [] => Val TUnknown)
   | A.ESuper _ =>
       (case cur_of jenv of
          k :: _ =>
            (case supers_of jenv (class_self jenv k) of s :: _ => Val s | [] => Val TUnknown)
        | [] => Val TUnknown)
   | A.EQualThis (e1, _) => (case type_of jenv e1 of Ty t => Val t | _ => Val TUnknown)
   | A.EQualSuper (e1, _) =>
       (case type_of jenv e1 of
          Ty t => (case supers_of jenv t of s :: _ => Val s | [] => Val TUnknown)
        | _ => Val TUnknown)
   | A.EParen (e1, _) => type_of jenv e1
   | A.EField (e1, A.Ident (name, _, _), _) =>
       (case type_of jenv e1 of
          Val (TArr _) => if name = "length" then Val (TPrimT "int") else Val TUnknown
        | Val t => (case find_field jenv 8 t name of SOME (_, ft) => Val ft | NONE => Val TUnknown)
        | Ty t =>
            (case find_field jenv 8 t name of
               SOME (_, ft) => Val ft
             | NONE =>
                 (case t of
                    TCls (k, _) =>
                      (case def_of jenv k of
                         SOME (CD {types, ...}) =>
                           (case AList.lookup (op =) types name of
                              SOME (key, _) => Ty (TCls (key, []))
                            | NONE => Val TUnknown)
                       | NONE => Val TUnknown)
                  | _ => Val TUnknown))
        | Pk => (case Option.mapPartial (platform_class jenv) (dotted e) of
                   SOME t => Ty t
                 | NONE => Pk))
   | A.EIndex (a, _, _) =>
       (case type_of jenv a of Val (TArr t) => Val t | _ => Val TUnknown)
   | A.ECall (recv, _, id, args, _) =>
       (case call_info jenv recv id args of SOME (_, t) => Val t | NONE => Val TUnknown)
   | A.ENew (_, t, _, _, _) => Val (ty_of_type jenv t)
   | A.ENewArray (t, des, ds, _, _) =>
       Val (fold (fn _ => fn x => TArr x) (des @ map (fn _ => e) ds) (ty_of_type jenv t))
   | A.EArrayInit _ => Val TUnknown
   | A.EClassLit _ => Val TUnknown
   | A.EMethodRef _ => Val TUnknown
   | A.ELambda _ => Val TUnknown
   | A.EUnary (u, e1, _) =>
       (case u of
          A.UNot => Val (TPrimT "boolean")
        | A.UCompl => Val (unary_ty (val_ty jenv e1))
        | A.UPlus => Val (unary_ty (val_ty jenv e1))
        | A.UMinus => Val (unary_ty (val_ty jenv e1))
        | _ => Val (val_ty jenv e1))
   | A.EBinary (b, l, r, _) =>
       let
         val tl = val_ty jenv l
         val tr = val_ty jenv r
       in
         (case b of
            A.LOr => Val (TPrimT "boolean") | A.LAnd => Val (TPrimT "boolean")
          | A.Eq => Val (TPrimT "boolean") | A.Ne => Val (TPrimT "boolean")
          | A.Lt => Val (TPrimT "boolean") | A.Gt => Val (TPrimT "boolean")
          | A.Le => Val (TPrimT "boolean") | A.Ge => Val (TPrimT "boolean")
          | A.Add =>
              if tl = string_ty orelse tr = string_ty then Val string_ty
              else (case (tl, tr) of
                      (TPrimT x, TPrimT y) => if numeric x andalso numeric y
                                              then Val (TPrimT (promote x y)) else Val TUnknown
                    | _ => Val TUnknown)
          | A.Shl => (case tl of TPrimT x => Val (TPrimT (unary_promote x)) | _ => Val TUnknown)
          | A.Shr => (case tl of TPrimT x => Val (TPrimT (unary_promote x)) | _ => Val TUnknown)
          | A.UShr => (case tl of TPrimT x => Val (TPrimT (unary_promote x)) | _ => Val TUnknown)
          | _ =>
              (case (tl, tr) of
                 (TPrimT "boolean", TPrimT "boolean") => Val (TPrimT "boolean")
               | (TPrimT x, TPrimT y) =>
                   if numeric x andalso numeric y then Val (TPrimT (promote x y)) else Val TUnknown
               | _ => Val TUnknown))
       end
   | A.EAssign (l, _, _, _) => Val (val_ty jenv l)
   | A.ECond (_, a, b, _) =>
       let
         val ta = val_ty jenv a
         val tb = val_ty jenv b
       in
         if ta = tb then Val ta
         else (case (ta, tb) of
                 (TPrimT x, TPrimT y) => if numeric x andalso numeric y
                                         then Val (TPrimT (promote x y)) else Val TUnknown
               | (TNull, t) => Val t
               | (t, TNull) => Val t
               | _ => Val TUnknown)
       end
   | A.ECast (ts, _, _) => (case ts of t :: _ => Val (ty_of_type jenv t) | [] => Val TUnknown)
   | A.EInstanceof _ => Val (TPrimT "boolean")
   | A.ESwitch (_, cases, _) => Val (switch_ty jenv cases))

and val_ty jenv e = (case type_of jenv e of Val t => t | _ => TUnknown)

(* The type of a switch expression: what the results of its arms agree on (numbers by promotion).
   An arm is typed in the scope of the pattern variables of its label; an arm whose block
   declares locals is not typed. *)
and switch_ty jenv (cases : pos A.jSwitchCase list) : ty =
  let
    fun pat_binds p =
      (case p of
         A.PType (_, t, SOME (A.Ident (n, _, ni)), _) =>
           if n = "_" then [] else [(n, A.pos_of_NodeInfo ni, ty_of_type jenv t)]
       | A.PType (_, _, NONE, _) => []
       | A.PRecord (_, ps, _) => maps pat_binds ps
       | A.PAny _ => [])
    fun label_binds l =
      (case l of
         A.LCase (items, _, _) =>
           maps (fn A.CIPattern p => pat_binds p | _ => []) items
       | A.LDefault _ => [])
    fun with_binds bs = fold (fn (n, pos, t) => fn j => bind_var n pos t j) bs jenv
    (* the yielded expressions of statements; NONE if there are locals *)
    fun yields ss =
      let
        fun one s =
          (case s of
             A.SYield (e, _) => SOME [e]
           | A.SBlock (A.Block (ss1, _)) => all ss1
           | A.SIf (_, t, e, _) =>
               (case (one t, (case e of SOME x => one x | NONE => SOME [])) of
                  (SOME a, SOME b) => SOME (a @ b)
                | _ => NONE)
           | A.SLabeled (_, s1, _) => one s1
           | A.SLocal _ => NONE
           | A.SClassDecl _ => NONE
           | A.SWhile (_, b, _) => one b
           | A.SDo (b, _, _) => one b
           | A.SFor _ => NONE
           | A.SForEach _ => NONE
           | A.STry _ => NONE
           | A.SSwitch _ => NONE
           | A.SSync _ => NONE
           | _ => SOME [])
        and all ss1 =
          fold (fn x => fn acc => (case (acc, one x) of
                                      (SOME a, SOME b) => SOME (a @ b)
                                    | _ => NONE)) ss1 (SOME [])
      in all ss end
    fun arm c : ty list option =
      (case c of
         A.SwRule (l, body, _) =>
           let val env = with_binds (label_binds l)
           in
             (case body of
                A.RBExpr e => SOME [val_ty env e]
              | A.RBBlock (A.Block (ss, _)) =>
                  Option.map (map (val_ty env)) (yields ss)
              | A.RBThrow _ => SOME [])
           end
       | A.SwGroup (ls, ss, _) =>
           let val env = with_binds (maps label_binds ls)
           in Option.map (map (val_ty env)) (yields ss) end)
    val arms = map arm cases
    val tys = if exists (not o is_some) arms then NONE else SOME (maps the arms)
    fun join ts =
      (case filter (fn t => t <> TNull) ts of
         [] => TUnknown
       | t :: rest =>
           if exists (fn x => x = TUnknown) (t :: rest) then TUnknown
           else if forall (fn x => x = t) rest then t
           else if forall (fn x => (case x of TPrimT p => numeric p | _ => false)) (t :: rest)
           then (TPrimT (fold (fn x => fn acc => (case x of TPrimT p => promote acc p | _ => acc))
                          rest (case t of TPrimT p => unary_promote p | _ => "int")))
           else TUnknown)
  in (case tys of SOME ts => join ts | NONE => TUnknown) end

(* The method that a call resolves to, with the types of the arguments. Without receiver, the
   innermost enclosing class that has a method of that name (inherited ones included) is the one
   that counts (JLS 15.12.1). A lambda must fit the arity of the functional interface that a
   candidate takes. *)
and call_pick jenv (recv : pos A.jExpr option) (A.Ident (name, _, _)) (args : pos A.jExpr list)
    : ((mdef * (string * ty) list) * ty list) option =
  let
    val arg_tys = map (val_ty jenv) args
    fun lambdas_ok c =
      let val n = length args
      in
        if not (fits_arity c n) then false
        else forall (fn (alts, a) => exists (fn p => lambda_arity_ok jenv p a) alts)
               (param_tys c n ~~ args)
      end
    fun finish cands =
      (case pick_method jenv (filter lambdas_ok cands) arg_tys of
         SOME c => SOME (c, arg_tys)
       | NONE => NONE)
  in
    (case recv of
       NONE =>
         let
           fun go [] = NONE
             | go (k :: rest) =
                 (case collect_methods jenv 8 (class_self jenv k) name of
                    [] => go rest
                  | cs => SOME cs)
         in
           (case go (cur_of jenv) of
              SOME cs => finish cs
            | NONE => finish (static_import_methods jenv name))
         end
     | SOME r =>
         (case type_of jenv r of
            Val (TArr _) => NONE
          | Val t => finish (collect_methods jenv 8 t name)
          | Ty t => finish (collect_methods jenv 8 t name)
          | Pk => NONE))
  end

(* what a lambda argument adds to the bindings of the type parameters: its result *)
and lambda_binds jenv (c as (MT {tps, ...}, _)) (args : pos A.jExpr list) (arg_tys : ty list)
    (binds0 : (string * ty) list) : (string * ty) list =
  let
    val known = filter (fn (_, t) => t <> TUnknown) (combine_binds tps binds0)
  in
    maps (fn (p, a) =>
            (case a of
               A.ELambda (lps, _, body, _) =>
                 (case sam_of jenv (subst known p) of
                    SOME (pts, TTv k) =>
                      if member (op =) tps k
                      then [(k, box_ty (lambda_ret jenv lps (map (erase_tps tps) pts) body))]
                      else []
                  | _ => [])
             | A.EMethodRef (tg, _, A.Ident (n, _, _), _) =>
                 (case sam_of jenv (subst known p) of
                    SOME (pts, TTv k) =>
                      if member (op =) tps k
                      then (case mref_info jenv tg n (map (erase_tps tps) pts) of
                              SOME (_, t) => [(k, box_ty t)]
                            | NONE => [])
                      else []
                  | _ => [])
             | _ => []))
      (arg_params c arg_tys ~~ args)
  end

(* the type of the result of a lambda: an expression, or a block that is one "return" *)
and lambda_ret jenv lps ptys (body : pos A.jLBody) : ty =
  let val env = bind_lparams jenv lps ptys
  in
    (case body of
       A.LBExpr e => val_ty env e
     | A.LBBlock (A.Block ([A.SReturn (SOME e, _)], _)) => val_ty env e
     | _ => TUnknown)
  end

(* The method that a method reference "target::name" denotes when the functional interface has
   the parameter types "pts": its declaration (none for a constructor of an unknown class) and
   the type of the result. *)
and mref_info jenv (tg : pos A.jMRTarget) name (pts : ty list) : (pos option * ty) option =
  let
    val tv = (case tg of
                A.MRExpr e => type_of jenv e
              | A.MRType t => Ty (ty_of_type jenv t))
    fun result (c as (MT {pos, ret, tps, ...}, mm)) tys =
      let val bs = combine_binds tps (arg_binds jenv c tys)
      in SOME (SOME pos, subst bs (subst mm ret)) end
    fun pick cands tys =
      (case pick_method jenv cands tys of SOME c => result c tys | NONE => NONE)
  in
    (case tv of
       Ty t =>
         if name = "new" then
           (case t of
              TCls (k, args) =>
                (case def_of jenv k of
                   SOME (CD {tps, ctors, ...}) =>
                     let val m = inst_map tps args
                     in
                       (case pick_method jenv (map (fn d => (d, m)) ctors) pts of
                          SOME (MT {pos, ...}, _) => SOME (SOME pos, t)
                        | NONE => SOME (NONE, t))
                     end
                 | NONE => SOME (NONE, t))
            | TArr _ => SOME (NONE, t)
            | _ => NONE)
         else
           let
             val cands = collect_methods jenv 8 t name
             val statics = filter (fn (MT {static, ...}, _) => static) cands
             val insts = filter (fn (MT {static, ...}, _) => not static) cands
             val a = pick statics pts
             val b = (case pts of
                        r :: rest => if is_sub jenv 8 r t <> N then pick insts rest else NONE
                      | [] => NONE)
           in (case (a, b) of (SOME x, NONE) => SOME x | (NONE, SOME y) => SOME y | _ => NONE) end
     | Val t => pick (filter (fn (MT {static, ...}, _) => not static)
                             (collect_methods jenv 8 t name)) pts
     | Pk => NONE)
  end

(* The method that a call resolves to, and the type of the call: the type parameters of the method
   are bound by the types of the arguments, and by the result of the lambdas among them. *)
and call_info jenv recv id (args : pos A.jExpr list) : (pos * ty) option =
  (case call_pick jenv recv id args of
     SOME (c as (MT {pos, tps, ret, ...}, mm), arg_tys) =>
       let
         val b0 = arg_binds jenv c arg_tys
         val bs = combine_binds tps (b0 @ lambda_binds jenv c args arg_tys b0)
       in SOME (pos, subst bs (subst mm ret)) end
   | NONE => NONE)

(* The type that the context expects of each argument of a call, for the lambdas and method
   references among them: the parameter type of the method, with the type parameters it has been
   possible to bind. *)
and call_expects jenv recv id (args : pos A.jExpr list) : ty list =
  (case call_pick jenv recv id args of
     SOME (c as (MT {tps, ...}, _), arg_tys) =>
       let
         val known = filter (fn (_, t) => t <> TUnknown)
                       (combine_binds tps (arg_binds jenv c arg_tys))
       in map (fn p => subst known p) (arg_params c arg_tys) end
   | NONE => map (K TUnknown) args)

(* the same for a constructor of a class *)
and new_expects jenv (t : ty) (args : pos A.jExpr list) : ty list =
  (case t of
     TCls (k, targs) =>
       (case def_of jenv k of
          SOME (CD {tps, ctors, ...}) =>
            let
              val m = inst_map tps targs
              val arg_tys = map (val_ty jenv) args
              val n = length args
              fun ok c = fits_arity c n andalso
                forall (fn (alts, a) => exists (fn p => lambda_arity_ok jenv p a) alts)
                  (param_tys c n ~~ args)
            in
              (case pick_method jenv (filter ok (map (fn d => (d, m)) ctors)) arg_tys of
                 SOME c => arg_params c arg_tys
               | NONE => map (K TUnknown) args)
            end
        | NONE => map (K TUnknown) args)
   | _ => map (K TUnknown) args)
fun put_name key kind jenv =
  set_scope (Symtab.update (key, kind) (names_of jenv), meths_of jenv,
             Symtab.delete_safe key (vtypes_of jenv)) jenv

fun put_name_t key kind ty jenv =
  set_scope (Symtab.update (key, kind) (names_of jenv), meths_of jenv,
             Symtab.update (key, ty) (vtypes_of jenv)) jenv

(* Declares a name, reporting its declaration site. The blank identifier declares nothing. *)
fun reg_with keyf mk_kind ty jenv (A.Ident (name, _, ni)) =
  if name = "_" then jenv
  else
    let
      val pos = A.pos_of_NodeInfo ni
      val kind = mk_kind pos
      val _ = report_decl (describe_kind kind) name pos
    in put_name_t (keyf name) kind ty jenv end

fun reg_v mk_kind jenv id = reg_with vkey mk_kind TUnknown jenv id
fun reg_vt mk_kind ty jenv id = reg_with vkey mk_kind ty jenv id
fun reg_t mk_kind jenv id = reg_with tkey mk_kind TUnknown jenv id

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
  in set_scope (names_of jenv, meths', vtypes_of jenv) jenv end

fun mod_kw_is ms kw = exists (fn A.MKw (s, _) => s = kw | A.MAnnot _ => false) ms

fun is_receiver (A.Ident (n, _, _)) = n = "this" orelse String.isSuffix ".this" n

fun dims_ty t ds = fold (fn _ => fn x => TArr x) ds t

fun param_ty jenv (A.Param (_, t, va, _, ds, _)) =
  let val b = dims_ty (ty_of_type jenv t) ds in if va then TArr b else b end

fun real_params ps = filter (fn A.Param (_, _, _, pid, _, _) => not (is_receiver pid)) ps

fun quiet_enter keyf mk_kind jenv (A.Ident (name, _, ni)) =
  if name = "_" then jenv else put_name (keyf name) (mk_kind (A.pos_of_NodeInfo ni)) jenv

fun tparam_key (A.TParam (_, pid, _, _)) = pos_key (ident_pos pid)

(* the parts of a class-like declaration: kind, name, modifiers, type parameters, supertypes, the
   permitted subtypes, enum constants, record components, body *)
fun class_parts (d : pos A.jDecl) =
  (case d of
     A.DClass (ms, id, tps, ext, impl, perm, body, _) =>
       SOME ("class", id, ms, tps, (case ext of SOME t => [t] | NONE => []) @ impl, perm, [], [],
             body)
   | A.DInterface (ms, id, tps, ext, perm, body, _) =>
       SOME ("interface", id, ms, tps, ext, perm, [], [], body)
   | A.DEnum (ms, id, impl, consts, _, body, _) =>
       SOME ("enum", id, ms, [], impl, [], consts, [], body)
   | A.DRecord (ms, id, tps, comps, impl, body, _) =>
       SOME ("record", id, ms, tps, impl, [], [], comps, body)
   | A.DAnnotType (ms, id, body, _) => SOME ("annotation", id, ms, [], [], [], [], [], body)
   | _ => NONE)

(* a method or a constructor, its type parameters in scope for the types of its signature *)
fun mk_mdef jenv ms mtps (ret : jenv -> ty) ps pos abs : mdef =
  let
    val s = fold (fn A.TParam (_, pid, _, _) => fn j => quiet_enter tkey Tparam j pid) mtps jenv
    val ps' = real_params ps
  in
    MT {pos = pos, tps = map tparam_key mtps, ps = map (param_ty s) ps',
        va = (case rev ps' of A.Param (_, _, v, _, _, _) :: _ => v | [] => false),
        ret = ret s, static = mod_kw_is ms "static", abs = abs}
  end

(* The definition of a class from its body, in a scope that has the type parameters and the member
   types; then the member classes. The result is the scope with the definitions added. *)
fun register_body s2 site key kind tp_keys supers consts comps (body : pos A.jDecl list) : jenv =
  let
    val self = TCls (key, map TTv tp_keys)
    val in_iface = (kind = "interface" orelse kind = "annotation")
    (* of a class of the platform only the members that a program can see are kept *)
    val platform = in_platform_unit s2
    fun vis ms =
      not platform orelse in_iface orelse mod_kw_is ms "public" orelse mod_kw_is ms "protected"
    val fields =
      maps (fn A.DField (ms, t, vds, _) =>
              if not (vis ms) then []
              else
                map (fn A.VarDecl (id, ds, _, _) =>
                       (ident_name_of id,
                        FD {pos = ident_pos id, ty = dims_ty (ty_of_type s2 t) ds,
                            static = in_iface orelse mod_kw_is ms "static"})) vds
             | _ => []) body
      @ map (fn A.EnumConst (_, id, _, _, _) =>
               (ident_name_of id, FD {pos = ident_pos id, ty = self, static = true})) consts
      @ (if platform then []
         else
           map (fn c as A.Param (_, _, _, id, _, _) =>
                  (ident_name_of id,
                   FD {pos = ident_pos id, ty = param_ty s2 c, static = false})) comps)
    val methods =
      maps (fn A.DMethod (ms, mtps, res, id, ps, ds, _, _, _, _) =>
              if not (vis ms) then []
              else
                [(ident_name_of id,
                  mk_mdef s2 ms mtps (fn s => dims_ty (ty_of_type s res) ds) ps (ident_pos id)
                    (in_iface andalso not (mod_kw_is ms "default" orelse mod_kw_is ms "static"
                                           orelse mod_kw_is ms "private")))]
             | _ => []) body
    val explicit = map #1 methods
    val accessors =
      maps (fn c as A.Param (_, _, _, id, _, _) =>
              if member (op =) explicit (ident_name_of id) then []
              else [(ident_name_of id,
                     MT {pos = ident_pos id, tps = [], ps = [], va = false, ret = param_ty s2 c,
                         static = false, abs = false})]) comps
    val ctors =
      maps (fn A.DCtor (ms, mtps, id, ps, _, _, _) =>
              if vis ms then [mk_mdef s2 ms mtps (K self) ps (ident_pos id) false] else []
             | _ => []) body
    val types =
      maps (fn m => (case class_parts m of
                       SOME (_, mid, ms, _, _, _, _, _, _) =>
                         if vis ms
                         then [(ident_name_of mid, (class_key s2 (ident_pos mid), ident_pos mid))]
                         else []
                     | NONE => [])) body
    val s3 = add_def key (CD {site = site, kind = kind, tps = tp_keys, supers = supers,
                              fields = fields, methods = methods @ accessors, ctors = ctors,
                              types = types}) s2
  in fold (fn m => fn s => register_class s m) body s3 end

and register_class scope (d : pos A.jDecl) : jenv =
  (case class_parts d of
     NONE => scope
   | SOME (kind, id, _, tps, sup_types, _, consts, comps, body) =>
       let
         val s1 = fold (fn A.TParam (_, pid, _,
           _) => fn s => quiet_enter tkey Tparam s pid) tps scope
         val s2 = fold (fn m => fn s =>
                          (case class_parts m of
                             SOME (_, mid, _, _, _, _, _, _, _) => quiet_enter tkey Typ s mid
                           | NONE => s)) body s1
         val key = class_key s2 (ident_pos id)
         (* Enum<E> and Record are known if the platform is *)
         val platform_super =
           if src_of s2 = "" then TUnknown
           else if kind = "enum" then
             TCls (Platform.key_of "java.lang.Enum", [TCls (key, [])])
           else TCls (Platform.key_of "java.lang.Record", [])
         val supers = map (ty_of_type s2) sup_types
                      @ (if kind = "enum" orelse kind = "record" then [platform_super] else [])
         val res = register_body s2 (ident_pos id) key kind (map tparam_key tps) supers
                     consts comps body
       in set_defs (defs_of res) scope end)

(* an anonymous class (or the body of an enum constant) of the given supertype *)
fun register_anon scope key (sup : ty) (body : pos A.jDecl list) : jenv =
  let
    val s2 = fold (fn m => fn s =>
                     (case class_parts m of
                        SOME (_, mid, _, _, _, _, _, _, _) => quiet_enter tkey Typ s mid
                      | NONE => s)) body scope
    val res = register_body s2 Position.none key "class" [] [sup] [] [] body
  in set_defs (defs_of res) scope end

(* --- imports, and the classes of the platform ----------------------------------------------------- *)

(* The imports of a unit as facts about the platform in the environment (see "put_vtype"): the
   package of the unit and the packages and classes imported on demand, the classes imported by
   name, and the classes whose static members are imported. *)
fun add_imports pkg (imports : pos A.jImport list) jenv : jenv =
  let
    fun qn_of ids = space_implode "." (map ident_name_of ids)
    fun one (A.Import (kind, ids, _)) s =
      (case (kind, rev ids) of
         (A.ImSingle, last :: _) =>
           put_vtype ("java:imp:" ^ ident_name_of last) (TCls (Platform.key_of (qn_of ids), [])) s
       | (A.ImDemand, _) => add_name_at "java:demand" (qn_of ids) s
       | (A.ImStaticSingle, last :: cls) =>
           add_name_at ("java:sti:" ^ ident_name_of last) (qn_of (rev cls)) s
       | (A.ImStaticDemand, _) => add_name_at "java:stid" (qn_of ids) s
       | _ => s)
    val s0 = if pkg = "" then jenv else add_name_at "java:pkg" pkg jenv
  in fold one imports s0 end

(* The sources of the platform: a "src.zip" of a JDK, or a directory with the same layout (the
   packages below a directory per module, or directly below it), as a tree of packages. *)
datatype tree = Tree of {root : string, zip : bool, modules : bool,
                         pkgs : (string * string list) Symtab.table}
  \<comment> \<open>"pkgs": the module of each package ("" if there are none) and its top-level classes\<close>

fun list_entries root zip : string list =
  let
    val cmd =
      if zip then "unzip -Z1 " ^ Bash.string root ^ " '*.java'"
      else "cd " ^ Bash.string root ^ " && find . -name '*.java' -print | sed 's|^\\./||'"
    val (out, rc) = Isabelle_System.bash_output cmd
  in if rc = 0 then split_lines out else [] end

fun build_tree root : tree option =
  let
    val zip = File.is_file (Path.explode root)
    val entries = list_entries root zip
    val modules = not (member (op =) entries "java/lang/Object.java")
    fun add e tab =
      let
        val comps = String.fields (fn c => c = #"/") e
        val (m, rest) = if modules then (hd comps, tl comps) else ("", comps)
      in
        if length rest < 2 then tab
        else
          let
            val pkg = space_implode "." (take (length rest - 1) rest)
            val file = List.last rest
            val base = String.substring (file, 0, size file - 5)
          in
            if base = "package-info" orelse base = "module-info" then tab
            else Symtab.map_default (pkg, (m, [])) (fn (m', ns) => (m', base :: ns)) tab
          end
      end
  in
    if null entries then NONE
    else SOME (Tree {root = root, zip = zip, modules = modules, pkgs = fold add entries Symtab.empty})
  end

val trees = Synchronized.var "Java_Platform.trees" (Symtab.empty : tree option Symtab.table)

(* a lock that its owner may take again, around the loading of classes: classes are read on demand
   by whichever theory first needs them, and what is read must be complete for all *)
val load_lock = Synchronized.var "Java_Platform.lock" (NONE : (Isabelle_Thread.T * int) option)

fun with_load_lock f =
  let
    val me = Isabelle_Thread.self ()
    val _ =
      Synchronized.guarded_access load_lock (fn st =>
        (case st of
           NONE => SOME ((), SOME (me, 1))
         | SOME (t, n) => if Isabelle_Thread.equal (t, me) then SOME ((), SOME (t, n + 1)) else NONE))
    val res = Exn.capture f ()
    val _ =
      Synchronized.change load_lock (fn st =>
        (case st of
           SOME (t, n) => if n > 1 then SOME (t, n - 1) else NONE
         | NONE => NONE))
  in Exn.release res end

fun tree_of src : tree option =
  if src = "" then NONE
  else
    (case Symtab.lookup (Synchronized.value trees) src of
       SOME t => t
     | NONE =>
         with_load_lock (fn () =>
           (case Symtab.lookup (Synchronized.value trees) src of
              SOME t => t
            | NONE =>
                let val t = Option.join (try build_tree src)
                    val _ = Synchronized.change trees (Symtab.update (src, t))
                in t end)))

(* the top-level class "name" of the package "pkg" *)
fun tree_type src pkg name : string option =
  (case tree_of src of
     SOME (Tree {pkgs, ...}) =>
       (case Symtab.lookup pkgs pkg of
          SOME (_, names) => if member (op =) names name then SOME (pkg ^ "." ^ name) else NONE
        | NONE => NONE)
   | NONE => NONE)

fun tree_pkg src pkg : bool =
  (case tree_of src of SOME (Tree {pkgs, ...}) => Symtab.defined pkgs pkg | NONE => false)

(* the package and the top-level class of the qualified name of a class *)
fun split_qn (Tree {pkgs, ...}) qn : (string * string) option =
  let
    val comps = String.fields (fn c => c = #".") qn
    fun try_at i =
      if i < 1 then NONE
      else
        let
          val pkg = space_implode "." (take i comps)
          val top = List.nth (comps, i)
        in
          (case Symtab.lookup pkgs pkg of
             SOME (_, names) => if member (op =) names top then SOME (pkg, top) else try_at (i - 1)
           | NONE => try_at (i - 1))
        end
  in try_at (length comps - 1) end

(* The source file of a class of the tree, extracted from the archive if there is one; the file
   is what the positions of the declarations of the class refer to. *)
fun class_file (Tree {root, zip, modules, pkgs}) pkg top : Path.T option =
  (case Symtab.lookup pkgs pkg of
     NONE => NONE
   | SOME (m, _) =>
       let
         val rel = space_implode "/" (String.fields (fn c => c = #".") pkg @ [top ^ ".java"])
         val full = if modules then m ^ "/" ^ rel else rel
       in
         if not zip then SOME (Path.append (Path.explode root) (Path.explode full))
         else
           let
             val cache = Path.explode ("$ISABELLE_TMP_PREFIX/java_src_" ^ Message_Digest.rep_short (SHA1.digest root))
             val target = Path.append cache (Path.explode full)
           in
             if File.is_file target then SOME target
             else
               let
                 val _ = Isabelle_System.make_directory (Path.dir target)
                 val (_, rc) =
                   Isabelle_System.bash_output
                     ("unzip -o -q " ^ Bash.string root ^ " " ^ Bash.string full ^ " -d "
                      ^ Bash.string (File.platform_path cache))
               in if rc = 0 andalso File.is_file target then SOME target else NONE end
           end
       end)

val platform_ctxt = Proof_Context.init_global \<^theory>

(* the qualified names of the classes of a declaration, as the keys of their positions *)
fun enter_aliases prefix (d : pos A.jDecl) jenv : jenv =
  (case class_parts d of
     NONE => jenv
   | SOME (_, id, _, _, _, _, _, _, body) =>
       let
         val qn = prefix ^ ident_name_of id
         val s1 = put_vtype ("java:qn:" ^ pos_key (ident_pos id)) (TCls (Platform.key_of qn, [])) jenv
       in fold (fn m => fn s => enter_aliases (qn ^ ".") m s) body s1 end)

(* Reads the unit of the top-level class "top" of "pkg" and publishes the definitions of its
   classes. *)
fun load_unit src tree pkg top : unit =
  (case class_file tree pkg top of
     NONE => ()
   | SOME file =>
       let
         val text = File.read file
         val pos = Position.line_file 1 (File.platform_path file)
         val source = Input.source false text (pos, pos)
       in
         (case Java_Parse.parse_quiet Java_Parse.Entry_Unit platform_ctxt source of
            SOME (A.Source (A.Unit (_, imports, A.Types ds, _))) =>
              let
                val prefix = pkg ^ "."
                val s0 = put_vtype "java:platform" TUnknown (set_src src empty_jenv)
                val s1 = add_imports pkg imports s0
                val s2 = fold (enter_aliases prefix) ds s1
                val s3 = fold (fn d => fn s =>
                                 (case class_parts d of
                                    SOME (_, id, _, _, _, _, _, _, _) => quiet_enter tkey Typ s id
                                  | NONE => s)) ds s2
                val s4 = fold (fn d => fn s => register_class s d) ds s3
              in
                Synchronized.change Platform.defs
                  (fold (fn (key, d) => Symtab.update (Platform.k src key, d))
                     (Symtab.dest (defs_of s4)))
              end
          | _ => ())
       end)

val loaded_units = Synchronized.var "Java_Platform.units" (Symtab.empty : unit Symtab.table)

fun load_class src key : cdef option =
  with_load_lock (fn () =>
    (case tree_of src of
       NONE => NONE
     | SOME tree =>
         (case split_qn tree (String.extract (key, 3, NONE)) of
            NONE => NONE
          | SOME (pkg, top) =>
              let
                val unit_key = Platform.k src (pkg ^ "." ^ top)
                val fresh = not (Symtab.defined (Synchronized.value loaded_units) unit_key)
                val _ =
                  if fresh
                  then (Synchronized.change loaded_units (Symtab.update (unit_key, ()));
                        ignore (try (load_unit src tree pkg) top))
                  else ()
              in Symtab.lookup (Synchronized.value Platform.defs) (Platform.k src key) end)))

val _ = Platform.load_hook := load_class
val _ = Platform.type_hook := tree_type
val _ = Platform.pkg_hook := tree_pkg

(* Where the platform is read from: the theory option "java_src" (a "src.zip" or a directory;
   "none" for no platform), else the "src.zip" of the JDK of Isabelle or of $JAVA_HOME. *)
val java_src = Attrib.setup_config_string \<^binding>\<open>java_src\<close> (K "")

fun platform_source thy : string =
  let
    fun usable p = p <> "" andalso (File.is_file (Path.explode p) orelse File.is_dir (Path.explode p))
    val cfg = Config.get_global thy java_src
    val candidates =
      map (fn h => if h = "" then "" else h ^ "/lib/src.zip")
        [getenv "ISABELLE_JDK_HOME", getenv "JAVA_HOME"]
  in
    if cfg = "none" then ""
    else if cfg <> "" then (if usable cfg then File.platform_path (Path.explode cfg) else "")
    else
      (case find_first usable candidates of
         SOME p => File.platform_path (Path.explode p)
       | NONE => "")
  end

(* A name that no declaration of the program or import resolves, as a class of the platform
   (java.lang, the package of the unit, an on-demand import): linked to its declaration there. *)
fun use_platform_class jenv (A.Ident (name, _, ni)) : bool =
  (case (if Symtab.defined (names_of jenv) (tkey name) then NONE else import_ty jenv name) of
     SOME (TCls (k, _)) =>
       (case def_of jenv k of
          SOME (CD {site, ...}) => (report_use "Java type" name (A.pos_of_NodeInfo ni) site; true)
        | NONE => false)
   | _ => false)

fun use_type_name_or_platform jenv id =
  if use_platform_class jenv id then () else use_type_name jenv id

(* a simple name in an expression: a variable, else a field inherited from an enclosing class, else
   a type, else a package *)
fun use_simple_name jenv (id as A.Ident (name, _, ni)) =
  if name = "_" then ()
  else
    let val tab = names_of jenv
    in
      if Symtab.defined tab (vkey name) then use_key jenv (vkey name) name (A.pos_of_NodeInfo ni)
      else
        (case inherited_field jenv name of
           SOME (p, _) => report_use "Java field" name (A.pos_of_NodeInfo ni) p
         | NONE => if use_platform_class jenv id then () else use_expr_name jenv id)
    end

fun link_select jenv e1 (A.Ident (name, _, ni)) =
  let val pos = A.pos_of_NodeInfo ni
  in
    (case type_of jenv e1 of
       Val (TArr _) => ()
     | Val t =>
         (case find_field jenv 8 t name of
            SOME (p, _) => report_use "Java field" name pos p
          | NONE => ())
     | Ty t =>
         (case find_field jenv 8 t name of
            SOME (p, _) => report_use "Java field" name pos p
          | NONE =>
              (case t of
                 TCls (k, _) =>
                   (case def_of jenv k of
                      SOME (CD {types, ...}) =>
                        (case AList.lookup (op =) types name of
                           SOME (_, p) => report_use "Java type" name pos p
                         | NONE => ())
                    | NONE => ())
               | _ => ()))
     | Pk => ())
  end

fun link_call jenv recv (id as A.Ident (name, _, ni)) args =
  (case call_info jenv recv id args of
     SOME (p, _) => report_use "Java method" name (A.pos_of_NodeInfo ni) p
   | NONE => ())

fun has_method_named jenv name =
  exists (fn k => not (null (collect_methods jenv 8 (class_self jenv k) name))) (cur_of jenv)

(* the fields, types, enum constants and components that a class body declares are in scope in the
   whole body, and so are its methods *)
fun predeclare_members senv self (members : pos A.jDecl list) consts comps : jenv =
  let
    val s1 = fold (fn m => fn s => (case class_parts m of
                                      SOME (_, id, _, _, _, _, _, _, _) => reg_t Typ s id
                                    | NONE => s)) members senv
    val s2 = fold (fn A.EnumConst (_, id, _, _, _) => fn s => reg_vt EnumC self s id) consts s1
    val s3 = fold (fn c as A.Param (_, _, _, id, _, _) => fn s => reg_vt Fld (param_ty s1 c) s id)
               comps s2
    val s4 = fold (fn m => fn s =>
                     (case m of
                        A.DField (_, t, vds, _) =>
                          fold (fn A.VarDecl (id, ds, _, _) => fn s' =>
                                  reg_vt Fld (dims_ty (ty_of_type s1 t) ds) s' id) vds s
                      | _ => s)) members s3
    fun method_of m = (case m of
        A.DMethod (_, _, _, id, ps, _, _, _, _, _) =>
          let
            val ps' = real_params ps
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
  in add_meths s4 ms end

(* Runs "f" in a nested scope: the tables are restored on exit. *)
fun scoped jenv f =
  let
    val scope = (names_of jenv, meths_of jenv, vtypes_of jenv)
    val cur = cur_of jenv
    val (jenv1, acts) = f jenv
  in (set_cur cur (set_scope scope jenv1), acts) end

fun optl f x = (case x of NONE => [] | SOME y => f y)

(* The type that the context expects of the expression about to be walked (the target type of a
   lambda or a method reference), and the result type of the method or lambda whose body is
   walked (for "return"). They are entries of "vtypes" (see "put_vtype"), so the expectation
   goes to the very next expression only: "walk_e" takes it. *)
fun with_expect t jenv = put_vtype "java:expect" t jenv
fun expect_of jenv = the_default TUnknown (Symtab.lookup (vtypes_of jenv) "java:expect")
fun clear_expect jenv =
  set_scope (names_of jenv, meths_of jenv, Symtab.delete_safe "java:expect" (vtypes_of jenv)) jenv
fun with_ret t jenv = put_vtype "java:ret" t jenv
fun ret_of jenv = the_default TUnknown (Symtab.lookup (vtypes_of jenv) "java:ret")

fun is_poly (e : pos A.jExpr) =
  (case e of
     A.ELambda _ => true | A.EMethodRef _ => true | A.EParen _ => true | A.ECond _ => true
   | A.ESwitch _ => true | A.EArrayInit _ => true | _ => false)

(* A compact wrapper for the antiquotations a node carries (its "nodeInfo"). *)
fun chk jenv ctx ni = check_antiq jenv ctx ni

(* The pattern variables a condition introduces when it is true / false. *)
type binds = (string * ident_kind * ty) list

fun add_binds jenv (bs : binds) = fold (fn (n, k, t) => fn g => put_name_t (vkey n) k t g) bs jenv

(* a name that a pattern introduced leaves the scope again *)
fun remove_binds old jenv (bs : binds) =
  fold (fn (n, _, _) => fn g =>
          let
            val key = vkey n
            fun restore tab_old tab =
              (case Symtab.lookup tab_old key of
                 SOME k => Symtab.update (key, k) tab
               | NONE => Symtab.delete_safe key tab)
          in set_scope (restore (names_of old) (names_of g), meths_of g,
                        restore (vtypes_of old) (vtypes_of g)) g end) bs jenv

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


fun walk_annot senv ctx (A.Annot (name, args, ni)) : acts =
  let
    val here = chk senv ctx ni
    val _ = (case name of id :: _ => use_type_name_or_platform senv id | [] => ())
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
           val _ = (case segs of A.TSeg (id, _) :: _ => use_type_name_or_platform senv id | [] => ())
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
and walk_e senv0 ctx (e : pos A.jExpr) : acts * binds * binds =
  let
    val ex = expect_of senv0
    val senv = clear_expect senv0
    val ctx' = A.Expr e :: ctx
    val here = chk senv ctx' (A.nodeInfo_of_expr e)
    fun plain acts = (here @ acts, [], [])
    fun seq es = maps (fn x => #1 (walk_e senv ctx' x)) es
    (* an expression with the type that the context expects of it *)
    fun walk_ex t x = #1 (walk_e (with_expect t senv) ctx' x)
    fun seq_ex tys es = maps (fn (t, x) => walk_ex t x) (tys ~~ es)
  in
    (case e of
       A.ELit _ => plain []
     | A.EName id => (use_simple_name senv id; plain [])
     | A.EField (e1, id, _) => (link_select senv e1 id; plain (seq [e1]))
     | A.EThis _ => plain []
     | A.ESuper _ => plain []
     | A.EQualThis (e1, _) => plain (seq [e1])
     | A.EQualSuper (e1, _) => plain (seq [e1])
     | A.EParen (e1, _) =>
         let val (a, t, f) = walk_e (with_expect ex senv) ctx' e1 in (here @ a, t, f) end
     | A.EIndex (a, i, _) => plain (seq [a, i])
     | A.ECall (recv, ta, id, args, _) =>
         let
           val ra = (case recv of
                       SOME r => (link_call senv recv id args; seq [r])
                     | NONE =>
                         ((if has_method_named senv (ident_name_of id)
                           then link_call senv NONE id args
                           else use_method senv id (length args));
                          []))
           val aacts = if exists is_poly args
                       then seq_ex (call_expects senv recv id args) args else seq args
         in plain (ra @ optl (walk_targs senv ctx') ta @ aacts) end
     | A.ENew (outer, t, args, body, _) =>
         plain (optl (fn o1 => seq [o1]) outer @ walk_type senv ctx' t
                @ (if exists is_poly args
                   then seq_ex (new_expects senv (ty_of_type senv t) args) args else seq args)
                @ optl (walk_anon senv ctx' (pos_key (A.pos_of_expr e)) (ty_of_type senv t)) body)
     | A.ENewArray (t, des, ds, init, _) =>
         plain (walk_type senv ctx' t @ seq des @ maps (walk_dim senv ctx') ds
                @ optl (fn i => seq [i]) init)
     | A.EArrayInit (es, _, _) =>
         plain (case ex of
                  TArr t => seq_ex (map (K t) es) es
                | _ => seq es)
     | A.EClassLit (t, _) => plain (walk_type senv ctx' t)
     | A.EMethodRef (tg, ta, id, _) =>
         let
           val name = ident_name_of id
           val _ = (case sam_of senv ex of
                      SOME (pts, _) =>
                        (case mref_info senv tg name pts of
                           SOME (SOME p, _) =>
                             if name = "new" then ()
                             else report_use "Java method" name (ident_pos id) p
                         | _ => ())
                    | NONE => ())
         in
           plain ((case tg of A.MRExpr e1 => seq [e1] | A.MRType t => walk_type senv ctx' t)
                  @ optl (walk_targs senv ctx') ta)
         end
     | A.ELambda (ps, _, body, _) =>
         let
           val (pts, rt) = (case sam_of senv ex of SOME (a, r) => (a, r) | NONE => ([], TUnknown))
           val (_, acts) = scoped senv (fn s =>
             let
               val (s1, pacts) = walk_lparams s ctx' ps pts
               val s1r = with_ret rt s1
               val bacts = (case body of
                              A.LBExpr e1 => #1 (walk_e (with_expect rt s1r) ctx' e1)
                            | A.LBBlock b => walk_block s1r ctx' b)
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
     | A.EAssign (l, _, r, _) => plain (seq [l] @ walk_ex (val_ty senv l) r)
     | A.ECond (c, a, b, _) =>
         let
           val (c1, tc, fc) = walk_e senv ctx' c
           val (a1, _, _) = walk_e (with_expect ex (add_binds senv tc)) ctx' a
           val (b1, _, _) = walk_e (with_expect ex (add_binds senv fc)) ctx' b
         in plain (c1 @ a1 @ b1) end
     | A.ECast (ts, e1, _) =>
         plain (maps (walk_type senv ctx') ts
                @ (case ts of t :: _ => walk_ex (ty_of_type senv t) e1 | [] => seq [e1]))
     | A.EInstanceof (e1, p, _) =>
         let
           val (a1, _, _) = walk_e senv ctx' e1
           val (pacts, bs) = walk_pattern senv ctx' p
         in (here @ a1 @ pacts, bs, []) end
     | A.ESwitch (e1, cases, _) => plain (seq [e1] @ walk_cases senv ctx' ex cases))
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
                           in (decl_only Var id; [(name, Var pos, ty_of_type senv t)]) end
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

and walk_cases senv ctx ex cases : acts =
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
                      A.RBExpr e1 => #1 (walk_e (with_expect ex env_l) ctx e1)
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

and walk_lparams senv ctx ps (ptys : ty list) : jenv * acts =
  let val tys = if length ptys = length ps then ptys else map (K TUnknown) ps
  in
    fold (fn (p, t) => fn (s, acc) =>
            (case p of
               A.LPInfer id => (reg_vt Param t s id, acc)
             | A.LPTyped (pr as A.Param (ms, ty, va, id, ds, ni)) =>
                 (case ty of
                    A.TVar _ =>
                      (* "var": the type is the one of the context *)
                      let val (s1, a) = walk_param s ctx pr
                      in ((if is_receiver id then s1 else reg_vt Param t s1 id), acc @ a) end
                  | _ => let val (s1, a) = walk_param s ctx pr in (s1, acc @ a) end)))
      (ps ~~ tys) (senv, [])
  end

and walk_param senv ctx (p as A.Param (ms, t, _, id, ds, ni)) : jenv * acts =
  let
    val acts = chk senv ctx ni @ walk_mods senv ctx ms @ walk_type senv ctx t
               @ maps (walk_dim senv ctx) ds
    val senv' = if is_receiver id then senv else reg_vt Param (param_ty senv p) senv id
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
              val ty = (case t of
                          A.TVar _ => (case init of SOME x => val_ty e x | NONE => TUnknown)
                        | _ => dims_ty (ty_of_type e t) ds)
              val e1 = reg_vt Var ty e id          (* in scope in its own initializer *)
              val a1 = chk e1 ctx vni @ maps (walk_dim e1 ctx) ds
                       @ (case init of
                            SOME x =>
                              #1 (walk_e (with_expect (case t of A.TVar _ => TUnknown | _ => ty) e1)
                                    ctx x)
                          | NONE => [])
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
           val senv1 = reg_with lkey Label TUnknown senv id
           val (e1, a) = walk_stmt senv1 ctx' s1
           val key = lkey (ident_name_of id)
           val tab = (case Symtab.lookup (names_of senv) key of
                        SOME k => Symtab.update (key, k) (names_of e1)
                      | NONE => Symtab.delete_safe key (names_of e1))
         in ret (set_scope (tab, meths_of e1, vtypes_of e1) e1, a) end
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
           val ety = (case t of
                        A.TVar _ => (case val_ty senv e of TArr x => x | _ => TUnknown)
                      | _ => ty_of_type senv t)
           val senv1 = reg_vt Var ety senv id
           val (_, ba) = walk_stmt senv1 ctx' b
         in ret (senv, ea @ a0 @ ba) end
     | A.SBreak (l, _) => (use_label senv l; ret (senv, []))
     | A.SContinue (l, _) => (use_label senv l; ret (senv, []))
     | A.SReturn (e, _) =>
         ret (senv, optl (fn x => #1 (walk_e (with_expect (ret_of senv) senv) ctx' x)) e)
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
                 val s1 = reg_vt Var (case ts of [t] => ty_of_type s t | _ => TUnknown) s id
               in (s1, a0 @ walk_block s1 ctx' cb) end))
           val facts = (case f of SOME fb => walk_block senv ctx' fb | NONE => [])
         in ret (senv, racts @ bacts @ maps catch_acts cs @ facts) end
     | A.SSwitch (e, cases, _) => ret (senv, expr e @ walk_cases senv ctx' TUnknown cases)
     | A.SCtorCall (q, ta, _, args, _) =>
         ret (senv, optl expr q @ optl (walk_targs senv ctx') ta @ maps expr args))
  end

(* a local class: its name is in scope in the class and in the rest of the block *)
and walk_local_class senv ctx d id : jenv * acts =
  let
    val senv1 = register_class (reg_t Typ senv id) d
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

and walk_anon senv ctx key sup members : acts =
  let
    val s0 = register_anon senv key sup members
    val s1 = set_cur (key :: cur_of s0) s0
    val s2 = predeclare_members s1 (TCls (key, [])) members [] []
  in #2 (scoped s2 (fn s => (s, maps (walk_decl s ctx) members))) end

and walk_enum_const senv ctx self (A.EnumConst (al, id, args, body, ni)) : acts =
  chk senv ctx ni @ walk_annots senv ctx al
  @ optl (maps (fn x => #1 (walk_e senv ctx x))) args
  @ optl (walk_anon senv ctx (pos_key (ident_pos id)) self) body

(* a class, an interface, an enum, a record or an annotation interface; its name is entered by
   the caller *)
and walk_class senv ctx (d : pos A.jDecl) : acts =
  let
    val ctx' = A.Decl d :: ctx
    val here = chk senv ctx' (A.nodeInfo_of_decl d)
    val (_, id, mods, tps, supers, permits, consts, comps, body) = the (class_parts d)
    val key = pos_key (ident_pos id)
    val htypes = supers @ permits
    val macts = walk_mods senv ctx' mods
  in
    here @ macts @
    #2 (scoped senv (fn s =>
      let
        val s0 = set_cur (key :: cur_of s) s
        val (s1, tpacts) = declare_tparams s0 ctx' tps
        val hacts = maps (walk_type s1 ctx') htypes
        val self = TCls (key, map (TTv o tparam_key) tps)
        val s2 = predeclare_members s1 self body consts comps
        val compacts =
          maps (fn A.Param (ms, t, _, _, _, pni) =>
                  chk s2 ctx' pni @ walk_mods s2 ctx' ms @ walk_type s2 ctx' t) comps
        val cacts = maps (walk_enum_const s2 ctx' self) consts
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
         fun var_init t (A.VarDecl (_, ds, init, vni)) =
           chk senv ctx' vni @ maps (walk_dim senv ctx') ds
           @ (case init of
                SOME x =>
                  #1 (walk_e (with_expect (dims_ty (ty_of_type senv t) ds) senv) ctx' x)
              | NONE => [])
       in
         here @
         (case d of
            A.DField (ms, t, vds, _) =>
              walk_mods senv ctx' ms @ walk_type senv ctx' t @ maps (var_init t) vds
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
                  val s2r = with_ret (dims_ty (ty_of_type s1 res) ds) s2
                  val a6 = (case body of SOME b => walk_block s2r ctx' b | NONE => [])
                in (s2, a0 @ a1 @ a2 @ a3 @ a4 @ a5 @ a6) end))
          | A.DCtor (ms, tps, id, ps, thr, b, _) =>
              #2 (scoped senv (fn s =>
                let
                  val _ = decl_only Ctor id
                  val a0 = walk_mods s ctx' ms
                  val (s1, a1) = declare_tparams s ctx' tps
                  val (s2, a2) = walk_params s1 ctx' ps
                  val a3 = maps (walk_type s2 ctx') thr
                in (s2, a0 @ a1 @ a2 @ a3 @ walk_block (with_ret TUnknown s2) ctx' b) end))
          | A.DCompact (ms, id, b, _) =>
              (decl_only Ctor id;
               walk_mods senv ctx' ms @ walk_block (with_ret TUnknown senv) ctx' b)
          | A.DInit (_, b, _) => walk_block (with_ret TUnknown senv) ctx' b
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
  let
    val senv0 = predeclare_members senv TUnknown decls [] []
    val senv1 = fold (fn d => fn s => register_class s d) decls senv0
  in (senv1, maps (walk_decl senv1 ctx) decls) end

fun analyse_and_eval0 (root : pos A.root) thy =
  let
    val jenv0 = set_src (platform_source thy) (get (Context.Theory thy))
    (* The bottom frame is always the top-level root itself, so "ctx" is never empty. *)
    val ctx0 = [root]
    fun drop acts = (thy, acts)
    fun persist (jenv1, acts) = (Context.theory_map (put jenv1) thy, acts)
  in
    case root of
      A.Id (id as A.Ident (_, _, ni)) =>
        let val here = check_antiq jenv0 ctx0 ni
            val _ = use_simple_name jenv0 id
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
          val pkg_name =
            (case pkg of SOME (_, ids) => space_implode "." (map ident_name_of ids) | NONE => "")
          val jenv1 = fold (fn i => fn s => walk_import s i) imports jenv0
                      |> add_imports pkg_name imports
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
