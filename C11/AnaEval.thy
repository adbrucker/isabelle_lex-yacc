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

theory AnaEval
  imports "CEnv"
begin

section\<open>Analyse and Eval\<close>

text\<open>
  \<open>analyse_and_eval\<close> is a single, purely functional, scoped walk over a parsed
  \<open>root\<close>: \<open>cenv\<close> is threaded through the descent (never \<open>thy\<close> itself, and no
  antiquotation action is ever applied to a theory \<^emph>\<open>during\<close> the walk - every
  \<open>type_antiq_fun\<close> instantiation is simply paired with its \<open>level\<close> and collected
  into the result list, to be run later by whoever calls this). Scoping (\<open>cenv\<close>'s
  \<open>idents\<close> table) is shadow-and-restore: entering a function body, a
  compound-statement block, or a \<open>for\<close>-loop's own declaration clause remembers the
  incoming \<open>idents\<close> table and restores exactly that (not the whole \<open>cenv\<close>, in case
  a later pass starts also touching \<open>types\<close>/\<open>c_antiq\<close> locally) once that scope's
  walk returns - giving ordinary sequential C scoping when folded across a block's
  items.

  A node's own antiquotations are always checked using the \<open>cenv\<close> \<^emph>\<open>inherited on
  entry\<close> to that node, i.e. before that node's own declaration (if it introduces
  one) is registered - matching a comment textually preceding what it is attached
  to.

  Separately from \<open>cenv\<close>, every \<open>walk_*\<close> function also threads a second,
  downward-only parameter \<open>ctx : pos C_Ast.root list\<close> (never empty - reuses the
  existing \<open>Id\<close>/\<open>Expr\<close>/\<open>Stmt\<close>/\<open>Units\<close> sum type, no new AST type needed): the
  \<^emph>\<open>closest surrounding context\<close> a comment attached to the current node should be
  evaluated against, as a genuine stack (not just "whatever the caller happens to
  pass down") so a later pass can navigate it, not only read its top. Construction:
  \<^item> \<open>walk_expr\<close> and \<open>walk_stat\<close> \<^emph>\<open>always\<close> push their own node - \<open>Expr e :: ctx\<close> /
    \<open>Stmt s :: ctx\<close> - before recursing into their own children, at \<^emph>\<open>every\<close> level of
    nesting, not just at "entry points" like an \<open>if\<close>'s condition: a comment on a
    sub-expression three levels deep inside a cast resolves to that sub-expression,
    not to the enclosing statement (confirmed with the user: needed for annotating
    casts specifically, where the closest node is what matters, unlike the coarser
    granularity that would suffice for an ordinary precondition/postcondition/
    invariant attached to a whole statement).
  \<^item> Declarations, declarators, initializers, designators, abstract type-names, and
    parameter lists never push - they thread \<open>ctx\<close> through to their own sub-walks
    unchanged, and use \<open>hd ctx\<close> (whatever expression/statement/unit is currently on
    top) as their own antiquotation root. This is what makes \<^emph>\<open>every\<close> node kind a
    valid antiquotation target: a block-local declaration, a \<open>for\<close>-loop's own
    clause, a function parameter, a cast's abstract type-name - all of these used to
    \<open>error "...not supported..."\<close> if an antiquotation was attached; now they simply
    fall back to their closest enclosing expression/statement/unit.
  \<^item> File-scope declarations, function definitions (their own header only - see
    below), \<open>#define\<close>s, and top-level \<open>asm\<close> blocks don't push either, by the same
    rule (they're declaration-like at the top level) - so \<^emph>\<open>every\<close> top-level
    antiquotation shares the one bottom \<open>Units us\<close> frame \<open>analyse_and_eval\<close> seeds
    \<open>ctx\<close> with. This is a deliberate change from an earlier version of this pass,
    which re-wrapped each top-level declaration as its own one-element
    \<open>Units [CTranslUnit ([ed], ni)]\<close>: a comment on global declaration \<open>#3\<close> among
    several now evaluates against the \<^emph>\<open>whole\<close> original translation unit, not just
    the one declaration it happens to sit on - matching "the AST the comment refers
    to" being always well-defined, at the coarsest, most-useful-by-default
    granularity for top-level context.
  \<^item> A function definition's own header (specs/declarator/parameters) doesn't push;
    only once \<open>walk_fun_def\<close> calls \<open>walk_stat\<close> on the function's \<^emph>\<open>body\<close> does that
    call push \<open>Stmt body\<close>, after which the body's own nested statements/expressions
    get progressively deeper frames exactly like anywhere else.

  Every physical antiquotation is now dispatched \<^emph>\<open>exactly once\<close>, regardless of how
  many AST nodes reachable from the walk happen to share its leftmost source
  position (the classic case: \<open>expression_statement: expression SEMI\<close>, whose own
  \<open>nodeInfo\<close> and its wrapped expression's \<open>nodeInfo\<close> start at the same token - but
  also, less obviously, ordinary leaf grammar rules that build a \<open>nodeInfo\<close> this
  walk never otherwise inspects, e.g. \<open>type_specifier\<close>'s \<open>INT (CIntType (ndi
  INTleft))\<close>, sharing a declaration's own leftmost position). \<^verbatim>\<open>C11_Comments.claim\<close>
  in \<^verbatim>\<open>C11_Parser.thy\<close> stays non-destructive - a genuinely destructive claim was
  tried and reverted, since it let exactly that kind of never-walked leaf node
  silently steal and lose a comment before the real, walked node (the
  \<open>CDecl\<close>) ever saw it. Instead, \<open>check_antiq\<close> itself tracks which physical
  antiquotation \<^emph>\<open>values\<close> it has already dispatched during the current
  \<open>analyse_and_eval\<close> call (\<^verbatim>\<open>Dispatched_Antiqs\<close>, reset once per call) and skips a
  repeat - since every \<open>walk_*\<close> checks its own antiquotations \<^emph>\<open>before\<close> recursing
  into children, whichever of several nodes genuinely tied at one position the
  walk reaches first (always the outermost of them) is the one that wins.

  Every identifier \<^emph>\<open>use\<close> (currently: a variable/function name in \<open>CVar\<close>, plus the
  bare \<open>Id\<close> root itself) is hyperlinked to its declaration via
  \<^ML>\<open>Position.entity_markup\<close> (Isabelle/Pure's standard def/ref markup - the
  declaration's own position is baked directly into the markup, so no
  serial-number correlation table is needed) and \<^ML>\<open>Position.report\<close>, reported
  once at the declaration site (self-referential) and once at every use. A use
  whose name resolves nowhere in \<open>cenv\<close> is reported with \<^ML>\<open>Markup.bad ()\<close>
  instead (a highlight/underline, not a hyperlink) - deliberately not an
  \<open>error\<close>, since this fragment has no cross-file symbol table and "undeclared
  here" routinely just means "declared somewhere this parse never saw".

  The two preprocessor-macro forms this fragment recognizes (\<open>#define name =
  expr\<close> and \<open>#define name(a, \<dots>) = expr\<close>, see \<open>cPreprocDirective\<close> in
  \<^verbatim>\<open>c_ast.ML\<close>) register into \<open>cenv\<close> exactly like an ordinary declaration -
  \<open>Cpp_const\<close>/\<open>Cpp_macro\<close> wrap a \<^emph>\<open>synthetic\<close> \<open>cDeclaration\<close> (the macro's own
  name as its declarator, its replacement expression as a pseudo-initializer),
  purely so \<open>find_decl_pos\<close>/\<open>report_use\<close> need no macro-specific case: a later
  \<open>CVar\<close>/\<open>CCall\<close> reference to the macro's name hyperlinks to its \<open>#define\<close> the
  same way a reference to an ordinary global does - this fragment never expands
  macros, so such a reference is, syntactically, just another use of that name
  in the same flat namespace. A function-like macro's parameter list is its own
  shadow-and-restored scope, exactly like a function's, so a parameter's own
  name inside the replacement expression resolves to the parameter, not to an
  enclosing global of the same name; \<open>Cpp_macro\<close> keeps that parameter list
  alongside the synthetic declaration. \<open>#define\<close> only ever occurs directly in
  a \<open>cExternalDeclaration list\<close> (the grammar has no block-item form for it), so
  \<open>#ifdef\<close>/\<open>#ifndef\<close> branches are walked the same way a translation unit's own
  external-declaration list is - and the tested name itself (the \<open>MAX_SIZE\<close> in
  \<open>#ifdef MAX_SIZE\<close>) is a genuine \<^emph>\<open>use\<close> of it too, checked against \<open>cenv\<close> via
  \<open>report_use\<close> exactly like any other reference, not merely a branch condition
  to recurse past.

  A struct/union/enum \<^emph>\<open>tag\<close> (\<open>struct point\<close>, \<open>enum Color\<close>) is registered into
  \<open>cenv\<close>'s \<open>types\<close> table - the C11 tag namespace, shared by all three and kept
  separate from \<open>idents\<close> - wherever a \<open>cDeclarationSpecifier list\<close> is walked
  (\<open>walk_decl_specs\<close>, called from both \<open>walk_decl\<close> and \<open>walk_fun_def\<close>): a
  defining occurrence (one that carries a member/constant list) registers the
  tag, a bare mention hyperlinks back to it. An enum's own constants are
  \<^emph>\<open>not\<close> a per-type member namespace in real C - they live in the ordinary
  \<open>idents\<close> table right alongside variables and functions (\<open>Enum\<close>), exactly
  like any other declared name. A struct/union member (\<open>pt.x\<close>, \<open>pp->y\<close>) is
  resolved only for the common case - a bare variable as the base expression
  (\<open>report_member_use\<close>, called from \<open>walk_expr\<close>'s \<open>CMember\<close> case): the base
  variable's own stored declaration is re-scanned for a struct/union tag
  among its declaration-specifiers (a \<^emph>\<open>direct\<close> \<open>struct point pt;\<close>-style
  specifier only - a \<open>typedef\<close>'d struct name is not chased, since typedef
  names are not tracked at all yet), that tag's registered member list is
  searched for the field name, and the result is hyperlinked exactly like an
  ordinary use - or left as \<^ML>\<open>Markup.bad ()\<close>, not an \<open>error\<close>, at any step
  that cannot be resolved (an anonymous struct, a non-variable base
  expression such as \<open>f().x\<close>, a member genuinely undeclared), matching
  \<open>report_use\<close>'s own philosophy: unresolved is routine here, not fatal. A
  K&R old-style parameter list still registers each name as \<open>Local\<close> straight
  from the bare identifier, without cross-referencing the trailing old-style
  declaration list for its real type. \<open>analyse_and_eval\<close> itself is not yet
  wired into \<open>run_c11_kind\<close>/\<open>c11\<close>.
\<close>
ML\<open>
structure AnaEval = struct

open CEnv

fun idents_of (mk {idents, ...} : cenv) = idents

fun set_idents idents' (mk {idents = _, types, c_antiq, predefined_envs, units}) =
  mk {idents = idents', types = types, c_antiq = c_antiq,
      predefined_envs = predefined_envs, units = units}

(* The position a "root" itself spans - the same position a "type_antiq_fun"
   sees as its own "current term" (see "check_antiq" below), so a handler
   wanting to report/highlight "where this term is" can get at it without
   re-deriving the "Id"/"Expr"/"Stmt"/"Units" case split itself. A "Units" of
   more than one "cTranslationUnit" (never produced by this grammar - see
   "start_rule" in C11_Parser.thy, which always wraps a whole parse into
   exactly one) or of none at all has no single span to report, so falls back
   to "Position.none" rather than guessing at one of several/none. *)
fun pos_of_root (C_Ast.Id (C_Ast.Ident (_, _, ni))) = C_Ast.pos_of_NodeInfo ni
  | pos_of_root (C_Ast.Expr e) = C_Ast.pos_of_CExpr e
  | pos_of_root (C_Ast.Stmt s) = C_Ast.pos_of_CStat s
  | pos_of_root (C_Ast.Units [C_Ast.CTranslUnit (_, ni)]) = C_Ast.pos_of_NodeInfo ni
  | pos_of_root (C_Ast.Units _) = Position.none

(* A declarator's own declared name and position, "NONE" for an abstract
   (unnamed) declarator - e.g. inside a "type_name" used by a cast/sizeof. *)
fun decl_name_pos (C_Ast.CDeclr (SOME (C_Ast.Ident (name, _, ni)), _, _, _, _)) =
      SOME (name, C_Ast.pos_of_NodeInfo ni)
  | decl_name_pos (C_Ast.CDeclr (NONE, _, _, _, _)) = NONE

(* Re-scans a stored declaration's declarator list for one specific name's own
   declared position - needed because "ident_kind" stores the whole
   "cDeclaration" (a single "CDecl" can name several identifiers at once, e.g.
   "int x, y;"), not a per-name position. *)
fun find_decl_pos (C_Ast.CDecl (_, entries, _)) name =
      let
        fun go [] = NONE
          | go (((declr_opt, _), _) :: rest) =
              (case declr_opt of
                 NONE => go rest
               | SOME declr =>
                   (case decl_name_pos declr of
                      SOME (n, p) => if n = name then SOME p else go rest
                    | NONE => go rest))
      in go entries end
  | find_decl_pos (C_Ast.CStaticAssert _) _ = NONE

(* "C11_Comments.claim" is deliberately non-destructive (see its own comment
   in C11_Parser.thy): several nodeInfo's built during parsing can genuinely
   share one leftmost position, including some the walk below never inspects
   for antiquotations at all (leaf grammar rules like "type_specifier"'s
   "INT (CIntType (ndi INTleft))"), so nothing at parse time can safely
   decide once and for all which single node "owns" a given comment. This
   structure enforces "exactly once dispatched" instead, downstream, at the
   one point that actually matters: tracking which physical antiquotation
   *values* "check_antiq" has already dispatched during the current
   "analyse_and_eval" call (reset there - see its own note), and skipping a
   repeat. Comments are built purely from strings/positions/records/lists of
   those, both "eqtype"s, so plain "=" already means "the very same source
   comment", not merely "same text" - a "Synchronized.var", not a functionally
   threaded parameter through every "walk_*" function, exactly like
   "C11_Comments.state" itself and for the same reason (thread-safety across
   Isabelle's parallel checking - see its own comment). *)
structure Dispatched_Antiqs = struct
  val state : Position.T C_Ast.comment list Synchronized.var =
    Synchronized.var "AnaEval.Dispatched_Antiqs.state" []
  fun reset () = Synchronized.change state (fn _ => [])
  fun already_dispatched c = member (op =) (Synchronized.value state) c
  fun mark c = Synchronized.change state (fn cs => c :: cs)
end

(* A navigation step's coarse target category - "Id"/"Expr"/"Stmt"/"Units",
   ignoring the specific constructor within each, purely so "select_ast"
   below can tell whether consecutive "ctx" frames belong to one "run" for
   "Up" to collapse (the user's own examples group frames this coarsely,
   e.g. "[expr, expr, expr, stmt, ...]", never by the exact expression/
   statement shape). *)
fun category (C_Ast.Id _)    = 0
  | category (C_Ast.Expr _)  = 1
  | category (C_Ast.Stmt _)  = 2
  | category (C_Ast.Units _) = 3

(* The length of the maximal prefix of "ctx" (including its own head) sharing
   the head's own category - "ctx" is never empty, so this is always >= 1. *)
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
  | select_u (C_Ast.up :: rest_navi, ctx) =
      if null rest_navi then ([], ctx)
      else (case ctx of
              [_] => select_u (rest_navi, ctx)
            | _ :: rest_ctx => select_u (rest_navi, rest_ctx))
  | select_u (C_Ast.Up :: rest_navi, ctx) =
      let val n = run_length ctx in
        if n > 1 then select_u (rest_navi, List.drop (ctx, n - 1))
        else (case ctx of
                [_] => select_u (C_Ast.up :: rest_navi, ctx)
              | _ :: rest_ctx => select_u (C_Ast.up :: rest_navi, rest_ctx))
      end
  | select_u (navi, ctx) = (navi, ctx) (* first "r"/"d": the "(u|U)*" phase is over *)

(* The ordered, per-node-kind list of children "r"/"d" may navigate into -
   "CIf" (the design discussion's own worked example: "[Expr cond, Stmt then,
   Stmt else?]") generalizes to every other "cStatement"/"cExpression"
   constructor the same way: its own "'a cExpression"/"'a cStatement" sub-
   fields, in declaration order, are its navigable children - an absent
   "option" field contributes no child (matching "CIf"'s own optional
   "else"), a "list" field contributes one child per element, and a field of
   any other type ("'a ident", "'a cDeclaration", a designator, a bool, an
   attribute list - none of which "root" has a variant for) contributes
   none, silently dropped rather than counted as a gap in the index. A
   constructor with no navigable field at all this way (an ordinary leaf
   like "CVar"/"CConst"/"CBreak", but also e.g. "CSizeofType"/
   "CAlignofType", whose only field *is* a type-name) gets the empty list,
   which "select_count_r" turns into a "navigation index ... out of range"
   error the same way an actual leaf does - per the user, "'d' on an element
   that is already a leaf in the AST is also an error", and these are
   observably the same case. "Id" and "Units" are not per-constructor at
   all: the user confirmed both are simply not "r"/"d"-navigable - "the
   toplevel father is Unit, not Unit list" (so there is no per-element
   indexing to define for it in the first place), and an identifier is
   always a leaf. *)
fun children_of_stmt s =
  case s of
    C_Ast.CLabel (_, s1, _, _) => [C_Ast.Stmt s1]
  | C_Ast.CCase (e, s1, _) => [C_Ast.Expr e, C_Ast.Stmt s1]
  | C_Ast.CCases (e1, e2, s1, _) => [C_Ast.Expr e1, C_Ast.Expr e2, C_Ast.Stmt s1]
  | C_Ast.CDefault (s1, _) => [C_Ast.Stmt s1]
  | C_Ast.CExpr (eo, _) => (case eo of NONE => [] | SOME e => [C_Ast.Expr e])
  | C_Ast.CCompound (_, items, _) =>
      (* Only "CBlockStmt" entries are navigable statements; "CBlockDecl"/
         "CNestedFunDef" entries are silently dropped (a declaration has no
         "root" variant), so a compound block's children are its statements
         alone, in order - a block-local declaration is simply not an "r"/
         "d" target, the same way any other declaration is not. *)
      List.mapPartial (fn C_Ast.CBlockStmt s1 => SOME (C_Ast.Stmt s1) | _ => NONE) items
  | C_Ast.CIf (e, s1, s2_opt, _) =>
      C_Ast.Expr e :: C_Ast.Stmt s1 :: (case s2_opt of NONE => [] | SOME s2 => [C_Ast.Stmt s2])
  | C_Ast.CSwitch (e, s1, _) => [C_Ast.Expr e, C_Ast.Stmt s1]
  | C_Ast.CWhile (e, s1, _, _) => [C_Ast.Expr e, C_Ast.Stmt s1]
  | C_Ast.CFor (init, cond_opt, step_opt, body, _) =>
      (case init of
         C_Ast.Left NONE => []
       | C_Ast.Left (SOME e) => [C_Ast.Expr e]
       | C_Ast.Right _ => [] (* a declaration-form init has no "root" variant *)) @
      (case cond_opt of NONE => [] | SOME e => [C_Ast.Expr e]) @
      (case step_opt of NONE => [] | SOME e => [C_Ast.Expr e]) @
      [C_Ast.Stmt body]
  | C_Ast.CGoto (_, _) => []
  | C_Ast.CGotoPtr (e, _) => [C_Ast.Expr e]
  | C_Ast.CCont _ => []
  | C_Ast.CBreak _ => []
  | C_Ast.CReturn (eo, _) => (case eo of NONE => [] | SOME e => [C_Ast.Expr e])
  | C_Ast.CAsm (_, _) => [] (* inline asm operands: out of scope, as elsewhere in this pass *)

fun children_of_expr e =
  case e of
    C_Ast.CComma (es, _) => map C_Ast.Expr es
  | C_Ast.CAssign (_, e1, e2, _) => [C_Ast.Expr e1, C_Ast.Expr e2]
  | C_Ast.CCond (e1, e2_opt, e3, _) =>
      C_Ast.Expr e1 :: (case e2_opt of NONE => [] | SOME e2 => [C_Ast.Expr e2]) @ [C_Ast.Expr e3]
  | C_Ast.CBinary (_, e1, e2, _) => [C_Ast.Expr e1, C_Ast.Expr e2]
  | C_Ast.CCast (_, e1, _) => [C_Ast.Expr e1] (* the type-name is dropped, no "root" variant *)
  | C_Ast.CUnary (_, e1, _) => [C_Ast.Expr e1]
  | C_Ast.CSizeofExpr (e1, _) => [C_Ast.Expr e1]
  | C_Ast.CSizeofType (_, _) => [] (* the only field is a type-name *)
  | C_Ast.CAlignofExpr (e1, _) => [C_Ast.Expr e1]
  | C_Ast.CAlignofType (_, _) => []
  | C_Ast.CComplexReal (e1, _) => [C_Ast.Expr e1]
  | C_Ast.CComplexImag (e1, _) => [C_Ast.Expr e1]
  | C_Ast.CIndex (e1, e2, _) => [C_Ast.Expr e1, C_Ast.Expr e2]
  | C_Ast.CCall (ef, args, _) => C_Ast.Expr ef :: map C_Ast.Expr args
  | C_Ast.CMember (e1, _, _, _) => [C_Ast.Expr e1]
  | C_Ast.CVar (_, _) => []
  | C_Ast.CConst _ => []
  | C_Ast.CCompoundLit (_, _, _) =>
      [] (* designators/initializers have no "root" variant *)
  | C_Ast.CGenericSelection (e1, assocs, _) =>
      C_Ast.Expr e1 :: map (fn (_, e2) => C_Ast.Expr e2) assocs
  | C_Ast.CStatExpr (s, _) => [C_Ast.Stmt s]
  | C_Ast.CLabAddrExpr (_, _) => []
  | C_Ast.CBuiltinExpr b =>
      (case b of
         C_Ast.CBuiltinVaArg (e1, _, _) => [C_Ast.Expr e1]
       | C_Ast.CBuiltinOffsetOf (_, _, _) => []
       | C_Ast.CBuiltinTypesCompatible (_, _, _) => [])

fun children_of _ (C_Ast.Stmt s) = children_of_stmt s
  | children_of _ (C_Ast.Expr e) = children_of_expr e
  | children_of antiq_pos (C_Ast.Id _) =
      error ("select_ast: an identifier is a leaf, no \"r\"/\"d\" children" ^ Position.here antiq_pos)
  | children_of antiq_pos (C_Ast.Units _) =
      error ("select_ast: a translation unit is not \"r\"/\"d\"-navigable" ^ Position.here antiq_pos)

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
   "C_Ast.navi") carries no source position of its own, and "node" can by
   now be arbitrarily far from where the user actually wrote the mistaken
   "[navi]" bracket - "antiq_pos" is the closest thing available to "where
   the string was written", and is what a user actually needs to jump to. *)
fun select_rd (antiq_pos, [], node) = node
  | select_rd (antiq_pos, navi as C_Ast.down :: _, node) = select_count_r (antiq_pos, 1, navi, node)
  | select_rd (antiq_pos, C_Ast.right :: rest, node) = select_count_r (antiq_pos, 1, rest, node)
  | select_rd (antiq_pos, C_Ast.up :: _, _) =
      error ("select_ast: \"u\" after \"r\"/\"d\"" ^ Position.here antiq_pos)
  | select_rd (antiq_pos, C_Ast.Up :: _, _) =
      error ("select_ast: \"U\" after \"r\"/\"d\"" ^ Position.here antiq_pos)
and select_count_r (antiq_pos, n, C_Ast.right :: rest, node) = select_count_r (antiq_pos, n + 1, rest, node)
  | select_count_r (antiq_pos, n, C_Ast.down :: rest, node) =
      let val cs = children_of antiq_pos node in
        if n > length cs then
          error ("select_ast: navigation index " ^ Int.toString n ^ " out of range (only " ^
                 Int.toString (length cs) ^ " navigable children here)" ^ Position.here antiq_pos)
        else select_rd (antiq_pos, rest, List.nth (cs, n - 1))
      end
  | select_count_r (antiq_pos, _, C_Ast.up :: _, _) =
      error ("select_ast: \"u\" after \"r\"" ^ Position.here antiq_pos)
  | select_count_r (antiq_pos, _, C_Ast.Up :: _, _) =
      error ("select_ast: \"U\" after \"r\"" ^ Position.here antiq_pos)
  | select_count_r (antiq_pos, _, [], _) =
      error ("select_ast: navigation string ends with a dangling \"r\", expected a final \"d\"" ^
             Position.here antiq_pos)

(* Maps an antiquotation's own "navi list" (the "@tag[navi] ..." bracket -
   see "C_Ast.navi") together with the closest-surrounding-context stack to
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
   "ni"'s comment list by tag in "cenv"'s "c_antiq", instantiates it with
   (cenv, select_ast tag_pos navi ctx, level), and pairs the resulting
   "theory -> theory" with its level - "select_ast" (and so "children_of",
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
   "type_antiq_fun" in CEnv.thy for why the cartouche's own position now
   travels all the way to the handler instead of being discarded here - and
   the *resolved* AST node ("select_ast tag_pos navi ctx"), not the raw navi
   list: a handler is never itself responsible for interpreting "up"/"Up"/
   "right"/"down". *)
fun check_antiq cenv (ctx : pos C_Ast.root list) (ni : pos C_Ast.nodeInfo)
    : (int * (theory -> theory)) list =
  case ni of
    C_Ast.OnlyPos _ => []
  | C_Ast.NodeInfo (cs, _) =>
      List.mapPartial
        (fn c as C_Ast.Antiquotation ({tag = (tag, tag_pos)}, navi, {level}, {cartouche = (body, body_pos)}) =>
              if Dispatched_Antiqs.already_dispatched c then NONE
              else
                let val mk {c_antiq, ...} = cenv in
                  case Symtab.lookup c_antiq tag of
                    NONE =>
                      error ("analyse_and_eval: no antiquotation handler registered for tag " ^
                             quote tag)
                  | SOME antiq_fun =>
                      (Dispatched_Antiqs.mark c;
                       SOME (level, antiq_fun (cenv, select_ast tag_pos navi ctx, level) (body, body_pos)))
                end
          | C_Ast.Raw_txt _ => NONE)
        cs

(* The full-token range a name spans, starting at "pos" - "pos" alone (a bare
   point, as every identifier's own "nodeInfo" carries: see "ndi" in
   C11_Parser.thy, which uses the same position for both its "claimed_at" and
   its "report_pos") makes an entity-markup report only "claim" a single
   character's worth of clickable/linked region - indistinguishable from the
   whole token for a one-character name, but visibly wrong for any longer
   one (only the token's first character then links/underlines/jumps).
   "Position.symbol_explode" advances "pos" through "name"'s own symbols to
   its end; "Position.range"/"range_position" combine start and end into the
   one merged position value "Position.report"/"Position.entity_markup" need. *)
fun name_range (name, pos) =
  Position.range_position (Position.range (pos, Position.symbol_explode name pos))

fun report_decl kind name decl_pos =
  let val range_pos = name_range (name, decl_pos)
  in Position.report range_pos (Position.entity_markup kind (name, range_pos)) end

(* Looks "name" up in "cenv"'s "idents" and, if found (and of a kind that
   currently carries a declaration position - see the "Enum" note above),
   hyperlinks "use_pos" back to its declaration. A macro/constant name is
   looked up exactly like an ordinary identifier: this fragment does not
   expand macros, so a later "CVar"/"CCall" reference to one is still just
   an ordinary use of that name in the same flat namespace.

   A name found nowhere in "idents" - genuinely undeclared, or merely
   declared somewhere this fragment never saw (an external library symbol,
   a header this recognizer does not itself follow) - is reported with
   \<^ML>\<open>Markup.bad ()\<close> instead: a highlight/underline in the IDE, not a
   hyperlink (there is no declaration to jump to) and, deliberately, not an
   \<open>error\<close> - this recognizer has no symbol table spanning multiple files, so
   "undeclared here" is routine, not necessarily a real defect; it should be
   visible, not fatal. *)
fun report_use cenv name use_pos =
  let
    val mk {idents, ...} = cenv
    val use_range = name_range (name, use_pos)
  in
    case Symtab.lookup idents name of
      NONE => Position.report use_range (Markup.bad ())
    | SOME ik =>
        (case (case ik of
                 Global decl => SOME ("C11 global variable", decl)
               | Local decl => SOME ("C11 local variable", decl)
               | Parameter decl => SOME ("C11 parameter", decl)
               | Cpp_const decl => SOME ("C11 preprocessor constant", decl)
               | Cpp_macro (_, decl) => SOME ("C11 preprocessor macro", decl)
               | Enum decl => SOME ("C11 enum constant", decl)) of
           NONE => ()
         | SOME (kind, decl) =>
             (case find_decl_pos decl name of
                NONE => Position.report use_range (Markup.bad ())
              | SOME decl_pos =>
                  Position.report use_range
                    (Position.entity_markup kind (name, name_range (name, decl_pos)))))
  end

(* Registers one declared name into "cenv"'s "idents", reporting its own
   declaration site (self-referential entity markup). *)
fun register kind_str mk_kind cenv (name, decl_pos, decl) =
  let
    val mk {idents, types, c_antiq, predefined_envs, units} = cenv
    val _ = report_decl kind_str name decl_pos
  in mk {idents = Symtab.update (name, mk_kind decl) idents, types = types, c_antiq = c_antiq,
         predefined_envs = predefined_envs, units = units} end

(* Registers a struct/union/enum tag's own defining occurrence into "cenv"'s
   "types" table, reporting its own declaration site - the "types" analogue
   of "register" above, for the separate tag namespace. Unlike "register",
   "ti" is the already-built "CEnv.type_ident" value itself (there is no
   single "raw declaration" shape to build it from generically the way
   "mk_kind decl" does for "idents": "Struct_tag"/"Union_tag" need the member
   list, "Enum_tag" needs nothing beyond the position). *)
fun register_type kind_str (ti : CEnv.type_ident) cenv (name, decl_pos) =
  let
    val mk {idents, types, c_antiq, predefined_envs, units} = cenv
    val _ = report_decl kind_str name decl_pos
  in mk {idents = idents, types = Symtab.update (name, ti) types, c_antiq = c_antiq,
         predefined_envs = predefined_envs, units = units} end

(* Looks "name" up in "cenv"'s "types" and hyperlinks "use_pos" back to its
   declaration - the "types" analogue of "report_use" above. A bare mention
   of a tag with no defining occurrence anywhere this fragment has seen (a
   forward declaration, or a use of a tag declared elsewhere) is reported
   with \<^ML>\<open>Markup.bad ()\<close>, exactly like an unresolved ordinary identifier. *)
fun report_type_use cenv name use_pos =
  let
    val mk {types, ...} = cenv
    val use_range = name_range (name, use_pos)
  in
    case Symtab.lookup types name of
      NONE => Position.report use_range (Markup.bad ())
    | SOME ti =>
        let
          val (kind, decl_pos) =
            case ti of
              CEnv.Struct_tag (pos, _) => ("C11 struct tag", pos)
            | CEnv.Union_tag  (pos, _) => ("C11 union tag", pos)
            | CEnv.Enum_tag   pos      => ("C11 enum tag", pos)
        in
          Position.report use_range (Position.entity_markup kind (name, name_range (name, decl_pos)))
        end
  end

(* The member-declaration list of the struct/union type a "cDeclarationSpecifier
   list" names, if any - used by "report_member_use" to find what a variable
   used as the base of a "CMember" access ("pt.x"/"pp->y") was declared with.
   Only the *first* type-specifying specifier is considered (a well-formed
   declaration has at most one anyway). Three shapes, the third one new (this
   is exactly the "member linking only resolves ... not chased through a
   typedef" gap the C11 manual's Limitations section used to document):
    - "CSUType" with its own inline member list ("struct point { ... } pt;",
      or the same with no tag name at all, "struct { ... } pt;") - the list
      is used directly, no lookup needed, so an anonymous struct/union now
      resolves too (a small, free improvement over the old, tag-only version
      of this function - anonymous struct/union variables used to fall
      through to "NONE"/\<^ML>\<open>Markup.bad ()\<close> here regardless of "typedef").
    - "CSUType" naming a tag with no inline body ("struct point pt;") - the
      list comes from "cenv"'s "types" table, exactly as before.
    - "CTypeDef" (a typedef'd name standing in for the real type, e.g.
      "point_t pt;" for "typedef struct point_s { ... } point_t;") - chased
      by looking the name up in "cenv"'s "idents" (typedef names are
      registered there like any other declared name - see "walk_decl") and
      recursing into *its own* declaration specifiers; this also, for free,
      chases a typedef of a typedef ("typedef point_t point_t2;"), since the
      recursive call is exactly the same function. *)
fun member_decls_of_specs cenv [] = NONE
  | member_decls_of_specs cenv
      (C_Ast.CTypeSpec (C_Ast.CSUType (C_Ast.CStruct (_, ident_opt, decls_opt, _, _), _)) :: _) =
      (case decls_opt of
         SOME decls => SOME decls
       | NONE =>
           (case ident_opt of
              NONE => NONE
            | SOME (C_Ast.Ident (name, _, _)) =>
                let val mk {types, ...} = cenv in
                  case Symtab.lookup types name of
                    SOME (CEnv.Struct_tag (_, decls)) => SOME decls
                  | SOME (CEnv.Union_tag (_, decls)) => SOME decls
                  | _ => NONE
                end))
  | member_decls_of_specs cenv (C_Ast.CTypeSpec (C_Ast.CTypeDef (C_Ast.Ident (name, _, _), _)) :: _) =
      let val mk {idents, ...} = cenv in
        case Symtab.lookup idents name of
          SOME (Global (C_Ast.CDecl (specs', _, _))) => member_decls_of_specs cenv specs'
        | SOME (Local (C_Ast.CDecl (specs', _, _))) => member_decls_of_specs cenv specs'
        | SOME (Parameter (C_Ast.CDecl (specs', _, _))) => member_decls_of_specs cenv specs'
        | _ => NONE
      end
  | member_decls_of_specs cenv (_ :: specs) = member_decls_of_specs cenv specs

(* A struct/union's registered member declaration list has no per-name index
   (see "CEnv.type_ident") - searched linearly here via "find_decl_pos",
   applied to each member "cDeclaration" in turn until "name" is found. *)
fun find_member_pos [] (_ : string) = NONE
  | find_member_pos (d :: ds) name =
      (case find_decl_pos d name of SOME p => SOME p | NONE => find_member_pos ds name)

(* Resolves a "CMember" access ("e1.field"/"e1->field", the "->" vs "."
   distinction is irrelevant here - both name a field of the same underlying
   struct/union type) to the field's own declaration, if possible, and
   hyperlinks "field_pos" to it - the "idents"/"types" analogue of
   "report_use" for the third, per-type C11 member namespace. Only resolves
   the common case, "e1" a bare variable: falls back to \<^ML>\<open>Markup.bad ()\<close>
   (not an \<open>error\<close>, matching "report_use"'s own philosophy) for every other
   base expression shape (a function call, an array index, another member
   access, \<open>\<dots>\<close>) - resolving those in general would need real type
   inference, which this fragment does not have - or a field genuinely not
   among the resolved type's own members. The base variable's type *is*
   chased through any number of "typedef"s via "member_decls_of_specs" (a
   real limitation this fragment used to have here - see its own note). *)
fun report_member_use cenv e1 (field_name, field_pos) =
  let val use_range = name_range (field_name, field_pos) in
    case e1 of
      C_Ast.CVar (C_Ast.Ident (base_name, _, _), _) =>
        let val mk {idents, ...} = cenv in
          case Symtab.lookup idents base_name of
            NONE => Position.report use_range (Markup.bad ())
          | SOME ik =>
              (case (case ik of
                       Global (C_Ast.CDecl (specs, _, _)) => SOME specs
                     | Local  (C_Ast.CDecl (specs, _, _)) => SOME specs
                     | Parameter (C_Ast.CDecl (specs, _, _)) => SOME specs
                     | _ => NONE) of
                 NONE => Position.report use_range (Markup.bad ())
               | SOME specs =>
                   (case member_decls_of_specs cenv specs of
                      NONE => Position.report use_range (Markup.bad ())
                    | SOME decls =>
                        (case find_member_pos decls field_name of
                           NONE => Position.report use_range (Markup.bad ())
                         | SOME decl_pos =>
                             Position.report use_range
                               (Position.entity_markup "C11 struct/union member"
                                 (field_name, name_range (field_name, decl_pos))))))
        end
    | _ => Position.report use_range (Markup.bad ())
  end

fun walk_exprs cenv ctx es acc =
  fold (fn e => fn (cenv, acc) => let val (cenv', acts) = walk_expr cenv ctx e in (cenv', acc @ acts) end)
    es (cenv, acc)

(* Always pushes its own node - "Expr e :: ctx" - before recursing into its own
   children, at every level of nesting (see the top-of-file note on "ctx"): this
   is what makes a sub-expression nested arbitrarily deep its own closest
   antiquotation context, not just the statement/expression a caller first
   descended from. *)
and walk_expr cenv ctx (e : pos C_Ast.cExpression) : cenv * (int * (theory -> theory)) list =
  let
    val ctx' = C_Ast.Expr e :: ctx
    val here = check_antiq cenv ctx' (C_Ast.nodeInfo_of_CExpr e)
  in
    case e of
      C_Ast.CComma (es, _) => walk_exprs cenv ctx' es here
    | C_Ast.CAssign (_, e1, e2, _) => walk_exprs cenv ctx' [e1, e2] here
    | C_Ast.CCond (e1, NONE, e3, _) => walk_exprs cenv ctx' [e1, e3] here
    | C_Ast.CCond (e1, SOME e2, e3, _) => walk_exprs cenv ctx' [e1, e2, e3] here
    | C_Ast.CBinary (_, e1, e2, _) => walk_exprs cenv ctx' [e1, e2] here
    | C_Ast.CCast (d, e1, _) =>
        let val (cenv1, acts1) = walk_type_decl cenv ctx' d in walk_exprs cenv1 ctx' [e1] (here @ acts1) end
    | C_Ast.CUnary (_, e1, _) => walk_exprs cenv ctx' [e1] here
    | C_Ast.CSizeofExpr (e1, _) => walk_exprs cenv ctx' [e1] here
    | C_Ast.CSizeofType (d, _) =>
        let val (cenv1, acts1) = walk_type_decl cenv ctx' d in (cenv1, here @ acts1) end
    | C_Ast.CAlignofExpr (e1, _) => walk_exprs cenv ctx' [e1] here
    | C_Ast.CAlignofType (d, _) =>
        let val (cenv1, acts1) = walk_type_decl cenv ctx' d in (cenv1, here @ acts1) end
    | C_Ast.CComplexReal (e1, _) => walk_exprs cenv ctx' [e1] here
    | C_Ast.CComplexImag (e1, _) => walk_exprs cenv ctx' [e1] here
    | C_Ast.CIndex (e1, e2, _) => walk_exprs cenv ctx' [e1, e2] here
    | C_Ast.CCall (ef, args, _) => walk_exprs cenv ctx' (ef :: args) here
    | C_Ast.CMember (e1, C_Ast.Ident (field_name, _, field_ni), _, _) =>
        let val _ = report_member_use cenv e1 (field_name, C_Ast.pos_of_NodeInfo field_ni)
        in walk_exprs cenv ctx' [e1] here end
    | C_Ast.CVar (C_Ast.Ident (name, _, ident_ni), _) =>
        (report_use cenv name (C_Ast.pos_of_NodeInfo ident_ni); (cenv, here))
    | C_Ast.CConst _ =>
        (* "nodeInfo_of_CExpr (CConst aa) = nodeInfo_of_CConst aa" - "here",
           above, already checked exactly this "nodeInfo" as "Expr e"-
           dispatchable (a constant genuinely is an ordinary expression); a
           second check on the same "nodeInfo" here would dispatch the very
           same "Antiquotation" a second time. *)
        (cenv, here)
    | C_Ast.CCompoundLit (d, inits, _) =>
        let
          val (cenv1, acts1) = walk_type_decl cenv ctx' d
          val (cenv2, acts2) =
            fold (fn (desigs, init) => fn (cenv, acc) =>
                    let
                      val (cenv_a, acts_a) = walk_designators cenv ctx' desigs
                      val (cenv_b, acts_b) = walk_initializer cenv_a ctx' init
                    in (cenv_b, acc @ acts_a @ acts_b) end)
              inits (cenv1, [])
        in (cenv2, here @ acts1 @ acts2) end
    | C_Ast.CGenericSelection (e1, assocs, _) =>
        let
          val (cenv1, acts1) = walk_expr cenv ctx' e1
          val (cenv2, acts2) =
            fold (fn (d_opt, e2) => fn (cenv, acc) =>
                    let
                      val (cenv_a, acts_a) =
                        case d_opt of NONE => (cenv, []) | SOME d => walk_type_decl cenv ctx' d
                      val (cenv_b, acts_b) = walk_expr cenv_a ctx' e2
                    in (cenv_b, acc @ acts_a @ acts_b) end)
              assocs (cenv1, [])
        in (cenv2, here @ acts1 @ acts2) end
    | C_Ast.CStatExpr (s, _) =>
        let val (cenv1, acts1) = walk_stat cenv ctx' s in (cenv1, here @ acts1) end
    | C_Ast.CLabAddrExpr (_, _) => (cenv, here)
    | C_Ast.CBuiltinExpr b =>
        (* "nodeInfo_of_CExpr (CBuiltinExpr aa) = nodeInfo_of_CBuiltin aa" -
           "here" already checked this "nodeInfo" as "Expr e"-dispatchable,
           for the same reason as "CConst" above; only the builtin's own
           nested expressions/type-names/designators still need walking. *)
        let
          val (cenv1, acts1) =
            case b of
              C_Ast.CBuiltinVaArg (e1, d, _) =>
                let
                  val (cenv_a, acts_a) = walk_expr cenv ctx' e1
                  val (cenv_b, acts_b) = walk_type_decl cenv_a ctx' d
                in (cenv_b, acts_a @ acts_b) end
            | C_Ast.CBuiltinOffsetOf (d, desigs, _) =>
                let
                  val (cenv_a, acts_a) = walk_type_decl cenv ctx' d
                  val (cenv_b, acts_b) = walk_designators cenv_a ctx' desigs
                in (cenv_b, acts_a @ acts_b) end
            | C_Ast.CBuiltinTypesCompatible (d1, d2, _) =>
                let
                  val (cenv_a, acts_a) = walk_type_decl cenv ctx' d1
                  val (cenv_b, acts_b) = walk_type_decl cenv_a ctx' d2
                in (cenv_b, acts_a @ acts_b) end
        in (cenv1, here @ acts1) end
  end

(* Designators never push their own frame (not a dispatchable "context" of
   their own, per the top-of-file note) - "ctx" passes through unchanged to
   any sub-expression, which pushes its own frame as usual. *)
and walk_designators cenv ctx ds =
  fold (fn d => fn (cenv, acc) =>
          case d of
            C_Ast.CArrDesig (e, _) =>
              let val (cenv1, acts1) = walk_expr cenv ctx e in (cenv1, acc @ acts1) end
          | C_Ast.CMemberDesig _ => (cenv, acc)
          | C_Ast.CRangeDesig (e1, e2, _) =>
              let
                val (cenv1, acts1) = walk_expr cenv ctx e1
                val (cenv2, acts2) = walk_expr cenv1 ctx e2
              in (cenv2, acc @ acts1 @ acts2) end)
    ds (cenv, [])

(* Initializers never push either - an antiquotation attached directly to an
   initializer (not one of its own sub-expressions, which push as usual) falls
   back to "hd ctx", the closest enclosing expression/statement/unit. *)
and walk_initializer cenv ctx (C_Ast.CInitExpr (e, ni)) =
      let
        val here = check_antiq cenv ctx ni
        val (cenv1, acts1) = walk_expr cenv ctx e
      in (cenv1, here @ acts1) end
  | walk_initializer cenv ctx (C_Ast.CInitList (pairs, ni)) =
      let
        val here = check_antiq cenv ctx ni
      in
        fold (fn (desigs, init) => fn (cenv, acc) =>
                let
                  val (cenv1, acts1) = walk_designators cenv ctx desigs
                  val (cenv2, acts2) = walk_initializer cenv1 ctx init
                in (cenv2, acc @ acts1 @ acts2) end)
          pairs (cenv, here)
      end

(* Declarators never push either, for the same reason; only the
   derived-declarator's own array-size expression (e.g. the "N" in "int
   arr[N]") is descended into - "CPtrDeclr"/"CFunDeclr" carry nothing further
   relevant to scoping/hyperlinking in this pass. *)
and walk_declarator cenv ctx (C_Ast.CDeclr (_, derived, _, _, ni)) =
      let
        val here = check_antiq cenv ctx ni
      in
        fold (fn d => fn (cenv, acc) =>
                let
                  val dni =
                    case d of
                      C_Ast.CPtrDeclr (_, ni) => ni
                    | C_Ast.CArrDeclr (_, _, ni) => ni
                    | C_Ast.CFunDeclr (_, _, ni) => ni
                  val dhere = check_antiq cenv ctx dni
                  val (cenv1, acts1) =
                    case d of
                      C_Ast.CArrDeclr (_, C_Ast.CArrSize (_, e), _) => walk_expr cenv ctx e
                    | _ => (cenv, [])
                in (cenv1, acc @ dhere @ acts1) end)
          derived (cenv, here)
      end

(* Walks a "cDeclarationSpecifier list" (a declaration's/function-definition's
   own leading specs, e.g. "struct point"/"enum Color" in "struct point pt;"
   or "enum Color make_color(void) { ... }") for the three things it can
   introduce: a struct/union/enum *tag* declaration or use (registered into,
   or looked up in, "cenv"'s "types" - the tag namespace, shared by all
   three); for an enum specifically, its own constant list, each registered
   into the ordinary "idents" table exactly like any other declared name
   ("Enum"), since C's enum constants are not a per-type namespace at all;
   and a "typedef"'d name's own *use* as a type ("CTypeDef", e.g. "jmp_buf"
   in "jmp_buf env;") - hyperlinked via the ordinary "report_use" (typedef
   names are registered into "idents" like any other declared name, by
   "walk_decl" - there is no dedicated "ident_kind" for them, so they show up
   with whatever generic kind label their own declaration had, e.g. "C11
   global variable"), *not* chased any further here (chasing a typedef'd
   name back to the real struct/union type it names, for member-access
   resolution, is "member_decls_of_specs"'s own, separate job, used by
   "report_member_use"). An anonymous struct/union/enum ("struct { ... } x;")
   has no tag to register, but an anonymous *enum*'s constants still are
   registered (they are not anonymous themselves, only their enclosing type
   is). Every other specifier ("CVoidType", "CTypeOfExpr", \<open>\<dots>\<close>) is not
   walked - "CTypeOfExpr"/"CTypeOfType"/"CAtomicType"'s own nested
   expression/declaration is left for a later pass, matching this fragment's
   existing, deliberate scope. *)
and walk_decl_specs cenv ctx specs =
  fold (fn spec => fn (cenv, acc) =>
          case spec of
            C_Ast.CTypeSpec (C_Ast.CSUType (C_Ast.CStruct (tag, ident_opt, decls_opt, _, _), _)) =>
              let val kind_str = case tag of C_Ast.CStructTag => "C11 struct tag" | C_Ast.CUnionTag => "C11 union tag"
              in
                case ident_opt of
                  NONE => (cenv, acc)
                | SOME (C_Ast.Ident (name, _, ident_ni)) =>
                    let val pos = C_Ast.pos_of_NodeInfo ident_ni in
                      case decls_opt of
                        SOME decls =>
                          let val ti = case tag of
                                         C_Ast.CStructTag => CEnv.Struct_tag (pos, decls)
                                       | C_Ast.CUnionTag  => CEnv.Union_tag  (pos, decls)
                          in (register_type kind_str ti cenv (name, pos), acc) end
                      | NONE => (report_type_use cenv name pos; (cenv, acc))
                    end
              end
          | C_Ast.CTypeSpec (C_Ast.CEnumType (C_Ast.CEnum (ident_opt, consts_opt, _, _), _)) =>
              let
                val cenv1 =
                  case ident_opt of
                    NONE => cenv
                  | SOME (C_Ast.Ident (name, _, ident_ni)) =>
                      let val pos = C_Ast.pos_of_NodeInfo ident_ni in
                        case consts_opt of
                          SOME _ => register_type "C11 enum tag" (CEnv.Enum_tag pos) cenv (name, pos)
                        | NONE => (report_type_use cenv name pos; cenv)
                      end
              in
                case consts_opt of
                  NONE => (cenv1, acc)
                | SOME consts =>
                    fold (fn (C_Ast.Ident (cname, cn, cni), init_opt) => fn (cenv, acc) =>
                            let
                              val cpos = C_Ast.pos_of_NodeInfo cni
                              val synth_declr = C_Ast.CDeclr (SOME (C_Ast.Ident (cname, cn, cni)), [], NONE, [], cni)
                              val synth = C_Ast.CDecl ([], [((SOME synth_declr, NONE), NONE)], cni)
                              val cenv' = register "C11 enum constant" Enum cenv (cname, cpos, synth)
                              val (cenv'', acts') =
                                case init_opt of NONE => (cenv', []) | SOME e => walk_expr cenv' ctx e
                            in (cenv'', acc @ acts') end)
                      consts (cenv1, acc)
              end
          | C_Ast.CTypeSpec (C_Ast.CTypeDef (C_Ast.Ident (name, _, ident_ni), _)) =>
              (report_use cenv name (C_Ast.pos_of_NodeInfo ident_ni); (cenv, acc))
          | _ => (cenv, acc))
    specs (cenv, [])

(* Shared by every context that names variables: top-level ("Global"), a
   compound-statement block or "for"-loop clause ("Local"), and a function's
   parameter list ("Parameter") - each declared name is registered with
   "kind_str"/"mk_kind" as given by the caller, which is a no-op whenever
   "decl_name_pos" finds no name (an abstract type-name used by a cast/sizeof/
   generic-selection/compound-literal/"_Alignas" - see "walk_type_decl").
   Declarations never push their own "ctx" frame (top-level or not - see the
   top-of-file note): every caller just passes its own inherited "ctx"
   unchanged, and "hd ctx" (whatever expression/statement/unit is currently
   on top) is used as this declaration's own antiquotation root - no more
   "error" for a nested
   declaration (a block-local one, a "for"-loop's own clause, a parameter,
   an abstract type-name): every one of those now simply resolves to its
   closest enclosing context instead of failing outright. Also walks the
   declaration's own leading "cDeclarationSpecifier list" ("walk_decl_specs")
   for any struct/union/enum tag (and, for an enum, its constants) it
   introduces or mentions - covering both an ordinary declaration and, via
   "walk_type_decl", an abstract type-name (so "sizeof(struct point)" also
   registers/links "point"). *)
and walk_decl kind_str mk_kind cenv ctx (cdecl as C_Ast.CDecl (specs, entries, ni)) =
      let
        val here = check_antiq cenv ctx ni
        val (cenv0, specs_acts) = walk_decl_specs cenv ctx specs
        val (cenv1, acts1) =
          fold (fn ((declr_opt, init_opt), width_opt) => fn (cenv, acc) =>
                  let
                    val (cenv_a, acts_a) =
                      case declr_opt of NONE => (cenv, []) | SOME declr => walk_declarator cenv ctx declr
                    val (cenv_b, acts_b) =
                      case init_opt of NONE => (cenv_a, []) | SOME init => walk_initializer cenv_a ctx init
                    val (cenv_c, acts_c) =
                      case width_opt of NONE => (cenv_b, []) | SOME e => walk_expr cenv_b ctx e
                    val cenv_d =
                      case declr_opt of
                        NONE => cenv_c
                      | SOME declr =>
                          (case decl_name_pos declr of
                             NONE => cenv_c
                           | SOME (name, pos) => register kind_str mk_kind cenv_c (name, pos, cdecl))
                  in (cenv_d, acc @ acts_a @ acts_b @ acts_c) end)
            entries (cenv0, here @ specs_acts)
      in (cenv1, acts1) end
  | walk_decl _ _ cenv ctx (C_Ast.CStaticAssert (e, _, ni)) =
      let
        val here = check_antiq cenv ctx ni
        val (cenv1, acts1) = walk_expr cenv ctx e
      in (cenv1, here @ acts1) end

(* An abstract type-name (cast/sizeof/alignof/generic-selection/compound-literal
   target type): walked the same way as an ordinary declaration for
   antiquotation-checking and nested-expression purposes, but its declarator (if
   any) is always unnamed, so "walk_decl" registers nothing; never itself a
   dispatchable "root" (it is not a complete declaration) - resolves to "hd ctx"
   like every other declaration. *)
and walk_type_decl cenv ctx d = walk_decl "C11 type" Local cenv ctx d

(* Always pushes its own node - "Stmt s :: ctx" - before recursing, exactly
   like "walk_expr" and for the same reason. *)
and walk_stat cenv ctx (s : pos C_Ast.cStatement) : cenv * (int * (theory -> theory)) list =
  let
    val ctx' = C_Ast.Stmt s :: ctx
    val here = check_antiq cenv ctx' (C_Ast.nodeInfo_of_CStat s)
  in
    case s of
      C_Ast.CLabel (_, s1, _, _) =>
        let val (cenv1, acts1) = walk_stat cenv ctx' s1 in (cenv1, here @ acts1) end
    | C_Ast.CCase (e, s1, _) =>
        let
          val (cenv1, acts1) = walk_expr cenv ctx' e
          val (cenv2, acts2) = walk_stat cenv1 ctx' s1
        in (cenv2, here @ acts1 @ acts2) end
    | C_Ast.CCases (e1, e2, s1, _) =>
        let
          val (cenv1, acts1) = walk_expr cenv ctx' e1
          val (cenv2, acts2) = walk_expr cenv1 ctx' e2
          val (cenv3, acts3) = walk_stat cenv2 ctx' s1
        in (cenv3, here @ acts1 @ acts2 @ acts3) end
    | C_Ast.CDefault (s1, _) =>
        let val (cenv1, acts1) = walk_stat cenv ctx' s1 in (cenv1, here @ acts1) end
    | C_Ast.CExpr (NONE, _) => (cenv, here)
    | C_Ast.CExpr (SOME e, _) =>
        let val (cenv1, acts1) = walk_expr cenv ctx' e in (cenv1, here @ acts1) end
    | C_Ast.CCompound (_, items, _) =>
        let
          val outer = idents_of cenv
          val (cenv1, acts1) = walk_block_items cenv ctx' items
        in (set_idents outer cenv1, here @ acts1) end
    | C_Ast.CIf (e, s1, s2_opt, _) =>
        let
          val (cenv1, acts1) = walk_expr cenv ctx' e
          val (cenv2, acts2) = walk_stat cenv1 ctx' s1
          val (cenv3, acts3) = case s2_opt of NONE => (cenv2, []) | SOME s2 => walk_stat cenv2 ctx' s2
        in (cenv3, here @ acts1 @ acts2 @ acts3) end
    | C_Ast.CSwitch (e, s1, _) =>
        let
          val (cenv1, acts1) = walk_expr cenv ctx' e
          val (cenv2, acts2) = walk_stat cenv1 ctx' s1
        in (cenv2, here @ acts1 @ acts2) end
    | C_Ast.CWhile (e, s1, _, _) =>
        let
          val (cenv1, acts1) = walk_expr cenv ctx' e
          val (cenv2, acts2) = walk_stat cenv1 ctx' s1
        in (cenv2, here @ acts1 @ acts2) end
    | C_Ast.CFor (init, cond_opt, step_opt, body, _) =>
        let
          val outer = idents_of cenv
          val (cenv1, acts1) =
            case init of
              C_Ast.Left NONE => (cenv, [])
            | C_Ast.Left (SOME e) => walk_expr cenv ctx' e
            | C_Ast.Right d => walk_decl "C11 local variable" Local cenv ctx' d
          val (cenv2, acts2) = case cond_opt of NONE => (cenv1, []) | SOME e => walk_expr cenv1 ctx' e
          val (cenv3, acts3) = case step_opt of NONE => (cenv2, []) | SOME e => walk_expr cenv2 ctx' e
          val (cenv4, acts4) = walk_stat cenv3 ctx' body
        in (set_idents outer cenv4, here @ acts1 @ acts2 @ acts3 @ acts4) end
    | C_Ast.CGoto (_, _) => (cenv, here)
    | C_Ast.CGotoPtr (e, _) =>
        let val (cenv1, acts1) = walk_expr cenv ctx' e in (cenv1, here @ acts1) end
    | C_Ast.CCont _ => (cenv, here)
    | C_Ast.CBreak _ => (cenv, here)
    | C_Ast.CReturn (NONE, _) => (cenv, here)
    | C_Ast.CReturn (SOME e, _) =>
        let val (cenv1, acts1) = walk_expr cenv ctx' e in (cenv1, here @ acts1) end
    | C_Ast.CAsm (_, _) => (cenv, here) (* inline asm operands: out of scope for this pass *)
  end

and walk_block_items cenv ctx items =
  fold (fn item => fn (cenv, acc) =>
          let
            val (cenv', acts) =
              case item of
                C_Ast.CBlockStmt s => walk_stat cenv ctx s
              | C_Ast.CBlockDecl d => walk_decl "C11 local variable" Local cenv ctx d
              | C_Ast.CNestedFunDef f => walk_fun_def "C11 local function" Local cenv ctx f
          in (cenv', acc @ acts) end)
    items (cenv, [])

(* The "CFunDeclr" among a declarator's derived-declarator list that carries the
   function's parameter list - the first one found, which is the only one that
   occurs for an ordinary (non declarator-inversion) function declarator. *)
and params_of_declarator (C_Ast.CDeclr (_, derived, _, _, _)) =
  List.find (fn C_Ast.CFunDeclr _ => true | _ => false) derived

and open_param_scope cenv ctx declr =
  case params_of_declarator declr of
    NONE => (cenv, [])
  | SOME (C_Ast.CFunDeclr (C_Ast.Left idents, _, _)) =>
      fold (fn C_Ast.Ident (name, n, ni) => fn (cenv, acc) =>
              let
                val pos = C_Ast.pos_of_NodeInfo ni
                val synth_declr = C_Ast.CDeclr (SOME (C_Ast.Ident (name, n, ni)), [], NONE, [], ni)
                val synth = C_Ast.CDecl ([], [((SOME synth_declr, NONE), NONE)], ni)
                val cenv' = register "C11 parameter" Local cenv (name, pos, synth)
              in (cenv', acc) end)
        idents (cenv, [])
  | SOME (C_Ast.CFunDeclr (C_Ast.Right (params, _), _, _)) =>
      fold (fn p => fn (cenv, acc) =>
              let
                val (cenv', acts) = walk_decl "C11 parameter" Local cenv ctx p
              in (cenv', acc @ acts) end)
        params (cenv, [])
  | SOME _ => (cenv, []) (* unreachable: "params_of_declarator" only ever finds a "CFunDeclr" *)

(* A function definition's own header (specs/declarator/parameters) never
   pushes a "ctx" frame - it resolves to "hd ctx" exactly like any other
   declaration (top-level or nested, "walk_ext_decl"/"walk_block_items" both
   just pass their own inherited "ctx" through unchanged). Only once the
   function's *body* is walked (via "walk_stat") does that call push its own
   "Stmt body" frame, after which the body's own nested statements/
   expressions get progressively deeper frames as usual. *)
and walk_fun_def kind_str mk_kind cenv ctx (C_Ast.CFunDef (specs, declr, _, body, ni)) =
      let
        val here = check_antiq cenv ctx ni
        val (cenv0, specs_acts) = walk_decl_specs cenv ctx specs
        val synthetic_decl = C_Ast.CDecl (specs, [((SOME declr, NONE), NONE)], ni)
        val cenv1 =
          case decl_name_pos declr of
            NONE => cenv0
          | SOME (name, pos) => register kind_str mk_kind cenv0 (name, pos, synthetic_decl)
        val outer = idents_of cenv1
        val (cenv_params, param_acts) = open_param_scope cenv1 ctx declr
        val (cenv_body, body_acts) = walk_stat cenv_params ctx body
      in (set_idents outer cenv_body, here @ specs_acts @ param_acts @ body_acts) end

(* Every branch here runs in a top-level (translation-unit) context. Unlike an
   earlier version of this pass, a top-level declaration/function-definition/
   "asm" block no longer gets its own private re-wrapped "Units [CTranslUnit
   ([ed], ...)]" root - like a nested declaration, it simply doesn't push its
   own "ctx" frame, so it resolves to "hd ctx": the one, whole, original
   translation unit "analyse_and_eval" seeded "ctx" with (see the top-of-file
   note) - shared by every top-level declaration in the unit, not just the
   one an antiquotation happens to sit on. *)
and walk_ext_decl cenv ctx (ed : pos C_Ast.cExternalDeclaration) : cenv * (int * (theory -> theory)) list =
  case ed of
    C_Ast.CDeclExt d => walk_decl "C11 global variable" Global cenv ctx d
  | C_Ast.CFDefExt f => walk_fun_def "C11 global function" Global cenv ctx f
  | C_Ast.CAsmExt (_, ni) =>
      let val here = check_antiq cenv ctx ni
      in (cenv, here) end
  | C_Ast.CPPExt d => walk_pp_directive cenv ctx d

(* Wraps an ident (a macro's own name, or one of a function-like macro's
   parameters) as a one-name, otherwise-empty "cDeclaration" - purely so
   "find_decl_pos"/"register" have the same shape to work with as every
   other "ident_kind" payload, without needing a macro-specific case. *)
and synth_decl_of_ident (id as C_Ast.Ident (_, _, ni)) init_opt =
  let val declr = C_Ast.CDeclr (SOME id, [], NONE, [], ni)
  in C_Ast.CDecl ([], [((SOME declr, init_opt), NONE)], ni) end

(* A preprocessor directive only ever occurs directly in a
   "cExternalDeclaration list" - i.e. this function always runs in a
   top-level context, same as "walk_ext_decl": no "ctx" push, resolves to
   "hd ctx"; computed once and reused for all four forms below, since they
   share the one "nodeInfo". *)
and walk_pp_directive cenv ctx (d : pos C_Ast.cPreprocDirective) : cenv * (int * (theory -> theory)) list =
  let
    val ni = C_Ast.nodeInfo_of_CPPDirective d
    val here = check_antiq cenv ctx ni
  in
    case d of
      C_Ast.CPPInclude (_, header, _) =>
        let val mk {predefined_envs, ...} = cenv in
          case Symtab.lookup predefined_envs header of
            NONE => (cenv, here) (* no "c11_predef [header] ..." seen anywhere in scope: still purely syntactic *)
          | SOME effect => (effect cenv, here)
        end
    | C_Ast.CPPDefine (id as C_Ast.Ident (name, _, ident_ni), e, _) =>
        let
          val pos = C_Ast.pos_of_NodeInfo ident_ni
          val (cenv1, acts1) = walk_expr cenv ctx e
          val synth = synth_decl_of_ident id (SOME (C_Ast.CInitExpr (e, C_Ast.nodeInfo_of_CExpr e)))
          val cenv2 = register "C11 preprocessor constant" Cpp_const cenv1 (name, pos, synth)
        in (cenv2, here @ acts1) end
    | C_Ast.CPPDefineFun (id as C_Ast.Ident (name, _, ident_ni), params, e, _) =>
        let
          val pos = C_Ast.pos_of_NodeInfo ident_ni
          (* A function-like macro's parameters are a textual-substitution
             namespace of their own, scoped only to the replacement
             expression - shadow/restore "idents" exactly like a function's
             own parameter scope (see "open_param_scope"), so a use of "a"/
             "b" inside the body resolves to the parameter, not to some
             enclosing global of the same name. *)
          val outer = idents_of cenv
          val cenv_params =
            fold (fn pid as C_Ast.Ident (pname, _, pni) => fn cenv =>
                    register "C11 macro parameter" Local cenv
                      (pname, C_Ast.pos_of_NodeInfo pni, synth_decl_of_ident pid NONE))
              params cenv
          val (cenv_body, acts1) = walk_expr cenv_params ctx e
          val cenv_restored = set_idents outer cenv_body
          val synth = synth_decl_of_ident id (SOME (C_Ast.CInitExpr (e, C_Ast.nodeInfo_of_CExpr e)))
          val cenv2 =
            register "C11 preprocessor macro" (fn decl => Cpp_macro (params, decl)) cenv_restored
              (name, pos, synth)
        in (cenv2, here @ acts1) end
    | C_Ast.CPPIfdef (_, C_Ast.Ident (name, _, ident_ni), thn, els, _) =>
        let
          (* "#ifdef name"/"#ifndef name" itself tests whether "name" is
             defined - genuinely a *use* of it (a constant or function-like
             macro, checked against "cenv" as it stands on entry, exactly
             like an ordinary expression use), not just a branch condition
             to skip over. *)
          val _ = report_use cenv name (C_Ast.pos_of_NodeInfo ident_ni)
          val (cenv1, acts1) = walk_ext_decls cenv ctx thn
          val (cenv2, acts2) = walk_ext_decls cenv1 ctx els
        in (cenv2, here @ acts1 @ acts2) end
  end

and walk_ext_decls cenv ctx eds =
  fold (fn ed => fn (cenv, acc) =>
          let val (cenv', acts) = walk_ext_decl cenv ctx ed in (cenv', acc @ acts) end)
    eds (cenv, [])

(* Now DOES "check_antiq" the whole unit's own "ni" too (an earlier version of
   this pass deliberately skipped it, to avoid double-dispatching against the
   first external declaration's nodeInfo, which shares its leftmost position
   by construction - "start_rule"'s "ndi2 (translation_unitleft,
   translation_unitright)" in C11_Parser.thy). That risk is now handled
   uniformly by "Dispatched_Antiqs" (see "check_antiq"'s own note) instead of
   by skipping this call: whichever of the two nodes the walk reaches first -
   here, always this "CTranslUnit" itself, since "walk_ext_decls"/
   "walk_ext_decl" (and so the first external declaration's own check) only
   run afterwards - dispatches the comment, and the first external
   declaration's later, same-position check safely finds it already
   dispatched. Checking here too closes a real edge case the old skip left
   open: a translation unit that is only a comment, with no declarations at
   all, used to lose that comment entirely (nothing else would ever have
   checked its position). Uses "hd ctx" like every other top-level node
   rather than reconstructing "Units [CTranslUnit (eds, ni)]" itself, so it
   resolves to the exact same, single shared root every other top-level
   antiquotation in this unit does. *)
and walk_translation_unit cenv ctx (C_Ast.CTranslUnit (eds, ni)) =
  let
    val here = check_antiq cenv ctx ni
    val (cenv1, acts1) = walk_ext_decls cenv ctx eds
  in (cenv1, here @ acts1) end

fun analyse_and_eval (root : pos C_Ast.root) thy =
  let
    val cenv0 = get (Context.Theory thy)
    (* The context stack's bottom frame is always the top-level "root" itself
       (see the top-of-file note on "ctx") - the only thing anything can ever
       fall back to, so it must never be empty. *)
    val ctx0 = [root]
    (* One "analyse_and_eval" call is one walk over one parsed root - resets
       "Dispatched_Antiqs" (see its own note on "check_antiq") so a comment's
       already-dispatched status never leaks from a previous, unrelated
       parse. *)
    val _ = Dispatched_Antiqs.reset ()
    fun finish (cenv1, acts) = (Context.theory_map (put cenv1) thy, acts)
  in
    case root of
      C_Ast.Id (C_Ast.Ident (name, _, ni)) =>
        let
          val here = check_antiq cenv0 ctx0 ni
          val _ = report_use cenv0 name (C_Ast.pos_of_NodeInfo ni)
        in (thy, here) end
    | C_Ast.Expr e => finish (walk_expr cenv0 ctx0 e)
    | C_Ast.Stmt s => finish (walk_stat cenv0 ctx0 s)
    | C_Ast.Units us =>
        finish (fold (fn tu => fn (cenv, acc) =>
                        let val (cenv', acts) = walk_translation_unit cenv ctx0 tu
                        in (cenv', acc @ acts) end)
                  us (cenv0, []))
  end

end
\<close>

subsection\<open>Some Basic Antiquotation Settings\<close>

(* "term_antiq" below needs a genuine catch-all "handle exn => ..." (see its
   own comment: "Syntax.read_term"'s failure comes back as "Par_Exn", not a
   bare "ERROR", so nothing narrower would catch it) - PolyML's compiler
   otherwise elevates ANY unconstrained "handle exn => ..." pattern from a
   warning to a hard "ML error" ("Handler catches all exceptions"),
   regardless of what the handler body does with it (it still correctly
   re-raises "Exn.is_interrupt"). "ML_catch_all" is the standard Isabelle/Pure
   config attribute for permitting this locally - see its own declaration in
   "ML_Bootstrap.thy", which sets it the same way for the same reason. *)
declare [[ML_catch_all = true]]

ML\<open>
val CENV = Unsynchronized.ref(CEnv.empty_cenv);
val probe_cenv = let fun probe (cenv, _ , _) (_ : string * Position.T) thy =
                              (CENV := cenv; thy)
                 in  CEnv.store_antiq ("probe_cenv",  probe) end


val AST = Unsynchronized.ref((C_Ast.Units []): (Position.T C_Ast.root) )
val probe_ast = let fun probe (_, c_ast , l) (_ : string * Position.T) thy =
                              (writeln("Level: "^ Int.toString l);
                               writeln("Read : " ^ C_Ast.pp_root c_ast);
                               AST := c_ast; thy)
                in  CEnv.store_antiq ("probe_ast",  probe) end


val highlight = let fun probe (_, c_ast , _) (_ : string * Position.T) thy =
                              (Position.report (AnaEval.pos_of_root c_ast) Markup.intensify;
                               thy)
                in  CEnv.store_antiq ("highlight",  probe) end

(* A "term" antiquotation: parses its cartouche body as a genuine HOL term
   against the theory's *current* context via "Syntax.read_term", so a
   malformed or ill-typed term (an unknown constant, a type error) is
   reported as a real Isabelle error rather than being silently accepted as
   opaque comment text - e.g. an ACSL-style "//@ requires \<open>x \<ge> 0\<close>" is now a
   genuine, checked HOL proposition, not just stored text. A demo/dummy
   registration exactly like the three above (stashes into a ref for
   inspection, returns "thy" unchanged) - not a real verification-condition-
   generation system.

   Reads via an "Input.source", not a bare string, exactly the way Isabelle's
   own \<^verbatim>\<open>Args.term\<close> reads a term from the *outer* token stream
   (\<^verbatim>\<open>Token.inner_syntax_of\<close>/\<^verbatim>\<open>Syntax.implode_input\<close>): a bare string handed
   to \<^ML>\<open>Syntax.read_term\<close> carries no position of its own, so Isabelle falls
   back to whatever ambient position happens to be active - here, that turned
   out to be the antiquotation's own *resolved C_Ast context* position (\<section>B's
   "ctx"-derived root), not any position inside the term text itself. In
   practice this meant hovering over a symbol *inside* the parsed term (e.g.
   the "0" or the "@" of a list-append) flickered between unrelated C-source
   locations, since every symbol in the term ended up sharing that one
   ambient position rather than each having its own. \<open>body_pos\<close> - now
   threaded all the way from \<open>check_antiq\<close> (see \<open>type_antiq_fun\<close> in
   \<^verbatim>\<open>CEnv.thy\<close>, previously discarded there) - is the cartouche's own real
   source range, so \<^ML>\<open>Syntax.implode_input\<close> can encode it as YXML position
   markup that \<^ML>\<open>Syntax.read_term\<close> decodes back into a genuine per-symbol
   position for every token of the term, exactly as if the term had been
   written directly in an outer-syntax \<open>@{term \<open>...\<close>}\<close> antiquotation.

   \<^ML>\<open>Syntax.read_term\<close>'s own failure is re-raised with the antiquotation's
   resolved closest-context position appended (\<^ML>\<open>AnaEval.pos_of_root\<close>) for
   cases where the failure itself has no better position to offer (e.g. an
   entirely empty body). Caught as a bare \<^ML>\<open>exn\<close>, not \<^ML>\<open>ERROR\<close>: a genuine
   syntax/type failure from \<^ML>\<open>Syntax.read_term\<close> comes back wrapped as
   \<^ML>\<open>Par_Exn\<close> (Isabelle's parallel-checking exception bundle), not a bare
   \<^ML>\<open>ERROR\<close>, so \<open>handle ERROR msg => ...\<close> alone would never actually
   catch it - confirmed empirically, not merely inferred. \<^ML>\<open>Runtime.exn_message\<close>
   is the standard Isabelle/Pure utility for turning *any* exception
   (\<^ML>\<open>Par_Exn\<close> included) into one readable message; \<^ML>\<open>Exn.is_interrupt\<close>
   must still be checked and reraised first, as with any catch-all handler,
   so a genuine user interrupt is never swallowed as if it were this
   antiquotation's own failure. *)
val TERM_PROBE = Unsynchronized.ref (Free ("dummy_term_probe", dummyT) : term)
val term_antiq =
  let
    fun probe (_, c_ast, _) (body, body_pos) thy =
      let
        val ctxt = Proof_Context.init_global thy
        (* "body_pos" is already a single merged range position (built via
           "Position.range_position (start, end)" in C11_Parser.thy), not the
           "Position.range" (a genuine start/end pair) "Input.source" needs -
           reconstruct that pair the same way "name_range" (above) rebuilds
           an end position from a start plus known text: "no_range_position"
           recovers the start (same offset, same props, end_offset zeroed),
           then "symbol_explode" re-advances through "body"'s own text to
           recover the end. *)
        val start_pos = Position.no_range_position body_pos
        val end_pos = Position.symbol_explode body start_pos
        val encoded = Syntax.implode_input (Input.source true body (start_pos, end_pos))
        val t = Syntax.read_term ctxt encoded
          handle exn =>
            if Exn.is_interrupt exn then Exn.reraise exn
            else error ("term antiquotation: " ^ Runtime.exn_message exn ^
                         Position.here (AnaEval.pos_of_root c_ast))
      in (TERM_PROBE := t; thy) end
  in CEnv.store_antiq ("term", probe) end

\<close>

setup\<open>probe_cenv\<close>
setup\<open>probe_ast\<close>
setup\<open>highlight\<close>
setup\<open>term_antiq\<close>

end
