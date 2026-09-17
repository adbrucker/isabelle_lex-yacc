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
  into the result list, to be run later by whoever calls this). Scoping is
  shadow-and-restore, not a stack: entering a function body, a compound-statement
  block, or a \<open>for\<close>-loop's own declaration clause remembers the incoming \<open>idents\<close>
  table and restores exactly that (not the whole \<open>cenv\<close>, in case a later pass
  starts also touching \<open>types\<close>/\<open>c_antiq\<close> locally) once that scope's walk returns -
  giving ordinary sequential C scoping when folded across a block's items.

  A node's own antiquotations are always checked using the \<open>cenv\<close> \<^emph>\<open>inherited on
  entry\<close> to that node, i.e. before that node's own declaration (if it introduces
  one) is registered - matching a comment textually preceding what it is attached
  to. \<open>ident\<close>/\<open>cExpression\<close>/\<open>cStatement\<close> nodes, a whole \<open>cTranslationUnit\<close> (as
  \<open>Units\<close>), and - also wrapped as a one-element \<open>Units\<close>, back into the
  \<open>cExternalDeclaration list\<close> each came from - a \<^emph>\<open>top-level\<close> declaration,
  function definition, file-scope \<open>asm\<close> block, or preprocessor directive, can
  all be turned into a \<open>root\<close> and dispatched: this is what lets the tests in
  \<^verbatim>\<open>C11.thy\<close>'s "Antiquotation-carrying Comments" section attach \<open>@tag \<open>...\<close>\<close> to
  an ordinary file-scope declaration. The wrapped \<open>ident\<close> case is dispatched
  only for the top-level \<open>c11_ident\<close> entry point (an \<open>ident\<close> embedded inside
  e.g. \<open>CVar\<close>/\<open>CGoto\<close> is not independently checked - it shares its leftmost
  position with the enclosing expression/statement, which already claims and
  checks any attached comment, so checking both would dispatch the same
  antiquotation twice); likewise a declaration/function definition is only
  dispatchable where it is genuinely top-level - a \<^emph>\<open>nested\<close> one (a block-local
  declaration, a \<open>for\<close>-loop's own clause, a function's parameter, an abstract
  type-name used by a cast/\<open>sizeof\<close>/\<open>_Generic\<close>/\<dots>, a "CNestedFunDef" GNU nested
  function) still raises \<open>error\<close> on its own \<open>nodeInfo\<close>, since none of those is
  itself a complete top-level declaration - "\<open>as_root\<close>" is threaded as an
  explicit parameter through \<open>walk_decl\<close>/\<open>walk_fun_def\<close> for exactly this: each
  caller supplies the thunk appropriate to \<^emph>\<open>its\<close> context, top-level or not.
  Declarators/initializers still carry no dispatchable shape of their own
  either way. A thunked \<open>root\<close> builder throughout means \<open>error\<close> only actually
  fires when such a comment is really present, never merely because a node of
  that kind exists.

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

  Left for a later pass, deliberately: \<open>Enum\<close> is not populated (enum constants
  live in the ordinary namespace in real C, but nothing here tracks them yet);
  struct/union member names are not registered into \<open>cenv\<close> either (they live in
  a per-type namespace, and \<open>type_ident\<close> is still \<open>NOT_YET_DEFINED\<close>) - nested
  \<open>cTypeSpecifier\<close>/\<open>cStructureUnion\<close>/\<open>cEnumeration\<close> content (a struct's member
  list, an enum's values) is consequently not walked; a K&R old-style parameter
  list registers each name as \<open>Local\<close> straight from the bare identifier,
  without cross-referencing the trailing old-style declaration list for its real
  type. \<open>analyse_and_eval\<close> itself is not yet wired into \<open>run_c11_kind\<close>/\<open>c11\<close>.
\<close>
ML\<open>
structure AnaEval = struct

open CEnv

fun idents_of (mk {idents, ...} : cenv) = idents

fun set_idents idents' (mk {idents = _, types, c_antiq, units}) =
  mk {idents = idents', types = types, c_antiq = c_antiq, units = units}

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

(* The shared antiquotation-dispatch helper: looks up every "Antiquotation" in
   "ni"'s comment list by tag in "cenv"'s "c_antiq", instantiates it with
   (cenv, as_root (), level), and pairs the resulting "theory -> theory" with
   its level - "as_root" is only forced (and so can only "error") when an
   "Antiquotation" genuinely needs it, never for an ordinary "Raw_txt" or an
   empty comment list. *)
fun check_antiq cenv (as_root : unit -> pos C_Ast.root) (ni : pos C_Ast.nodeInfo)
    : (int * (theory -> theory)) list =
  case ni of
    C_Ast.OnlyPos _ => []
  | C_Ast.NodeInfo (cs, _) =>
      List.mapPartial
        (fn C_Ast.Antiquotation ({tag = (tag, _)}, {level}, {cartouche = (body, _)}) =>
              let val mk {c_antiq, ...} = cenv in
                case Symtab.lookup c_antiq tag of
                  NONE =>
                    error ("analyse_and_eval: no antiquotation handler registered for tag " ^
                           quote tag)
                | SOME antiq_fun => SOME (level, antiq_fun (cenv, as_root (), level) body)
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
               | Enum => NONE) of
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
    val mk {idents, types, c_antiq, units} = cenv
    val _ = report_decl kind_str name decl_pos
  in mk {idents = Symtab.update (name, mk_kind decl) idents, types = types, c_antiq = c_antiq, units = units} end

fun walk_exprs cenv es acc =
  fold (fn e => fn (cenv, acc) => let val (cenv', acts) = walk_expr cenv e in (cenv', acc @ acts) end)
    es (cenv, acc)

and walk_expr cenv (e : pos C_Ast.cExpression) : cenv * (int * (theory -> theory)) list =
  let
    val here = check_antiq cenv (fn () => C_Ast.Expr e) (C_Ast.nodeInfo_of_CExpr e)
  in
    case e of
      C_Ast.CComma (es, _) => walk_exprs cenv es here
    | C_Ast.CAssign (_, e1, e2, _) => walk_exprs cenv [e1, e2] here
    | C_Ast.CCond (e1, NONE, e3, _) => walk_exprs cenv [e1, e3] here
    | C_Ast.CCond (e1, SOME e2, e3, _) => walk_exprs cenv [e1, e2, e3] here
    | C_Ast.CBinary (_, e1, e2, _) => walk_exprs cenv [e1, e2] here
    | C_Ast.CCast (d, e1, _) =>
        let val (cenv1, acts1) = walk_type_decl cenv d in walk_exprs cenv1 [e1] (here @ acts1) end
    | C_Ast.CUnary (_, e1, _) => walk_exprs cenv [e1] here
    | C_Ast.CSizeofExpr (e1, _) => walk_exprs cenv [e1] here
    | C_Ast.CSizeofType (d, _) =>
        let val (cenv1, acts1) = walk_type_decl cenv d in (cenv1, here @ acts1) end
    | C_Ast.CAlignofExpr (e1, _) => walk_exprs cenv [e1] here
    | C_Ast.CAlignofType (d, _) =>
        let val (cenv1, acts1) = walk_type_decl cenv d in (cenv1, here @ acts1) end
    | C_Ast.CComplexReal (e1, _) => walk_exprs cenv [e1] here
    | C_Ast.CComplexImag (e1, _) => walk_exprs cenv [e1] here
    | C_Ast.CIndex (e1, e2, _) => walk_exprs cenv [e1, e2] here
    | C_Ast.CCall (ef, args, _) => walk_exprs cenv (ef :: args) here
    | C_Ast.CMember (e1, _, _, _) =>
        (* the field name itself has no cenv entry (member namespace, see above) *)
        walk_exprs cenv [e1] here
    | C_Ast.CVar (C_Ast.Ident (name, _, ident_ni), _) =>
        (report_use cenv name (C_Ast.pos_of_NodeInfo ident_ni); (cenv, here))
    | C_Ast.CConst _ =>
        (* "nodeInfo_of_CExpr (CConst aa) = nodeInfo_of_CConst aa" - "here",
           above, already checked exactly this "nodeInfo" as "Expr e"-
           dispatchable (a constant genuinely is an ordinary expression); a
           second, separately-erroring check on the same "nodeInfo" here
           would not just be redundant but wrong, dispatching the very same
           "Antiquotation" a second time only to then unconditionally error
           on it. *)
        (cenv, here)
    | C_Ast.CCompoundLit (d, inits, _) =>
        let
          val (cenv1, acts1) = walk_type_decl cenv d
          val (cenv2, acts2) =
            fold (fn (desigs, init) => fn (cenv, acc) =>
                    let
                      val (cenv_a, acts_a) = walk_designators cenv desigs
                      val (cenv_b, acts_b) = walk_initializer cenv_a init
                    in (cenv_b, acc @ acts_a @ acts_b) end)
              inits (cenv1, [])
        in (cenv2, here @ acts1 @ acts2) end
    | C_Ast.CGenericSelection (e1, assocs, _) =>
        let
          val (cenv1, acts1) = walk_expr cenv e1
          val (cenv2, acts2) =
            fold (fn (d_opt, e2) => fn (cenv, acc) =>
                    let
                      val (cenv_a, acts_a) =
                        case d_opt of NONE => (cenv, []) | SOME d => walk_type_decl cenv d
                      val (cenv_b, acts_b) = walk_expr cenv_a e2
                    in (cenv_b, acc @ acts_a @ acts_b) end)
              assocs (cenv1, [])
        in (cenv2, here @ acts1 @ acts2) end
    | C_Ast.CStatExpr (s, _) =>
        let val (cenv1, acts1) = walk_stat cenv s in (cenv1, here @ acts1) end
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
                  val (cenv_a, acts_a) = walk_expr cenv e1
                  val (cenv_b, acts_b) = walk_type_decl cenv_a d
                in (cenv_b, acts_a @ acts_b) end
            | C_Ast.CBuiltinOffsetOf (d, desigs, _) =>
                let
                  val (cenv_a, acts_a) = walk_type_decl cenv d
                  val (cenv_b, acts_b) = walk_designators cenv_a desigs
                in (cenv_b, acts_a @ acts_b) end
            | C_Ast.CBuiltinTypesCompatible (d1, d2, _) =>
                let
                  val (cenv_a, acts_a) = walk_type_decl cenv d1
                  val (cenv_b, acts_b) = walk_type_decl cenv_a d2
                in (cenv_b, acts_a @ acts_b) end
        in (cenv1, here @ acts1) end
  end

and walk_designators cenv ds =
  fold (fn d => fn (cenv, acc) =>
          case d of
            C_Ast.CArrDesig (e, _) =>
              let val (cenv1, acts1) = walk_expr cenv e in (cenv1, acc @ acts1) end
          | C_Ast.CMemberDesig _ => (cenv, acc)
          | C_Ast.CRangeDesig (e1, e2, _) =>
              let
                val (cenv1, acts1) = walk_expr cenv e1
                val (cenv2, acts2) = walk_expr cenv1 e2
              in (cenv2, acc @ acts1 @ acts2) end)
    ds (cenv, [])

and walk_initializer cenv (C_Ast.CInitExpr (e, ni)) =
      let
        val here = check_antiq cenv
          (fn () => error "analyse_and_eval: antiquotations are not supported on initializers") ni
        val (cenv1, acts1) = walk_expr cenv e
      in (cenv1, here @ acts1) end
  | walk_initializer cenv (C_Ast.CInitList (pairs, ni)) =
      let
        val here = check_antiq cenv
          (fn () => error "analyse_and_eval: antiquotations are not supported on initializers") ni
      in
        fold (fn (desigs, init) => fn (cenv, acc) =>
                let
                  val (cenv1, acts1) = walk_designators cenv desigs
                  val (cenv2, acts2) = walk_initializer cenv1 init
                in (cenv2, acc @ acts1 @ acts2) end)
          pairs (cenv, here)
      end

(* Only the derived-declarator's own array-size expression (e.g. the "N" in
   "int arr[N]") is descended into - "CPtrDeclr"/"CFunDeclr" carry nothing
   further relevant to scoping/hyperlinking in this pass. *)
and walk_declarator cenv (C_Ast.CDeclr (_, derived, _, _, ni)) =
      let
        val here = check_antiq cenv
          (fn () => error "analyse_and_eval: antiquotations are not supported on declarators") ni
      in
        fold (fn d => fn (cenv, acc) =>
                let
                  val dni =
                    case d of
                      C_Ast.CPtrDeclr (_, ni) => ni
                    | C_Ast.CArrDeclr (_, _, ni) => ni
                    | C_Ast.CFunDeclr (_, _, ni) => ni
                  val dhere = check_antiq cenv
                    (fn () => error "analyse_and_eval: antiquotations are not supported on derived declarators") dni
                  val (cenv1, acts1) =
                    case d of
                      C_Ast.CArrDeclr (_, C_Ast.CArrSize (_, e), _) => walk_expr cenv e
                    | _ => (cenv, [])
                in (cenv1, acc @ dhere @ acts1) end)
          derived (cenv, here)
      end

(* Shared by every context that names variables: top-level ("Global"), a
   compound-statement block or "for"-loop clause ("Local"), and a function's
   parameter list ("Parameter") - each declared name is registered with
   "kind_str"/"mk_kind" as given by the caller, which is a no-op whenever
   "decl_name_pos" finds no name (an abstract type-name used by a cast/sizeof/
   generic-selection/compound-literal/"_Alignas" - see "walk_type_decl").
   "as_root" is likewise caller-supplied: "walk_ext_decl" passes one that
   wraps the whole declaration as "Units", since a top-level declaration
   genuinely is a dispatchable antiquotation target (as the "Antiquotation-
   carrying Comments" tests in C11.thy rely on); every other caller (a block-
   local declaration, a "for"-loop's own clause, a parameter, an abstract
   type-name) passes one that errors, since none of those are "ident"/
   "expr"/"statement"/"unit"-shaped. *)
and walk_decl kind_str mk_kind as_root cenv (cdecl as C_Ast.CDecl (_, entries, ni)) =
      let
        val here = check_antiq cenv as_root ni
        val (cenv1, acts1) =
          fold (fn ((declr_opt, init_opt), width_opt) => fn (cenv, acc) =>
                  let
                    val (cenv_a, acts_a) =
                      case declr_opt of NONE => (cenv, []) | SOME declr => walk_declarator cenv declr
                    val (cenv_b, acts_b) =
                      case init_opt of NONE => (cenv_a, []) | SOME init => walk_initializer cenv_a init
                    val (cenv_c, acts_c) =
                      case width_opt of NONE => (cenv_b, []) | SOME e => walk_expr cenv_b e
                    val cenv_d =
                      case declr_opt of
                        NONE => cenv_c
                      | SOME declr =>
                          (case decl_name_pos declr of
                             NONE => cenv_c
                           | SOME (name, pos) => register kind_str mk_kind cenv_c (name, pos, cdecl))
                  in (cenv_d, acc @ acts_a @ acts_b @ acts_c) end)
            entries (cenv, here)
      in (cenv1, acts1) end
  | walk_decl _ _ as_root cenv (C_Ast.CStaticAssert (e, _, ni)) =
      let
        val here = check_antiq cenv as_root ni
        val (cenv1, acts1) = walk_expr cenv e
      in (cenv1, here @ acts1) end

(* An abstract type-name (cast/sizeof/alignof/generic-selection/compound-literal
   target type): walked the same way as an ordinary declaration for
   antiquotation-checking and nested-expression purposes, but its declarator (if
   any) is always unnamed, so "walk_decl" registers nothing; never itself a
   dispatchable "root" (it is not a complete declaration). *)
and walk_type_decl cenv d =
  walk_decl "C11 type" Local
    (fn () => error "analyse_and_eval: antiquotations are not supported on type names") cenv d

and walk_stat cenv (s : pos C_Ast.cStatement) : cenv * (int * (theory -> theory)) list =
  let
    val here = check_antiq cenv (fn () => C_Ast.Stmt s) (C_Ast.nodeInfo_of_CStat s)
  in
    case s of
      C_Ast.CLabel (_, s1, _, _) =>
        let val (cenv1, acts1) = walk_stat cenv s1 in (cenv1, here @ acts1) end
    | C_Ast.CCase (e, s1, _) =>
        let
          val (cenv1, acts1) = walk_expr cenv e
          val (cenv2, acts2) = walk_stat cenv1 s1
        in (cenv2, here @ acts1 @ acts2) end
    | C_Ast.CCases (e1, e2, s1, _) =>
        let
          val (cenv1, acts1) = walk_expr cenv e1
          val (cenv2, acts2) = walk_expr cenv1 e2
          val (cenv3, acts3) = walk_stat cenv2 s1
        in (cenv3, here @ acts1 @ acts2 @ acts3) end
    | C_Ast.CDefault (s1, _) =>
        let val (cenv1, acts1) = walk_stat cenv s1 in (cenv1, here @ acts1) end
    | C_Ast.CExpr (NONE, _) => (cenv, here)
    | C_Ast.CExpr (SOME e, _) =>
        let val (cenv1, acts1) = walk_expr cenv e in (cenv1, here @ acts1) end
    | C_Ast.CCompound (_, items, _) =>
        let
          val outer = idents_of cenv
          val (cenv1, acts1) = walk_block_items cenv items
        in (set_idents outer cenv1, here @ acts1) end
    | C_Ast.CIf (e, s1, s2_opt, _) =>
        let
          val (cenv1, acts1) = walk_expr cenv e
          val (cenv2, acts2) = walk_stat cenv1 s1
          val (cenv3, acts3) = case s2_opt of NONE => (cenv2, []) | SOME s2 => walk_stat cenv2 s2
        in (cenv3, here @ acts1 @ acts2 @ acts3) end
    | C_Ast.CSwitch (e, s1, _) =>
        let
          val (cenv1, acts1) = walk_expr cenv e
          val (cenv2, acts2) = walk_stat cenv1 s1
        in (cenv2, here @ acts1 @ acts2) end
    | C_Ast.CWhile (e, s1, _, _) =>
        let
          val (cenv1, acts1) = walk_expr cenv e
          val (cenv2, acts2) = walk_stat cenv1 s1
        in (cenv2, here @ acts1 @ acts2) end
    | C_Ast.CFor (init, cond_opt, step_opt, body, _) =>
        let
          val outer = idents_of cenv
          val (cenv1, acts1) =
            case init of
              C_Ast.Left NONE => (cenv, [])
            | C_Ast.Left (SOME e) => walk_expr cenv e
            | C_Ast.Right d =>
                walk_decl "C11 local variable" Local
                  (fn () => error "analyse_and_eval: antiquotations are not supported on declarations")
                  cenv d
          val (cenv2, acts2) = case cond_opt of NONE => (cenv1, []) | SOME e => walk_expr cenv1 e
          val (cenv3, acts3) = case step_opt of NONE => (cenv2, []) | SOME e => walk_expr cenv2 e
          val (cenv4, acts4) = walk_stat cenv3 body
        in (set_idents outer cenv4, here @ acts1 @ acts2 @ acts3 @ acts4) end
    | C_Ast.CGoto (_, _) => (cenv, here)
    | C_Ast.CGotoPtr (e, _) =>
        let val (cenv1, acts1) = walk_expr cenv e in (cenv1, here @ acts1) end
    | C_Ast.CCont _ => (cenv, here)
    | C_Ast.CBreak _ => (cenv, here)
    | C_Ast.CReturn (NONE, _) => (cenv, here)
    | C_Ast.CReturn (SOME e, _) =>
        let val (cenv1, acts1) = walk_expr cenv e in (cenv1, here @ acts1) end
    | C_Ast.CAsm (_, _) => (cenv, here) (* inline asm operands: out of scope for this pass *)
  end

and walk_block_items cenv items =
  fold (fn item => fn (cenv, acc) =>
          let
            val (cenv', acts) =
              case item of
                C_Ast.CBlockStmt s => walk_stat cenv s
              | C_Ast.CBlockDecl d =>
                  walk_decl "C11 local variable" Local
                    (fn () => error "analyse_and_eval: antiquotations are not supported on declarations")
                    cenv d
              | C_Ast.CNestedFunDef f =>
                  walk_fun_def "C11 local function" Local
                    (fn () =>
                       error "analyse_and_eval: antiquotations are not supported on function definitions")
                    cenv f
          in (cenv', acc @ acts) end)
    items (cenv, [])

(* The "CFunDeclr" among a declarator's derived-declarator list that carries the
   function's parameter list - the first one found, which is the only one that
   occurs for an ordinary (non declarator-inversion) function declarator. *)
and params_of_declarator (C_Ast.CDeclr (_, derived, _, _, _)) =
  List.find (fn C_Ast.CFunDeclr _ => true | _ => false) derived

and open_param_scope cenv declr =
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
                val (cenv', acts) =
                  walk_decl "C11 parameter" Local
                    (fn () => error "analyse_and_eval: antiquotations are not supported on declarations")
                    cenv p
              in (cenv', acc @ acts) end)
        params (cenv, [])
  | SOME _ => (cenv, []) (* unreachable: "params_of_declarator" only ever finds a "CFunDeclr" *)

(* "as_root" is caller-supplied exactly like in "walk_decl" (see its own note)
   and for the same reason: "walk_ext_decl" passes one wrapping the whole
   function definition as "Units" (a top-level function definition is a
   dispatchable antiquotation target), a nested ("CNestedFunDef") one passes
   an erroring thunk instead. *)
and walk_fun_def kind_str mk_kind as_root cenv (C_Ast.CFunDef (specs, declr, _, body, ni)) =
      let
        val here = check_antiq cenv as_root ni
        val synthetic_decl = C_Ast.CDecl (specs, [((SOME declr, NONE), NONE)], ni)
        val cenv1 =
          case decl_name_pos declr of
            NONE => cenv
          | SOME (name, pos) => register kind_str mk_kind cenv (name, pos, synthetic_decl)
        val outer = idents_of cenv1
        val (cenv_params, param_acts) = open_param_scope cenv1 declr
        val (cenv_body, body_acts) = walk_stat cenv_params body
      in (set_idents outer cenv_body, here @ param_acts @ body_acts) end

(* Every branch here runs in a top-level (translation-unit) context, so
   "as_root" wraps the whole external declaration back into the one-element
   list it came from ("Units [CTranslUnit ([ed], ...)]") rather than
   erroring - unlike a nested declaration/function definition (block-local,
   a parameter, a "for"-clause, a type-name), a complete top-level one
   genuinely is a dispatchable antiquotation target, as the "Antiquotation-
   carrying Comments" tests in C11.thy rely on (an "@tag ..." attached to a
   file-scope declaration). *)
and walk_ext_decl cenv (ed : pos C_Ast.cExternalDeclaration) : cenv * (int * (theory -> theory)) list =
  case ed of
    C_Ast.CDeclExt d =>
      walk_decl "C11 global variable" Global
        (fn () => C_Ast.Units [C_Ast.CTranslUnit ([ed], C_Ast.nodeInfo_of_CDecl d)]) cenv d
  | C_Ast.CFDefExt f =>
      walk_fun_def "C11 global function" Global
        (fn () => C_Ast.Units [C_Ast.CTranslUnit ([ed], C_Ast.nodeInfo_of_CFunDef f)]) cenv f
  | C_Ast.CAsmExt (_, ni) =>
      let val here = check_antiq cenv (fn () => C_Ast.Units [C_Ast.CTranslUnit ([ed], ni)]) ni
      in (cenv, here) end
  | C_Ast.CPPExt d => walk_pp_directive cenv d

(* Wraps an ident (a macro's own name, or one of a function-like macro's
   parameters) as a one-name, otherwise-empty "cDeclaration" - purely so
   "find_decl_pos"/"register" have the same shape to work with as every
   other "ident_kind" payload, without needing a macro-specific case. *)
and synth_decl_of_ident (id as C_Ast.Ident (_, _, ni)) init_opt =
  let val declr = C_Ast.CDeclr (SOME id, [], NONE, [], ni)
  in C_Ast.CDecl ([], [((SOME declr, init_opt), NONE)], ni) end

(* A preprocessor directive only ever occurs directly in a
   "cExternalDeclaration list" (see "walk_ext_decl"/"walk_pp_directive"'s own
   caller) - i.e. this function always runs in a top-level context - so its
   own "here" is, like "CDeclExt"/"CFDefExt" in "walk_ext_decl", dispatchable
   as "Units", wrapping the whole directive back into the one-element
   external-declaration list it came from; computed once and reused for all
   four forms below, since they share the one "nodeInfo". *)
and walk_pp_directive cenv (d : pos C_Ast.cPreprocDirective) : cenv * (int * (theory -> theory)) list =
  let
    val ni = C_Ast.nodeInfo_of_CPPDirective d
    val here = check_antiq cenv (fn () => C_Ast.Units [C_Ast.CTranslUnit ([C_Ast.CPPExt d], ni)]) ni
  in
    case d of
      C_Ast.CPPInclude _ => (cenv, here)
    | C_Ast.CPPDefine (id as C_Ast.Ident (name, _, ident_ni), e, _) =>
        let
          val pos = C_Ast.pos_of_NodeInfo ident_ni
          val (cenv1, acts1) = walk_expr cenv e
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
          val (cenv_body, acts1) = walk_expr cenv_params e
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
             to skip over. Previously unreported entirely: the tested name
             was pattern-matched away with "_" here, so "#ifdef MAX_SIZE"
             never hyperlinked "MAX_SIZE" back to its own "#define", nor
             flagged a name undefined anywhere in this parse with
             \<^ML>\<open>Markup.bad ()\<close> the way every other use does. *)
          val _ = report_use cenv name (C_Ast.pos_of_NodeInfo ident_ni)
          val (cenv1, acts1) = walk_ext_decls cenv thn
          val (cenv2, acts2) = walk_ext_decls cenv1 els
        in (cenv2, here @ acts1 @ acts2) end
  end

and walk_ext_decls cenv eds =
  fold (fn ed => fn (cenv, acc) =>
          let val (cenv', acts) = walk_ext_decl cenv ed in (cenv', acc @ acts) end)
    eds (cenv, [])

(* Deliberately does NOT also "check_antiq" the whole unit's own "ni" here:
   by construction ("start_rule"'s "ndi2 (translation_unitleft,
   translation_unitright)" in C11_Parser.thy), a "CTranslUnit"'s own leftmost
   position always *is* its first external declaration's leftmost position -
   the same "two nodes genuinely share a leftmost token" situation
   "C11_Comments.claim"'s own non-destructiveness exists for (see its comment
   in C11_Parser.thy), except here both nodes are reachable from the *same*
   walk, so checking both would not just let two different call sites each
   see a shared comment (which is the intended, harmless case that
   non-destructive "claim" was built for) but would dispatch the very same
   "Antiquotation" twice from a single "analyse_and_eval" call. The first
   external declaration's own check (in "walk_ext_decl", via "walk_ext_decls"
   below) already covers every comment reachable this way - a translation
   unit with no declarations at all has no leftmost token to attach a
   comment to regardless, so nothing is lost by not checking here too. *)
and walk_translation_unit cenv (C_Ast.CTranslUnit (eds, _)) = walk_ext_decls cenv eds

fun analyse_and_eval (root : pos C_Ast.root) thy =
  let
    val cenv0 = get (Context.Theory thy)
    fun finish (cenv1, acts) = (Context.theory_map (put cenv1) thy, acts)
  in
    case root of
      C_Ast.Id (C_Ast.Ident (name, _, ni)) =>
        let
          val here = check_antiq cenv0 (fn () => root) ni
          val _ = report_use cenv0 name (C_Ast.pos_of_NodeInfo ni)
        in (thy, here) end
    | C_Ast.Expr e => finish (walk_expr cenv0 e)
    | C_Ast.Stmt s => finish (walk_stat cenv0 s)
    | C_Ast.Units us =>
        finish (fold (fn tu => fn (cenv, acc) =>
                        let val (cenv', acts) = walk_translation_unit cenv tu
                        in (cenv', acc @ acts) end)
                  us (cenv0, []))
  end

end
\<close>

subsection\<open>Some Basic Antiquotation Settings\<close>

ML\<open>
val CENV = Unsynchronized.ref(CEnv.empty_cenv);
val probe_cenv = let fun probe (cenv, _ , _) _ thy = (CENV := cenv; thy) 
                 in  CEnv.store_antiq ("probe_cenv",  probe) end


val AST = Unsynchronized.ref((C_Ast.Units []): (Position.T C_Ast.root) )
val probe_ast = let fun probe (_, c_ast , l) _ thy = 
                              (writeln("Level: "^ Int.toString l); 
                               writeln("Read : " ^ C_Ast.pp_root c_ast);
                               AST := c_ast; thy) 
                in  CEnv.store_antiq ("probe_ast",  probe) end


val highlight = let fun probe (_, c_ast , _) _ thy =
                              (Position.report (AnaEval.pos_of_root c_ast) Markup.intensify;
                               thy)
                in  CEnv.store_antiq ("highlight",  probe) end

\<close>

setup\<open>probe_cenv\<close>
setup\<open>probe_ast\<close>
setup\<open>highlight\<close>

end
