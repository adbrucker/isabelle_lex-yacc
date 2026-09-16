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
  to. Only \<open>ident\<close>/\<open>cExpression\<close>/\<open>cStatement\<close> nodes, plus a whole
  \<open>cTranslationUnit\<close> (as \<open>Units\<close>), can be turned into a \<open>root\<close> and hit one of the
  four cases; the wrapped \<open>ident\<close> case is dispatched only for the top-level
  \<open>c11_ident\<close> entry point (an \<open>ident\<close> embedded inside e.g. \<open>CVar\<close>/\<open>CGoto\<close> is not
  independently checked - it shares its leftmost position with the enclosing
  expression/statement, which already claims and checks any attached comment, so
  checking both would dispatch the same antiquotation twice). Every other node kind
  that carries a \<open>nodeInfo\<close> (declarations, function definitions, declarators,
  initializers, file-scope \<open>asm\<close>, preprocessor directives) is still walked for
  registration/hyperlinking, but an \<open>Antiquotation\<close> found on \<^emph>\<open>its\<close> \<open>nodeInfo\<close>
  raises \<open>error\<close> - not \<^emph>\<open>ident\<close>, \<^emph>\<open>expr\<close>, \<^emph>\<open>statement\<close>, or \<^emph>\<open>unit\<close>. A thunked
  \<open>root\<close> builder means that \<open>error\<close> only actually fires when such a comment is
  really present, never merely because a node of that kind exists.

  Every identifier \<^emph>\<open>use\<close> (currently: a variable/function name in \<open>CVar\<close>, plus the
  bare \<open>Id\<close> root itself) is hyperlinked to its declaration via
  \<^ML>\<open>Position.entity_markup\<close> (Isabelle/Pure's standard def/ref markup - the
  declaration's own position is baked directly into the markup, so no
  serial-number correlation table is needed) and \<^ML>\<open>Position.report\<close>, reported
  once at the declaration site (self-referential) and once at every use.

  Left for a later pass, deliberately: \<open>Enum\<close>/\<open>Cpp_const\<close>/\<open>Cpp_macro\<close> are not
  populated (no position payload exists yet to hyperlink them by); struct/union
  member names and enum constants are not registered into \<open>cenv\<close> (they live in a
  per-type namespace, and \<open>type_ident\<close> is still \<open>NOT_YET_DEFINED\<close>) - nested
  \<open>cTypeSpecifier\<close>/\<open>cStructureUnion\<close>/\<open>cEnumeration\<close> content (a struct's member
  list, an enum's values) is consequently not walked; a K&R old-style parameter
  list registers each name as \<open>Parameter\<close> straight from the bare identifier,
  without cross-referencing the trailing old-style declaration list for its real
  type. \<open>analyse_and_eval\<close> itself is not yet wired into \<open>run_c11_kind\<close>/\<open>c11\<close>.
\<close>
ML\<open>
structure AnaEval = struct
open CEnv


fun idents_of (mk {idents, ...} : cenv) = idents

fun set_idents idents' (mk {idents = _, types, c_antiq, units}) =
  mk {idents = idents', types = types, c_antiq = c_antiq, units = units}

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

fun report_decl kind name decl_pos =
  Position.report decl_pos (Position.entity_markup kind (name, decl_pos))

(* Looks "name" up in "cenv"'s "idents" and, if found (and of a kind that
   currently carries a declaration position - see the "Enum"/"Cpp_const"/
   "Cpp_macro" note above), hyperlinks "use_pos" back to its declaration. *)
fun report_use cenv name use_pos =
  let val mk {idents, ...} = cenv in
    case Symtab.lookup idents name of
      NONE => ()
    | SOME ik =>
        (case (case ik of
                 Global decl => SOME ("C11 global variable", decl)
               | Local decl => SOME ("C11 local variable", decl)
               | Parameter decl => SOME ("C11 parameter", decl)
               | Enum => NONE
               | Cpp_const => NONE
               | Cpp_macro => NONE) of
           NONE => ()
         | SOME (kind, decl) =>
             (case find_decl_pos decl name of
                NONE => ()
              | SOME decl_pos => Position.report use_pos (Position.entity_markup kind (name, decl_pos))))
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
    | C_Ast.CConst c =>
        let val acts = check_antiq cenv
              (fn () => error "analyse_and_eval: antiquotations are not supported on constants")
              (C_Ast.nodeInfo_of_CConst c)
        in (cenv, here @ acts) end
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
        let val acts = check_antiq cenv
              (fn () => error "analyse_and_eval: antiquotations are not supported on builtins")
              (C_Ast.nodeInfo_of_CBuiltin b)
        in (cenv, here @ acts) end
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
   generic-selection/compound-literal/"_Alignas" - see "walk_type_decl"). *)
and walk_decl kind_str mk_kind cenv (cdecl as C_Ast.CDecl (_, entries, ni)) =
      let
        val here = check_antiq cenv
          (fn () => error "analyse_and_eval: antiquotations are not supported on declarations") ni
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
  | walk_decl _ _ cenv (C_Ast.CStaticAssert (e, _, ni)) =
      let
        val here = check_antiq cenv
          (fn () => error "analyse_and_eval: antiquotations are not supported on declarations") ni
        val (cenv1, acts1) = walk_expr cenv e
      in (cenv1, here @ acts1) end

(* An abstract type-name (cast/sizeof/alignof/generic-selection/compound-literal
   target type): walked the same way as an ordinary declaration for
   antiquotation-checking and nested-expression purposes, but its declarator (if
   any) is always unnamed, so "walk_decl" registers nothing. *)
and walk_type_decl cenv d = walk_decl "C11 type" Local cenv d

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
            | C_Ast.Right d => walk_decl "C11 local variable" Local cenv d
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
              | C_Ast.CBlockDecl d => walk_decl "C11 local variable" Local cenv d
              | C_Ast.CNestedFunDef f => walk_fun_def "C11 local function" Local cenv f
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
              let val (cenv', acts) = walk_decl "C11 parameter" Local cenv p
              in (cenv', acc @ acts) end)
        params (cenv, [])
  | SOME _ => (cenv, []) (* unreachable: "params_of_declarator" only ever finds a "CFunDeclr" *)

and walk_fun_def kind_str mk_kind cenv (C_Ast.CFunDef (specs, declr, _, body, ni)) =
      let
        val here = check_antiq cenv
          (fn () => error "analyse_and_eval: antiquotations are not supported on function definitions") ni
        val synthetic_decl = C_Ast.CDecl (specs, [((SOME declr, NONE), NONE)], ni)
        val cenv1 =
          case decl_name_pos declr of
            NONE => cenv
          | SOME (name, pos) => register kind_str mk_kind cenv (name, pos, synthetic_decl)
        val outer = idents_of cenv1
        val (cenv_params, param_acts) = open_param_scope cenv1 declr
        val (cenv_body, body_acts) = walk_stat cenv_params body
      in (set_idents outer cenv_body, here @ param_acts @ body_acts) end

and walk_ext_decl cenv (ed : pos C_Ast.cExternalDeclaration) : cenv * (int * (theory -> theory)) list =
  case ed of
    C_Ast.CDeclExt d => walk_decl "C11 global variable" Global cenv d
  | C_Ast.CFDefExt f => walk_fun_def "C11 global function" Global cenv f
  | C_Ast.CAsmExt (_, ni) =>
      let val here = check_antiq cenv
            (fn () => error "analyse_and_eval: antiquotations are not supported on file-scope asm blocks") ni
      in (cenv, here) end
  | C_Ast.CPPExt d =>
      let val here = check_antiq cenv
            (fn () => error "analyse_and_eval: antiquotations are not supported on preprocessor directives")
            (C_Ast.nodeInfo_of_CPPDirective d)
      in (cenv, here) end

and walk_translation_unit cenv (tu as C_Ast.CTranslUnit (eds, ni)) =
  let
    val here = check_antiq cenv (fn () => C_Ast.Units [tu]) ni
    val (cenv1, acts1) =
      fold (fn ed => fn (cenv, acc) =>
              let val (cenv', acts) = walk_ext_decl cenv ed in (cenv', acc @ acts) end)
        eds (cenv, [])
  in (cenv1, here @ acts1) end

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

end
