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

theory CEnv
  imports "C_Ast"
begin

section\<open>The CEnv Environment: storing Ast's and Environments\<close>

text\<open>
  \<^verbatim>\<open>CEnv\<close> is the environment/AST-store infrastructure shared by every \<open>c11\<close>-family
  command and by \<^verbatim>\<open>AnaEval\<close> (the \<open>analyse_and_eval\<close> pass, in its own theory
  importing this one). It bundles two plain \<^verbatim>\<open>Generic_Data\<close> registries (the standard
  Isabelle/Pure idiom for per-theory, persistent-through-merge state) behind one
  structure: \<^verbatim>\<open>Env\<close> holds the symbolic environment - \<open>idents\<close> (declared names),
  \<open>types\<close> (struct/union/enum tags), \<open>c_antiq\<close> (registered antiquotation handlers),
  and \<open>predefined_envs\<close> (\<^verbatim>\<open>c11_predef\<close>'s own reusable header effects, applied by a
  later \<open>#include\<close> - see the note on \<open>predefined_envs\<close> below) - plus the running
  \<open>units\<close> counter that gives every AST this theory
  stores a fresh, per-theory sequence number; \<^verbatim>\<open>Ast_Store\<close> maps \<open>(theory_name,
  unit_number)\<close> - encoded as one \<^verbatim>\<open>Symtab\<close> key, since \<^verbatim>\<open>Symtab.table\<close> is
  string-keyed - to the \<^verbatim>\<open>Position.T root\<close> that one of the \<open>c11\<close>/\<open>c11_file\<close>/
  \<open>c11_ident\<close>/\<open>c11_expr\<close>/\<open>c11_statement\<close> commands parsed there; see \<open>store_root\<close>,
  below, for the key format and the counter update. \<^verbatim>\<open>Env\<close> and \<^verbatim>\<open>Ast_Store\<close> are
  declared as \<^emph>\<open>sibling\<close> substructures of \<^verbatim>\<open>CEnv\<close> - not \<^verbatim>\<open>Ast_Store\<close> nested inside
  a structure also named \<^verbatim>\<open>Env\<close> or vice versa, and neither named \<^verbatim>\<open>CEnv\<close> itself -
  which would self-shadow; \<^verbatim>\<open>get\<close>/\<^verbatim>\<open>put\<close> re-export \<^verbatim>\<open>Env\<close>'s own
  \<^verbatim>\<open>Generic_Data\<close> accessors directly on \<^verbatim>\<open>CEnv\<close>, so a caller never needs to name
  \<^verbatim>\<open>Env\<close> itself - \<^verbatim>\<open>Env.map\<close> is deliberately \<^emph>\<open>not\<close> re-exported under the bare
  name \<open>map\<close>, since that would silently shadow the ubiquitous \<^verbatim>\<open>List.map\<close>/Basis
  \<open>map\<close> for every caller using \<^verbatim>\<open>open CEnv\<close> - a real problem, not a hypothetical
  one (it broke an unrelated theory's own \<open>map\<close> calls the first time this was
  tried). Callers elsewhere are expected to write \<^verbatim>\<open>open CEnv\<close> where that
  reads better than qualifying every operation.
\<close>
ML\<open>
structure CEnv = struct

type pos = Position.T

datatype ident_kind = Global of (pos C_Ast.cDeclaration)
                    | Local  of (pos C_Ast.cDeclaration)
                    | Enum   of (pos C_Ast.cDeclaration)
                    | Parameter of (pos C_Ast.cDeclaration) (* really  ? *)
                    | Cpp_const of (pos C_Ast.cDeclaration)
                    | Cpp_macro of (pos C_Ast.ident list * pos C_Ast.cDeclaration)

(* A struct/union/enum tag's own registration in "cenv"'s "types" table - the
   C11 tag namespace, shared by all three, kept separate from "idents" (see
   "AnaEval.walk_decl_specs"). "Struct_tag"/"Union_tag" carry the defining
   occurrence's own position and its raw member declaration list (searched on
   demand by "AnaEval.report_member_use", not pre-indexed by member name - a
   struct/union rarely has enough members for a linear scan to matter);
   "Enum_tag" carries only its own position - an enum's constants are *not* a
   per-type member namespace in C, they live in the ordinary "idents" table
   right alongside variables and functions (see "Enum" above), so there is
   nothing further to store here for them. *)
datatype type_ident = Struct_tag of pos * pos C_Ast.cDeclaration list
                     | Union_tag  of pos * pos C_Ast.cDeclaration list
                     | Enum_tag   of pos

(* The cartouche/string body handed to a handler now carries its own source
   position alongside its text ("pos", the antiquotation's "cartouche"
   payload's own position - see C11_Parser.thy's "antiq_body_finish"/
   "antiq_tag_and_string_seen" and the "comment" datatype in c_ast.ML) -
   previously only the bare "string" reached the handler, discarding this
   position entirely (it existed in the AST, just never threaded past
   "check_antiq"). A handler that only cares about the text can still ignore
   it; "term" (AnaEval.thy) needs it to build a genuinely position-carrying
   "Input.source" for Isabelle's own term parser, so hovering over a symbol
   *inside* the parsed term links back to *that* symbol's own place in the
   C source, not to some unrelated fallback position.

   The "root" a handler receives is already the antiquotation's *resolved*
   context: "check_antiq" (AnaEval.thy) interprets the antiquotation's own
   "navi list" - the "up"/"Up"/"right"/"down" steps written as an optional
   bracketed "@tag[navi] ..." right after the tag (see "C_Ast.navi",
   "parse_tag_navi_level" in C11_Parser.thy for the syntax, and
   "AnaEval.select_ast" for the resolution algorithm) - against the closest-
   surrounding-context stack *before* calling the handler, so a handler never
   sees a navi list at all, only the single AST node it ends up denoting
   (the closest context itself, when the navi list is empty, matching every
   test that predates this round). *)
type 'a type_antiq_fun0 = 'a * pos C_Ast.root * int -> (string * pos) ->  theory -> theory

datatype cenv = mk of {idents  : ident_kind Symtab.table,
                       types   : type_ident Symtab.table,
                       c_antiq : (cenv type_antiq_fun0) Symtab.table,
                       predefined_envs : (cenv -> cenv) Symtab.table,
                       units   : int} \<comment> \<open>used for numbering translation units internally.\<close>

type type_antiq_fun = cenv type_antiq_fun0

(* "predefined_envs" holds, per header name (\<^verbatim>\<open>c11_predef\<close>'s own bracketed
   label, e.g. \<open>"stdio.h"\<close>), the reusable *effect* that header's own
   declarations have on an arbitrary "cenv" - captured once, when
   \<^verbatim>\<open>c11_predef\<close> itself is walked, as a plain function rather than applied
   there and then discarded, precisely so a *later* \<open>#include <header>\<close>
   (\<^verbatim>\<open>AnaEval.walk_pp_directive\<close>'s \<open>CPPInclude\<close> case) can re-apply the very
   same effect to whatever "cenv" is current at that point - the mechanism
   that actually connects \<open>#include\<close> to something, instead of it staying
   purely syntactic. \<^verbatim>\<open>c11_predef\<close> itself does *not* also register the
   declared names directly into "idents"/"types" - only "predefined_envs"
   changes when it runs; a name it declares is not yet in scope anywhere
   until some \<open>#include\<close> actually pulls it in, matching real C. *)
val empty_cenv = mk{idents  = Symtab.empty,
                  types   = Symtab.empty ,
                  c_antiq = Symtab.empty,
                  predefined_envs = Symtab.empty,
                  units = 0}

(* "merge = K empty" (discard both sides, reset to empty) is exactly wrong
   for live, incremental PIDE use: Isabelle forks/merges theory state
   routinely while a buffer is being edited (parallel/incremental checking,
   not just at the very end of a batch build), so every such merge would
   silently wipe every "c11"-family command's own registrations back to
   empty. A batch "isabelle build" essentially never exercises this path,
   which is why it was invisible to every build-based regression test in
   this session - still a real, separate bug worth fixing here even though
   it turned out not to be the cause of the point-vs-range hyperlinking bug
   diagnosed in "AnaEval.thy" ("report_use"/"report_decl"/"name_range").
   "Symtab.merge (K true)" takes the left side's entry on a key collision
   (both sides originate from the same walk of the same source text in
   practice, so a genuine conflict would mean a real bug elsewhere, not a
   case this needs to resolve cleverly); "units" takes the larger of the two
   counters, so a merge can only grow it, never shrink it back into a range
   that could collide with already-issued "Ast_Store" keys. *)
fun merge_cenv (mk {idents = i1, types = t1, c_antiq = a1, predefined_envs = p1, units = u1},
                mk {idents = i2, types = t2, c_antiq = a2, predefined_envs = p2, units = u2}) =
  mk {idents = Symtab.merge (K true) (i1, i2),
      types = Symtab.merge (K true) (t1, t2),
      c_antiq = Symtab.merge (K true) (a1, a2),
      predefined_envs = Symtab.merge (K true) (p1, p2),
      units = Int.max (u1, u2)}

structure Env = Generic_Data
  (type T = cenv
   val empty = empty_cenv
   val merge = merge_cenv)

structure Ast_Store = Generic_Data
  (type T = (Position.T C_Ast.root) Symtab.table
   val  empty = Symtab.empty
   val  merge = Symtab.merge (K true))

(* Deliberately not re-exporting "Env.map" under the bare name "map": every
   caller of this structure via "open CEnv" would then have the ubiquitous
   "List.map"/Basis "map" silently shadowed by "Generic_Data"'s very
   differently-typed one - a real, previously-hit problem, not a hypothetical
   one. "get"/"put" collide with nothing comparably common, so those two stay. *)
val get = Env.get
val put = Env.put

(* The (theory_name, unit_number) pair, encoded as one Symtab key ("name#N") -
   theory_name via "Context.theory_name {long = false}" (the short name, not the
   fully qualified session-path one), unit_number as the decimal string of the
   CEnv-held counter's current value before it is bumped. *)
fun ast_store_key thy unit_no =
  Context.theory_name {long = false} thy ^ "#" ^ Int.toString unit_no

(* Stores "root" under a fresh unit number for "thy", bumping CEnv's counter.
   Returns the store key (for user-facing reporting) and the updated theory. *)
fun store_root (root : Position.T C_Ast.root) thy =
    let
      val mk {idents, types, c_antiq, predefined_envs, units} = get (Context.Theory thy)
      val key = ast_store_key thy units
      val cenv' = mk {idents = idents, types = types, c_antiq = c_antiq,
                       predefined_envs = predefined_envs, units = units + 1}
      val thy' = thy
        |> Context.theory_map (put cenv')
        |> Context.theory_map (Ast_Store.map (Symtab.update (key, root)))
    in (key, thy') end

fun get_ast key thy =
    let val store = Ast_Store.get (Context.Theory thy)
    in  Symtab.lookup store key end

fun store_antiq (name, antiq_fun) thy =
    let
       val mk {idents, types, c_antiq, predefined_envs, units} = get (Context.Theory thy)
       val c_antiq' = Symtab.update(name, antiq_fun) c_antiq
       val cenv' = mk {idents = idents, types = types, c_antiq = c_antiq',
                        predefined_envs = predefined_envs, units = units}
    in thy |> Context.theory_map (put cenv')
    end

fun get_antiq name thy =
    let
       val mk {c_antiq, ...} = get (Context.Theory thy)
    in Symtab.lookup c_antiq name end

(* Registers "header"'s own reusable "cenv -> cenv" effect (see the note on
   "predefined_envs" above) - the "predefined_envs" analogue of
   "store_antiq"/"get_antiq". Deliberately does *not* touch "idents"/
   "types"/"c_antiq" at all: registering a header's effect is not the same
   as applying it - that only happens via a later "#include". *)
fun store_predefined_env (header, f) thy =
    let
       val mk {idents, types, c_antiq, predefined_envs, units} = get (Context.Theory thy)
       val predefined_envs' = Symtab.update (header, f) predefined_envs
       val cenv' = mk {idents = idents, types = types, c_antiq = c_antiq,
                        predefined_envs = predefined_envs', units = units}
    in thy |> Context.theory_map (put cenv')
    end

fun get_predefined_env header thy =
    let
       val mk {predefined_envs, ...} = get (Context.Theory thy)
    in Symtab.lookup predefined_envs header end

end
\<close>


end
