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

theory C11_Env
  imports "C11_Ast"
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
  below, for the key format and the counter update. \<^verbatim>\<open>Source_Store\<close>, a
  sibling table keyed the same way, holds each of those commands' own
  verbatim source text alongside its AST - written together with
  \<^verbatim>\<open>Ast_Store\<close> by the very same \<open>store_root\<close> call, so the two never drift
  out of sync - for \<open>c11_export_h\<close>/\<open>c11_export_c\<close>'s \<open>[verbatim]\<close> option
  (\<open>\<section>3\<close>) to hand back later. \<^verbatim>\<open>Env\<close> and \<^verbatim>\<open>Ast_Store\<close> are
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
   "antiq_tag_and_string_seen" and the "comment" datatype in c11_ast.ML) -
   previously only the bare "string" reached the handler, discarding this
   position entirely (it existed in the AST, just never threaded past
   "check_antiq"). A handler that only cares about the text can still ignore
   it; "term" (C11_AnaEval.thy) needs it to build a genuinely position-carrying
   "Input.source" for Isabelle's own term parser, so hovering over a symbol
   *inside* the parsed term links back to *that* symbol's own place in the
   C source, not to some unrelated fallback position.

   The "root" a handler receives is already the antiquotation's *resolved*
   context: "check_antiq" (C11_AnaEval.thy) interprets the antiquotation's own
   "navi list" - the "up"/"Up"/"right"/"down" steps written as an optional
   bracketed "@tag[navi] ..." right after the tag (see "C_Ast.navi",
   "parse_tag_navi_level" in C11_Parser.thy for the syntax, and
   "AnaEval.select_ast" for the resolution algorithm) - against the closest-
   surrounding-context stack *before* calling the handler, so a handler never
   sees a navi list at all, only the single AST node it ends up denoting
   (the closest context itself, when the navi list is empty, matching every
   test that predates this round).

   The result is "Context.generic -> Context.generic", not "theory -> theory":
   the original Isabelle/C (the AFP entry, "C11-FrontEnd/src/C_Command.thy"'s
   "C_Isar_Cmd.ML") shows why a handler needs to operate one level deeper than
   "theory" - its own "ML" inner command runs genuine ML code at the real ML
   toplevel via "ML_Context.exec"/"ML_Context.eval_source", which mutates the
   *ML environment*, not theory *data*, something no "theory -> theory"
   function can express at all. Confirmed directly in
   "Pure/Isar/toplevel.ML": "Toplevel.theory"/"Toplevel.generic_theory" each
   *append one alternative* action to a transition's own "trans: trans list"
   field ("primitive transitions (union)") - chaining several such
   already-lifted functions with "#>"/"o" does *not* run them in sequence,
   only the first applicable one ever fires - so every antiquotation action
   must be folded together as a plain "Context.generic -> Context.generic"
   function (ordinary composition) *before* ever being lifted to
   "Toplevel.transition -> Toplevel.transition", and that lift must happen
   exactly once, at the outermost point (C11.thy's own "c11"/"c11_file"
   command registrations), not per handler. *)
type 'a type_antiq_fun0 = 'a * pos C_Ast.root * int -> (string * pos) -> Context.generic -> Context.generic

datatype cenv = mk of {idents  : ident_kind Symtab.table,
                       types   : type_ident Symtab.table,
                       c_antiq : (cenv type_antiq_fun0) Symtab.table,
                       predefined_envs : (pos * (cenv -> cenv)) Symtab.table,
                       units   : int} \<comment> \<open>used for numbering translation units internally.\<close>

type type_antiq_fun = cenv type_antiq_fun0

(* Recaptures a handler written the simpler, "theory -> theory" way (every
   handler in this project, before this round) as a genuine "type_antiq_fun0"
   - exactly the idiom "Pure/ML/ml_file.ML" itself uses for its own "provide"
   step ("Context.mapping provide (Local_Theory.background_theory provide)"),
   confirmed by reading that file during this project's own Isabelle2026 port
   earlier this session. "local_theory" is "Proof.context" itself (a standard
   Isabelle/Pure type synonym), so "Local_Theory.background_theory f" is
   already usable directly as "Context.mapping"'s second,
   "Proof.context -> Proof.context" argument. *)
fun lift_theory_antiq (f : 'a * pos C_Ast.root * int -> (string * pos) -> theory -> theory)
    : 'a * pos C_Ast.root * int -> (string * pos) -> Context.generic -> Context.generic =
  fn args => fn body => Context.mapping (f args body) (Local_Theory.background_theory (f args body))

(* "predefined_envs" holds, per header name (\<^verbatim>\<open>c11_predef\<close>'s own bracketed
   label, e.g. \<open>"stdio.h"\<close>), a pair of the reusable *effect* that header's
   own declarations have on an arbitrary "cenv" - captured once, when
   \<^verbatim>\<open>c11_predef\<close> itself is walked, as a plain function rather than applied
   there and then discarded, precisely so a *later* \<open>#include <header>\<close>
   (\<^verbatim>\<open>AnaEval.walk_pp_directive\<close>'s \<open>CPPInclude\<close> case) can re-apply the very
   same effect to whatever "cenv" is current at that point - the mechanism
   that actually connects \<open>#include\<close> to something, instead of it staying
   purely syntactic - together with the position of \<^verbatim>\<open>c11_predef\<close>'s own
   header-name token, so a later \<open>#include <header>\<close> can hyperlink back to
   it (matching \<open>report_use\<close>'s own "declared here, used there" style, for
   the header-name "namespace"). \<^verbatim>\<open>c11_predef\<close> itself does *not* also
   register the declared names directly into "idents"/"types" - only
   "predefined_envs" changes when it runs; a name it declares is not yet in
   scope anywhere until some \<open>#include\<close> actually pulls it in, matching
   real C. *)
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
   diagnosed in "C11_AnaEval.thy" ("report_use"/"report_decl"/"name_range").
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

(* The verbatim source text of every "c11"-family fragment, keyed by the very
   same "ast_store_key" as "Ast_Store" itself (updated alongside it, in
   "store_root", so the two tables never drift apart) - kept as a *separate*
   sibling table rather than folded into "Ast_Store"'s own value type, so
   every existing "get_ast" caller (C11_AnaEval.thy's header hyperlink,
   C11_Tests.thy's own tests) keeps matching on a bare "Position.T C_Ast.root"
   and does not have to unpack a pair it never wanted. Exists purely for
   "c11_export_h"/"c11_export_c [verbatim]" (C11.thy): a user may want their
   own original indentation/formatting back, not this project's own
   admittedly "simple" pretty-printer's ("C_Ast.pp_root") rendering of it. *)
structure Source_Store = Generic_Data
  (type T = string Symtab.table
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

(* Stores "root" - together with its own verbatim source "text", the exact
   cartouche/file text it was parsed from ("Input.text_of source" at every
   call site) - under a fresh unit number for "thy", bumping CEnv's counter.
   Returns the store key (for user-facing reporting) and the updated theory. *)
fun store_root (root : Position.T C_Ast.root) (text : string) thy =
    let
      val mk {idents, types, c_antiq, predefined_envs, units} = get (Context.Theory thy)
      val key = ast_store_key thy units
      val cenv' = mk {idents = idents, types = types, c_antiq = c_antiq,
                       predefined_envs = predefined_envs, units = units + 1}
      val thy' = thy
        |> Context.theory_map (put cenv')
        |> Context.theory_map (Ast_Store.map (Symtab.update (key, root)))
        |> Context.theory_map (Source_Store.map (Symtab.update (key, text)))
    in (key, thy') end

fun get_ast key thy =
    let val store = Ast_Store.get (Context.Theory thy)
    in  Symtab.lookup store key end

(* The verbatim source text stored alongside "key"'s own AST (see
   "Source_Store" above) - always present exactly when "get_ast key thy" is
   "SOME _", since "store_root" is the only way either table is ever written
   and it always writes both under the same key in the same call. *)
fun get_source key thy =
    let val store = Source_Store.get (Context.Theory thy)
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

(* Registers "header"'s own reusable "cenv -> cenv" effect, together with
   "pos" (the "c11_predef [header] ..." command's own header-name token
   position - see the note on "predefined_envs" above) - the
   "predefined_envs" analogue of "store_antiq"/"get_antiq". Deliberately
   does *not* touch "idents"/"types"/"c_antiq" at all: registering a
   header's effect is not the same as applying it - that only happens via a
   later "#include". *)
fun store_predefined_env (header, pos, f) thy =
    let
       val mk {idents, types, c_antiq, predefined_envs, units} = get (Context.Theory thy)
       val predefined_envs' = Symtab.update (header, (pos, f)) predefined_envs
       val cenv' = mk {idents = idents, types = types, c_antiq = c_antiq,
                        predefined_envs = predefined_envs', units = units}
    in thy |> Context.theory_map (put cenv')
    end

fun get_predefined_env header thy =
    let
       val mk {predefined_envs, ...} = get (Context.Theory thy)
    in Symtab.lookup predefined_envs header end

(* Backs the "set_cenv_default"/"reset_cenv" commands (C11.thy): lets a
   theory nominate its own "cenv" snapshot, at whatever point in the
   document it chooses, as the value "reset_cenv" later restores - e.g.
   right after the standard antiquotation handlers are registered
   (C11_AnaEval.thy's own "setup"s), or later still, once a downstream theory
   has also predefined the headers it wants known by default. A genuinely
   separate "Generic_Data" registry, not a field folded into "cenv" itself
   (which would make every snapshot recursively carry a copy of itself) -
   "NONE" until "set_cenv_default" is first used, at which point
   "reset_cenv" restores exactly that snapshot; used before that, it falls
   back to "empty_cenv", matching "reset" being meaningful even for a
   theory that never bothered to nominate a richer default. "merge" keeps
   whichever side already has a snapshot (arbitrarily the left, on the rare
   case both do - the two would only genuinely differ if two branches of a
   theory-merge graph each called "set_cenv_default" with different
   content, a corner case no more resolvable "correctly" here than
   "merge_cenv"'s own key-collision tie-break above is). *)
structure Default_Env = Generic_Data
  (type T = cenv option
   val empty = NONE
   val merge = fn (a, b) => if is_some a then a else b)

fun set_cenv_default thy = Context.theory_map (Default_Env.put (SOME (get (Context.Theory thy)))) thy

fun reset_cenv thy =
    let val default = case Default_Env.get (Context.Theory thy) of SOME c => c | NONE => empty_cenv
    in Context.theory_map (put default) thy end

end
\<close>


end
