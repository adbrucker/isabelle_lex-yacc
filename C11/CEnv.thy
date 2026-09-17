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
  structure: \<^verbatim>\<open>Env\<close> holds the (still largely unused - \<open>types\<close>/\<open>c_antiq\<close> are
  placeholders for a future symbol table and antiquotation-command registry) symbolic
  environment, plus the running \<open>units\<close> counter that gives every AST this theory
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
                    | Enum
                    | Parameter of (pos C_Ast.cDeclaration) (* really  ? *)
                    | Cpp_const of (pos C_Ast.cDeclaration)
                    | Cpp_macro of (pos C_Ast.ident list * pos C_Ast.cDeclaration)

datatype type_ident = NOT_YET_DEFINED

type 'a type_antiq_fun = 'a * pos C_Ast.root * int -> string ->  theory -> theory

datatype cenv = mk of {idents  : ident_kind Symtab.table,
                       types   : type_ident Symtab.table,
                       c_antiq : (cenv type_antiq_fun) Symtab.table,
                       units   : int} \<comment> \<open>used for numbering translation units internally.\<close>

val empty_cenv = mk{idents  = Symtab.empty,
                  types   = Symtab.empty ,
                  c_antiq = Symtab.empty,
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
fun merge_cenv (mk {idents = i1, types = t1, c_antiq = a1, units = u1},
                mk {idents = i2, types = t2, c_antiq = a2, units = u2}) =
  mk {idents = Symtab.merge (K true) (i1, i2),
      types = Symtab.merge (K true) (t1, t2),
      c_antiq = Symtab.merge (K true) (a1, a2),
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
      val mk {idents, types, c_antiq, units} = get (Context.Theory thy)
      val key = ast_store_key thy units
      val cenv' = mk {idents = idents, types = types, c_antiq = c_antiq, units = units + 1}
      val thy' = thy
        |> Context.theory_map (put cenv')
        |> Context.theory_map (Ast_Store.map (Symtab.update (key, root)))
    in (key, thy') end

fun get_ast key thy =
    let val store = Ast_Store.get (Context.Theory thy)
    in  Symtab.lookup store key end

fun store_antiq (name, antiq_fun) thy =
    let
       val mk {idents, types, c_antiq, units} = get (Context.Theory thy)
       val c_antiq' = Symtab.update(name, antiq_fun) c_antiq
       val cenv' = mk {idents = idents, types = types, c_antiq = c_antiq', units = units}
    in thy |> Context.theory_map (put cenv')
    end

fun get_antiq name thy =
    let
       val mk {c_antiq, ...} = get (Context.Theory thy)
    in Symtab.lookup c_antiq name end

end
\<close>


end
