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

theory Occam2_Env
  imports "Occam2_Ast"
begin

section\<open>The OEnv Environment: storing Ast's and Environments\<close>

text\<open>
  \<^verbatim>\<open>OEnv\<close> is the occam 2 counterpart of \<^verbatim>\<open>CEnv\<close> (\<^verbatim>\<open>C11_Env.thy\<close>): the environment and
  AST-store infrastructure shared by every \<open>occam2\<close>-family command and by \<^verbatim>\<open>AnaEval\<close>
  (the \<open>analyse_and_eval\<close> pass, in \<^verbatim>\<open>Occam2_AnaEval.thy\<close>). It bundles the same plain
  \<^verbatim>\<open>Generic_Data\<close> registries behind one structure: \<^verbatim>\<open>Env\<close> holds the symbolic
  environment - \<open>idents\<close> (every declared name), \<open>occam_antiq\<close> (registered antiquotation
  handlers) - plus the running \<open>units\<close> counter that gives every AST this theory stores a
  fresh, per-theory sequence number; \<^verbatim>\<open>Ast_Store\<close> maps \<open>(theory_name, unit_number)\<close> -
  encoded as one \<^verbatim>\<open>Symtab\<close> key - to the parsed \<^verbatim>\<open>Position.T root\<close>; \<^verbatim>\<open>Source_Store\<close>,
  keyed the same way, keeps each fragment's verbatim source text.

  Differences to \<^verbatim>\<open>CEnv\<close>, all consequences of the language rather than of the
  design: occam has \<^emph>\<open>one\<close> name space (variables, channels, abbreviations, procedures,
  functions, protocols and protocol tags are all just "names" in the manual's sense),
  so there is no separate tag table like C's \<open>types\<close>; and the grammar has no
  \<open>#include\<close>-like construct, so there is no \<open>predefined_envs\<close> table either - a
  library-style unit (specifications only, see \<open>Specs\<close> in \<^verbatim>\<open>occam2_ast.ML\<close>) is
  instead \<^emph>\<open>itself\<close> the way to make names visible to later fragments, because the
  names a \<open>Specs\<close> unit declares stay in the stored \<open>idents\<close> table.
\<close>
ML\<open>
structure OEnv = struct

type pos = Position.T

(* What a name was declared as. The payload is always the declaring
   occurrence's own position (every declared name is an "ident" carrying one),
   which is all hyperlinking needs. *)
datatype ident_kind = Variable   of pos   (* "INT x:", also array variables *)
                    | Channel    of pos   (* "CHAN OF p c:", also TIMER and PORT *)
                    | Abbrev     of pos   (* "x IS e:", "VAL x IS e:", RETYPES *)
                    | Param      of pos   (* a formal parameter of a PROC/FUNCTION *)
                    | Replicator of pos   (* the index of "SEQ i = 0 FOR n" *)
                    | Proc       of pos
                    | Function   of pos
                    | Protocol   of pos
                    | Tag        of pos   (* a "PROTOCOL p CASE" tag *)

fun pos_of_kind k = (case k of
    Variable p => p | Channel p => p | Abbrev p => p | Param p => p
  | Replicator p => p | Proc p => p | Function p => p | Protocol p => p | Tag p => p)

fun describe_kind k = (case k of
    Variable _ => "occam 2 variable" | Channel _ => "occam 2 channel"
  | Abbrev _ => "occam 2 abbreviation" | Param _ => "occam 2 parameter"
  | Replicator _ => "occam 2 replicator index" | Proc _ => "occam 2 procedure"
  | Function _ => "occam 2 function" | Protocol _ => "occam 2 protocol"
  | Tag _ => "occam 2 protocol tag")

(* The handler's result is "Context.generic -> Context.generic", not
   "theory -> theory", for the same reason as in C11_Env.thy (an "ML"
   antiquotation has to mutate the ML environment, which no theory function can
   express); "lift_theory_antiq" recaptures the simpler kind. The "root" a handler
   receives is the antiquotation's already *resolved* context (its "[navi]"
   bracket interpreted against the closest-surrounding-context stack, see
   "AnaEval.select_ast"). *)
type 'a type_antiq_fun0 =
  'a * pos Occam2_Ast.root * int -> (string * pos) -> Context.generic -> Context.generic

datatype oenv = mk of {idents : ident_kind Symtab.table,
                       occam_antiq : (oenv type_antiq_fun0) Symtab.table,
                       units : int} \<comment> \<open>used for numbering program units internally.\<close>

type type_antiq_fun = oenv type_antiq_fun0

fun lift_theory_antiq (f : 'a * pos Occam2_Ast.root * int -> (string * pos) -> theory -> theory)
    : 'a * pos Occam2_Ast.root * int -> (string * pos) -> Context.generic -> Context.generic =
  fn args => fn body => Context.mapping (f args body) (Local_Theory.background_theory (f args body))

val empty_oenv = mk {idents = Symtab.empty, occam_antiq = Symtab.empty, units = 0}

(* Merging must not reset to empty (Isabelle forks and merges theory state
   routinely during live editing - see the same note on "merge_cenv" in
   C11_Env.thy); "units" takes the larger counter so a merge can never re-issue
   an already-used "Ast_Store" key. *)
fun merge_oenv (mk {idents = i1, occam_antiq = a1, units = u1},
                mk {idents = i2, occam_antiq = a2, units = u2}) =
  mk {idents = Symtab.merge (K true) (i1, i2),
      occam_antiq = Symtab.merge (K true) (a1, a2),
      units = Int.max (u1, u2)}

structure Env = Generic_Data
  (type T = oenv
   val empty = empty_oenv
   val merge = merge_oenv)

structure Ast_Store = Generic_Data
  (type T = (Position.T Occam2_Ast.root) Symtab.table
   val  empty = Symtab.empty
   val  merge = Symtab.merge (K true))

structure Source_Store = Generic_Data
  (type T = string Symtab.table
   val  empty = Symtab.empty
   val  merge = Symtab.merge (K true))

(* Deliberately no bare "map": see the note in C11_Env.thy. *)
val get = Env.get
val put = Env.put

fun ast_store_key thy unit_no =
  Context.theory_name {long = false} thy ^ "#" ^ Int.toString unit_no

(* Stores "root" with its verbatim source "text" under a fresh unit number for
   "thy", bumping the counter. Returns the key and the updated theory. *)
fun store_root (root : Position.T Occam2_Ast.root) (text : string) thy =
    let
      val mk {idents, occam_antiq, units} = get (Context.Theory thy)
      val key = ast_store_key thy units
      val oenv' = mk {idents = idents, occam_antiq = occam_antiq, units = units + 1}
      val thy' = thy
        |> Context.theory_map (put oenv')
        |> Context.theory_map (Ast_Store.map (Symtab.update (key, root)))
        |> Context.theory_map (Source_Store.map (Symtab.update (key, text)))
    in (key, thy') end

fun get_ast key thy = Symtab.lookup (Ast_Store.get (Context.Theory thy)) key

fun get_source key thy = Symtab.lookup (Source_Store.get (Context.Theory thy)) key

fun store_antiq (name, antiq_fun) thy =
    let
       val mk {idents, occam_antiq, units} = get (Context.Theory thy)
       val oenv' = mk {idents = idents, occam_antiq = Symtab.update (name, antiq_fun) occam_antiq,
                       units = units}
    in thy |> Context.theory_map (put oenv') end

fun get_antiq name thy =
    let val mk {occam_antiq, ...} = get (Context.Theory thy)
    in Symtab.lookup occam_antiq name end

(* "set_oenv_default"/"reset_oenv" (Occam2.thy): a theory nominates its own
   snapshot as what "reset_oenv" later restores; a separate registry, not a
   field of "oenv" itself, which would make every snapshot carry a copy of itself. *)
structure Default_Env = Generic_Data
  (type T = oenv option
   val empty = NONE
   val merge = fn (a, b) => if is_some a then a else b)

fun set_oenv_default thy = Context.theory_map (Default_Env.put (SOME (get (Context.Theory thy)))) thy

fun reset_oenv thy =
    let val default = case Default_Env.get (Context.Theory thy) of SOME c => c | NONE => empty_oenv
    in Context.theory_map (put default) thy end

end
\<close>

end
