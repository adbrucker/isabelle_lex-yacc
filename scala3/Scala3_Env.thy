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

theory Scala3_Env
  imports "Scala3_Ast"
begin

section\<open>The SEnv Environment: storing Ast's and Environments\<close>

text\<open>
  \<^verbatim>\<open>SEnv\<close> is the Scala 3 counterpart of \<^verbatim>\<open>OEnv\<close> (\<^verbatim>\<open>Occam2_Env.thy\<close>) and \<^verbatim>\<open>CEnv\<close>
  (\<^verbatim>\<open>C11_Env.thy\<close>): the environment and AST-store infrastructure shared by every \<open>scala3\<close>-family
  command and by \<^verbatim>\<open>AnaEval\<close> (the \<open>analyse_and_eval\<close> pass, in \<^verbatim>\<open>Scala3_AnaEval.thy\<close>). It bundles the
  same plain \<^verbatim>\<open>Generic_Data\<close> registries behind one structure: \<^verbatim>\<open>Env\<close> holds the symbolic
  environment - \<open>terms\<close> and \<open>types\<close> (the declared names of the two name spaces), \<open>scala_antiq\<close>
  (registered antiquotation handlers) - plus the running \<open>units\<close> counter that gives every AST
  this theory stores a fresh, per-theory sequence number; \<^verbatim>\<open>Ast_Store\<close> maps \<open>(theory_name,
  unit_number)\<close> to the parsed \<^verbatim>\<open>Position.T root\<close>; \<^verbatim>\<open>Source_Store\<close> keeps each fragment's verbatim
  source text. \<^verbatim>\<open>Backend\<close> is the semantic-backend hook, as in C11 and occam 2.

  What is specific to Scala: there are \<^emph>\<open>two\<close> name spaces. A class, trait, enum or type alias lives
  in \<open>types\<close>, a value, variable, method, parameter, pattern variable, object or enum case in
  \<open>terms\<close>; a \<open>case class\<close> (and an \<open>enum\<close>, and an \<open>object\<close>'s companion) declares a name in
  both. A name that is declared by an \<open>import\<close> is recorded at its selector. As a Scala name
  routinely comes from the standard library, an import wildcard or an inherited member, a name
  that resolves nowhere is \<^emph>\<open>not\<close> marked as an error (see \<^verbatim>\<open>Scala3_AnaEval.thy\<close>).
\<close>
ML\<open>
structure SEnv = struct

type pos = Position.T

(* What a name was declared as. The payload is always the declaring
   occurrence's own position (every declared name is an "ident" carrying one),
   which is all hyperlinking needs. *)
datatype ident_kind = Val       of pos   (* "val x" *)
                    | Var       of pos   (* "var x" *)
                    | Def       of pos   (* "def f" *)
                    | Param     of pos   (* a parameter of a method, lambda or constructor *)
                    | Local     of pos   (* a pattern variable, a generator's or a case clause's *)
                    | Object    of pos
                    | Class     of pos   (* class, case class, trait, enum, type alias, type parameter *)
                    | Enum_case of pos
                    | Given     of pos
                    | Import    of pos   (* a name brought in by "import" *)

fun pos_of_kind k = (case k of
    Val p => p | Var p => p | Def p => p | Param p => p | Local p => p | Object p => p
  | Class p => p | Enum_case p => p | Given p => p | Import p => p)

fun describe_kind k = (case k of
    Val _ => "Scala 3 value" | Var _ => "Scala 3 variable" | Def _ => "Scala 3 method"
  | Param _ => "Scala 3 parameter" | Local _ => "Scala 3 pattern variable"
  | Object _ => "Scala 3 object" | Class _ => "Scala 3 class or type"
  | Enum_case _ => "Scala 3 enum case" | Given _ => "Scala 3 given" | Import _ => "Scala 3 imported name")

(* The handler's result is "Context.generic -> Context.generic", not
   "theory -> theory", for the same reason as in C11_Env.thy (an "ML"
   antiquotation has to mutate the ML environment, which no theory function can
   express); "lift_theory_antiq" recaptures the simpler kind. The "root" a handler
   receives is the antiquotation's already *resolved* context (its "[navi]"
   bracket interpreted against the closest-surrounding-context stack, see
   "AnaEval.select_ast"). *)
type 'a type_antiq_fun0 =
  'a * pos Scala3_Ast.root * int -> (string * pos) -> Context.generic -> Context.generic

datatype senv = mk of {terms : ident_kind Symtab.table,
                       types : ident_kind Symtab.table,
                       scala_antiq : (senv type_antiq_fun0) Symtab.table,
                       units : int} \<comment> \<open>used for numbering program units internally.\<close>

type type_antiq_fun = senv type_antiq_fun0

fun lift_theory_antiq (f : 'a * pos Scala3_Ast.root * int -> (string * pos) -> theory -> theory)
    : 'a * pos Scala3_Ast.root * int -> (string * pos) -> Context.generic -> Context.generic =
  fn args => fn body => Context.mapping (f args body) (Local_Theory.background_theory (f args body))

val empty_senv = mk {terms = Symtab.empty, types = Symtab.empty, scala_antiq = Symtab.empty, units = 0}

(* Merging must not reset to empty (Isabelle forks and merges theory state
   routinely during live editing - see the same note on "merge_cenv" in
   C11_Env.thy); "units" takes the larger counter so a merge can never re-issue
   an already-used "Ast_Store" key. *)
fun merge_senv (mk {terms = i1, types = t1, scala_antiq = a1, units = u1},
                mk {terms = i2, types = t2, scala_antiq = a2, units = u2}) =
  mk {terms = Symtab.merge (K true) (i1, i2),
      types = Symtab.merge (K true) (t1, t2),
      scala_antiq = Symtab.merge (K true) (a1, a2),
      units = Int.max (u1, u2)}

structure Env = Generic_Data
  (type T = senv
   val empty = empty_senv
   val merge = merge_senv)

structure Ast_Store = Generic_Data
  (type T = (Position.T Scala3_Ast.root) Symtab.table
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
fun store_root (root : Position.T Scala3_Ast.root) (text : string) thy =
    let
      val mk {terms, types, scala_antiq, units} = get (Context.Theory thy)
      val key = ast_store_key thy units
      val senv' = mk {terms = terms, types = types, scala_antiq = scala_antiq, units = units + 1}
      val thy' = thy
        |> Context.theory_map (put senv')
        |> Context.theory_map (Ast_Store.map (Symtab.update (key, root)))
        |> Context.theory_map (Source_Store.map (Symtab.update (key, text)))
    in (key, thy') end

fun get_ast key thy = Symtab.lookup (Ast_Store.get (Context.Theory thy)) key

fun get_source key thy = Symtab.lookup (Source_Store.get (Context.Theory thy)) key

fun store_antiq (name, antiq_fun) thy =
    let
       val mk {terms, types, scala_antiq, units} = get (Context.Theory thy)
       val senv' = mk {terms = terms, types = types, scala_antiq = Symtab.update (name, antiq_fun) scala_antiq,
                       units = units}
    in thy |> Context.theory_map (put senv') end

fun get_antiq name thy =
    let val mk {scala_antiq, ...} = get (Context.Theory thy)
    in Symtab.lookup scala_antiq name end

(* The semantic-backend hook, as in C11_Env.thy (see the note on "Backend" there):
   "full_eval_and_store" (Scala3.thy) calls the function stored here, on the parsed
   root and the theory it has just stored that root into, as the last step of every
   "occam2"/"occam2_file". The default is "K I"; "setup_backend" (Scala3.thy)
   installs another one. A separate registry, not a field of "senv": "reset_senv"
   resets what has been declared, not which backend is installed. "NONE" stands for
   the default, so that "merge" is well defined for a function type. *)
type backend = pos Scala3_Ast.root -> theory -> theory

structure Backend = Generic_Data
  (type T = backend option
   val empty = NONE
   val merge = fn (a, b) => if is_some a then a else b)

fun get_backend thy : backend = the_default (K I) (Backend.get (Context.Theory thy))

fun set_backend (f : backend) = Context.theory_map (Backend.put (SOME f))

fun reset_backend thy = Context.theory_map (Backend.put NONE) thy

(* "set_senv_default"/"reset_senv" (Scala3.thy): a theory nominates its own
   snapshot as what "reset_senv" later restores; a separate registry, not a
   field of "senv" itself, which would make every snapshot carry a copy of itself. *)
structure Default_Env = Generic_Data
  (type T = senv option
   val empty = NONE
   val merge = fn (a, b) => if is_some a then a else b)

fun set_senv_default thy = Context.theory_map (Default_Env.put (SOME (get (Context.Theory thy)))) thy

fun reset_senv thy =
    let val default = case Default_Env.get (Context.Theory thy) of SOME c => c | NONE => empty_senv
    in Context.theory_map (put default) thy end

end
\<close>

end
