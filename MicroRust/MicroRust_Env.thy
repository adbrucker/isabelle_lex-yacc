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

theory MicroRust_Env
  imports "MicroRust_Ast"
begin

section\<open>The REnv Environment: storing Ast's and Environments\<close>

text\<open>
  \<^verbatim>\<open>REnv\<close> is the MicroRust counterpart of \<^verbatim>\<open>SEnv\<close> (\<^verbatim>\<open>Scala3_Env.thy\<close>), \<^verbatim>\<open>OEnv\<close> (\<^verbatim>\<open>Occam2_Env.thy\<close>) and
  \<^verbatim>\<open>CEnv\<close> (\<^verbatim>\<open>C11_Env.thy\<close>): the environment and AST-store infrastructure shared by every
  \<open>microrust\<close>-family command and by \<^verbatim>\<open>AnaEval\<close> (the \<open>analyse_and_eval\<close> pass, in
  \<^verbatim>\<open>MicroRust_AnaEval.thy\<close>). It bundles the same plain \<^verbatim>\<open>Generic_Data\<close> registries behind one structure:
  \<^verbatim>\<open>Env\<close> holds the symbolic environment - \<open>terms\<close> and \<open>types\<close> (the declared names of the two name
  spaces), \<open>rust_antiq\<close> (registered antiquotation handlers) - plus the running \<open>units\<close> counter that
  gives every AST this theory stores a fresh, per-theory sequence number; \<^verbatim>\<open>Ast_Store\<close> maps
  \<open>(theory_name, unit_number)\<close> to the parsed \<^verbatim>\<open>Position.T root\<close>; \<^verbatim>\<open>Source_Store\<close> keeps each fragment's
  verbatim source text. \<^verbatim>\<open>Backend\<close> is the semantic-backend hook, as in the other front-ends.

  What is specific to Rust: there are \<^emph>\<open>two\<close> name spaces, as in Rust itself. A struct, enum, trait, type
  alias, module or type parameter lives in \<open>types\<close>; a function, constant, static, local variable,
  parameter or pattern variable in \<open>terms\<close>; a tuple or unit struct declares a name in both. A name that
  is declared by a \<open>use\<close> is recorded at its path segment. As a Rust name routinely comes from the
  prelude, a glob import or the standard library, a name that resolves nowhere is \<^emph>\<open>not\<close> marked as an
  error (see \<^verbatim>\<open>MicroRust_AnaEval.thy\<close>).
\<close>
ML\<open>
structure REnv = struct

type pos = Position.T

(* What a name was declared as. The payload is always the declaring
   occurrence's own position (every declared name is an "ident" carrying one),
   which is all hyperlinking needs. *)
datatype ident_kind = Local     of pos   (* a "let" or pattern variable, a "for" or closure variable *)
                    | Param     of pos   (* a parameter of a function *)
                    | Fn        of pos   (* "fn f" *)
                    | Const     of pos   (* "const X", and uRust's "const x = e;" *)
                    | Static    of pos
                    | Struct    of pos   (* struct, tuple/unit struct, union *)
                    | Enum      of pos
                    | Variant   of pos   (* an enum variant *)
                    | Trait     of pos
                    | Alias     of pos   (* "type A = .." *)
                    | Tparam    of pos   (* a generic parameter *)
                    | Mod       of pos
                    | Import    of pos   (* a name brought in by "use" *)

fun pos_of_kind k = (case k of
    Local p => p | Param p => p | Fn p => p | Const p => p | Static p => p | Struct p => p
  | Enum p => p | Variant p => p | Trait p => p | Alias p => p | Tparam p => p | Mod p => p
  | Import p => p)

fun describe_kind k = (case k of
    Local _ => "MicroRust variable" | Param _ => "MicroRust parameter" | Fn _ => "MicroRust function"
  | Const _ => "MicroRust constant" | Static _ => "MicroRust static" | Struct _ => "MicroRust struct"
  | Enum _ => "MicroRust enum" | Variant _ => "MicroRust enum variant" | Trait _ => "MicroRust trait"
  | Alias _ => "MicroRust type alias" | Tparam _ => "MicroRust generic parameter"
  | Mod _ => "MicroRust module" | Import _ => "MicroRust imported name")

(* The handler's result is "Context.generic -> Context.generic", not
   "theory -> theory", for the same reason as in C11_Env.thy (an "ML"
   antiquotation has to mutate the ML environment, which no theory function can
   express); "lift_theory_antiq" recaptures the simpler kind. The "root" a handler
   receives is the antiquotation's already *resolved* context (its "[navi]"
   bracket interpreted against the closest-surrounding-context stack, see
   "AnaEval.select_ast"). *)
type 'a type_antiq_fun0 =
  'a * pos MicroRust_Ast.root * int -> (string * pos) -> Context.generic -> Context.generic

datatype renv = mk of {terms : ident_kind Symtab.table,
                       types : ident_kind Symtab.table,
                       rust_antiq : (renv type_antiq_fun0) Symtab.table,
                       units : int} \<comment> \<open>used for numbering program units internally.\<close>

type type_antiq_fun = renv type_antiq_fun0

fun lift_theory_antiq (f : 'a * pos MicroRust_Ast.root * int -> (string * pos) -> theory -> theory)
    : 'a * pos MicroRust_Ast.root * int -> (string * pos) -> Context.generic -> Context.generic =
  fn args => fn body => Context.mapping (f args body) (Local_Theory.background_theory (f args body))

val empty_renv = mk {terms = Symtab.empty, types = Symtab.empty, rust_antiq = Symtab.empty, units = 0}

(* Merging must not reset to empty (Isabelle forks and merges theory state
   routinely during live editing - see the same note on "merge_cenv" in
   C11_Env.thy); "units" takes the larger counter so a merge can never re-issue
   an already-used "Ast_Store" key. *)
fun merge_renv (mk {terms = i1, types = t1, rust_antiq = a1, units = u1},
                mk {terms = i2, types = t2, rust_antiq = a2, units = u2}) =
  mk {terms = Symtab.merge (K true) (i1, i2),
      types = Symtab.merge (K true) (t1, t2),
      rust_antiq = Symtab.merge (K true) (a1, a2),
      units = Int.max (u1, u2)}

structure Env = Generic_Data
  (type T = renv
   val empty = empty_renv
   val merge = merge_renv)

structure Ast_Store = Generic_Data
  (type T = (Position.T MicroRust_Ast.root) Symtab.table
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
fun store_root (root : Position.T MicroRust_Ast.root) (text : string) thy =
    let
      val mk {terms, types, rust_antiq, units} = get (Context.Theory thy)
      val key = ast_store_key thy units
      val renv' = mk {terms = terms, types = types, rust_antiq = rust_antiq, units = units + 1}
      val thy' = thy
        |> Context.theory_map (put renv')
        |> Context.theory_map (Ast_Store.map (Symtab.update (key, root)))
        |> Context.theory_map (Source_Store.map (Symtab.update (key, text)))
    in (key, thy') end

fun get_ast key thy = Symtab.lookup (Ast_Store.get (Context.Theory thy)) key

fun get_source key thy = Symtab.lookup (Source_Store.get (Context.Theory thy)) key

fun store_antiq (name, antiq_fun) thy =
    let
       val mk {terms, types, rust_antiq, units} = get (Context.Theory thy)
       val renv' = mk {terms = terms, types = types, rust_antiq = Symtab.update (name, antiq_fun) rust_antiq,
                       units = units}
    in thy |> Context.theory_map (put renv') end

fun get_antiq name thy =
    let val mk {rust_antiq, ...} = get (Context.Theory thy)
    in Symtab.lookup rust_antiq name end

(* The semantic-backend hook, as in C11_Env.thy (see the note on "Backend" there):
   "full_eval_and_store" (MicroRust.thy) calls the function stored here, on the parsed
   root and the theory it has just stored that root into, as the last step of every
   "microrust"/"microrust_body"/"microrust_file". The default is "K I"; "setup_backend" (MicroRust.thy)
   installs another one. A separate registry, not a field of "renv": "reset_renv"
   resets what has been declared, not which backend is installed. "NONE" stands for
   the default, so that "merge" is well defined for a function type. *)
type backend = pos MicroRust_Ast.root -> theory -> theory

structure Backend = Generic_Data
  (type T = backend option
   val empty = NONE
   val merge = fn (a, b) => if is_some a then a else b)

fun get_backend thy : backend = the_default (K I) (Backend.get (Context.Theory thy))

fun set_backend (f : backend) = Context.theory_map (Backend.put (SOME f))

fun reset_backend thy = Context.theory_map (Backend.put NONE) thy

(* "set_renv_default"/"reset_renv" (MicroRust.thy): a theory nominates its own
   snapshot as what "reset_renv" later restores; a separate registry, not a
   field of "renv" itself, which would make every snapshot carry a copy of itself. *)
structure Default_Env = Generic_Data
  (type T = renv option
   val empty = NONE
   val merge = fn (a, b) => if is_some a then a else b)

fun set_renv_default thy = Context.theory_map (Default_Env.put (SOME (get (Context.Theory thy)))) thy

fun reset_renv thy =
    let val default = case Default_Env.get (Context.Theory thy) of SOME c => c | NONE => empty_renv
    in Context.theory_map (put default) thy end

end
\<close>

end
