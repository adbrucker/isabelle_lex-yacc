(******************************************************************************
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

theory AdaSpark_Env
  imports "AdaSpark_Ast"
begin

section\<open>The AEnv Environment: storing Ast's and Environments\<close>

text\<open>
  \<^verbatim>\<open>AEnv\<close> is the AdaSpark counterpart of \<^verbatim>\<open>REnv\<close> (\<^verbatim>\<open>MicroRust_Env.thy\<close>), \<^verbatim>\<open>SEnv\<close>,
  \<^verbatim>\<open>OEnv\<close> and \<^verbatim>\<open>CEnv\<close>: the environment and AST-store infrastructure shared by
  every \<open>adaspark\<close>-family command and by \<^verbatim>\<open>AnaEval\<close> (the \<open>analyse_and_eval\<close> pass,
  in \<^verbatim>\<open>AdaSpark_AnaEval.thy\<close>). It bundles the same plain \<^verbatim>\<open>Generic_Data\<close>
  registries behind one structure: \<^verbatim>\<open>Env\<close> holds the symbolic environment -
  \<open>names\<close> (the declared names) and \<open>ada_antiq\<close> (registered antiquotation
  handlers) - plus the running \<open>units\<close> counter that gives every AST this theory
  stores a fresh, per-theory sequence number; \<^verbatim>\<open>Ast_Store\<close> maps \<open>(theory_name,
  unit_number)\<close> to the parsed \<^verbatim>\<open>Position.T root\<close>; \<^verbatim>\<open>Source_Store\<close> keeps each
  fragment's verbatim source text. \<^verbatim>\<open>Backend\<close> is the semantic-backend hook, as in
  the other front-ends.

  What is specific to Ada: there is \<^emph>\<open>one\<close> name space, as in the language itself
  - an object, a type, a subprogram, a package, an exception and an enumeration
  literal are all just names, and an overloaded name has one entry, the latest
  declaration. Ada is case insensitive: the table is keyed by the \<^emph>\<open>lower-case\<close>
  name; a declaration or use is reported with the spelling it has in the source.
  The entities a package \<open>P\<close> declares are also entered under their \<^emph>\<open>qualified\<close>
  name (\<open>p.x\<close>), so that the body of the package, and a selected name \<open>P.X\<close>
  elsewhere, can find them. A name that is declared by a \<open>with\<close> clause is not
  recorded (the unit it names is not seen by this pass), and a name that
  resolves nowhere is \<^emph>\<open>not\<close> marked as an error (see \<^verbatim>\<open>AdaSpark_AnaEval.thy\<close>).
\<close>
ML\<open>
structure AEnv = struct

type pos = Position.T

(* What a name was declared as. The payload is always the declaring
   occurrence's own position (every declared name is an "ident" carrying one),
   which is all hyperlinking needs. *)
datatype ident_kind = Obj
  of pos   (* a variable, or a loop or quantifier variable *)
                    | Const    of pos   (* a constant or a number *)
                    | Param    of pos   (* a formal parameter *)
                    | Typ      of pos   (* a type or subtype *)
                    | Lit      of pos   (* an enumeration literal *)
                    | Proc     of pos   (* a procedure *)
                    | Func     of pos   (* a function *)
                    | Pack     of pos   (* a package *)
                    | Exn      of pos   (* an exception *)
                    | Comp     of pos   (* a record component, a discriminant *)
                    | Label    of pos   (* a loop or block name *)

fun pos_of_kind k = (case k of
    Obj p => p | Const p => p | Param p => p | Typ p => p | Lit p => p
  | Proc p => p | Func p => p | Pack p => p | Exn p => p | Comp p => p
  | Label p => p)

fun describe_kind k = (case k of
    Obj _ => "AdaSpark object" | Const _ => "AdaSpark constant"
  | Param _ => "AdaSpark parameter" | Typ _ => "AdaSpark type"
  | Lit _ => "AdaSpark enumeration literal" | Proc _ => "AdaSpark procedure"
  | Func _ => "AdaSpark function" | Pack _ => "AdaSpark package"
  | Exn _ => "AdaSpark exception" | Comp _ => "AdaSpark component"
  | Label _ => "AdaSpark label")

(* The handler's result is "Context.generic -> Context.generic", not "theory ->
   theory", for the same reason as in C11_Env.thy (an "ML" antiquotation has to
   mutate the ML environment, which no theory function can express);
   "lift_theory_antiq" recaptures the simpler kind. The "root" a handler
   receives is the antiquotation's already *resolved* context (its "[navi]"
   bracket interpreted against the closest-surrounding-context stack, see
   "AnaEval.select_ast"). *)
type 'a type_antiq_fun0 =
  'a * pos AdaSpark_Ast.root * int -> (string * pos) -> Context.generic
    -> Context.generic

datatype aenv = mk of {names : ident_kind Symtab.table,
                       ada_antiq : (aenv type_antiq_fun0) Symtab.table,
                       units : int}
  \<comment> \<open>"units" numbers the program units internally.\<close>

type type_antiq_fun = aenv type_antiq_fun0

fun lift_theory_antiq
  (f : 'a * pos AdaSpark_Ast.root * int -> (string * pos) -> theory -> theory)
    : 'a * pos AdaSpark_Ast.root * int -> (string * pos) -> Context.generic
      -> Context.generic =
  fn args => fn body =>
    Context.mapping (f args body) (Local_Theory.background_theory (f args body))

val empty_aenv =
  mk {names = Symtab.empty, ada_antiq =
      Symtab.empty, units = 0}

(* Merging must not reset to empty (Isabelle forks and merges theory state
   routinely during live editing - see the same note on "merge_cenv" in
   C11_Env.thy); "units" takes the larger counter so a merge can never re-issue
   an already-used "Ast_Store" key. *)
fun merge_aenv (mk {names = i1, ada_antiq = a1, units = u1},
                mk {names = i2, ada_antiq = a2, units = u2}) =
  mk {names = Symtab.merge (K true) (i1, i2),
      ada_antiq = Symtab.merge (K true) (a1, a2),
      units = Int.max (u1, u2)}

structure Env = Generic_Data
  (type T = aenv
   val empty = empty_aenv
   val merge = merge_aenv)

structure Ast_Store = Generic_Data
  (type T = (Position.T AdaSpark_Ast.root) Symtab.table
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
fun store_root (root : Position.T AdaSpark_Ast.root) (text : string) thy =
    let
      val mk {names, ada_antiq, units} = get (Context.Theory thy)
      val key = ast_store_key thy units
      val aenv' =
        mk {names = names, ada_antiq = ada_antiq, units = units + 1}
      val thy' = thy
        |> Context.theory_map (put aenv')
        |> Context.theory_map (Ast_Store.map (Symtab.update (key, root)))
        |> Context.theory_map (Source_Store.map (Symtab.update (key, text)))
    in (key, thy') end

fun get_ast key thy = Symtab.lookup (Ast_Store.get (Context.Theory thy)) key

fun get_source key thy =
  Symtab.lookup (Source_Store.get (Context.Theory thy)) key

fun store_antiq (name, antiq_fun) thy =
    let
       val mk {names, ada_antiq, units} = get (Context.Theory thy)
       val aenv' =
         mk {names = names,
             ada_antiq = Symtab.update (name, antiq_fun) ada_antiq,
             units = units}
    in thy |> Context.theory_map (put aenv') end

fun get_antiq name thy =
    let val mk {ada_antiq, ...} = get (Context.Theory thy)
    in Symtab.lookup ada_antiq name end

(* The semantic-backend hook, as in C11_Env.thy (see the note on "Backend"
   there): "full_eval_and_store" (AdaSpark.thy) calls the function stored here,
   on the parsed root and the theory it has just stored that root into, as the
   last step of every "adaspark"/"adaspark_body"/"adaspark_file". The default
   is "K I"; "setup_backend" (AdaSpark.thy) installs another one. A separate
   registry, not a field of "aenv": "reset_aenv" resets what has been declared,
   not which backend is installed. "NONE" stands for the default, so that
   "merge" is well defined for a function type. *)
type backend = pos AdaSpark_Ast.root -> theory -> theory

structure Backend = Generic_Data
  (type T = backend option
   val empty = NONE
   val merge = fn (a, b) => if is_some a then a else b)

fun get_backend thy : backend =
  the_default (K I) (Backend.get (Context.Theory thy))

fun set_backend (f : backend) = Context.theory_map (Backend.put (SOME f))

fun reset_backend thy = Context.theory_map (Backend.put NONE) thy

(* "set_aenv_default"/"reset_aenv" (AdaSpark.thy): a theory nominates its own
   snapshot as what "reset_aenv" later restores; a separate registry, not a
   field of "aenv" itself, which would make every snapshot carry a copy of
   itself. *)
structure Default_Env = Generic_Data
  (type T = aenv option
   val empty = NONE
   val merge = fn (a, b) => if is_some a then a else b)

fun set_aenv_default thy =
  Context.theory_map (Default_Env.put (SOME (get (Context.Theory thy)))) thy

fun reset_aenv thy =
    let val default = case Default_Env.get (Context.Theory thy) of SOME c =>
      c | NONE => empty_aenv
    in Context.theory_map (put default) thy end

end
\<close>

end
