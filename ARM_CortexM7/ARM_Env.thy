(******************************************************************************
 * Copyright (c) University of Paris-Saclay
 *
 * All rights reserved.
 *
 * Authors: Burkhart Wolff, Claude Sonnet 5.5
 *
 * This is an LLM-generated replication of the Isabelle/C version 2 design to
 * the programming language Java (language version 25). It provides an efficient
 * parser for Java, deeply integrated into the Isabelle/PIDE document model,
 * allowing external files as well as in-theory code-snippets which are
 * transparent to the underlying theory. It provides an API for the generated
 * AST’s, and an API to hook up semantic backends that compile these AST’s to
 * theory extensions in Isabelle/HOL. Members of the family come with a
 * Java-specific antiquotation mechanism allowing programmable links to the
 * semantic backends as necessary for support of program-annotations with HOL
 * formulas.
 *
 * This session is part of the Isabelle Programming Language Toolkit
 * (Isabelle/PLTk). The generation has been done with Claude Sonnet 5.5; while
 * the replicants come with a detailed (generated) test-suite for Java, I
 * expect that human users might find errors or inconsistencies; experience
 * reports and comments are therefore welcomed. The concrete and abstract
 * syntax, being generated from Isabelle/LexYacc specifications, should be easy
 * to modify and adapt.
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


theory ARM_Env
  imports "ARM_Ast"
begin

section\<open>The ARMEnv Environment: storing Ast's and Environments\<close>

text\<open>
  \<^verbatim>\<open>ARMEnv\<close> is the assembler counterpart of \<^verbatim>\<open>JEnv\<close> (\<^verbatim>\<open>Java_Env.thy\<close>) and of the environments of the
  other front-ends: the environment and AST-store infrastructure shared by every
  \<open>arm\<close>-family command and by \<^verbatim>\<open>AnaEval\<close> (the \<open>analyse_and_eval\<close> pass, in \<^verbatim>\<open>ARM_AnaEval.thy\<close>). It
  bundles the same plain \<^verbatim>\<open>Generic_Data\<close> registries behind one structure: \<^verbatim>\<open>Env\<close> holds the symbolic
  environment - \<open>names\<close> (the declared names), \<open>macros\<close> (the parameters of the declared macros),
  \<open>locals\<close> (the numeric labels of the unit being analysed) and \<open>arm_antiq\<close> (registered
  antiquotation handlers) - plus the running \<open>units\<close> counter that gives every AST this theory
  stores a fresh, per-theory sequence number; \<^verbatim>\<open>Ast_Store\<close> maps \<open>(theory_name, unit_number)\<close> to the
  parsed \<^verbatim>\<open>Position.T root\<close>; \<^verbatim>\<open>Source_Store\<close> keeps each fragment's verbatim source text. \<^verbatim>\<open>Backend\<close>
  is the semantic-backend hook, as in the other front-ends.

  What is specific to the assembler: it has \<^emph>\<open>namespaces\<close> of its own, kept apart by a prefix in
  the key of \<open>names\<close>. The \<^emph>\<open>symbols\<close> - labels (\<open>start:\<close>) and the symbols that \<open>=\<close>, \<open>.set\<close>,
  \<open>.equ\<close> and
  \<open>.comm\<close> define - are visible in the whole file whether they are defined before or after a use;
  a \<^emph>\<open>register alias\<close> (\<open>acc .req r4\<close>, prefix \<open>reg:\<close>) and a \<^emph>\<open>macro\<close> (prefix \<open>macro:\<close>) are
  visible from
  their definition on (and a macro of the name of an instruction hides the instruction); a
  \<^emph>\<open>macro parameter\<close> (prefix \<open>param:\<close>) is visible in the body of its macro, as \<^verbatim>\<open>\name\<close>. The
  numeric labels (\<open>1:\<close>, referred to as \<open>1b\<close> and \<open>1f\<close>) may be defined many times and are resolved by
  their position, from the list \<open>locals\<close>. A name that resolves nowhere is \<^emph>\<open>not\<close> marked as an error
  (see \<^verbatim>\<open>ARM_AnaEval.thy\<close>): it very often comes from another file, or from the linker.
\<close>
ML\<open>
structure ARMEnv = struct

type pos = Position.T

(* What a name was declared as. The payload is always the declaring occurrence's own position
   (every declared name is an "ident" carrying one), which is all hyperlinking needs. *)
datatype ident_kind = Label  of pos   (* a label *)
                    | Symbol of pos   (* a symbol defined by "=", ".set", ".equ", ".comm" *)
                    | Alias  of pos   (* a register alias, "name .req reg" *)
                    | Macro  of pos   (* a macro *)
                    | Param  of pos   (* a parameter of a macro, or the variable of ".irp" *)

fun pos_of_kind k = (case k of
    Label p => p | Symbol p => p | Alias p => p | Macro p => p | Param p => p)

fun describe_kind k = (case k of
    Label _ => "ARM label" | Symbol _ => "ARM symbol" | Alias _ => "ARM register alias"
  | Macro _ => "ARM macro" | Param _ => "ARM macro parameter")

(* The handler's result is "Context.generic -> Context.generic", not "theory -> theory", for the
   same reason as in C11_Env.thy (an "ML" antiquotation has to mutate the ML environment, which
   no theory function can express); "lift_theory_antiq" recaptures the simpler kind. The "root" a
   handler receives is the antiquotation's already *resolved* context (its "[navi]" bracket
   interpreted against the closest-surrounding-context stack, see "AnaEval.select_ast"). *)
type 'a type_antiq_fun0 =
  'a * pos ARM_Ast.root * int -> (string * pos) -> Context.generic -> Context.generic

datatype armenv = mk of {names : ident_kind Symtab.table,
                         macros : (string * pos) list Symtab.table,
                         locals : (string * pos) list,
                         arm_antiq : (armenv type_antiq_fun0) Symtab.table,
                         units : int}
  \<comment> \<open>"names" holds the declared names of all namespaces (see the prefixes above), "macros" the
      parameters of the macros (their names and the positions of their declarations; for the
      keyword arguments of a call), "locals" the numeric labels of the unit being analysed, by
      number, in the order of the text; "units" numbers the program units internally.\<close>

type type_antiq_fun = armenv type_antiq_fun0

fun lift_theory_antiq
  (f : 'a * pos ARM_Ast.root * int -> (string * pos) -> theory -> theory)
    : 'a * pos ARM_Ast.root * int -> (string * pos) -> Context.generic -> Context.generic =
  fn args => fn body =>
    Context.mapping (f args body) (Local_Theory.background_theory (f args body))

val empty_armenv =
  mk {names = Symtab.empty, macros = Symtab.empty, locals = [], arm_antiq = Symtab.empty,
      units = 0}

(* Merging must not reset to empty (Isabelle forks and merges theory state routinely during live
   editing - see the same note on "merge_cenv" in C11_Env.thy); "units" takes the larger counter
   so a merge can never re-issue an already-used "Ast_Store" key. *)
fun merge_armenv (mk {names = i1, macros = m1, locals = l1, arm_antiq = a1, units = u1},
                  mk {names = i2, macros = m2, locals = _, arm_antiq = a2, units = u2}) =
  mk {names = Symtab.merge (K true) (i1, i2),
      macros = Symtab.merge (K true) (m1, m2),
      locals = l1,
      arm_antiq = Symtab.merge (K true) (a1, a2),
      units = Int.max (u1, u2)}

structure Env = Generic_Data
  (type T = armenv
   val empty = empty_armenv
   val merge = merge_armenv)

structure Ast_Store = Generic_Data
  (type T = (Position.T ARM_Ast.root) Symtab.table
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

(* Stores "root" with its verbatim source "text" under a fresh unit number for "thy", bumping the
   counter. Returns the key and the updated theory. *)
fun store_root (root : Position.T ARM_Ast.root) (text : string) thy =
    let
      val mk {names, macros, locals, arm_antiq, units} = get (Context.Theory thy)
      val key = ast_store_key thy units
      val armenv' = mk {names = names, macros = macros, locals = locals, arm_antiq = arm_antiq,
                        units = units + 1}
      val thy' = thy
        |> Context.theory_map (put armenv')
        |> Context.theory_map (Ast_Store.map (Symtab.update (key, root)))
        |> Context.theory_map (Source_Store.map (Symtab.update (key, text)))
    in (key, thy') end

fun get_ast key thy = Symtab.lookup (Ast_Store.get (Context.Theory thy)) key

fun get_source key thy = Symtab.lookup (Source_Store.get (Context.Theory thy)) key

fun store_antiq (name, antiq_fun) thy =
    let
       val mk {names, macros, locals, arm_antiq, units} = get (Context.Theory thy)
       val armenv' = mk {names = names, macros = macros, locals = locals,
                         arm_antiq = Symtab.update (name, antiq_fun) arm_antiq, units = units}
    in thy |> Context.theory_map (put armenv') end

fun get_antiq name thy =
    let val mk {arm_antiq, ...} = get (Context.Theory thy)
    in Symtab.lookup arm_antiq name end

(* The semantic-backend hook, as in C11_Env.thy (see the note on "Backend" there):
   "full_eval_and_store" (ARM.thy) calls the function stored here, on the parsed root and the
   theory it has just stored that root into, as the last step of every "arm"/"arm_file". The
   default is "K I"; "setup_backend" (ARM.thy) installs another one. A separate registry, not a
   field of "armenv": "reset_armenv" resets what has been declared, not which backend is
   installed. "NONE" stands for the default, so that "merge" is well defined for a function
   type. *)
type backend = pos ARM_Ast.root -> theory -> theory

structure Backend = Generic_Data
  (type T = backend option
   val empty = NONE
   val merge = fn (a, b) => if is_some a then a else b)

fun get_backend thy : backend =
  the_default (K I) (Backend.get (Context.Theory thy))

fun set_backend (f : backend) = Context.theory_map (Backend.put (SOME f))

fun reset_backend thy = Context.theory_map (Backend.put NONE) thy

(* "set_armenv_default"/"reset_armenv" (ARM.thy): a theory nominates its own snapshot as what
   "reset_armenv" later restores; a separate registry, not a field of "armenv" itself, which would
   make every snapshot carry a copy of itself. *)
structure Default_Env = Generic_Data
  (type T = armenv option
   val empty = NONE
   val merge = fn (a, b) => if is_some a then a else b)

fun set_armenv_default thy =
  Context.theory_map (Default_Env.put (SOME (get (Context.Theory thy)))) thy

fun reset_armenv thy =
    let
      val default = case Default_Env.get (Context.Theory thy) of SOME c => c | NONE => empty_armenv
    in Context.theory_map (put default) thy end

end
\<close>

end
