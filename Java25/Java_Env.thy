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

theory Java_Env
  imports "Java_Ast"
begin

section\<open>The JEnv Environment: storing Ast's and Environments\<close>

text\<open>
  \<^verbatim>\<open>JEnv\<close> is the Java counterpart of \<^verbatim>\<open>GEnv\<close> (\<^verbatim>\<open>Go_Env.thy\<close>), \<^verbatim>\<open>AEnv\<close>, \<^verbatim>\<open>REnv\<close>, \<^verbatim>\<open>SEnv\<close>,
  \<^verbatim>\<open>OEnv\<close> and \<^verbatim>\<open>CEnv\<close>: the environment and AST-store infrastructure shared by every
  \<open>java\<close>-family command and by \<^verbatim>\<open>AnaEval\<close> (the \<open>analyse_and_eval\<close> pass, in
  \<^verbatim>\<open>Java_AnaEval.thy\<close>). It bundles the same plain \<^verbatim>\<open>Generic_Data\<close> registries behind one
  structure: \<^verbatim>\<open>Env\<close> holds the symbolic environment - \<open>names\<close> (the declared names),
  \<open>meths\<close> (the declared methods) and \<open>java_antiq\<close> (registered antiquotation handlers) - plus
  the running \<open>units\<close> counter that gives every AST this theory stores a fresh, per-theory
  sequence number; \<^verbatim>\<open>Ast_Store\<close> maps \<open>(theory_name, unit_number)\<close> to the parsed
  \<^verbatim>\<open>Position.T root\<close>; \<^verbatim>\<open>Source_Store\<close> keeps each fragment's verbatim source text. \<^verbatim>\<open>Backend\<close> is
  the semantic-backend hook, as in the other front-ends.

  What is specific to Java: it has \<^emph>\<open>several\<close> name spaces (JLS 6.4.2: the same name may denote a
  package, a type, a method and a variable at once), so the table of names is keyed by a prefix:
  a variable (a local variable, a parameter, a field, an enum constant) by its name, a type
  (a class, an interface, an enum, a record, an annotation interface, a type parameter, an
  imported type) by \<open>type:\<close>,
    a package by \<open>pkg:\<close> and a label by \<open>label:\<close>. Methods are different again: a
  method name denotes \<^emph>\<open>all\<close> the methods of that name that are in scope (overloading), and a
  declaration of a method named \<open>n\<close> in a class shadows every method \<open>n\<close> of the enclosing classes,
  whatever its signature (JLS 6.4.1). They are therefore kept in a table of their own, \<open>meths\<close>,
  that maps a name to the list of the declarations of the innermost class that has any (their
  position, their number of parameters and whether the last one is variable). A name that
  resolves nowhere is \<^emph>\<open>not\<close> marked as an error (see \<^verbatim>\<open>Java_AnaEval.thy\<close>): it very often comes from
  an inherited member, an on-demand import or the platform.
\<close>
ML\<open>
structure JEnv = struct

type pos = Position.T

(* What a name was declared as. The payload is always the declaring occurrence's own position
   (every declared name is an "ident" carrying one), which is all hyperlinking needs. *)
datatype ident_kind = Var     of pos   (* a local variable, a pattern variable, a resource *)
                    | Param   of pos   (* a parameter of a method, a constructor or a lambda *)
                    | Fld     of pos   (* a field *)
                    | EnumC   of pos   (* an enum constant *)
                    | Typ     of pos   (* a class, an interface, an enum, a record, an annotation *)
                    | Tparam  of pos   (* a type parameter *)
                    | Imp     of pos   (* a type imported by name *)
                    | Pkg     of pos   (* a package *)
                    | Label   of pos   (* a label *)
                    | Meth    of pos   (* a method (for the reports of declarations) *)
                    | Ctor    of pos   (* a constructor *)

fun pos_of_kind k = (case k of
    Var p => p | Param p => p | Fld p => p | EnumC p => p | Typ p => p | Tparam p => p
  | Imp p => p | Pkg p => p | Label p => p | Meth p => p | Ctor p => p)

fun describe_kind k = (case k of
    Var _ => "Java variable" | Param _ => "Java parameter" | Fld _ => "Java field"
  | EnumC _ => "Java enum constant" | Typ _ => "Java type" | Tparam _ => "Java type parameter"
  | Imp _ => "Java import" | Pkg _ => "Java package" | Label _ => "Java label"
  | Meth _ => "Java method" | Ctor _ => "Java constructor")

(* A declared method: the position of its name, the number of its parameters and whether the
   last one is variable ("T... x"). *)
datatype mdecl = MD of {pos : pos, arity : int, varargs : bool}

(* The types of the declared things, as far as the selection pass needs them (see the note on
   "type_of" in Java_AnaEval.thy). A class is a *reference* to its declaration, by the position key
   of the declared name: classes, their fields and their methods may therefore be mutually
   recursive, in any order, without any cycle in the data. *)
datatype ty =
    TUnknown                         (* nothing is known: no link is ever made on this basis *)
  | TPrimT of string                 (* int, boolean, ..., void *)
  | TNull                            (* the type of null *)
  | TCls of string * ty list         (* declaration key (or "String", "Object"), type arguments *)
  | TTv of string                    (* a type variable, by the key of its declaration *)
  | TArr of ty

(* A field, a method (type parameters by key, parameters, variable arity, result) *)
datatype fdef = FD of {pos : pos, ty : ty, static : bool}
datatype mdef = MT of {pos : pos, tps : string list, ps : ty list, va : bool, ret : ty,
                       static : bool}

(* A class: its kind (class, interface, enum, record, annotation), its type parameters (keys), its
   supertypes (the superclass first), its fields (enum constants and record components included),
   methods (the accessors of a record included), constructors and member types (by key and site). *)
datatype cdef = CD of {kind : string, tps : string list, supers : ty list,
                       fields : (string * fdef) list, methods : (string * mdef) list,
                       ctors : mdef list, types : (string * (string * pos)) list}

(* The key identifying a declaration: its position. *)
fun pos_key (p : pos) =
  String.concatWith "," (map (fn (a, b) => a ^ "=" ^ b) (Position.properties_of p))

(* The handler's result is "Context.generic -> Context.generic", not "theory -> theory", for the
   same reason as in C11_Env.thy (an "ML" antiquotation has to mutate the ML environment, which
   no theory function can express); "lift_theory_antiq" recaptures the simpler kind. The "root" a
   handler receives is the antiquotation's already *resolved* context (its "[navi]" bracket
   interpreted against the closest-surrounding-context stack, see "AnaEval.select_ast"). *)
type 'a type_antiq_fun0 =
  'a * pos Java_Ast.root * int -> (string * pos) -> Context.generic -> Context.generic

datatype jenv = mk of {names : ident_kind Symtab.table,
                       meths : mdecl list Symtab.table,
                       vtypes : ty Symtab.table,
                       defs : cdef Symtab.table,
                       cur : string list,
                       java_antiq : (jenv type_antiq_fun0) Symtab.table,
                       units : int}
  \<comment> \<open>"names" holds the declared names of all name spaces but methods (see the prefixes above),
      "meths" the visible methods by name (those of the top level of a compact unit, and static
      imports: the methods of classes are in "defs"); "vtypes" the types of the variables in
      "names" (scoped with them), "defs" the classes by key, "cur" the keys of the classes that
      enclose the point of analysis, the innermost first; "units" numbers the program units
      internally.\<close>

type type_antiq_fun = jenv type_antiq_fun0

fun lift_theory_antiq
  (f : 'a * pos Java_Ast.root * int -> (string * pos) -> theory -> theory)
    : 'a * pos Java_Ast.root * int -> (string * pos) -> Context.generic -> Context.generic =
  fn args => fn body =>
    Context.mapping (f args body) (Local_Theory.background_theory (f args body))

val empty_jenv =
  mk {names = Symtab.empty, meths = Symtab.empty, vtypes = Symtab.empty, defs = Symtab.empty,
      cur = [], java_antiq = Symtab.empty, units = 0}

(* Merging must not reset to empty (Isabelle forks and merges theory state routinely during live
   editing - see the same note on "merge_cenv" in C11_Env.thy); "units" takes the larger counter
   so a merge can never re-issue an already-used "Ast_Store" key. *)
fun merge_jenv (mk {names = i1, meths = m1, vtypes = v1, defs = d1, cur = c1, java_antiq = a1,
                    units = u1},
                mk {names = i2, meths = m2, vtypes = v2, defs = d2, cur = _, java_antiq = a2,
                    units = u2}) =
  mk {names = Symtab.merge (K true) (i1, i2),
      meths = Symtab.merge (K true) (m1, m2),
      vtypes = Symtab.merge (K true) (v1, v2),
      defs = Symtab.merge (K true) (d1, d2),
      cur = c1,
      java_antiq = Symtab.merge (K true) (a1, a2),
      units = Int.max (u1, u2)}

structure Env = Generic_Data
  (type T = jenv
   val empty = empty_jenv
   val merge = merge_jenv)

structure Ast_Store = Generic_Data
  (type T = (Position.T Java_Ast.root) Symtab.table
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
fun store_root (root : Position.T Java_Ast.root) (text : string) thy =
    let
      val mk {names, meths, vtypes, defs, cur, java_antiq, units} = get (Context.Theory thy)
      val key = ast_store_key thy units
      val jenv' = mk {names = names, meths = meths, vtypes = vtypes, defs = defs, cur = cur,
                      java_antiq = java_antiq, units = units + 1}
      val thy' = thy
        |> Context.theory_map (put jenv')
        |> Context.theory_map (Ast_Store.map (Symtab.update (key, root)))
        |> Context.theory_map (Source_Store.map (Symtab.update (key, text)))
    in (key, thy') end

fun get_ast key thy = Symtab.lookup (Ast_Store.get (Context.Theory thy)) key

fun get_source key thy = Symtab.lookup (Source_Store.get (Context.Theory thy)) key

fun store_antiq (name, antiq_fun) thy =
    let
       val mk {names, meths, vtypes, defs, cur, java_antiq, units} = get (Context.Theory thy)
       val jenv' = mk {names = names, meths = meths, vtypes = vtypes, defs = defs, cur = cur,
                       java_antiq = Symtab.update (name, antiq_fun) java_antiq, units = units}
    in thy |> Context.theory_map (put jenv') end

fun get_antiq name thy =
    let val mk {java_antiq, ...} = get (Context.Theory thy)
    in Symtab.lookup java_antiq name end

(* The semantic-backend hook, as in C11_Env.thy (see the note on "Backend" there):
   "full_eval_and_store" (Java.thy) calls the function stored here, on the parsed root and the
   theory it has just stored that root into, as the last step of every "java"/"java_file". The
   default is "K I"; "setup_backend" (Java.thy) installs another one. A separate registry, not a
   field of "jenv": "reset_jenv" resets what has been declared, not which backend is installed.
   "NONE" stands for the default, so that "merge" is well defined for a function type. *)
type backend = pos Java_Ast.root -> theory -> theory

structure Backend = Generic_Data
  (type T = backend option
   val empty = NONE
   val merge = fn (a, b) => if is_some a then a else b)

fun get_backend thy : backend =
  the_default (K I) (Backend.get (Context.Theory thy))

fun set_backend (f : backend) = Context.theory_map (Backend.put (SOME f))

fun reset_backend thy = Context.theory_map (Backend.put NONE) thy

(* "set_jenv_default"/"reset_jenv" (Java.thy): a theory nominates its own snapshot as what
   "reset_jenv" later restores; a separate registry, not a field of "jenv" itself, which would
   make every snapshot carry a copy of itself. *)
structure Default_Env = Generic_Data
  (type T = jenv option
   val empty = NONE
   val merge = fn (a, b) => if is_some a then a else b)

fun set_jenv_default thy =
  Context.theory_map (Default_Env.put (SOME (get (Context.Theory thy)))) thy

fun reset_jenv thy =
    let val default = case Default_Env.get (Context.Theory thy) of SOME c => c | NONE => empty_jenv
    in Context.theory_map (put default) thy end

end
\<close>

end
