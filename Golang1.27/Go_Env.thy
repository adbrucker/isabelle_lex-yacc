(******************************************************************************
 * Copyright (c) University of Paris-Saclay
 *
 * All rights reserved.
 *
 * Authors: Burkhart Wolff, Claude Sonnet 5.5
 *
 * This is an LLM-generated replication of the Isabelle/C version 2 design to
 * the programming language Go (language version 1.27). It provides an efficient
 * parser for Go, deeply integrated into the Isabelle/PIDE document model,
 * allowing external files as well as in-theory code-snippets which are
 * transparent to the underlying theory. It provides an API for the generated
 * AST’s, and an API to hook up semantic backends that compile these AST’s to
 * theory extensions in Isabelle/HOL. Members of the family come with a
 * Go-specific antiquotation mechanism allowing programmable links to the
 * semantic backends as necessary for support of program-annotations with HOL
 * formulas.
 *
 * This session is part of the Isabelle Programming Language Toolkit
 * (Isabelle/PLTk). The generation has been done with Claude Sonnet 5.5; while
 * the replicants come with a detailed (generated) test-suite for Go, I
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

theory Go_Env
  imports "Go_Ast"
begin

section\<open>The GEnv Environment: storing Ast's and Environments\<close>

text\<open>
  \<^verbatim>\<open>GEnv\<close> is the Go counterpart of \<^verbatim>\<open>AEnv\<close> (\<^verbatim>\<open>AdaSpark_Env.thy\<close>), \<^verbatim>\<open>REnv\<close>, \<^verbatim>\<open>SEnv\<close>,
  \<^verbatim>\<open>OEnv\<close> and \<^verbatim>\<open>CEnv\<close>: the environment and AST-store infrastructure shared by every
  \<open>go\<close>-family command and by \<^verbatim>\<open>AnaEval\<close> (the \<open>analyse_and_eval\<close> pass, in
  \<^verbatim>\<open>Go_AnaEval.thy\<close>). It bundles the same plain \<^verbatim>\<open>Generic_Data\<close> registries behind one
  structure: \<^verbatim>\<open>Env\<close> holds the symbolic environment - \<open>names\<close> (the declared names) and
  \<open>go_antiq\<close> (registered antiquotation handlers) - plus the running \<open>units\<close> counter that
  gives every AST this theory stores a fresh, per-theory sequence number; \<^verbatim>\<open>Ast_Store\<close>
  maps \<open>(theory_name, unit_number)\<close> to the parsed \<^verbatim>\<open>Position.T root\<close>; \<^verbatim>\<open>Source_Store\<close> keeps each
  fragment's verbatim source text. \<^verbatim>\<open>Backend\<close> is the semantic-backend hook, as in the other
  front-ends.

  What is specific to Go: there is \<^emph>\<open>one\<close> lexical name space, as in the language itself - a
  variable, a constant, a parameter, a type, a function, an imported package and a type
  parameter are all just names, and a name is declared in the innermost block it occurs in; Go is
  case sensitive, so the table is keyed by the name as written. Labels have a name space of their
  own (a label and a variable of the same name do not clash): they are entered under a key that
  no identifier can have. The fields of a struct and the methods of a type are declared, and the
  declaration site is reported, but they are not entered into the table: they are reached by
  selection (\<open>x.f\<close>), which this pass resolves with the type information that \<open>genv\<close> also
  holds - \<open>vtypes\<close> (the type of each name of \<open>names\<close>, scoped with it), \<open>defs\<close> (the type
  declarations, by the position of the declared name) and \<open>meths\<close> (the methods, by type and
  name); see the datatype \<open>ty\<close> below and the note in \<^verbatim>\<open>Go_AnaEval.thy\<close>. A name that resolves nowhere is \<^emph>\<open>not\<close>
  marked as an error (see \<^verbatim>\<open>Go_AnaEval.thy\<close>): it very often comes from the universe block
  (\<open>int\<close>, \<open>len\<close>, \<open>nil\<close>), a dot import or another file of the package.
\<close>
ML\<open>
structure GEnv = struct

type pos = Position.T

(* What a name was declared as. The payload is always the declaring
   occurrence's own position (every declared name is an "ident" carrying one),
   which is all hyperlinking needs. *)
datatype ident_kind = Var     of pos   (* a variable: "var", ":=", a range or switch variable *)
                    | Const   of pos   (* a constant *)
                    | Param   of pos   (* a parameter, a result or a receiver *)
                    | Typ     of pos   (* a type, defined or alias *)
                    | Func    of pos   (* a function *)
                    | Pkg     of pos   (* an imported package *)
                    | Label   of pos   (* a label *)
                    | Tparam  of pos   (* a type parameter *)
                    | Fld     of pos   (* a struct field *)
                    | Meth    of pos   (* a method, an interface method *)

fun pos_of_kind k = (case k of
    Var p => p | Const p => p | Param p => p | Typ p => p | Func p => p | Pkg p => p
  | Label p => p | Tparam p => p | Fld p => p | Meth p => p)

fun describe_kind k = (case k of
    Var _ => "Go variable" | Const _ => "Go constant" | Param _ => "Go parameter"
  | Typ _ => "Go type" | Func _ => "Go function" | Pkg _ => "Go package"
  | Label _ => "Go label" | Tparam _ => "Go type parameter" | Fld _ => "Go field"
  | Meth _ => "Go method")

(* The types of the declared things, as far as the selection pass needs them (see the note on
   "type_of" in Go_AnaEval.thy). A named type is a *reference* to its declaration, by the
   position key of the declared name: a type, its fields and its methods may therefore be
   mutually recursive, in any order, without any cycle in the data. A struct type carries the
   declaration site of each of its fields, an interface type that of each of its methods. *)
datatype ty =
    TUnknown                         (* nothing is known: no link is ever made on this basis *)
  | TBasic of string                 (* a predeclared type: int, string, ... *)
  | TNamed of string * ty list       (* declaration key, type arguments *)
  | TVar of string                   (* a type parameter, by the key of its declaration *)
  | TPtr of ty
  | TSlice of ty
  | TArray of ty
  | TMap of ty * ty
  | TChan of ty
  | TFunc of tsig
  | TStruct of tfield list
  | TIface of tmeth list * ty list   (* its methods, and the embedded types *)
  | TTuple of ty list                (* the results of a call with several results *)
  | TGeneric of string list * tsig   (* a generic function: its type parameters (keys), signature *)
  | TTilde of ty                     (* ~T, a term of a constraint *)
  | TUnion of ty list                (* a union of terms, in a constraint *)
and tsig = TSig of ty list * ty list * bool   (* parameters, results, variadic *)
and tfield = TF of string * pos * ty * bool   (* name, declaration site, type, embedded *)
and tmeth = TM of string * pos * tsig

(* A type declaration: its type parameters (keys), its right-hand side and whether it is an alias.
   The constraint of a type parameter is recorded the same way, under the key of the parameter. *)
datatype tydef = TDef of {tparams : string list, rhs : ty, alias : bool}

(* A method: declaration site, signature, pointer receiver, and the type parameters (keys) its
   receiver names for those of the type, and the type parameters (keys) of the method itself (Go
   1.27: generic methods). *)
datatype methdef =
  MDef of {pos : pos, sg : tsig, ptr : bool, rtvars : string list, mtvars : string list}

(* The key identifying a declaration: its position. *)
fun pos_key (p : pos) =
  String.concatWith "," (map (fn (a, b) => a ^ "=" ^ b) (Position.properties_of p))

(* The handler's result is "Context.generic -> Context.generic", not "theory ->
   theory", for the same reason as in C11_Env.thy (an "ML" antiquotation has to
   mutate the ML environment, which no theory function can express);
   "lift_theory_antiq" recaptures the simpler kind. The "root" a handler
   receives is the antiquotation's already *resolved* context (its "[navi]"
   bracket interpreted against the closest-surrounding-context stack, see
   "AnaEval.select_ast"). *)
type 'a type_antiq_fun0 =
  'a * pos Go_Ast.root * int -> (string * pos) -> Context.generic
    -> Context.generic

datatype genv = mk of {names : ident_kind Symtab.table,
                       vtypes : ty Symtab.table,
                       defs : tydef Symtab.table,
                       meths : methdef Symtab.table,
                       go_antiq : (genv type_antiq_fun0) Symtab.table,
                       units : int}
  \<comment> \<open>"vtypes" holds the types of the names in "names" (scoped exactly like them), "defs" the
      type declarations by key, "meths" the methods by type key and name; "units" numbers the
      program units internally.\<close>

type type_antiq_fun = genv type_antiq_fun0

fun lift_theory_antiq
  (f : 'a * pos Go_Ast.root * int -> (string * pos) -> theory -> theory)
    : 'a * pos Go_Ast.root * int -> (string * pos) -> Context.generic
      -> Context.generic =
  fn args => fn body =>
    Context.mapping (f args body) (Local_Theory.background_theory (f args body))

val empty_genv =
  mk {names = Symtab.empty, vtypes = Symtab.empty, defs = Symtab.empty, meths = Symtab.empty,
      go_antiq = Symtab.empty, units = 0}

(* Merging must not reset to empty (Isabelle forks and merges theory state
   routinely during live editing - see the same note on "merge_cenv" in
   C11_Env.thy); "units" takes the larger counter so a merge can never re-issue
   an already-used "Ast_Store" key. *)
fun merge_genv (mk {names = i1, vtypes = v1, defs = d1, meths = m1, go_antiq = a1, units = u1},
                mk {names = i2, vtypes = v2, defs = d2, meths = m2, go_antiq = a2, units = u2}) =
  mk {names = Symtab.merge (K true) (i1, i2),
      vtypes = Symtab.merge (K true) (v1, v2),
      defs = Symtab.merge (K true) (d1, d2),
      meths = Symtab.merge (K true) (m1, m2),
      go_antiq = Symtab.merge (K true) (a1, a2),
      units = Int.max (u1, u2)}

structure Env = Generic_Data
  (type T = genv
   val empty = empty_genv
   val merge = merge_genv)

structure Ast_Store = Generic_Data
  (type T = (Position.T Go_Ast.root) Symtab.table
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
fun store_root (root : Position.T Go_Ast.root) (text : string) thy =
    let
      val mk {names, vtypes, defs, meths, go_antiq, units} = get (Context.Theory thy)
      val key = ast_store_key thy units
      val genv' =
        mk {names = names, vtypes = vtypes, defs = defs, meths = meths, go_antiq = go_antiq,
            units = units + 1}
      val thy' = thy
        |> Context.theory_map (put genv')
        |> Context.theory_map (Ast_Store.map (Symtab.update (key, root)))
        |> Context.theory_map (Source_Store.map (Symtab.update (key, text)))
    in (key, thy') end

fun get_ast key thy = Symtab.lookup (Ast_Store.get (Context.Theory thy)) key

fun get_source key thy =
  Symtab.lookup (Source_Store.get (Context.Theory thy)) key

fun store_antiq (name, antiq_fun) thy =
    let
       val mk {names, vtypes, defs, meths, go_antiq, units} = get (Context.Theory thy)
       val genv' =
         mk {names = names, vtypes = vtypes, defs = defs, meths = meths,
             go_antiq = Symtab.update (name, antiq_fun) go_antiq,
             units = units}
    in thy |> Context.theory_map (put genv') end

fun get_antiq name thy =
    let val mk {go_antiq, ...} = get (Context.Theory thy)
    in Symtab.lookup go_antiq name end

(* The semantic-backend hook, as in C11_Env.thy (see the note on "Backend"
   there): "full_eval_and_store" (Go.thy) calls the function stored here,
   on the parsed root and the theory it has just stored that root into, as the
   last step of every "go"/"go_body"/"go_file". The default
   is "K I"; "setup_backend" (Go.thy) installs another one. A separate
   registry, not a field of "genv": "reset_genv" resets what has been declared,
   not which backend is installed. "NONE" stands for the default, so that
   "merge" is well defined for a function type. *)
type backend = pos Go_Ast.root -> theory -> theory

structure Backend = Generic_Data
  (type T = backend option
   val empty = NONE
   val merge = fn (a, b) => if is_some a then a else b)

fun get_backend thy : backend =
  the_default (K I) (Backend.get (Context.Theory thy))

fun set_backend (f : backend) = Context.theory_map (Backend.put (SOME f))

fun reset_backend thy = Context.theory_map (Backend.put NONE) thy

(* "set_genv_default"/"reset_genv" (Go.thy): a theory nominates its own
   snapshot as what "reset_genv" later restores; a separate registry, not a
   field of "genv" itself, which would make every snapshot carry a copy of
   itself. *)
structure Default_Env = Generic_Data
  (type T = genv option
   val empty = NONE
   val merge = fn (a, b) => if is_some a then a else b)

fun set_genv_default thy =
  Context.theory_map (Default_Env.put (SOME (get (Context.Theory thy)))) thy

fun reset_genv thy =
    let val default = case Default_Env.get (Context.Theory thy) of SOME c =>
      c | NONE => empty_genv
    in Context.theory_map (put default) thy end

end
\<close>

end
