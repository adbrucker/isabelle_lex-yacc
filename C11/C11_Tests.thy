(***********************************************************************************
 * Copyright (c) University of Paris-Saclay
 *
 * Author : Burkhart Wolff
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

theory C11_Tests
  imports "C11"
begin

text\<open>
  The test suite for the C11 grammar/parser/\<open>analyse_and_eval\<close> machinery defined in
  \<^verbatim>\<open>C11.thy\<close> - split out into its own theory so that \<^verbatim>\<open>C11.thy\<close> itself stays a light
  import for other theories that only want the \<open>c11\<close>/\<open>c11_ident\<close>/\<open>c11_expr\<close>/
  \<open>c11_statement\<close>/\<open>c11_file\<close> commands, without pulling in this whole test suite.
  \<^verbatim>\<open>C11.thy\<close> is the project root to import going forward; this theory is built only
  as part of a full/global session build.
\<close>

section\<open>Testing the generated C11 Parser with Syntax Highlighting\<close>

subsection\<open>A Light-Import Smoke Test\<close>
text\<open>
  Regression test for the \<^verbatim>\<open>C11.thy\<close>/\<^verbatim>\<open>C11_Tests.thy\<close> split: exercises just the
  \<open>c11\<close>-family commands \<^verbatim>\<open>C11.thy\<close> itself provides (\<open>c11\<close>, \<open>c11_ident\<close>,
  \<open>c11_expr\<close>, \<open>c11_statement\<close>, \<open>c11_reject\<close> - \<open>c11_file\<close> is exercised at
  length further below, in this very same theory, so is not duplicated
  here), confirming that \<^verbatim>\<open>C11.thy\<close> alone - without anything from later in
  this test suite (a registered antiquotation handler, a helper only
  defined there, \<open>\<dots>\<close>) - is genuinely sufficient for a downstream theory
  that just wants those commands.
\<close>

c11\<open>
int standalone_test(int x) {
  return x + 1;
}
\<close>

c11_ident\<open>standalone_test\<close>

c11_expr\<open>1 + 2\<close>

c11_statement\<open>{ int y = 0; y = y + 1; }\<close>

c11_reject\<open>int + ;\<close>

subsection\<open>A more Comprehensive Program Text\<close>

c11\<open>
#include <stdio.h>
#include "local_header.h"

#define MAX_SIZE = 100
#define SQUARE(x) = x * x

#ifdef MAX_SIZE
int buffer[MAX_SIZE];
#else
int buffer[10];
#endif

#ifndef NDEBUG
int debug_flag = 1;
#endif

int max(int a, int b) {
  if (a > b)
    return a;
  else
    return b;
}

int main(void) {
  int x = max(3, 42);
  return x;
}
\<close>


subsection\<open>Declaration/Use Highlighting, Including Undeclared Names\<close>
text\<open>
  \<open>AnaEval.report_use\<close> hyperlinks a name's use back to its declaration when
  one is found in scope; a name found \<^emph>\<open>nowhere\<close> in scope is reported with
  \<^ML>\<open>Markup.bad ()\<close> instead - a highlight/underline in the IDE, not a
  hyperlink, and deliberately \<^emph>\<open>not\<close> an \<open>error\<close>: this fragment has no
  cross-file symbol table, so "undeclared in what this parse saw" routinely
  just means "declared in a header this recognizer does not itself follow"
  (\<open>#include\<close> is purely syntactic here - see the preprocessor fragment above),
  not necessarily a real defect. The tests below exercise this directly: each
  references a name that is never declared anywhere in the same fragment, and
  each is expected to succeed exactly like its declared-name counterparts
  elsewhere in this theory - only the markup differs, not the outcome.
\<close>
c11\<open>
int g;

int f(void) {
  return g + totally_undeclared;
}
\<close>

text\<open>The same, for a standalone \<open>c11_expr\<close>/\<open>c11_statement\<close> fragment - these
  run \<open>analyse_and_eval\<close> purely for its hyperlinking side effect (see
  \<open>run_c11_kind\<close>'s \<open>full_eval\<close> flag above), which includes this "bad" markup
  just the same.\<close>
c11_expr\<open>also_undeclared + 1\<close>

c11_statement\<open>{ int local_var = 0; local_var = yet_another_undeclared; }\<close>

subsection\<open>Declaration/Use Highlighting for Functions and Their Calls\<close>
text\<open>
  A function name is registered into the very same flat \<open>idents\<close> namespace
  a variable is (see \<open>ident_kind\<close> in \<^verbatim>\<open>CEnv.thy\<close> - functions and variables
  share one \<open>Global\<close> bucket, no separate function/data distinction), and a
  call's own callee (\<open>ef\<close> in \<open>CCall (ef, args, _)\<close>) is walked exactly like
  any other expression, going through the very same \<open>CVar\<close>/\<open>report_use\<close>
  path an ordinary variable use does - \<open>walk_expr\<close> has no function-specific
  case at all. This had not previously been exercised by any test here, so
  the blocks below add that directly: a definition with a later (and a
  recursive) call, and the more demanding ordinary C idiom of a forward
  declaration, a caller sitting textually \<^emph>\<open>between\<close> the declaration and
  the real definition, and the definition itself - exercising that the
  walk's sequential, scope-respecting threading of \<open>cenv\<close> (see the notes at
  the top of \<^verbatim>\<open>AnaEval.thy\<close>) resolves such a call against whatever is in
  scope \<^emph>\<open>at that point in the source\<close>, not against whatever the same name
  is last registered as by the time the whole file has been walked.
\<close>
c11\<open>
int fact(int n) {
  if (n <= 1) return 1;
  return n * fact(n - 1);
}

int use_fact(void) {
  return fact(5);
}
\<close>

c11\<open>
int helper(int x);

int caller(void) {
  return helper(3) + 1;
}

int helper(int x) {
  return x * 2;
}
\<close>

subsection\<open>Declaration/Use Highlighting for Preprocessor Constants and Macros\<close>
text\<open>
  \<open>#define\<close> constants and function-like macros register into \<open>cenv\<close> exactly
  like an ordinary declaration (see \<open>Cpp_const\<close>/\<open>Cpp_macro\<close> in
  \<^verbatim>\<open>CEnv.thy\<close>, and the note above \<open>walk_pp_directive\<close> in \<^verbatim>\<open>AnaEval.thy\<close>),
  so a later \<open>CVar\<close>/\<open>CCall\<close> reference to the macro's name hyperlinks to its
  \<open>#define\<close> the same way a reference to an ordinary global does - this
  fragment never expands macros, so such a reference is, syntactically, just
  another use of that name. \<open>#ifdef name\<close>/\<open>#ifndef name\<close> is \<^emph>\<open>also\<close> a use of
  \<open>name\<close> (testing whether it is defined), not merely a branch condition to
  recurse past - previously the tested name was not walked/reported at all
  (fixed in \<open>walk_pp_directive\<close>'s \<open>CPPIfdef\<close> case, above). None of this had
  a dedicated test before: the "comprehensive program" test further below
  happens to use \<open>MAX_SIZE\<close> once, but never calls its own function-like
  macro \<open>SQUARE\<close> anywhere, and no test exercised \<open>#ifdef\<close>/\<open>#ifndef\<close> at all
  as a use site - including the case of testing a name that is genuinely
  undeclared anywhere in the same parse, which (exactly like an ordinary
  undeclared variable, see above) should still succeed, just with
  \<^ML>\<open>Markup.bad ()\<close> instead of a hyperlink.
\<close>
c11\<open>
#define ANSWER = 42
#define DOUBLE(x) = x * 2

int use_constant(void) {
  return ANSWER + 1;
}

int use_macro(void) {
  return DOUBLE(ANSWER);
}

#ifdef ANSWER
int defined_branch = ANSWER;
#endif

#ifndef NOT_DEFINED_ANYWHERE
int else_branch = 0;
#endif
\<close>

text\<open>Hard, batch-checkable confirmation that the block above actually
  registered \<open>ANSWER\<close>/\<open>DOUBLE\<close> as \<open>Cpp_const\<close>/\<open>Cpp_macro\<close> in \<open>CEnv\<close>, rather
  than merely parsing without error - a parse also succeeds when a name
  resolves nowhere (that is exactly what \<^ML>\<open>Markup.bad ()\<close> is for), so
  successful parsing alone would not witness that registration/resolution
  actually happened.\<close>
ML\<open>
val CEnv.mk {idents, ...} = CEnv.get (Context.Theory @{theory})
val _ =
  case Symtab.lookup idents "ANSWER" of
    SOME (CEnv.Cpp_const _) => writeln "PASS: ANSWER registered as Cpp_const"
  | other => error ("FAIL: ANSWER not registered as Cpp_const: " ^
                     (case other of NONE => "not found" | SOME _ => "found as a different kind"))
val _ =
  case Symtab.lookup idents "DOUBLE" of
    SOME (CEnv.Cpp_macro _) => writeln "PASS: DOUBLE registered as Cpp_macro"
  | other => error ("FAIL: DOUBLE not registered as Cpp_macro: " ^
                     (case other of NONE => "not found" | SOME _ => "found as a different kind"))
\<close>

subsection\<open>Struct/Union/Enum Tags, and Struct/Union Member Linking\<close>
text\<open>
  A struct/union/enum \<^emph>\<open>tag\<close> is registered into \<open>cenv\<close>'s \<open>types\<close> table (the
  tag namespace, shared by all three - see \<open>walk_decl_specs\<close> in
  \<^verbatim>\<open>AnaEval.thy\<close>) the first time its defining occurrence (one carrying a
  member/constant list) is walked; a later, bare mention of the same tag
  hyperlinks back to it instead of registering again. An enum's own
  constants are \<^emph>\<open>not\<close> a per-type namespace - they are registered into the
  ordinary \<open>idents\<close> table right alongside variables and functions, exactly
  like any other declared name, so a later \<open>CVar\<close> reference to one
  hyperlinks through the very same path an ordinary variable use does.\<close>
c11\<open>
struct point { int x; int y; };
struct point pt = { .x = 1, .y = 2 };
struct point *pp = &pt;

int use_point_twice(void) {
  struct point another;
  return pt.x + pp->y + another.x;
}
\<close>

text\<open>Hard, batch-checkable confirmation that the block above actually
  registered \<open>point\<close> as a \<open>Struct_tag\<close> (with both its member declarations),
  rather than merely parsing without error.\<close>
ML\<open>
val CEnv.mk {types, ...} = CEnv.get (Context.Theory @{theory})
val _ =
  case Symtab.lookup types "point" of
    SOME (CEnv.Struct_tag (_, decls)) =>
      if length decls = 2 then writeln "PASS: point registered as Struct_tag with 2 member declarations"
      else error ("FAIL: point's Struct_tag has " ^ Int.toString (length decls) ^
                   " member declarations, expected 2")
  | other => error ("FAIL: point not registered as Struct_tag: " ^
                     (case other of NONE => "not found" | SOME _ => "found as a different kind"))
\<close>

text\<open>A union shares the very same tag namespace and the very same member
  resolution as a struct (\<open>walk_decl_specs\<close> handles both via one
  \<open>CStruct\<close> constructor, distinguished only by \<open>cStructTag\<close>).\<close>
c11\<open>
union num { int i; double d; };
union num n = { .i = 42 };

int use_union(void) {
  return n.i;
}
\<close>
ML\<open>
val CEnv.mk {types, ...} = CEnv.get (Context.Theory @{theory})
val _ =
  case Symtab.lookup types "num" of
    SOME (CEnv.Union_tag _) => writeln "PASS: num registered as Union_tag"
  | other => error ("FAIL: num not registered as Union_tag: " ^
                     (case other of NONE => "not found" | SOME _ => "found as a different kind"))
\<close>

text\<open>An enum's constants land in the ordinary \<open>idents\<close> namespace, tagged
  \<open>Enum\<close> - both for a named enum (whose tag is \<^emph>\<open>also\<close> registered, into
  \<open>types\<close>) and an anonymous one (which still has real, nameable constants,
  even though its own type has no tag to register).\<close>
c11\<open>
enum Color { RED, GREEN, BLUE };
enum Color c = RED;

int use_color(void) {
  return c == GREEN;
}

enum { FOO, BAR };

int use_anonymous_enum(void) {
  return FOO + BAR;
}
\<close>
ML\<open>
val CEnv.mk {idents, types, ...} = CEnv.get (Context.Theory @{theory})
val _ =
  case Symtab.lookup types "Color" of
    SOME (CEnv.Enum_tag _) => writeln "PASS: Color registered as Enum_tag"
  | other => error ("FAIL: Color not registered as Enum_tag: " ^
                     (case other of NONE => "not found" 
                                  | SOME _ => "found as a different kind"))
val _ =
  List.app (fn name =>
              case Symtab.lookup idents name of
                SOME (CEnv.Enum _) => writeln ("PASS: " ^ name ^ " registered as Enum")
              | other => error ("FAIL: " ^ name ^ " not registered as Enum: " ^
                                 (case other of NONE => "not found" 
                                              | SOME _ => "found as a different kind")))
    ["RED", "GREEN", "BLUE", "FOO", "BAR"]
\<close>

text\<open>Member linking (\<open>AnaEval.report_member_use\<close>) falls back to
  \<^ML>\<open>Markup.bad ()\<close>, not an \<open>error\<close>, for anything it cannot resolve - a
  field name genuinely not among the resolved type's own members, or (still,
  even after the non-bare-variable-base extension below) a base expression
  shape \<open>AnaEval.base_specs_of_expr\<close> does not cover at all (a binary
  expression, say). Both are expected to succeed exactly like their
  resolvable counterparts elsewhere in this theory - only the markup
  differs, not the outcome. \<open>make_point().x\<close> itself is \<^emph>\<open>not\<close> such a case
  any more (a function-call base, see the next subsection) - only
  \<open>pt.not_a_real_field\<close> genuinely is here.\<close>
c11\<open>
struct point make_point(void);

int use_unresolved_members(void) {
  struct point pt;
  return make_point().x + pt.not_a_real_field;
}
\<close>

subsection\<open>Member Linking Through a \<open>typedef\<close>\<close>
text\<open>
  \<open>AnaEval.member_decls_of_specs\<close> is what \<open>report_member_use\<close> actually
  calls to find a base variable's member-declaration list: it chases a
  \<open>CTypeDef\<close> specifier back through \<open>idents\<close> to the \<open>typedef\<close>'s own
  declaration specifiers and recurses - so a \<open>typedef\<close>'d name standing in
  for a struct/union type is now resolved, any number of \<open>typedef\<close>s deep,
  and an inline struct/union body (named tag or fully anonymous) is used
  directly, with no separate \<open>types\<close> lookup needed at all. Since
  \<open>report_member_use\<close> itself only ever produces PIDE markup (never a
  checkable ML value, see the note above), these tests call
  \<open>member_decls_of_specs\<close> directly against the real \<open>specs\<close> stored for
  each variable, the same way the tag tests above check \<open>types\<close> directly
  rather than relying on markup.\<close>
c11\<open>
typedef struct point_s { int x; int y; } point_t;
int dummy_intervening_1;
point_t p;

typedef struct { int a; int b; int c; } triple_t;
int dummy_intervening_2;
triple_t t;

typedef point_t point_t2;
int dummy_intervening_3;
point_t2 q;

struct { int z; } w;

int use_typedef_members(void) {
  return p.x + t.b + q.y + w.z;
}
\<close>
ML\<open>
val cenv = CEnv.get (Context.Theory @{theory})
val CEnv.mk {idents, ...} = cenv
fun specs_of name =
  case Symtab.lookup idents name of
    SOME (CEnv.Global (C_Ast.CDecl (specs, _, _))) => specs
  | SOME (CEnv.Local (C_Ast.CDecl (specs, _, _))) => specs
  | _ => error ("FAIL: " ^ name ^ " not registered as a variable with declaration specifiers")
fun check_members (var, expected_len, descr) =
  case AnaEval.member_decls_of_specs cenv (specs_of var) of
    NONE => error ("FAIL: " ^ descr ^ " (" ^ var ^ ") did not chase to any member list")
  | SOME decls =>
      if length decls = expected_len then
        writeln ("PASS: " ^ descr ^ " (" ^ var ^ ") chased to " ^ Int.toString expected_len ^
                 " member declaration(s)")
      else
        error ("FAIL: " ^ descr ^ " (" ^ var ^ ") chased to " ^ Int.toString (length decls) ^
               " member declaration(s), expected " ^ Int.toString expected_len)
val _ = check_members ("p", 2, "named-tag typedef (point_t -> struct point_s)")
val _ = check_members ("t", 3, "anonymous-struct typedef (triple_t)")
val _ = check_members ("q", 2, "typedef of a typedef (point_t2 -> point_t -> struct point_s)")
val _ = check_members ("w", 1, "a direct (non-typedef) anonymous struct variable")
\<close>

subsection\<open>Member Linking Through Non-Bare-Variable Base Expressions\<close>
text\<open>
  \<open>AnaEval.base_specs_of_expr\<close> is what \<open>report_member_use\<close> now calls
  first, to find the declaration-specifiers describing an arbitrary base
  expression's type - a bare variable is only its simplest case. As with
  the \<open>typedef\<close>-chasing tests above, \<open>report_member_use\<close> itself only ever
  produces PIDE markup, so these tests call \<open>base_specs_of_expr\<close> (and,
  on its result, the already-tested \<open>member_decls_of_specs\<close>) directly,
  against small, hand-built expression values exercising each shape it
  handles - reusing \<open>point_s\<close> (2 members, registered above) as the common
  struct type throughout, so every check below shares the same expected
  member count.\<close>
c11\<open>
struct point_s make_point2(void);
struct point_s arr_of_points[5];
struct point_s *pp_of_point;
struct point_s plain_point_var;
struct container_s { struct point_s inner; };
struct container_s a_container;
\<close>
ML\<open>
val cenv = CEnv.get (Context.Theory @{theory})
val dummy_ni = C_Ast.OnlyPos Position.none
fun mkvar name = C_Ast.CVar (C_Ast.Ident (name, 0, dummy_ni), dummy_ni)
fun check_base_specs (descr, e) =
  case AnaEval.base_specs_of_expr cenv e of
    NONE => error ("FAIL: " ^ descr ^ " - base_specs_of_expr returned NONE")
  | SOME specs =>
      (case AnaEval.member_decls_of_specs cenv specs of
         NONE => error ("FAIL: " ^ descr ^ " - member_decls_of_specs did not chase to a member list")
       | SOME decls =>
           if length decls = 2 then
             writeln ("PASS: " ^ descr ^ " chased to the expected 2 member declarations")
           else
             error ("FAIL: " ^ descr ^ " chased to " ^ Int.toString (length decls) ^
                    " member declaration(s), expected 2"))

val _ = check_base_specs ("f().field - CCall, the callee's own return type",
           C_Ast.CCall (mkvar "make_point2", [], dummy_ni))
val _ = check_base_specs ("arr[0].field - CIndex, the element type (index expr itself unused)",
           C_Ast.CIndex (mkvar "arr_of_points", mkvar "arr_of_points", dummy_ni))
val _ = check_base_specs ("dereferenced-pointer.field - CUnary CIndOp, the pointee type",
           C_Ast.CUnary (C_Ast.CIndOp, mkvar "pp_of_point", dummy_ni))
val _ = check_base_specs ("addressed-variable->field - CUnary CAdrOp",
           C_Ast.CUnary (C_Ast.CAdrOp, mkvar "plain_point_var", dummy_ni))
val _ = check_base_specs ("cast-target->field - CCast, the cast's own type, not the operand's",
           C_Ast.CCast
             (C_Ast.CDecl
                ([C_Ast.CTypeSpec
                    (C_Ast.CSUType
                       (C_Ast.CStruct (C_Ast.CStructTag,
                          SOME (C_Ast.Ident ("point_s", 0, dummy_ni)), NONE, [], dummy_ni),
                        dummy_ni))],
                 [], dummy_ni),
              mkvar "plain_point_var", dummy_ni))
val _ = check_base_specs ("a.b.c - chained CMember, \"inner\"'s own declared type",
           C_Ast.CMember (mkvar "a_container", C_Ast.Ident ("inner", 0, dummy_ni), false, dummy_ni))
\<close>

subsection\<open>\<open>c11_predef\<close>: a Basic Predefined-Header Mechanism\<close>
text\<open>
  \<open>c11_predef [header] \<open>decl_list\<close>\<close> does \<^emph>\<open>not\<close> itself register any
  declared name into \<open>cenv\<close>'s \<open>idents\<close>/\<open>types\<close> - it only captures walking
  \<open>decl_list\<close> as a reusable \<open>cenv -> cenv\<close> effect and registers \<^emph>\<open>that\<close>
  under \<open>header\<close> in \<open>cenv\<close>'s \<open>predefined_envs\<close> (\<^verbatim>\<open>CEnv.thy\<close>). A later
  \<open>#include <header>\<close> - genuinely \<^emph>\<open>connected\<close> to \<open>c11_predef\<close> now, unlike
  every other recognized preprocessor form, which stays purely syntactic -
  is what actually applies it (\<open>AnaEval.walk_pp_directive\<close>'s \<open>CPPInclude\<close>
  case), matching real C: a header's declarations are only in scope once it
  is genuinely included, not merely known about somewhere in the theory.

  Four small, genuinely representative fragments below cover the common,
  non-\<open>FILE\<close>-taking parts of \<open>stdio.h\<close> (\<open>printf\<close>/\<open>putchar\<close>/\<open>getchar\<close>/
  \<open>puts\<close> need only built-in types; \<open>fopen\<close>/\<open>fprintf\<close> and friends need
  \<open>FILE\<close>, out of scope - see below), all of \<open>stdlib.h\<close>'s allocation/exit/
  conversion functions, \<open>errno.h\<close>'s \<open>errno\<close> plus two error-code constants,
  and \<open>assert.h\<close>'s \<open>assert\<close> - written here as this fragment's simplified,
  single-expression \<open>#define\<close> (\<open>\<section>\<close> "The Preprocessor Fragment" above), so
  it registers and type-checks as a call, not with real assertion-failure
  semantics (which would need a statement, not an expression).\<close>
c11_predef [stdio.h] \<open>
int printf(const char *format, ...);
int putchar(int c);
int getchar(void);
int puts(const char *s);
\<close>

c11_predef [stdlib.h] \<open>
void *malloc(unsigned long size);
void *calloc(unsigned long nmemb, unsigned long size);
void *realloc(void *ptr, unsigned long size);
void free(void *ptr);
void exit(int status);
void abort(void);
int atoi(const char *nptr);
double atof(const char *nptr);
\<close>

c11_predef [errno.h] \<open>
extern int errno;
#define EDOM = 33
#define ERANGE = 34
\<close>

c11_predef [assert.h] \<open>
#define assert(expr) = expr
\<close>

text\<open>Hard, batch-checkable confirmation that \<open>c11_predef\<close> alone, with no
  \<open>#include\<close> anywhere yet, really does leave \<open>idents\<close> untouched.\<close>
ML\<open>
val CEnv.mk {idents = idents_before_include, ...} = CEnv.get (Context.Theory @{theory})
val _ =
  List.app (fn name =>
              case Symtab.lookup idents_before_include name of
                NONE => ()
              | SOME _ => error ("FAIL: " ^ name ^ " already registered before any #include"))
    ["printf", "putchar", "getchar", "puts", "malloc", "calloc", "realloc", "free",
     "exit", "abort", "atoi", "atof", "errno", "EDOM", "ERANGE", "assert"]
\<close>

text\<open>Only once each header is actually \<open>#include\<close>d - here, in a single
  translation unit together with the code using them, exactly as in real
  C - do its names become ordinary, resolvable uses, not \<open>Markup.bad ()\<close>.\<close>
c11\<open>
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <assert.h>

int use_predefined(int argc, char **argv) {
  int r = atoi(argv[0]);
  if (r == 0) {
    printf("bad: %d\n", errno);
    exit(EDOM);
  }
  putchar(getchar());
  assert(r > 0);
  return r;
}
\<close>

text\<open>Hard, batch-checkable confirmation that every name above actually
  registered into \<open>idents\<close> once \<open>#include\<close>d, rather than merely parsing
  without error.\<close>
ML\<open>
val CEnv.mk {idents, ...} = CEnv.get (Context.Theory @{theory})
val _ =
  List.app (fn name =>
              case Symtab.lookup idents name of
                SOME _ => ()
              | NONE => error ("FAIL: " ^ name ^ " not registered after #include"))
    ["printf", "putchar", "getchar", "puts", "malloc", "calloc", "realloc", "free",
     "exit", "abort", "atoi", "atof", "errno", "EDOM", "ERANGE", "assert"]
\<close>

text\<open>A header never \<open>#include\<close>d stays exactly as unresolved as an ordinary
  undeclared name - \<open>ERANGE\<close> was declared under \<open>errno.h\<close> above, but
  \<open>EOVERFLOW\<close> was not declared anywhere at all, and neither is in scope
  without its own \<open>#include\<close>; both fall back to \<^ML>\<open>Markup.bad ()\<close> here,
  not a hyperlink - only the markup differs, not the outcome.\<close>
c11\<open>
int use_without_include(void) {
  return ERANGE + EOVERFLOW;
}
\<close>

text\<open>\<open>c11_predef\<close> rejects a function \<^emph>\<open>definition\<close> (a real body) outright -
  it is for declaring an interface, never an implementation. This is a
  deliberately-failing case (a bare \<open>c11_predef\<close> with a genuine \<open>{ ... }\<close>
  body errors immediately), so it cannot sit in this permanent, always-
  succeeding suite - confirmed instead via an isolated probe, per this
  project's own verification convention: \<open>c11_predef [bad_impl.h] \<open>int
  bad_fn(void) { return 1; }\<close>\<close> fails with "function definitions are not
  allowed here, only prototypes".

  A real limitation this fragment \<^emph>\<open>used\<close> to have here - the lexer never
  producing a \<open>TYPEDEF_NAME\<close> token at all, so \<open>setjmp.h\<close>'s \<open>jmp_buf\<close> and
  \<open>stdarg.h\<close>'s \<open>va_list\<close> (both always \<open>typedef\<close>'d types in a real C
  library) could not be declared - is now resolved, see the subsection
  right below.\<close>

subsection\<open>\<open>typedef\<close> Support: \<open>setjmp.h\<close> and \<open>stdarg.h\<close>\<close>
text\<open>
  \<open>C11_Typedefs\<close> (\<^verbatim>\<open>C11_Parser.thy\<close>) gives the lexer real "lexer hack"
  feedback: once a \<open>typedef\<close> declaration has been reduced, its name is
  recognized as \<open>TYPEDEF_NAME\<close> (not a plain identifier) in every later use,
  in the same or a later command - exactly what a standards-faithful
  \<open>c11_predef [setjmp.h]\<close>/\<open>c11_predef [stdarg.h]\<close> needs, since both
  headers' one exported type is itself always a \<open>typedef\<close>. The genuine
  glibc shape of \<open>jmp_buf\<close> - an array of a tagged struct, not the struct
  itself - registers and resolves correctly, same as \<open>stdarg.h\<close>'s simpler
  \<open>va_list\<close>.

  This mechanism has two narrow, documented limitations (\<open>C11_Typedefs\<close>'s
  own note in \<^verbatim>\<open>C11_Parser.thy\<close>), neither exercised by the headers below:
  a typedef'd name used as the \<^emph>\<open>literal next\<close> token right after its own
  \<open>";"\<close> is not recognized (the lexer may already have fetched that token as
  a plain identifier, its own required lookahead, before registration can
  run); and once registered, a name stays a typedef name for the rest of
  the session, so - matching real C's own restriction - it cannot later be
  redeclared as an unrelated, fresh typedef.\<close>
c11_predef [setjmp.h] \<open>
typedef struct __jmp_buf_tag { int __magic; } jmp_buf[1];
int setjmp(jmp_buf env);
void longjmp(jmp_buf env, int val);
\<close>

c11_predef [stdarg.h] \<open>
typedef struct { int __offset; } va_list;
int vprintf(const char *format, va_list ap);
\<close>

text\<open>Confirmed via the same "not registered before \<open>#include\<close>, registered
  after" round-trip as the other headers above - both \<open>jmp_buf\<close>/\<open>va_list\<close>
  themselves (as types) and the functions declared in terms of them use
  correctly within one translation unit.\<close>
c11\<open>
#include <setjmp.h>
#include <stdarg.h>

int use_typedefs(void) {
  jmp_buf env;
  va_list ap;
  return setjmp(env);
}
\<close>

ML\<open>
val CEnv.mk {idents, ...} = CEnv.get (Context.Theory @{theory})
val _ =
  List.app (fn name =>
              case Symtab.lookup idents name of
                SOME _ => ()
              | NONE => error ("FAIL: " ^ name ^ " not registered after #include"))
    ["setjmp", "longjmp", "vprintf"]
\<close>

text\<open>Regression test for the error-recovery corruption this feature's
  registration side effect was originally vulnerable to (see the long note
  on \<open>C11_Typedefs.snapshot\<close>/\<open>restore\<close> in \<^verbatim>\<open>C11_Parser.thy\<close>): a
  \<open>c11_reject\<close> fragment reusing a fresh name right next to a malformed
  declaration must never leak a spurious typedef registration for that
  name, even though the fragment drives ML-Yacc's error-recovery path -
  confirmed here by using that same name in an ordinary, immediately
  following declaration and checking it is \<^emph>\<open>not\<close> mistaken for a type.\<close>
c11_reject\<open>
regression_probe_name y = 5 regression_probe_name z = 6;
\<close>
c11\<open>
int regression_probe_name = 7;
\<close>

subsection\<open>\<open>set_cenv_default\<close>/\<open>reset_cenv\<close>: Explicit Control over \<open>cenv\<close>'s Scope\<close>
text\<open>
  Every \<open>c11\<close>-family command threads \<open>cenv\<close> through the theory like any
  other persistent, per-theory Isabelle state, which is what lets \<open>c11\<close>
  fragments be freely interleaved with arbitrary Isar content and still
  resolve a name back to its declaration in an earlier fragment - but it
  also means \<open>cenv\<close> only ever grows, with no built-in notion of "start
  fresh". \<open>set_cenv_default\<close> nominates the \<^emph>\<open>current\<close> \<open>cenv\<close> as the
  snapshot a later \<open>reset_cenv\<close> restores; \<open>reset_cenv\<close> alone, with no
  prior \<open>set_cenv_default\<close>, falls back to \<^ML>\<open>CEnv.empty_cenv\<close> rather than
  erroring (confirmed separately via an isolated probe, per this project's
  own verification convention, since every test in \<^emph>\<open>this\<close> theory runs
  after \<open>fact\<close>/\<open>helper\<close>/\<open>\<dots>\<close> above have already accumulated into \<open>cenv\<close>,
  so "no prior default anywhere in scope" cannot be exercised here).

  \<open>set_cenv_default\<close> is called first below, so the snapshot it captures
  already includes everything the \<^emph>\<open>rest of this theory\<close> - both above and
  below this point - depends on (\<open>fact\<close>, the struct/union/enum tags, \<open>\<dots>\<close>);
  only the throwaway names declared \<^emph>\<open>after\<close> that point and \<^emph>\<open>before\<close> the
  matching \<open>reset_cenv\<close> are ever at risk of being discarded.\<close>
set_cenv_default
c11\<open>int cenv_reset_probe_a;\<close>
ML\<open>
val CEnv.mk {idents, ...} = CEnv.get (Context.Theory @{theory})
val _ =
  if Symtab.defined idents "cenv_reset_probe_a" andalso Symtab.defined idents "fact" then ()
  else error "FAIL: both the just-declared probe and an earlier declaration should be visible"
\<close>
reset_cenv
ML\<open>
val CEnv.mk {idents, ...} = CEnv.get (Context.Theory @{theory})
val _ =
  if Symtab.defined idents "cenv_reset_probe_a" then
    error "FAIL: cenv_reset_probe_a (declared after set_cenv_default) should not survive reset_cenv"
  else ()
val _ =
  if Symtab.defined idents "fact" then ()
  else error "FAIL: fact (declared before set_cenv_default) should survive reset_cenv"
\<close>
text\<open>Accumulation resumes normally from the restored baseline - a fresh
  declaration after \<open>reset_cenv\<close> is visible, the discarded one stays gone.\<close>
c11\<open>int cenv_reset_probe_b;\<close>
ML\<open>
val CEnv.mk {idents, ...} = CEnv.get (Context.Theory @{theory})
val _ =
  if Symtab.defined idents "cenv_reset_probe_b" andalso Symtab.defined idents "fact"
     andalso not (Symtab.defined idents "cenv_reset_probe_a")
  then ()
  else error "FAIL: accumulation after reset_cenv did not resume from the restored baseline"
\<close>

subsection\<open>\<open>c11_file\<close> on real-world C11 sources (\<^verbatim>\<open>parser_menhir\<close>)\<close>
text\<open>
  \<^verbatim>\<open>examples/\<close> vendors three files, unmodified, from the \<^verbatim>\<open>parser_menhir\<close>
  C11 conformance test suite (via its copy in the Isabelle_C AFP entry, see
  \<^verbatim>\<open>examples/README.md\<close> for provenance and license), the same files
  Isabelle_C's own \<open>C0.thy\<close> exercises its lexer/parser against. None of them
  use this fragment's unsupported constructs (real \<open>#define\<close>, \<open>#if\<close>/\<open>#elif\<close>,
  backslash-newline), so all three are expected to succeed here too - genuine,
  non-trivial C11 (compound literals, deeply nested declarators, anonymous
  struct/union members, \<open>[*]\<close> parameter arrays, the dangling-\<open>else\<close> case,
  \<open>\<dots>\<close>), not code written for this theory.
\<close>
c11_file \<open>examples/expressions.c\<close>
ML\<open>Position.file_of (AnaEval.pos_of_root (!AST))\<close>

c11_file \<open>examples/dangling_else.c\<close>
c11_file \<open>examples/declarators.c\<close>

text\<open>Regression test for \<open>run_c11_file\<close>'s own fix, above: \<open>c11_file\<close> used to
  call neither \<open>analyse_and_eval\<close> nor \<open>full_eval_and_store\<close> at all, so a
  file read this way got no declaration/use hyperlinking whatsoever, unlike
  every other accepting command. \<^verbatim>\<open>examples/expressions.c\<close> alone declares
  several functions (\<open>test1\<close>/\<open>test2\<close>/\<open>test3\<close>/\<open>test4\<close>/\<open>test_sizeof\<close>, with
  \<open>test4\<close> even calling itself recursively) - checking that \<^emph>\<open>some\<close> \<open>Global\<close>
  identifier ended up registered in \<open>CEnv\<close> after the three \<open>c11_file\<close> calls
  above is a direct, batch-checkable witness that \<open>analyse_and_eval\<close>
  genuinely ran against file-sourced input, not just inline \<open>c11\<close> ones.\<close>
ML\<open>
val CEnv.mk {idents, ...} = CEnv.get (Context.Theory @{theory})
val globals = Symtab.dest idents |> List.filter (fn (_, CEnv.Global _) => true | _ => false)
val _ =
  if null globals
  then error "FAIL: c11_file did not register any Global identifiers - analyse_and_eval did not run"
  else writeln ("PASS: c11_file registered " ^ Int.toString (length globals) ^
                " global identifier(s), e.g. \"" ^ #1 (hd globals) ^ "\"")
\<close>


subsection\<open>Tests for Arithmetic, Bitwise, Relational and Logical Operators\<close>
text\<open>
  The following blocks exercise the expression language (\<open>expression\<close> down to
  \<open>primary_expression\<close>) more broadly, roughly one grammar layer at a time.
\<close>

c11\<open>
int test_arith(void) {
  int a = 10, b = 3, c; /* @ probe_ast \<open>hjgfhg\<close> */
  c = a + b - a * b / b % a ;
  c = (a << 1) >> 1; /* just a text
                        @ highlight
                        that ends here.
                      */
  c = (a & b) | (a ^ b);
  c = ~a & !b;
  c = a < b || a > b;
  c = a <= b && a >= b;
  c = a == b;
  c = a != b;
  return c;
}
\<close>

ML\<open>CEnv.get_ast "C11_Tests#4" @{theory}\<close>

c11\<open>
int f(int x) {
  int a = 10, b = 3, c; /* @highlight */
  c = a + b - a * b / b % a ;
  return c;
}
\<close>

declare [[ML_print_depth=100]]
ML\<open>CEnv.get_ast "C11_Tests#5" @{theory}\<close>


subsection\<open>Tests on Assignment operators, Increment/decrement, Comma and ternary Operators\<close>
c11\<open>
int test_assign(void) {
  int a = 1, b = 2, r;
  a += 1; a -= 1; a *= 2; a /= 2; a %= 3;
  a <<= 1; a >>= 1; a &= 1; a |= 2; a ^= 1;
  r = a++;
  r = ++a;
  r = b--;
  r = --b;
  r = (a = b);
  r = a > b ? a : b;
  r = (a += 1, b += 1, a + b);
  return r;
}
\<close>

subsection\<open>Pointers, arrays, structs, casts, sizeof/alignof, and generic selection\<close>
c11\<open>
struct point { int x; int y; };

int test_misc(int n, ...) {
  int arr[5] = {1, 2, 3, 4, 5};
  int *p = &arr[0];
  struct point pt = { .x = 1, .y = 2 };
  struct point *pp = &pt;
  int s1 = sizeof(int);
  int s2 = sizeof arr;
  int s3 = _Alignof(int);
  int c1 = (int) 3.14;
  double c2 = (double) n;
  int g = _Generic(n, int: 1, default: 0);
  int cl = (int[]){1, 2, 3}[0];
  return *p + arr[n] + pt.x + pp->y + s1 + s2 + s3 + c1 + g + cl;
}
\<close>

text\<open>
  The following blocks exercise statement-level constructs (\<open>statement\<close> and its
  alternatives): iteration, selection/switch, and jump statements including \<open>goto\<close>.
\<close>

subsection\<open>Iteration statements: while, do-while, and all four for-loop forms\<close>
c11\<open>
int test_loops(void) {
  int i = 0;
  int sum = 0;

  while (i < 10) {
    sum += i;
    i++;
  }

  i = 0;
  do {
    sum += i;
    i++;
  } while (i < 5);

  for (i = 0; i < 10; i++) {
    if (i == 5)
      continue;
    sum += i;
  }

  for (i = 0; i < 10; )
    i++;

  for (int j = 0; j < 10; )
    j++;

  for (int j = 0, k = 10; j < k; j++, k--) {
    sum += j - k;
  }

  return sum;
}
\<close>


subsection\<open>Switch statement, fallthrough, labeled statements, and goto\<close>
c11\<open>
int test_switch_goto(int x) {
  int result = 0;

  switch (x) {
    case 0:
      result = 100;
      break;
    case 1:
    case 2:
      result = 200;
      break;
    default:
      result = -1;
      break;
  }

  int i = 0;
  loop_start:
  if (i < 5) {
    result += i;
    i++;
    goto loop_start;
  }

  switch (x) {
    case 3: {
      int y = x * 2;
      result += y;
    }
    default:
      result += 1;
  }

  return result;
}
\<close>



section\<open>Error-recovery / Malformed-input Tests\<close>

text\<open>Each of the following fragments is syntactically invalid, and \<open>c11_reject\<close>
  (defined above) fails the theory build if the parser unexpectedly \<^emph>\<open>accepts\<close>
  one of them, rather than reporting the expected parse error.\<close>

subsection\<open>Unbalanced braces and parentheses\<close>
c11_reject\<open>
int main(void) { return 0;
\<close>
c11_reject\<open>
int max(int a, int b { return a; }
\<close>
c11_reject\<open>
int main(void) { return 0; } }
\<close>

subsection\<open>Missing Separators and dangling Operators\<close>
c11_reject\<open>
int x = 5 int y = 6;
\<close>
c11_reject\<open>
int x = 1 + ;
\<close>
c11_reject\<open>
int y = ;
\<close>

subsection\<open>Keywords vs. Identifiers\<close>
text\<open>Keywords cannot be used as identifiers.\<close>
c11_reject\<open>
int if = 5;
\<close>

subsection\<open>C11 - Specifics\<close>
text\<open>Unlike pre-C99 Kernighan\<open>&\<close>Ritchie C, C11 has no implicit \<open>int\<close>:
     a function definition needs declaration specifiers.\<close>
c11_reject\<open>
main(void) { return 0; }
\<close>


subsection\<open>The Preprocessor Fragment\<close>
text\<open>The preprocessor fragment: a missing header name, and an unterminated \<open>#ifdef\<close>.\<close>
c11_reject\<open>
#include
int x;
\<close>

c11_reject\<open>
#ifdef DEBUG
int x;
\<close>

section\<open>Antiquotation-carrying Comments (cf. Isabelle_C's \<^verbatim>\<open>C1.thy\<close>)\<close>

text\<open>
  \<open>analyse_and_eval\<close> (wired into \<open>run_c11_kind\<close> above) errors on any
  \<open>Antiquotation\<close> whose tag has no handler registered in \<open>CEnv\<close>, so the
  \<open>@setup\<close>/\<open>@requires\<close>/\<open>@ensures\<close> tags the tests below carry each need one -
  a dummy is enough here: none of these tests are about what the handler
  \<^emph>\<open>does\<close>, only about the lexer/parser/\<open>analyse_and_eval\<close> machinery around
  it, so each dummy simply reports it ran and returns the theory unchanged.
\<close>
ML\<open>
fun dummy_antiq tag =
  let
    fun probe (_, _, level) (body, _ : Position.T) thy =
      (writeln (quote tag ^ " (level " ^ Int.toString level 
                          ^ "): This is a dummy-antiquotation. body=" 
                          ^ quote body);
       thy)
  in CEnv.store_antiq (tag, probe) end
\<close>
setup\<open>dummy_antiq "setup"\<close>
setup\<open>dummy_antiq "requires"\<close>
setup\<open>dummy_antiq "ensures"\<close>

text\<open>
  A line comment carrying a tag and a properly-nested cartouche, adapted from
  Isabelle_C's own \<open>#include\<close> example (\<^verbatim>\<open>C11-FrontEnd/examples/C1.thy\<close>). The
  lexer reports \<open>@setup\<close> and the cartouche as PIDE markup; \<open>analyse_and_eval\<close>
  dispatches it to the dummy handler just above.
\<close>
c11\<open>
int b;
//@ setup \<open>Include.append "tmp" [\<open>b\<close>]\<close>
int a = b;
\<close>

text\<open>A block-comment variant, with a doubly-nested cartouche.\<close>
c11\<open>
/*@ setup \<open>Include.append "tmp" [\<open>b\<close>, \<open>c\<close>]\<close> */
int a = 0;
\<close>

text\<open>
  A Frama-C/ACSL-style annotation comment (Isabelle_C's other supported style):
  each line is introduced by ACSL's own \<open>@\<close> continuation marker, followed by
  a bare keyword and a plain double-quoted string. Syntactically this is
  exactly the \<open>@tag "..."\<close> shape from above, so - now that a quoted string is
  a recognized alternative to a cartouche body - \<open>requires\<close>/\<open>ensures\<close> are
  picked up as genuine (level-\<open>0\<close>) antiquotation nodes here, tag and body
  text alike; nothing about \<open>requires\<close>/\<open>ensures\<close> is otherwise special to the
  lexer - it has no notion of an ACSL command language, and each dispatches
  to the same dummy handler as \<open>@setup\<close> above (registered for exactly this
  reason) - it just happens that ACSL's own annotation syntax already fits
  the general tag+string shape this fragment recognizes.
\<close>
c11\<open>
/*@ requires "n >= 0"
  @ ensures "result >= 0"
  @ highlight
 */
int abs(int n) {
  if (n < 0) return -n;
  return n;
}
\<close>

text\<open>
  The tag may also carry an optional parenthesized integer \<open>level\<close>
  (\<open>@tag(N) ...\<close>, \<open>0\<close> when omitted), and the body may be written either as
  a cartouche, as above, or - an equivalent alternative notation - as a
  double-quoted string \<open>@tag(N) "..."\<close>; both spellings are recorded
  identically in the AST (same tag, level, and body text).
\<close>
c11\<open>
int b;
//@ setup(2) \<open>beta\<close>
//@ setup(1) \<open>alfa - textually later, executed earlier!\<close>
int a = b;
\<close>

c11\<open>
/*@ setup(3) \<open>Include.append "tmp" [\<open>c\<close>]\<close> */
int a = 0;
\<close>

c11\<open>
/*@ setup "a plain quoted body, default level" */
int a = 0;
\<close>

text\<open>
  A bare quote with no tag anywhere nearby is never mistaken for an
  antiquotation body: the combined tag+string rule only fires when a quote
  genuinely follows a tag (modulo horizontal whitespace), so unrelated
  quoted text elsewhere in a comment keeps parsing as ordinary comment text.
\<close>
c11\<open>
/* just a "quoted" word here, no tag in sight */
int a = 0;
\<close>

subsection\<open>Exactly-Once Dispatch, an Always-Defined Context, and \<open>term\<close>\<close>
text\<open>
  \<open>analyse_and_eval\<close> threads a second, downward-only \<open>ctx\<close> parameter through
  every walk function (see the design note at the top of \<^verbatim>\<open>AnaEval.thy\<close>):
  \<open>walk_expr\<close>/\<open>walk_stat\<close> always push their own node, at every level of
  nesting, so a comment resolves to the \<^emph>\<open>closest\<close> enclosing expression/
  statement/unit rather than only to a whole top-level declaration or
  statement; a node kind that used to \<open>error "...not supported..."\<close> (a
  block-local declaration, a \<open>for\<close>-loop's own clause, a function parameter, a
  cast's abstract type-name) now simply falls back to its closest enclosing
  context instead. Separately, \<open>check_antiq\<close> tracks already-dispatched
  antiquotation \<^emph>\<open>values\<close> (\<^verbatim>\<open>Dispatched_Antiqs\<close>) so a single physical comment
  is never evaluated twice, however many AST nodes reachable from the walk
  happen to share its leftmost source position.
\<close>
ML\<open>
val COUNT = Unsynchronized.ref 0
val counting_antiq = 
       let fun probe _ _ thy = (COUNT := !COUNT + 1; thy) 
       in CEnv.store_antiq ("counter", probe) end
\<close>
setup\<open>counting_antiq\<close>

text\<open>Exactly-once dispatch: the comment sits right before the leftmost token
  of both the wrapped expression's own \<open>nodeInfo\<close> and the enclosing
  expression-statement's own \<open>nodeInfo\<close> - the classic shared-position case
  that used to double-dispatch.\<close>
c11\<open>
int test_dispatch_once(void) {
  /*@ counter */ 1 + 1;
  return 0;
}
\<close>
ML\<open>if !COUNT = 1 then ()
   else error ("Antiquotation dispatched " 
               ^ Int.toString (!COUNT) 
               ^ " times, expected exactly 1")\<close>

text\<open>Always-defined context, at four different granularities that used to
  either \<open>error\<close> outright or only ever resolve to one whole top-level
  declaration: a block-local declaration resolves to the enclosing compound
  statement; a \<open>for\<close>-loop's own declaration clause resolves to the enclosing
  \<open>for\<close> statement; a function parameter resolves to the shared top-level
  unit (a function header never pushes its own frame); and - the finest
  granularity, needed specifically for cast-level annotations - a
  sub-expression nested three levels deep (inside a multiplication, inside a
  cast, inside an addition) resolves to exactly that sub-expression, not the
  cast, not the addition, not the enclosing statement.\<close>
c11\<open>
int test_ctx_block_local(void) {
  /*@ probe_ast
    @ highlight */ 
  int x = 5;
  return x;
}
\<close>
ML\<open>case !AST of
     C_Ast.Stmt (C_Ast.CCompound _) => ()
   | other => error ("Expected Stmt (CCompound _), got " ^ C_Ast.pp_root other)\<close>

c11\<open>
int test_ctx_for_clause(void) {
  int s = 0;
  for (/*@ probe_ast */ int i = 0; i < 3; i = i + 1) { s = s + i; }
  return s;
}
\<close>
ML\<open>case !AST of
     C_Ast.Stmt (C_Ast.CFor _) => ()
   | other => error ("Expected Stmt (CFor _), got " ^ C_Ast.pp_root other)\<close>

c11\<open>
int test_ctx_param(/*@ probe_ast */ int p) {
  return p;
}
\<close>
ML\<open>case !AST of
     C_Ast.Units [C_Ast.CTranslUnit _] => ()
   | other => error ("Expected Units [CTranslUnit _], got " ^ C_Ast.pp_root other)\<close>

c11\<open>
int test_ctx_finest(int a, int b, int c) {
  int r = a + (int)(/*@ probe_ast */ b * c);
  return r;
}
\<close>
ML\<open>case !AST of
     C_Ast.Expr (C_Ast.CBinary (_,
                   C_Ast.CVar (C_Ast.Ident ("b", _, _), _),
                   C_Ast.CVar (C_Ast.Ident ("c", _, _), _), _)) => ()
   | other => error ("Expected Expr (CBinary (_, b, c, _)), got " ^ C_Ast.pp_root other)\<close>

text\<open>Top-level sharing: a comment on one global declaration among several now
  resolves to the whole original translation unit, not just the one
  declaration it sits on.\<close>
c11\<open>
int test_ctx_g1;
int test_ctx_g2;
/*@ probe_ast */
int test_ctx_g3;
\<close>
ML\<open>case !AST of
     C_Ast.Units [C_Ast.CTranslUnit (eds, _)] =>
       if length eds = 3 then ()
       else error ("Shared root holds " ^ Int.toString (length eds) ^ " declarations, expected 3")
   | other => error ("Expected Units [CTranslUnit (_, _)], got " ^ C_Ast.pp_root other)\<close>

text\<open>The \<open>term\<close> antiquotation: parses its cartouche body as a genuine HOL
  term against the theory's current context via \<^ML>\<open>Syntax.read_term\<close> - an
  ACSL-style \<open>requires\<close>/\<open>ensures\<close> clause written this way is now a real,
  checked HOL proposition, not just stored text. Note that the term 
  antiquotation allows fot type-checking, navigation, hovering and coloring
  of free variables in the current Isabelle/HOL context.\<close>
c11\<open>
//@ term \<open>\<lambda>x. [1 + (0::nat) + a] @ [] = [2+x]\<close>
int test_term_anchor;              
\<close>

ML\<open>if !TERM_PROBE <> Free ("dummy_term_probe", dummyT) then ()
   else error "TERM_PROBE ref was never updated"\<close>

subsection\<open>Navigation Strings in Antiquotations\<close>
text\<open>
  An antiquotation may carry a navigation string - zero or more
  \<open>u\<close>/\<open>U\<close> steps followed by zero or more \<open>r\<close>/\<open>d\<close> steps (so it may be
  empty), written as an optional bracketed \<open>[navi]\<close> right after the tag and
  before the optional \<open>(level)\<close> or the body: \<open>@tag[navi](level) \<open>...\<close>\<close>. It
  is mapped into \<open>C_Ast.navi list\<close> (\<open>u\<close>\<open>\<mapsto>\<close>\<open>up\<close>, \<open>U\<close>\<open>\<mapsto>\<close>\<open>Up\<close>, \<open>r\<close>\<open>\<mapsto>\<close>
  \<open>right\<close>, \<open>d\<close>\<open>\<mapsto>\<close>\<open>down\<close>) and, unlike the round that first introduced the
  syntax, is now genuinely *interpreted*: \<open>AnaEval.check_antiq\<close> resolves it
  against the closest-surrounding-context stack via \<open>AnaEval.select_ast\<close>
  \<^emph>\<open>before\<close> calling the handler, so a handler only ever sees the resulting
  AST node (\<open>type_antiq_fun\<close> in \<^verbatim>\<open>CEnv.thy\<close> has no navi-list parameter at
  all any more) - the tests below therefore check the resolved \<open>!AST\<close>
  (via \<open>probe_ast\<close>), not a stashed navi list.

  The bracket is its own delimiter rather than bare adjacency to the tag,
  deliberately: \<open>u\<close>/\<open>U\<close>/\<open>r\<close>/\<open>d\<close> are ordinary identifier characters with no
  special lexical status, and the tag regex is greedy, so \<open>@answer\<close> (a tag
  that happens to end in the single-character navi alphabet) must keep
  meaning the whole tag \<open>"answer"\<close> with no navi steps at all, not
  \<open>"answe"\<close> plus a navi step \<open>r\<close> - the ambiguity check below confirms this
  explicitly.\<close>

ML\<open>
val NAVI_COUNT = Unsynchronized.ref 0
val counting_navi_antiq = let fun probe _ _ thy = (NAVI_COUNT := !NAVI_COUNT + 1; thy) in CEnv.store_antiq ("answer", probe) end
\<close>
setup\<open>counting_navi_antiq\<close>

text\<open>No brackets at all, and empty brackets, both give an empty navi list -
  \<open>select_ast\<close> is the identity on an empty list, so both resolve to the same
  closest context as an ordinary, navi-free antiquotation (cf. the
  "top-level sharing" tests above).\<close>
c11\<open>
/*@ probe_ast */
int navi_none;
\<close>
ML\<open>case !AST of C_Ast.Units [C_Ast.CTranslUnit _] => ()
   | other => error ("Expected Units [CTranslUnit _], got " ^ C_Ast.pp_root other)\<close>

c11\<open>
/*@ probe_ast[] */
int navi_empty;
\<close>
ML\<open>case !AST of C_Ast.Units [C_Ast.CTranslUnit _] => ()
   | other => error ("Expected Units [CTranslUnit _], got " ^ C_Ast.pp_root other)\<close>

text\<open>The ambiguity check: a tag ending in a navi-alphabet letter, with no
  brackets, must still parse as that whole tag with an empty navi list.\<close>
c11\<open>
/*@ answer */
int navi_tag_ends_in_r;
\<close>
ML\<open>if !NAVI_COUNT = 1 then ()
   else error ("Expected the \"answer\" tag to fire exactly once, fired " ^ Int.toString (!NAVI_COUNT))\<close>

text\<open>\<open>u\<close>/\<open>U\<close> ascent: the antiquotation sits on the innermost \<open>b * c\<close>, whose
  closest-context stack is three consecutive \<open>Expr\<close> frames (\<open>b * c\<close>, the
  cast around it, the addition around that) before the enclosing statement -
  exactly the \<open>[expr, expr, expr, stmt, ...]\<close> shape from the design
  discussion. A lone, final \<open>u\<close> is a no-op (rule 1); two \<open>u\<close>s pop exactly
  one frame (rule 2); a single \<open>U\<close> collapses the whole three-\<open>expr\<close> run to
  its outermost member in one step (rule 3), landing on the very same node
  three plain \<open>u\<close>s reach - a direct consistency check between the two rules;
  \<open>Uuu\<close> continues two further ascents past that collapsed run.\<close>
c11\<open>
int test_navi_u(int a, int b, int c) {
  int r = a + (int)(/*@ probe_ast[uu] 
                      @ highlight[uu] */ b * c);
  return r;
}
\<close>
ML\<open>case !AST of C_Ast.Expr (C_Ast.CCast _) => ()
   | other => error ("[uu]: expected Expr (CCast _), got " ^ C_Ast.pp_root other)\<close>

c11\<open>
int test_navi_uuu(int a, int b, int c) {
  int r = a + (int)(/*@ probe_ast[uuu]
                      @ highlight[uuu] */ b * c);
  return r;
}
\<close>
ML\<open>case !AST of
     C_Ast.Expr (C_Ast.CBinary (C_Ast.CAddOp, _, _, _)) => ()
   | other => error ("[uuu]: expected Expr (CBinary (CAddOp, _, _, _)), got " ^ C_Ast.pp_root other)\<close>

c11\<open>
int test_navi_bigU(int a, int b, int c) {
  int r = a + (int)(/*@ probe_ast[U] */ b * c);
  return r;
}
\<close>
ML\<open>case !AST of
     C_Ast.Expr (C_Ast.CBinary (C_Ast.CAddOp, _, _, _)) => ()
   | other => error ("[U]: expected Expr (CBinary (CAddOp, _, _, _)), same as [uuu], got " ^
                      C_Ast.pp_root other)\<close>

c11\<open>
int test_navi_Uuu(int a, int b, int c) {
  int r = a + (int)(/*@ probe_ast[Uuu] */ b * c);
  return r;
}
\<close>
ML\<open>case !AST of C_Ast.Stmt (C_Ast.CCompound _) => ()
   | other => error ("[Uuu]: expected Stmt (CCompound _) (the function body), got " ^
                      C_Ast.pp_root other)\<close>

text\<open>\<open>r\<close>/\<open>d\<close> descent: the antiquotation sits directly on an \<open>if\<close> statement
  (so its own closest context already \<^emph>\<open>is\<close> that \<open>CIf\<close>, no \<open>u\<close>/\<open>U\<close> prefix
  needed), whose three navigable children are the condition, the \<open>then\<close>
  branch, and the \<open>else\<close> branch, in that order: \<open>rd\<close>/\<open>rrd\<close>/\<open>rrrd\<close> select
  the first/second/third respectively - matching the design discussion's
  own worked example.\<close>
c11\<open>
int test_navi_rd(int a) {
  /*@ highlight[rd] */ if (a) return 1; else return 0;
}\<close>
c11\<open>
int test_navi_rrd(int a) {
  /*@ highlight[rrd] */ if (a) return 1; else return 0;
}\<close>
c11\<open>
int test_navi_rrrd(int a) {
  /*@ highlight[rrrd] */ if (a) return 1; else return 0;
}\<close>

text\<open>\<open>r\<close>/\<open>d\<close> descent generalizes to every \<open>cStatement\<close>/\<open>cExpression\<close>
  constructor, not just \<open>CIf\<close> (\<open>AnaEval.children_of_stmt\<close>/
  \<open>AnaEval.children_of_expr\<close>): the antiquotation here sits on the whole
  expression-\<^emph>\<open>statement\<close> \<open>a + b;\<close>, so a first \<open>d\<close> descends into
  \<open>CExpr\<close>'s one child (the wrapped \<open>CBinary\<close>) before a second \<open>d\<close>/\<open>rd\<close>
  reaches the binary's own left/right operand.\<close>
c11\<open>
int test_navi_binary_left(int a, int b) {
  /*@ highlight[dd] */ a + b;
  return 0;
}\<close>
c11\<open>
int test_navi_binary_right(int a, int b) {
  /*@ highlight */ a + b;
  return 0;
}\<close>

text\<open>\<open>CCall\<close>'s children are the called function expression followed by its
  arguments, in order.\<close>
c11\<open>
int test_navi_call_arg(int f(int, int), int x, int y) {
  /*@ highlight[drrrd] */ f(x, y);
  return 0;
}\<close>

text\<open>\<open>CCompound\<close>'s children are its \<^emph>\<open>statements\<close> alone, in order -
  a block-local declaration has no \<open>root\<close> variant, so it is silently
  skipped rather than occupying a navigable index.\<close>
c11\<open>
int test_navi_compound_skips_decl(void) {
  /*@ highlight[d] */
  {
    int x = 0;
    x = 1;
  }
  return 0;
}\<close>

text\<open>\<open>d\<close> on a leaf must \<open>error\<close>, not raise an uncaught SML \<open>Subscript\<close>
  exception - the antiquotation here sits on \<open>a\<close> (an expression-statement
  wrapping a bare \<open>CVar\<close>), so \<open>[dd]\<close> reaches the leaf via one \<open>d\<close> through
  \<open>CExpr\<close>'s own single child before the second \<open>d\<close> finds nothing to
  descend into. \<open>c11_reject\<close> cannot express this: it only ever exercises
  the parser, never \<open>analyse_and_eval\<close>, so a fragment that parses fine but
  fails \<open>select_ast\<close> is not something it can reject. This is therefore run
  directly via \<open>run_c11\<close> (the same function the \<open>c11\<close> command itself
  calls) inside a \<open>handle ERROR\<close> that re-raises unless the message is
  exactly the expected "navigation index ... out of range" one - the
  resulting theory is discarded either way, so this never actually stores
  anything.

  \<open>@{here}\<close>, not \<open>Input.string\<close>, supplies the source's start/end position:
  \<open>Input.string\<close>'s \<open>Position.no_range\<close> starves the lexer of a real
  reference offset, which silently breaks position-based comment
  attachment (the antiquotation ends up attached to the whole function
  instead of \<open>a\<close>, so the wrong error fires) rather than failing loudly -
  confirmed empirically, not merely inferred.\<close>
ML\<open>
val _ =
  (run_c11 (Input.source true
       "int leaf_error_test(int a) {\n  /*@ probe_ast[dd] */ a;\n  return 0;\n}\n"
       (@{here}, @{here})) @{theory};
   error "leaf-error test: expected a select_ast navigation error, but none occurred")
  handle ERROR msg =>
    if String.isSubstring "navigation index" msg then ()
    else error ("leaf-error test: unexpected error message: " ^ msg)
\<close>

section\<open>Comment Nesting (cf. Isabelle_C's \<^verbatim>\<open>C0.thy\<close>)\<close>

text\<open>
  Adapted from Isabelle_C's own comment-nesting example, which follows
  \<^url>\<open>https://gcc.gnu.org/onlinedocs/cpp/Initial-processing.html\<close>: a \<open>/* */\<close>
  comment does \<^emph>\<open>not\<close> nest, so the first \<open>*/\<close> closes it - the code after is
  live, not still-commented-out. \<open>c11\<close> succeeding on this is itself the test.
\<close>
c11\<open>
/* inside /* inside */ int a = 1;
// inside // inside until end of line
int b = 2;
/* inside
  // inside
inside
*/ int c = 3;
// inside /* inside until end of line
int d = 4;
\<close>

section\<open>What Falls Outside This Fragment (cf. Isabelle_C's \<^verbatim>\<open>C0.thy\<close>)\<close>

text\<open>
  Isabelle_C's directive/macro stress tests use the real C preprocessor's
  \<open>#define\<close> (juxtaposed replacement-list, no \<open>=\<close>) and general \<open>#if\<close>/\<open>#elif\<close>,
  neither of which this simplified fragment implements (this theory's own
  \<open>#define name = expr\<close> and \<open>#ifdef\<close>/\<open>#ifndef\<close> only). \<open>c11_reject\<close> documents
  the boundary instead of silently skipping it.
\<close>
c11_reject\<open>
#define a zz
\<close>
c11_reject\<open>
#ifdef a
#elif
#else
#if
#endif
#endif
\<close>

text\<open>
  Likewise, backslash-newline splicing (ISO C11 translation phase 2, which
  would let a keyword be split across lines by ending each fragment with a
  backslash, e.g. \<open>i\<close> then a line break then \<open>nt\<close> for \<open>int\<close>) is not
  implemented: it would require preprocessing the source text before lexing,
  with its own position-mapping machinery, which is out of scope here. Below,
  the split keyword is lexed as the two identifiers \<open>i\<close> and \<open>nt\<close> rather
  than as \<open>int\<close>, so the fragment is correctly rejected.
\<close>
c11_reject\<open>
i\
nt a = 1;
\<close>

section\<open>A Pitfall: a Point Reported as a Range Looks Fine Until It Isn't\<close>

text\<open>
  This note documents a concrete case, found while hyperlinking declarations and uses of
  identifiers in a language built on this framework, of the pitfall already flagged in
  \secref{sec:positions}: ``A single point position is rarely what a caller wants to
  highlight - a \<^emph>\<open>range\<close> is.'' It is included here as its own section, separate from the
  main manual, so it can be pulled into \<^verbatim>\<open>Manual.thy\<close>'s ``Calculating Positions'' section
  (or elsewhere) once its final placement is decided.

  It is tempting, for a single token such as an identifier, to build its @{ML_type
  \<open>Position.T\<close>} once at the token's start and then reuse that same point wherever the
  framework asks for a range - as the value passed to @{ML \<open>Context_Position.report\<close>} or
  wrapped in @{ML \<open>Position.entity_markup\<close>}, say. This compiles, and it even \<^emph>\<open>looks\<close>
  correct under casual testing, because a bare point and a genuine one-symbol range render
  identically: there is nothing for the IDE to show differently between ``this token is one
  symbol wide and fully covered'' and ``only the first symbol of this token is covered''.
  The mistake only becomes visible once a token \<^emph>\<open>longer\<close> than one symbol is reported the
  same way - and then only its very first symbol ends up highlighted, hoverable, or
  clickable, with the rest of the token showing no markup at all. Test cases built from
  short, one-letter example names (\<open>x\<close>, \<open>i\<close>) will never expose this; the bug hides until
  someone happens to click on the third letter of a longer name and finds nothing there.

  The fix is to never pass a bare point where a range is wanted: given the point @{term
  \<open>pos\<close>} at which a name of known text @{term \<open>name\<close>} starts, @{ML
  \<open>fn (name, pos) => Position.symbol_explode name pos\<close>} advances @{term \<open>pos\<close>} across
  exactly that text to the name's own end position (correctly, in symbols -
  \secref{sec:positions}), and
  @{ML \<open>fn (name, pos) => Position.range_position (Position.range (pos, Position.symbol_explode name pos))\<close>}
  folds start and end back into the one @{ML_type \<open>Position.T\<close>} the reporting functions
  expect. Build that combined position once and report \<^emph>\<open>it\<close>, not the bare start point, at
  every use of that name - declaration, self-reference, and every later occurrence alike.
\<close>

end
