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

(*<*)
theory Java_Manual
  imports "Java25.Java"
begin
(*>*)

section\<open>What is Isabelle/Java\<close>

text\<open>
  Isabelle/Java is a front-end that lets Java source text live inside an Isabelle theory as a
  first-class citizen: parsed by a real grammar, checked incrementally under Isabelle/PIDE (so a
  syntax error or a malformed annotation is reported like any other Isabelle error, with the
  usual jEdit markup, hyperlinking and hovering), and open to attaching arbitrary
  Isabelle-level content - proof obligations, HOL terms, arbitrary Isar commands - to specific
  points of the Java source via a comment-based antiquotation mechanism. It is not a Java
  compiler, nor a verification tool in its own right: it is the \<^emph>\<open>front-end layer\<close> on which one
  builds a verification tool (a semantic backend, for instance a translation of Java programs
  into HOL), a documentation generator, or a static analysis.
\<close>

subsection\<open>Context\<close>

text\<open>
  \<^bold>\<open>Java has an official grammar.\<close> \<^emph>\<open>The Java Language Specification, Java SE 25
  Edition\<close> \<^cite>\<open>"java:jls:2026"\<close> repeats the syntax of the whole language in its chapter 19,
  and this front-end follows it for the whole language as the specification has it: with
  everything that became final up to Java 25 - records, sealed classes, text blocks, pattern
  matching for \<open>instanceof\<close> and \<open>switch\<close> with record patterns and guards, the unnamed variable
  \<open>_\<close>, module import declarations, compact source files with instance \<open>main\<close> methods, and
  constructors with statements before \<open>this(\<dots>)\<close> or \<open>super(\<dots>)\<close> - and without the preview features
  (primitive types in patterns, for instance, are rejected).

  The grammar is \<^emph>\<open>checked against the real thing\<close>. Isabelle2026 comes with a JDK 25 whose
  \<^verbatim>\<open>lib/src.zip\<close> holds the 15\,371 \<^verbatim>\<open>.java\<close> files of OpenJDK 25 \<^cite>\<open>"java:jdk:2026"\<close>: the class
  library, the compiler \<^verbatim>\<open>javac\<close>, the tools and 69 module declarations. All of them are read by
  this front-end, printed back to text with exactly the tokens of the source, and read again
  (\<open>\<section>5\<close>).

  The folder of this front-end is \<^verbatim>\<open>Java25\<close>, after the language version it implements; the
  session is \<open>Java25\<close>, the theory and the commands are called \<open>Java\<close> and \<open>java\<close>.

  Isabelle/Java is the seventh language front-end built on the design of \<^bold>\<open>Isabelle/C, Version
  2.0\<close>, which this repository's \<^verbatim>\<open>C11/\<close> folder contains \<^cite>\<open>"tuong.ea:isabellec:2019" and
  "tuong.ea:deeply:2019"\<close>, after occam 2, Scala 3, MicroRust, AdaSpark and Go. It is built from the
  same parts and carries the same concepts over one for one: the \<^verbatim>\<open>ml_lex_yacc\<close> command of this
  repository (an ML-Lex/ML-Yacc integration \<^cite>\<open>"appel.ea:lexical:1994" and
  "tarditi.ea:ml-yacc:2000"\<close>) generates lexer and parser; every node of the abstract syntax tree
  carries a source position plus the comments and antiquotations attached to it; a per-theory
  environment tracks the declared names for declaration/use hyperlinking; programmable handlers, a
  navigation language and an evaluation order give meaning to the antiquotations; and a family of
  Isar commands (\<open>java\<close>, \<open>java_stmt\<close>, \<open>java_file\<close>, \<open>\<dots>\<close>) drive all of it. Someone who knows the
  C11 manual will find the same structure in this one, and the same names with \<open>c11\<close> replaced by
  \<open>java\<close>, \<open>cenv\<close> by \<open>jenv\<close>, and \<open>CEnv\<close> by \<open>JEnv\<close>. Like the other members it is
  \<^emph>\<open>re-entrant\<close>: it is built with \<open>ml_lex_yacc [state]\<close>, every parse has a state object of its
  own, and any number of parses may run at the same time.

  What differs is dictated by the language and takes up most of the remainder: the things in
  Java's syntax that an LALR(1) grammar cannot see over the tokens - a \<open><\<close> that opens type
  arguments or compares, a \<open>(\<close> that opens a lambda, a cast, a record pattern or a parenthesis, the
  contextual keywords (\<open>\<section>2.1\<close>); the several name spaces of Java and the flow scoping of pattern
  variables (\<open>\<section>2.2\<close>); and a type pass that reads the classes of the platform from the sources
  of a JDK (\<open>\<section>2.3\<close>).
\<close>

section\<open>Main Features of Isabelle/Java\<close>

text\<open>
  Five pieces fit together to give the \<open>java\<close>-family commands (\<open>\<section>3\<close>) their behaviour: a
  lexer, a layout stream and a parser that produce a real AST with genuine source positions at
  every node (\<open>\<section>2.1\<close>); a per-theory environment tracking every declared name, used to
  hyperlink each name \<^emph>\<open>use\<close> back to its declaration, and a type pass that resolves selections and
  calls (\<open>\<section>2.2\<close>, \<open>\<section>2.3\<close>); a mechanism for attaching programmable content to a specific AST
  node via a comment (\<open>\<section>2.4\<close>); and a well-defined order and navigation language governing
  exactly \<^emph>\<open>which\<close> node an antiquotation resolves to and \<^emph>\<open>when\<close> it runs (\<open>\<section>2.5\<close>).
\<close>

subsection\<open>Parsing\<close>

text\<open>
  The grammar (\<^verbatim>\<open>Java_Parser.thy\<close>) is an ordinary LALR(1) ml-yacc grammar, and it is
  \<^emph>\<open>conflict free\<close>: ml-yacc reports neither a shift/reduce nor a reduce/reduce conflict (the one
  place where shifting is the reading Java intends - a lambda body extends as far as it can - is
  declared with a precedence). It covers

  \<^item> \<^bold>\<open>compilation units\<close>: ordinary ones (package, imports of all five kinds - single, on
    demand, static, static on demand and module - and type declarations), module declarations
    (\<open>requires\<close>, \<open>exports\<close>, \<open>opens\<close>, \<open>uses\<close>, \<open>provides\<close>) and compact source files, whose
    top level has fields and methods;
  \<^item> \<^bold>\<open>declarations\<close>: classes, interfaces, enums (constants with arguments and bodies), records
    (with compact constructors), annotation types, with type parameters, \<open>extends\<close>, \<open>implements\<close>
    and \<open>permits\<close>, fields, methods (\<open>throws\<close>, receivers, variable arity, annotation defaults),
    constructors, initializers, and annotations with all their forms of values;
  \<^item> \<^bold>\<open>types\<close>: primitive and class types with type arguments (also of the outer class,
    \<open>Outer<A>.Inner\<close>), wildcards, arrays, annotations on types, intersection casts;
  \<^item> \<^bold>\<open>statements\<close>: all of them, including labels, the four loops, \<open>switch\<close> in both forms,
    \<open>try\<close> with resources and multi-catch, \<open>yield\<close>, local classes and records;
  \<^item> \<^bold>\<open>expressions\<close>: the precedence levels of Java, lambdas, method references, \<open>switch\<close>
    expressions, \<open>instanceof\<close> with type and record patterns, the unnamed pattern, guards
    (\<open>when\<close>), anonymous classes, array creation and initializers, text blocks, and every form of
    literal.

  \<^bold>\<open>What an LALR(1) grammar cannot see\<close> is decided in a small \<^emph>\<open>stream\<close> between lexer and parser
  (\<open>Java_Parse.java_stream\<close>), as javac does it: the stream buffers the tokens of the lexer, looks
  ahead in the list - it scans a type without building any tree - and \<^emph>\<open>relabels\<close> the tokens, so
  that the grammar itself stays an ordinary context-free one:

  \<^enum> \<^emph>\<open>Type arguments against comparisons.\<close> A \<open><\<close> that begins a list of type arguments is a
    different token (\<open>TLT\<close>) from the comparison; so is the \<open>>\<close> that ends it (\<open>TGT\<close>). A \<open>>>\<close> or
    \<open>>>>\<close> that closes two or three lists is split. In the arguments of a call \<open>f(a < b, c > d)\<close>
    is two comparisons, as javac reads it.
  \<^enum> \<^emph>\<open>Parentheses.\<close> A \<open>(\<close> is the beginning of a lambda (\<open>LAMLP\<close>), of a cast (\<open>CASTLP\<close>, also an
    intersection cast), of the components of a record pattern (\<open>RECLP\<close>) or is just a parenthesis; a
    lambda parameter without a type is a \<open>LAMID\<close>. The stream keeps a stack of the parentheses it
    is in, so that the parentheses of a call or of an annotation are never read as one of those.
  \<^enum> \<^emph>\<open>Contextual keywords.\<close> \<open>var\<close>, \<open>yield\<close>, \<open>record\<close>, \<open>sealed\<close>, \<open>permits\<close>, \<open>when\<close>, \<open>module\<close>,
    \<open>open\<close>, \<open>requires\<close>, \<open>exports\<close>, \<open>opens\<close>, \<open>uses\<close>, \<open>provides\<close>, \<open>to\<close>, \<open>with\<close> and \<open>transitive\<close> are
    keywords or names by their surroundings: \<open>yield (int) x;\<close> is a statement and \<open>yield(x);\<close> too,
    but \<open>yield++;\<close> is an increment of a variable called \<open>yield\<close>, by javac's rule. A name of a
    variable \<open>record\<close> is still a name.
  \<^enum> \<^emph>\<open>Empty brackets.\<close> \<open>[\<close> followed by \<open>]\<close> is one token, so that the dimensions of a type are not
    mistaken for an index.

  \<^bold>\<open>Positions and comments.\<close> Every node carries the exact source range of its text, from its
  first to its last token; a name carries the range of the name. Comments, and the
  antiquotations among them (\<open>\<section>2.4\<close>), are not part of the grammar: the lexer collects them and
  attaches them to the node of the next real token. The Javadoc tags \<open>@param\<close>, \<open>@return\<close> and
  \<open>{@code \<dots>}\<close> are not antiquotations.

  A first example, a generic stack with a nested class, an anonymous class and a bounded generic
  method:
\<close>

java\<open>
package demo;

import java.util.ArrayList;
import java.util.List;

public class Stack<T> {
    private final List<T> items = new ArrayList<>();

    public void push(T x) {
        items.add(x);
    }

    public T pop() {
        if (items.isEmpty()) {
            throw new IllegalStateException("stack is empty");
        }
        return items.remove(items.size() - 1);
    }

    public static <U extends Comparable<U>> U max(List<U> xs) {
        U best = xs.get(0);
        for (U x : xs) {
            if (x.compareTo(best) > 0) {
                best = x;
            }
        }
        return best;
    }

    public Runnable clearer() {
        return new Runnable() {
            @Override
            public void run() {
                items.clear();
            }
        };
    }
}
\<close>

text\<open>
  Literals and the lexical structure are part of the grammar: numbers with prefixes, underscores
  and exponents, characters, text blocks, and the constructs that need the stream. The fragments
  below are accepted (a comparison against type arguments, a cast against a parenthesis, a lambda,
  a method reference, a pattern); the last two are not:
\<close>

java_expr\<open>0xF_F + 0b1010 + 017 + 1_000L + 1.5e3 + 0x1p-2 + 'a' + '\n'\<close>

java_expr\<open>a < b ? (int) x + 1 : f(c < d, e > f)\<close>

java_expr\<open>xs.stream().map(x -> x * 2).filter(Objects::nonNull).toList()\<close>

java_expr\<open>o instanceof Point(int x, var y) && x > y\<close>

java_stmt\<open>
Map<String, List<Integer>> m = new HashMap<>();
for (var e : m.entrySet()) {
    if (!(e.getValue() instanceof ArrayList<Integer> l)) continue;
    use(l);
}
\<close>

java_expr_reject\<open>a +\<close>

java_type_reject\<open>int[\<close>

subsection\<open>The Java Environment, and Declaration/Use Navigation\<close>

text\<open>
  \<^verbatim>\<open>Java_Env.thy\<close> defines \<open>jenv\<close>, the counterpart of C11's \<open>cenv\<close>: a record stored as ordinary
  \<^verbatim>\<open>Generic_Data\<close>, so that it persists across commands within a theory and merges correctly
  under Isabelle's parallel, incremental checking. It holds

  \<^enum> \<open>names\<close>, the declared names, with what each was declared as (a variable, a parameter, a
  field, an enum constant, a type, a type parameter, an import, a package, a label, a method, a
  constructor). Java has \<^emph>\<open>several name spaces\<close>, which are kept apart by a prefix in the key: a
  variable and a type of the same name do not clash, and neither do a label and a variable;
  \<^enum> \<open>meths\<close>, the visible methods by name, with their number of arguments, for a call without a
  receiver whose class is not known;
  \<^enum> \<open>vtypes\<close> and \<open>defs\<close>, the types of the names and the definitions of the classes, which the
  type pass uses (\<open>\<section>2.3\<close>);
  \<^enum> \<open>java_antiq\<close>, the registry of antiquotation handlers (\<open>\<section>2.4\<close>); and
  \<^enum> a per-theory unit counter, used to name the sections processed by a \<open>java\<close> command.

  \<^verbatim>\<open>Java_AnaEval.thy\<close>'s \<open>analyse_and_eval\<close> is a single, purely functional, scoped walk over a
  parsed root that fills \<open>jenv\<close> as it goes. Every name \<^emph>\<open>use\<close> is hyperlinked to its declaration
  via \<^ML>\<open>Position.entity_markup\<close>, reported once at the declaration site and once at every use.
  \<^bold>\<open>A name that resolves nowhere is not marked\<close> - unlike C11 and occam 2, where it is underlined.
  In Java a name very often comes from an inherited member, an on-demand import or a library
  that this pass does not see; underlining them would drown the useful markup. The \<^emph>\<open>scoping
  rules\<close> are those of Java, implemented as shadow-and-restore (the environment is a value; a
  scope simply does not hand its extension back):

  \<^item> \<^bold>\<open>Members of a class\<close> are in scope in the whole body of the class, whatever the order of the
    declarations: a method may use a field or call a method that is declared further down, and
    a member class is visible before its declaration. The type parameters of a class or of a
    method are visible in their declaration and body.
  \<^item> \<^bold>\<open>Block scoping.\<close> A local variable is visible from the end of its declarator to the end of
    the innermost block; it is not visible in its own initializer. A block, a method (its
    parameters and type parameters), a constructor, a lambda (its parameters), a \<open>for\<close> statement
    (with the variables of its header), an enhanced \<open>for\<close>, a \<open>try\<close> with resources, a \<open>catch\<close> clause
    and a \<open>switch\<close> rule are scopes. In an old-style \<open>switch\<close> block the variables of one group stay
    in scope for the next one.
  \<^item> \<^bold>\<open>Flow scoping of pattern variables\<close> (JLS 6.3.1). The variable of \<open>o instanceof String s\<close> is
    in scope where the pattern has certainly matched: in \<open>a && b\<close> to the right of the pattern, in
    the true branch of a condition, in the false branch if the condition is negated, and in the
    statements that \<^emph>\<open>follow\<close> an \<open>if\<close> whose branch cannot complete normally (a \<open>return\<close>, a \<open>throw\<close>,
    a \<open>break\<close>): \<open>if (!(o instanceof String s)) return; use(s);\<close>. The bindings of a condition are
    computed as a pair of sets, the ones that hold when it is true and the ones that hold when it
    is false. The unnamed pattern \<open>_\<close> declares nothing.
  \<^item> \<^bold>\<open>Labels\<close> have a name space of their own; \<open>break\<close> and \<open>continue\<close> are hyperlinked to the label.
  \<^item> \<^bold>\<open>Imports\<close> declare the simple name of an imported type - the last element of the path - at
    that element; a static import declares the name of a variable and of a method. A use is
    hyperlinked to the import. On-demand imports declare nothing.
  \<^item> \<^bold>\<open>Names with a dot.\<close> In \<open>a.b.c\<close> the first name is looked up as a variable, else as a type, else
    as a package; the others are members and are linked by the type pass (\<open>\<section>2.3\<close>).
  \<^item> \<^bold>\<open>The top level persists.\<close> After \<open>java\<close> has analysed a compilation unit (or \<open>java_decl\<close> some
    declarations), the types, the imports and (in a compact unit) the fields and methods it
    declares at the top level stay in \<open>jenv\<close> for the following commands, as the files of a package
    do for each other. A block does not leave anything behind.

  Being persistent per-theory data - the same idiom a simp set uses - is what lets Java fragments
  be freely \<^emph>\<open>interleaved\<close> with arbitrary Isar content and still resolve a name used in one
  fragment back to its declaration in an earlier one. The flip side is that \<open>jenv\<close> only ever
  grows across a theory; the commands \<open>set_jenv_default\<close> and \<open>reset_jenv\<close> (\<open>\<section>3\<close>) give a theory
  explicit control. A small example of the scoping rules (hover over the names in jEdit): members
  that are used before they are declared, a pattern variable that outlives its \<open>if\<close>, a labelled
  loop, a lambda and a record pattern in a \<open>switch\<close>.
\<close>

java\<open>
package scopes;

import java.util.function.IntUnaryOperator;

public class Scopes {
    record Point(int x, int y) {}

    int run(Object o, int[] data) {
        if (!(o instanceof String s)) {
            return total(data);
        }
        int n = s.length();
        IntUnaryOperator twice = v -> v * 2 + n;
    outer:
        for (int i = 0; i < data.length; i++) {
            for (int j = 0; j < i; j++) {
                if (data[j] > data[i]) {
                    break outer;
                }
            }
        }
        return twice.applyAsInt(offset);
    }

    int offset = 1;

    int total(int[] data) {
        int sum = 0;
        for (int d : data) {
            sum += d;
        }
        return sum;
    }

    static int sumOf(Object o) {
        return switch (o) {
            case Point(int x, int y) when x > 0 -> x + y;
            case Point p -> p.x();
            default -> 0;
        };
    }
}
\<close>

subsection\<open>Types, and the Platform\<close>

text\<open>
  Selections and calls are resolved by a type pass, a pure function over the environment, and
  \<^emph>\<open>only when that is certain\<close>. A selection \<open>x.f\<close> or a call \<open>x.m(a)\<close> is hyperlinked to the field
  or the method when the type of \<open>x\<close> is known well enough to tell, and left unmarked otherwise.

  \<^bold>\<open>Types of expressions.\<close> The type of a name is the one it was declared with (a local variable,
  a parameter, a field, a pattern variable, a \<open>catch\<close> parameter; for \<open>var\<close> and an enhanced \<open>for\<close>
  the one of the initializer or of the array); a literal, \<open>new\<close>, a cast, \<open>this\<close> and an array
  access have their natural types, an operator the type that the numeric promotion gives, and a
  call the result type of the method it resolves to, with the type arguments of the receiver
  substituted and the type parameters of the method bound by the arguments that are exactly such
  a parameter. A class is a \<^emph>\<open>reference\<close> to its declaration, so classes, fields and methods may be
  mutually recursive and declared in any order: the classes of a unit - member classes, local
  classes and anonymous classes too - are registered before anything is walked.

  \<^bold>\<open>Members.\<close> A field is found in the class, else in its superclass and interfaces provided they
  are all known and exactly one of them has it (a supertype that is not known could have the
  same name). The methods of a name are those of the class, of its supertypes and of \<open>Object\<close>, an
  inherited method of the same signature being hidden. A call is linked if the types of the
  arguments leave exactly one applicable method, or one that is more specific than all the
  others (JLS 15.12.2); subtyping is answered \<^emph>\<open>yes\<close>, \<^emph>\<open>no\<close> or \<^emph>\<open>perhaps\<close>, and an unknown type is
  always \<^emph>\<open>perhaps\<close>, so that a doubtful call stays unlinked. A call without a receiver belongs to
  the innermost enclosing class that has a method of that name (JLS 15.12.1), else to a
  statically imported method.

  \<^bold>\<open>Lambdas, method references, switch expressions.\<close> These have no type of their own;
  they get one from their context. The context \<^emph>\<open>expects\<close> a type of the expression it is about to
  walk: the parameter type of the method or constructor that the call resolves to (with the type
  parameters bound so far), the declared type of a variable or field, the result type of the
  method or lambda around a \<open>return\<close>, the type of a cast, the type of the left side of an
  assignment; a conditional and a parenthesis pass it on. If that type is a functional
  interface - an interface with one abstract method, not counting those of \<open>Object\<close> - the
  parameters of a lambda get the parameter types of that method (wildcards count as their
  bounds), so that the body is analysed with typed names, and the result of the lambda is
  expected of its body. A call is then typed in two steps, as the specification has it in spirit:
  the arguments that have a type bind the type parameters of the method (through their
  supertypes, an array or a variable-arity argument included), and the results of the lambdas
  and method references bind the rest, so that \<open>xs.stream().map(s -> s.length())\<close> is a
  \<open>Stream<Integer>\<close> (a primitive result is boxed). A lambda is also a criterion for the
  choice of an overload: a candidate whose functional interface takes another number of
  parameters is not applicable. A method reference \<open>T::m\<close> is resolved with the parameter types of
  the interface, as a static method taking all of them or as an instance method of the first;
  \<open>e::m\<close> as an instance method; \<open>T::new\<close> gives \<open>T\<close>; the reference is hyperlinked to the method.
  A \<open>switch\<close> expression has the type its arms agree on - each arm is typed in the scope of the
  pattern variables of its label - with numbers promoted and \<open>null\<close> ignored.

  \<^bold>\<open>The platform.\<close> A class that the program does not declare - one it imports, one of
  \<open>java.lang\<close>, one named by its package (\<open>java.util.Map.Entry\<close>) - is \<^emph>\<open>read from the sources of
  a JDK\<close>. The theory option \<open>java_src\<close> says where: a \<^verbatim>\<open>src.zip\<close>, or a directory with the same
  layout (the packages below a directory per module, or directly below it); \<open>none\<close> switches the
  platform off. By default it is the \<^verbatim>\<open>lib/src.zip\<close> of the JDK of Isabelle (\<^verbatim>\<open>$ISABELLE_JDK_HOME\<close>),
  else of \<^verbatim>\<open>$JAVA_HOME\<close>:

  \<^verbatim>\<open>declare [[java_src = "/usr/lib/jvm/java-25-openjdk/lib/src.zip"]]\<close>

  A class is parsed the first time it is needed (a file out of the archive is extracted to
  \<^verbatim>\<open>$ISABELLE_TMP_PREFIX\<close>, which is what a hyperlink opens), and its definitions are kept for the
  session, shared by all theories, so the cost is paid once; a typical class takes a second or
  less. Of a class of the platform the members that a program can see are known (public,
  protected, and those of an interface); the \<open>Enum\<close> of an enum and the \<open>Record\<close> of a record are the
  real ones; member classes are found; a static import brings in the static methods of its
  class. A primitive type may be the box that a platform class is (\<open>list.add(1)\<close>), and an array
  is an \<open>Object\<close>, a \<open>Cloneable\<close> and a \<open>Serializable\<close>. Without a JDK, or with \<open>none\<close>, nothing is known
  of the platform and nothing is linked on that basis. The following unit uses the platform in
  every line: \<open>s.length()\<close>, \<open>l.get(0)\<close> with its type argument, \<open>System.out.println\<close>,
  \<open>Map.Entry\<close> and a static method; hover over the names, and click through to the JDK:
\<close>

java\<open>
package platform;

import java.util.*;

public class Uses {
    static int first(List<String> l) {
        return l.get(0).length();
    }

    static void show(Map<String, Integer> m) {
        for (Map.Entry<String, Integer> e : m.entrySet()) {
            System.out.println(e.getKey() + "=" + e.getValue().intValue());
        }
    }

    static boolean none(Object o) {
        return Objects.isNull(o) || o.toString().isEmpty();
    }
}
\<close>

text\<open>
  Lambdas, method references and \<open>switch\<close> expressions get their types from the context. In the
  unit below the parameter \<open>p\<close> of the first lambda is a \<open>Person\<close> (the \<open>Consumer<? super Person>\<close>
  that \<open>forEach\<close> takes), so \<open>name\<close> and \<open>length\<close> are linked; \<open>Person::name\<close> is linked and its
  result type binds the \<open>R\<close> of \<open>map\<close>, so \<open>n\<close> is a \<open>String\<close>; and \<open>r\<close> has the type that both arms of
  the \<open>switch\<close> agree on:
\<close>

java\<open>
package platform;

import java.util.*;

public class Lambdas {
    record Person(String name, int age) {}

    static int totalLength(List<Person> ps) {
        int[] total = {0};
        ps.forEach(p -> total[0] += p.name().length());
        return total[0];
    }

    static void names(List<Person> ps) {
        ps.stream().map(Person::name).forEach(n -> System.out.println(n.length()));
    }

    static String kind(Object o) {
        var r = switch (o) {
            case Person p -> p;
            default -> new Person("?", 0);
        };
        return r.name();
    }
}
\<close>

subsection\<open>Programmable Java-Antiquotations, and Handlers\<close>

text\<open>
  A comment of the shape \<open>@tag[navi](level) \<open>body\<close>\<close> - an \<open>@\<close>-prefixed tag, an optional bracketed
  navigation string (\<open>\<section>2.5\<close>), an optional parenthesised integer \<open>level\<close> (\<open>0\<close> when omitted), and
  a body written as a nested Isabelle cartouche or, equivalently, a double-quoted string - is
  recognised lexically inside a \<open>//\<close> or \<open>/* \<dots> */\<close> comment, and attached to whichever AST node
  it resolves against (\<open>\<section>2.5\<close>). The cartouche may span several lines, which a \<open>//\<close> comment
  cannot. Any other comment is kept as plain text (\<open>Raw_txt\<close>). A comment is attached to the AST
  node that begins at the \<^emph>\<open>next real token\<close>, so an annotation is written on the line(s) \<^emph>\<open>above\<close>
  what it annotates:

  \<^verbatim>\<open>//@ highlight\<close>

  (a tag alone is a complete antiquotation with an empty body). Because Java has Javadoc, a
  tag with a quoted body is an antiquotation only directly after the comment opener
  (\<open>//@\<close>, \<open>/*@\<close>), so that \<open>{@code "x"}\<close>, \<open>@param x\<close> or an e-mail address in running text is
  not mistaken for one; the cartouche form is one anywhere in a comment. A consequence is that a
  comment which \<^emph>\<open>begins\<close> with a JML-like or annotation-like tag (\<open>//@Deprecated\<close>) is an
  antiquotation whose tag has no handler, as in the other front-ends; \<open>// @Deprecated\<close> is not.

  The \<open>tag\<close> selects a \<^emph>\<open>handler\<close>: an ordinary ML function of type

  \<^verbatim>\<open>type type_antiq_fun =
    jenv * pos Java_Ast.root * int -> (string * pos) ->
    Context.generic -> Context.generic\<close>

  registered once, ahead of time, via \<open>JEnv.store_antiq (tag, handler)\<close>. When
  \<open>analyse_and_eval\<close> reaches a node carrying an \<open>@tag \<dots>\<close> antiquotation, it resolves the
  navigation string against the closest-surrounding-context stack (\<open>\<section>2.5\<close>) into a single
  concrete \<open>root\<close> value, then instantiates the handler with \<open>(jenv, resolved_root, level)\<close> and
  the body text together with its own source position; a handler is never itself responsible
  for interpreting \<open>u\<close>/\<open>U\<close>/\<open>r\<close>/\<open>d\<close>.

  \<open>Context.generic\<close> rather than \<open>theory\<close>, deliberately: a handler may do anything a genuine
  Isar toplevel command can, including running real ML code at the ML environment level (the
  \<open>ML\<close> antiquotation, below). All collected actions are folded into one \<open>Context.generic ->
  Context.generic\<close> function by ordinary composition and lifted to the toplevel exactly once, at
  the end (\<open>full_eval_and_store\<close> in \<^verbatim>\<open>Java.thy\<close>). Most handlers never need this generality: an
  ordinary \<open>theory -> theory\<close> function is \<^emph>\<open>recaptured\<close> by \<open>JEnv.lift_theory_antiq\<close> when it is
  registered. A first handler, which turns a plain comment into a checked diagnostic reported
  against the exact node the comment resolves to:
\<close>

ML\<open>
val todo_antiq =
  let
    fun handler (_ : JEnv.jenv, ast, level) (body, _ : Position.T) thy =
      (warning ("TODO (level " ^ Int.toString level ^ ") at " ^
                Position.here (AnaEval.pos_of_root ast) ^ ": " ^ body);
       thy)
  in JEnv.store_antiq ("todo", JEnv.lift_theory_antiq handler) end
\<close>
setup\<open>todo_antiq\<close>

java\<open>
package p;

class Cleaner {
    void clear(int[] xs) {
        //@ todo \<open>check the range of xs first\<close>
        xs[0] = 0;
    }
}
\<close>

text\<open>
  A tag with no registered handler is a hard error: every tag that can appear in a theory's
  source must be registered before that theory's \<open>java\<close>-family commands run.
\<close>

subsection\<open>Execution (Order, Navigation, etc.)\<close>

text\<open>
  \<^bold>\<open>Order.\<close> A unit can carry several antiquotations whose handlers have side effects that
  depend on one another (a \<open>definition\<close> must precede the \<open>lemma\<close> that mentions it). \<open>level\<close> is
  the author's explicit ordering knob: \<open>full_eval_and_store\<close> collects every \<open>(level, action)\<close> pair
  the walk produces, sorts by \<open>level\<close> - a stable sort, so equal levels keep their textual order -
  and chains them, each against the context the previous one produced. A physical antiquotation
  is dispatched \<^emph>\<open>exactly once\<close>, no matter how many AST nodes share its leftmost source position
  (the classic case: a statement, its expression and the name that begins it all start at the
  same token).

  \<^bold>\<open>Context.\<close> Every antiquotation resolves, by default, to its \<^emph>\<open>closest surrounding
  context\<close>: the walk threads a stack of enclosing nodes. Four kinds of node push themselves on
  that stack at every level of nesting: \<^emph>\<open>expressions\<close>, \<^emph>\<open>types\<close>, \<^emph>\<open>statements\<close> and
  \<^emph>\<open>declarations\<close> - the root type has the variants \<open>Expr\<close>, \<open>Type\<close>, \<open>Stmt\<close>, \<open>Decl\<close> in addition to
  \<open>Id\<close> for a bare name, \<open>Stmts\<close> for a statement list, \<open>Decls\<close> for member declarations and
  \<open>Source\<close> for a compilation unit. Everything else - parameters, annotations, switch labels,
  catch clauses, enum constants, the modifiers - never pushes and resolves to what is on top,
  which is what makes every node kind a valid place for a comment. A comment in front of a
  top-level declaration is therefore in the context of the compilation unit, and \<open>[d]\<close> reaches
  the declaration.

  \<^bold>\<open>Navigation.\<close> The bracketed \<open>[navi]\<close> string points an antiquotation \<^emph>\<open>away\<close> from its closest
  context. Its syntax and its rules are exactly those of C11: written \<open>(u|U)*(r|d)*\<close>, zero or
  more ascend steps followed by zero or more descend steps. \<open>u\<close> ascends one level (a lone, final
  \<open>u\<close> is a no-op); \<open>U\<close> ascends past a whole run of consecutive ancestors of the same category;
  \<open>r\<close> advances a 1-based cursor among the current node's children in source order and \<open>d\<close>
  descends into the child at the cursor (cursor 1 if no \<open>r\<close> preceded it). There is no wrapping: a
  cursor beyond the children, or \<open>d\<close> on a leaf, is a hard error reported at the antiquotation's
  own tag position. The children of a node, in source order, are its sub-expressions, types,
  statements and declarations; blocks are flattened into their parent, so the children of an
  assignment are the expressions of its two sides, those of a call its receiver followed by its
  arguments, and those of an \<open>if\<close> its condition and its two branches. A few examples (the node a
  handler receives, on the statement \<open>x = x + y;\<close>):

  \<^item> no navigation: the statement itself;
  \<^item> \<open>[d]\<close> or \<open>[rd]\<close>: its first child, the expression \<open>x = x + y\<close>; \<open>[drd]\<close>: its first child, \<open>x\<close>;
    \<open>[drrd]\<close>: its second child, \<open>x + y\<close>;
  \<^item> \<open>[uu]\<close>: the enclosing method.

\<close>

java\<open>
package p;

class Sum {
    int sum(int x, int y) {
        //@ probe_ast[drrd]
        //@ highlight[drrd]
        x = x + y;
        return x;
    }
}
\<close>

ML\<open>
val _ = if Java_Pp.pp_root (!JAVA_AST) = "x + y"
  then writeln "[drrd] reaches the second operand"
        else error "navigation"
\<close>

subsection\<open>Standard Antiquotations\<close>

text\<open>
  \<^verbatim>\<open>Java_AnaEval.thy\<close> registers the same eight demonstration antiquotations as C11. All of them
  are written in a comment and see the node their navigation string selects:

  \<^descr> \<open>probe_jenv\<close> stores the current \<open>jenv\<close> into an ML reference (\<open>JAVA_JENV\<close>) for inspection.
  \<^descr> \<open>probe_ast\<close> prints the resolved node, pretty-printed back to Java, with its level, and
    stores it into \<open>JAVA_AST\<close>.
  \<^descr> \<open>highlight\<close> marks the resolved node's source range in the editor - the quickest way to
    \<^emph>\<open>see\<close> what a navigation string selects.
  \<^descr> \<open>term \<open>t\<close>\<close> reads \<open>t\<close> as a HOL term in the theory's current context; a malformed or
    ill-typed term is a real Isabelle error positioned inside the Java comment.
  \<^descr> \<open>ML \<open>code\<close>\<close> runs \<open>code\<close> as ML source, so a definition written in a Java comment becomes a
    later-visible ML binding.
  \<^descr> \<open>text \<open>t\<close>\<close> runs \<open>t\<close> through the document machinery of Isabelle's \<open>text\<close> command, so that
    inner antiquotations are checked and hyperlinked (the result is stashed, not typeset; see
    \<open>\<section>6\<close>).
  \<^descr> \<open>definition \<open>d\<close>\<close> is Isabelle's \<open>definition\<close> command: the new constant is a genuine,
    later-visible theory constant.
  \<^descr> \<open>lemma \<open>l\<close>\<close> states \<open>l\<close> and proves it with one terminal \<open>by\<close> proof - proof-carrying code: a
    formal property of the program's constants, \<^emph>\<open>actually proved\<close>, right where the Java text that
    motivates it lives. A failed proof is an Isabelle error positioned in the comment.

\<close>

section\<open>The Java Main Commands\<close>

text\<open>

  \<^descr> \<open>java \<open>\<dots>\<close>\<close> parses its argument as a compilation unit - ordinary, modular or compact - runs
    \<open>analyse_and_eval\<close>, chains the collected antiquotation actions in level order, and stores the
    AST under a fresh key, reported as \<open>[stored as Theory#N]\<close>.
  \<^descr> \<open>java_decl \<open>\<dots>\<close>\<close> is the same for member declarations \<^emph>\<open>without\<close> a class around them - the
    way to add a method or a field one piece at a time - and \<open>java_stmt \<open>\<dots>\<close>\<close> for block
    statements, as they stand between the braces of a method.
  \<^descr> \<open>java_file \<open>path\<close>\<close> is the same as \<open>java\<close>, reading the compilation unit from an external file
    (resolved relative to the theory's master directory via \<^ML>\<open>Resources.parse_file\<close>, so file
    positions and build-dependency tracking come for free).
  \<^descr> \<open>java_expr \<open>\<dots>\<close>\<close>, \<open>java_type \<open>\<dots>\<close>\<close> and \<open>java_ident \<open>\<dots>\<close>\<close> parse a bare expression, type,
    respectively name. The analysis still runs, for its hyperlinks, but its antiquotation actions
    are discarded: a standalone fragment is a syntax check, not a program.
  \<^descr> \<open>java_reject\<close>, \<open>java_decl_reject\<close>, \<open>java_stmt_reject\<close>, \<open>java_expr_reject\<close>,
    \<open>java_type_reject\<close> and \<open>java_ident_reject\<close> document a fragment as correctly \<^emph>\<open>not\<close> accepted by
    the corresponding entry point. They are silent (no error markup is left on the expected
    failure) and are the means of writing negative tests.
  \<^descr> \<open>set_jenv_default\<close> and \<open>reset_jenv\<close> control the ever-growing \<open>jenv\<close>. \<open>set_jenv_default\<close>
    nominates what \<open>jenv\<close> holds \<^emph>\<open>right now\<close> as the snapshot a later \<open>reset_jenv\<close> restores; with
    no earlier \<open>set_jenv_default\<close> in scope \<open>reset_jenv\<close> falls back to the empty \<open>jenv\<close>.
    \<^verbatim>\<open>Java.thy\<close> itself nominates, as its last step, the environment holding exactly the standard
    antiquotation handlers.
  \<^descr> \<open>setup_backend \<open>f\<close>\<close> installs the \<^emph>\<open>semantic backend\<close>: \<open>f\<close> is an ML expression of type
    \<open>Position.T Java_Ast.root -> theory -> theory\<close>, evaluated like the argument of Isabelle's own
    \<open>setup\<close> command. At the very end of every \<open>java\<close>, \<open>java_decl\<close>, \<open>java_stmt\<close> and \<open>java_file\<close> -
    after the antiquotation actions have run and the AST is stored - the installed function is
    applied to the parsed root and the theory the command has produced, and its result is the
    theory the command returns; the fragment commands never trigger it. The default is \<open>K I\<close>,
    which \<open>setup_backend \<open>K I\<close>\<close> restores. The function is kept in the theory's context
    (separately from \<open>jenv\<close>, so \<open>reset_jenv\<close> does not uninstall it) and is inherited by later
    theories. This is where a translation of Java programs into HOL would plug in.
  \<^descr> \<open>java_export \<open>path\<close> exports \<open>key\<^sub>1\<close> \<open>\<dots>\<close> \<open>key\<^sub>n\<close>\<close> renders previously stored sections - given by
    the store keys the accepting commands report - back to Java text with \<^ML>\<open>Java_Pp.pp_root\<close> and
    writes them to \<open>path.java\<close>. With \<open>[verbatim]\<close> after the command name the original source
    text is written instead of the pretty-printer's.

  The accepting commands are \<open>thy_decl\<close> commands, because they change theory data (\<open>java_file\<close> is
  \<open>thy_load\<close>, so that Isabelle tracks the file dependency); the \<open>_reject\<close> commands, which store
  nothing, are \<open>diag\<close>. Isabelle evaluates a \<open>diag\<close> command asynchronously, in parallel with the
  commands that follow; that is harmless here, because every parse has its own state (\<open>\<section>2.1\<close>).
\<close>

subsection\<open>A Worked Example\<close>

text\<open>
  A program in the style of a verified library: a constant mirrored in HOL, a loop, and a
  property proved about the constant. The first annotation introduces a HOL constant for the bound
  (a \<open>definition\<close>, evaluated at level 0), the second proves a fact about it (level 1, so after
  the definition), the third checks a HOL term mentioning it (level 2).
\<close>

java\<open>
package counting;

//@ definition \<open>bound :: nat where "bound = 10"\<close>
//@ lemma(1) \<open>bound_double: "bound * 2 = 20" by (simp add: bound_def)\<close>
//@ term(2) \<open>bound + 1\<close>
public class Counting {
    static final int BOUND = 10;

    static int countUp() {
        int i = 0;
        //@ highlight
        while (i < BOUND) {
            i++;
        }
        return i;
    }
}
\<close>

thm bound_def bound_double

subsection\<open>Source Files, Backends, Export\<close>

text\<open>
  \<open>java_file\<close> reads an external file (here two of the examples of this repository: a program
  with imports and loops, and a generic stack) and stores its AST; the names of its declarations
  are visible to the following commands. A semantic backend is an ML function installed with
  \<open>setup_backend\<close>. The following one only counts the type declarations of every compilation
  unit it is applied to; a real backend would translate them. It is applied to the \<^emph>\<open>parsed
  root\<close> and the theory, after the annotations have run:
\<close>

ML\<open>
val type_counts = Unsynchronized.ref ([] : int list)
\<close>

setup_backend\<open>fn root => fn thy =>
  (case root of
     Java_Ast.Source (Java_Ast.Unit (_, _, Java_Ast.Types decls, _)) =>
       (type_counts := length decls :: !type_counts; thy)
   | _ => thy)\<close>

java_file \<open>../examples/Hello.java\<close>

java_file \<open>../examples/Stack.java\<close>

setup_backend\<open>K I\<close>

ML\<open>
val _ = writeln ("type declarations per unit seen by the backend: " ^
                 commas (map Int.toString (rev (!type_counts))))
\<close>

text\<open>
  Further examples: sealed interfaces, records and pattern switches with guards and record
  patterns; labels, flow scoping, \<open>try\<close> with resources, lambdas, enum constants with bodies and an
  old-style \<open>switch\<close>; a compact source file with an instance \<open>main\<close>; and a module declaration:
\<close>

java_file \<open>../examples/Shapes.java\<close>

java_file \<open>../examples/Flow.java\<close>

java_file \<open>../examples/Compact.java\<close>

java_file \<open>../examples/module-info.java\<close>

text\<open>
  An accepted unit can be written back as Java, in the canonical layout of the pretty-printer
  (or, with \<open>[verbatim]\<close>, as it was written): four spaces per level of indentation, one statement
  per line, a blank line between declarations, and exactly the tokens of the source. The key of
  the unit is the one the command reported when it was stored. This is the way a generated or
  normalised file is produced from a theory:
\<close>

java\<open>
package p; class Id { int id(int x) { return x; } }
\<close>

ML\<open>
val key_of_last =
  let val JEnv.mk {units, ...} = JEnv.get (Context.Theory @{theory})
  in JEnv.ast_store_key @{theory} (units - 1) end
val _ = writeln ("the last unit is stored as " ^ key_of_last)
val _ = writeln (case JEnv.get_ast key_of_last @{theory} of
                   SOME root => Java_Pp.pp_root root | NONE => "?")
\<close>

section\<open>The Abstract Syntax\<close>

text\<open>
  The AST in \<^verbatim>\<open>java_ast.ML\<close> has one datatype per syntactic category, one constructor per
  alternative, close enough to the concrete syntax that \<^ML>\<open>Java_Pp.pp_root\<close> can print any
  parsed program back as Java, \<^emph>\<open>with exactly the tokens of the source\<close> - that is what the corpus
  test checks (\<open>\<section>5\<close>). Layout is \<^emph>\<open>not\<close> part of it: the printer regenerates a canonical layout.
  Parentheses \<^emph>\<open>are\<close> part of it (\<open>EParen\<close>), so the printer needs no precedence reasoning, and so
  are the optional trailing commas and the trailing \<open>;\<close> of a list of resources. All datatypes are
  parametrised by the position type \<open>'a\<close> (instantiated with \<^verbatim>\<open>Position.T\<close>), and every constructor
  but the pure wrappers carries a \<open>'a nodeInfo\<close> as its last field.

  \<^bold>\<open>Annotations\<close>, shared with C11 and so with everything built on it: \<open>nodeInfo\<close> is a bare
  position or a position with the comments attached; a \<open>comment\<close> is raw text or an antiquotation
  (tag, navigation steps, level, cartouche with its position); \<open>ident\<close> is a name with its
  \<open>nodeInfo\<close>.

  \<^bold>\<open>Syntactic categories\<close> (the constructors are those of \<^verbatim>\<open>java_ast.ML\<close>; the prefix \<open>j\<close> stands for
  ``Java''):

  \<^item> \<open>jType\<close>: \<open>TPrim\<close> (also \<open>void\<close>), \<open>TClass\<close> (the segments of \<open>a.b.C<T>.D\<close>, each with its type
    arguments, the diamond being the empty list), \<open>TArray\<close> (the element type and the dimensions),
    \<open>TVar\<close> (\<open>var\<close>); type arguments are types or wildcards (\<open>TAWild\<close>, bounded by \<open>extends\<close> or
    \<open>super\<close>); \<open>jTParam\<close> are type parameters with their bounds.
  \<^item> \<open>jExpr\<close>: \<open>ELit\<close> (the \<open>lit\<close>s \<open>LInt\<close>, \<open>LFloat\<close>, \<open>LChar\<close>, \<open>LString\<close>, \<open>LTextBlock\<close>, \<open>LBool\<close>, \<open>LNull\<close>, all
    as written), \<open>EName\<close> and \<open>EField\<close> (a simple name, and a selection \<open>e.f\<close>, which is also the
    qualified name \<open>a.b\<close>), \<open>EThis\<close>, \<open>ESuper\<close>, \<open>EQualThis\<close>, \<open>EQualSuper\<close>, \<open>EParen\<close>, \<open>EIndex\<close>,
    \<open>ECall\<close> (receiver, type arguments, name, arguments), \<open>ENew\<close> (with an optional class body: an
    anonymous class), \<open>ENewArray\<close>, \<open>EArrayInit\<close>, \<open>EClassLit\<close>, \<open>EMethodRef\<close>, \<open>ELambda\<close> (with
    inferred or typed parameters and an expression or a block as body), \<open>EUnary\<close>, \<open>EBinary\<close> (with
    the \<open>binop\<close>s), \<open>EAssign\<close> (with the operator of a compound assignment), \<open>ECond\<close>, \<open>ECast\<close> (more
    than one type: an intersection), \<open>EInstanceof\<close> and \<open>ESwitch\<close>.
  \<^item> \<open>jPattern\<close>: \<open>PType\<close> (a type and a name; without name, a plain type), \<open>PRecord\<close> (a record type
    and its component patterns) and \<open>PAny\<close> (\<open>_\<close>); \<open>jSwitchCase\<close> is a rule (\<open>->\<close>) or a group (\<open>:\<close>) with
    its \<open>jLabel\<close>s, which have items (constants, patterns, \<open>null\<close>, \<open>default\<close>) and a guard.
  \<^item> \<open>jStmt\<close>: \<open>SBlock\<close>, \<open>SLocal\<close>, \<open>SClassDecl\<close>, \<open>SEmpty\<close>, \<open>SExpr\<close>, \<open>SLabeled\<close>, \<open>SIf\<close>, \<open>SWhile\<close>,
    \<open>SDo\<close>, \<open>SFor\<close>, \<open>SForEach\<close>, \<open>SBreak\<close>, \<open>SContinue\<close>, \<open>SReturn\<close>, \<open>SThrow\<close>, \<open>SYield\<close>, \<open>SAssert\<close>,
    \<open>SSync\<close>, \<open>STry\<close> (resources, \<open>catch\<close> clauses, \<open>finally\<close>), \<open>SSwitch\<close> and \<open>SCtorCall\<close> (\<open>this(\<dots>)\<close>
    and \<open>super(\<dots>)\<close>).
  \<^item> \<open>jDecl\<close>: \<open>DClass\<close>, \<open>DInterface\<close>, \<open>DEnum\<close> (with \<open>jEnumConst\<close>s), \<open>DRecord\<close>, \<open>DAnnotType\<close>, \<open>DField\<close>,
    \<open>DMethod\<close>, \<open>DCtor\<close>, \<open>DCompact\<close> (the compact constructor of a record), \<open>DInit\<close> and \<open>DEmpty\<close>, with
    their \<open>jModifier\<close>s (keywords and annotations) and \<open>jParam\<close>s.
  \<^item> \<open>jUnit\<close>: the package (with its annotations), the \<open>jImport\<close>s of five kinds and a body, either
    \<open>Types\<close> - the declarations of an ordinary or compact unit - or a \<open>Module\<close> with its \<open>jModDir\<close>
    directives.
  \<^item> \<open>root\<close>: the result of a parse by entry point - \<open>Id\<close>, \<open>Expr\<close>, \<open>Type\<close>, \<open>Stmts\<close>, \<open>Decls\<close> or
    \<open>Source\<close> - plus \<open>Stmt\<close> and \<open>Decl\<close>, never produced by a parse but used by the analysis as the
    closest context of an annotation on a statement or a declaration.

  Where the grammar is ambiguous without name resolution, the AST follows the syntactic reading
  and leaves the decision to the analysis: \<open>a.b.c\<close> is a chain of \<open>EField\<close> whether \<open>a\<close> is a variable,
  a type or a package, and a compact unit is told from an ordinary one only by its top level
  having fields or methods.
\<close>

section\<open>The Test Corpus: the OpenJDK Sources\<close>

text\<open>
  A grammar is only as good as the programs it has been tested on, and Java has a corpus at hand:
  the JDK of Isabelle2026 (version 25.0.4) carries its own sources. The test theory
  \<^verbatim>\<open>Java_Tests.thy\<close> therefore ends with a corpus test: if the environment variable \<^verbatim>\<open>JAVA_SRC\<close>
  names a directory of Java sources - for instance the extracted \<^verbatim>\<open>lib/src.zip\<close> -, every
  \<^verbatim>\<open>.java\<close> file below it is read, printed back, and read again; the two prints must be equal, and
  the tokens of the print are those of the source. These are 15\,371 files, among them 69 module
  declarations and the generated tables of the character sets, and all of them pass. The sources
  are also what \<^verbatim>\<open>javac\<close> accepts, and \<^verbatim>\<open>javac --release 25\<close> checks the examples of this repository.

  The test found a number of facts about Java that its specification says in prose or not at all.
  A \<open>>>\<close> can close two lists of type arguments, and a \<open>>>>\<close> three; a generic type in an
  \<open>implements\<close> list is followed by a comma that is not a comparison; a qualified type may carry
  type arguments on the way (\<open>Outer<A>.Inner\<close>); a cast and a parenthesised expression differ by the
  token after the closing parenthesis (\<open>(int) -x\<close> against \<open>(a) - x\<close>); an annotation's parentheses
  are not a cast (\<open>@A(x) long y\<close>); \<open>case X when (\<dots>) ->\<close> is a guard, not a lambda; \<open>yield\<close> is a
  statement unless javac's rule says it is a variable; \<open>o instanceof T ? f(x) : y\<close> is not a record
  pattern; the resources of a \<open>try\<close> may end in a semicolon; an initializer of a constant that
  is a text block may contain a quote; \<open>.75f\<close>, \<open>1e16\<close>, \<open>0F\<close> and \<open>0d\<close> are floats; and a Javadoc
  \<open>{@code "x"}\<close> is not an antiquotation.

  Besides the corpus, the test theories contain round-trip tests for every construct (a program
  in the printer's canonical layout comes back unchanged, and every accepted program is a fixed
  point of parse-then-print), tests of the tokens that the stream delivers, rejection tests, and,
  in \<^verbatim>\<open>Java_Cmd_Tests.thy\<close>, tests of the commands: the number of entity markups for each scoping
  rule and each rule of the type pass (without the platform, so that the counts do not depend on a
  JDK; the platform has its own tests, on a small tree written to a temporary directory and on
  the JDK of Isabelle), navigation, the evaluation order, \<open>java_file\<close> on the examples, export
  and the backend hook.

  The analysis has been run over the whole corpus as well: the 15\,371 files give about 3 million
  entity markups without a crash, in about two minutes on 8 threads with the platform (45 seconds without
  it). The only errors are comments like \<open>//@Deprecated\<close> that begin with an \<open>@\<close>-tag no handler
  is registered for.
\<close>

section\<open>Limitations\<close>

text\<open>
  Isabelle/Java covers the language but is deliberately modest about what it does with it, and the
  navigation language is the narrowed one of Isabelle/C 2.0. Concretely:

  \<^item> \<^bold>\<open>The stream is a lookahead on tokens.\<close> It decides by the tokens alone, without knowing
    types, as javac's parser does, so the readings it chooses are those of javac: in the
    arguments of a call \<open>f(a < b, c > d)\<close> is two comparisons, and a member declaration
    \<open>Foo(Map<A, B> m)\<close> in the body of an enum constant is read as a call if it is the first in a
    block. Unicode escapes (\<^verbatim>\<open>\u0041\<close>) are translated before lexing by the specification; here they
    are recognised inside literals and comments, where they occur in practice. Identifiers are
    ASCII letters, digits, \<open>_\<close> and \<open>$\<close> plus every non-ASCII byte. The preview features of Java 25
    are not Java 25 and are rejected.
  \<^item> \<^bold>\<open>No semantics.\<close> There is no type checker: no definite assignment, no checked exceptions, no
    constant evaluation. The type pass links only what is certain, so a call with arguments of
    unknown type, a generic method whose type parameters the arguments do not determine, or a
    member inherited through a supertype that cannot be found is left unmarked. A lambda has a
    type only where the context gives one (\<open>\<section>2.3\<close>), and its result binds a type parameter only
    if its body is an expression or one \<open>return\<close>; a \<open>switch\<close> expression is typed by its arms
    unless one of them declares locals, and the join of reference types is not computed. The classes of the platform are read from a JDK; the other files of the
    program's own package are not seen (only the unit being analysed is), and neither is a
    library other than the JDK.
  \<^item> \<^bold>\<open>Cost of the platform.\<close> A class of the JDK is parsed once per session; a program that uses a
    few hundred of them (the whole of the JDK analysed in one session) takes minutes. The lookups
    of the type pass are not cached.
  \<^item> \<^bold>\<open>Contract-free.\<close> Java has no contract language of its own, and the front-end adds none: what
    a comment means is up to its antiquotation, and what a program means is up to a semantic
    backend. A JML-style comment that begins with \<open>//@\<close> needs a handler or a space.
  \<^item> \<^bold>\<open>Comment placement.\<close> A comment is attached to the node starting at the next real token.
    A comment before a name that does not begin its line is attached to that name, not to the
    construct around it; an annotation meant for a statement belongs on its own line above it.
  \<^item> \<^bold>\<open>The \<open>text\<close> antiquotation never reaches the generated document.\<close> It runs the body
    through the real \<^ML>\<open>Document_Output.output_document\<close>, but the result only reaches a probe
    reference. This is a limitation of Isabelle itself, not of this front-end: the presentation
    of a command is only consulted for document-class commands, which a \<open>thy_decl\<close> command can
    never be.
  \<^item> \<^bold>\<open>Navigation is not total.\<close> An \<open>Id\<close> root is a leaf and is never navigable by \<open>r\<close>/\<open>d\<close>; there
    is no wrapping; and nodes without a \<open>root\<close> variant (parameters, modifiers, switch labels,
    catch clauses, enum constants) cannot be navigation targets.

\<close>

section\<open>Conclusion\<close>

text\<open>
  Isabelle/Java shows that the design of Isabelle/C Version 2.0 carries over to a language whose
  syntax is, at the level of tokens, ambiguous in a dozen places: the grammar of the whole
  language is an ordinary ml-yacc grammar over an ordinary ml-lex lexer, with no conflict, once a
  small stream has told the type argument list from the comparison, the lambda and the cast from
  the parenthesis, and the keyword from the name; and the source of the JDK - over fifteen
  thousand files - is its test suite. Everything on top of the parser - positions, environment,
  hyperlinks, antiquotations, navigation, commands - is the C11 design instantiated for a new
  AST. The type pass goes one step further than the other front-ends in one respect: because the
  JDK ships with its own sources, the classes of the platform are known by reading them, and
  \<open>s.length()\<close> is linked to the code of \<open>String\<close>. What is documented in \<open>\<section>6\<close> as missing is, in
  every case, a scoping decision rather than an accident: the natural next steps are the
  inference of the type arguments of a call from the target type, a faster lookup of members, a semantic backend that translates Java
  programs into HOL - the antiquotations of \<open>\<section>2.4\<close> then state and discharge the
  specifications in the comments next to the program, as the \<open>lemma\<close> above - and the reading of
  the other files of a program from a source path.

  \pagebreak
\<close>

section\<open>Annex: The Java Grammar as Railroad Diagrams\<close>

subsection\<open>Lexical Structure\<close>

text\<open>
  The lexer is a small ml-lex specification in \<^verbatim>\<open>Java_Parser.thy\<close>. The reserved keywords of Java
  (\<open>abstract\<close>, \<open>assert\<close>, \<open>boolean\<close>, \<open>break\<close>, \<open>byte\<close>, \<open>case\<close>, \<open>catch\<close>, \<open>char\<close>, \<open>class\<close>, \<open>const\<close>,
  \<open>continue\<close>, \<open>default\<close>, \<open>do\<close>, \<open>double\<close>, \<open>else\<close>, \<open>enum\<close>, \<open>extends\<close>, \<open>final\<close>, \<open>finally\<close>,
  \<open>float\<close>, \<open>for\<close>, \<open>goto\<close>, \<open>if\<close>, \<open>implements\<close>, \<open>import\<close>, \<open>instanceof\<close>, \<open>int\<close>, \<open>interface\<close>,
  \<open>long\<close>, \<open>native\<close>, \<open>new\<close>, \<open>package\<close>, \<open>private\<close>, \<open>protected\<close>, \<open>public\<close>, \<open>return\<close>, \<open>short\<close>,
  \<open>static\<close>, \<open>strictfp\<close>, \<open>super\<close>, \<open>switch\<close>, \<open>synchronized\<close>, \<open>this\<close>, \<open>throw\<close>, \<open>throws\<close>,
  \<open>transient\<close>, \<open>try\<close>, \<open>void\<close>, \<open>volatile\<close>, \<open>while\<close>, and the underscore \<open>_\<close>) are reserved, as are
  the literals \<open>true\<close>, \<open>false\<close> and \<open>null\<close>; the contextual keywords (\<open>\<section>2.1\<close>) are names to the
  lexer and are told apart by the stream. Integer literals are decimal, binary (\<open>0b\<close>), octal
  (\<open>0\<close>) or hexadecimal (\<open>0x\<close>), with underscores between digits and an \<open>l\<close> or \<open>L\<close> suffix;
  floating-point literals have a fraction or an exponent, or are hexadecimal with a binary
  exponent (\<open>0x1.8p3\<close>), with an \<open>f\<close>, \<open>F\<close>, \<open>d\<close> or \<open>D\<close> suffix. A character literal is \<open>'x'\<close> with the
  escapes of the specification; a string is \<open>"\<dots>"\<close> or a text block between two triple quotes.
  The comment machinery lives in the lexer, as in the other front-ends: \<open>//\<close> enters a comment
  state that runs to the end of the line, \<open>/*\<close> one that runs to the next \<open>*/\<close> (comments do not
  nest), and an antiquotation is recognised by a regular expression for its head, followed by a
  nesting-depth counter for a cartouche body. The syntax of the head:

  \<^rail>\<open>
    antiquotation : '@' tag navi? level? body?
    ;
    navi : '[' (step *) ']'
    ;
    step : 'u' | 'U' | 'r' | 'd'
    ;
    level : '(' integer ')'
    ;
    body : cartouche | '"' text '"'
  \<close>

  The bracket around the navigation steps is a delimiter on purpose: \<open>u\<close>, \<open>U\<close>, \<open>r\<close>, \<open>d\<close> are
  ordinary identifier characters, so a tag ending in one of them (\<open>@answer\<close>) would otherwise be
  ambiguous between a tag and a tag plus a step. A body in double quotes, and a tag without a
  body, are antiquotations only directly after the comment opener.
\<close>

subsection\<open>Grammar\<close>

text\<open>
  The grammar is reproduced here after the specification (chapter 19), slightly simplified: the
  tokens that the stream relabels (\<open>TLT\<close>, \<open>TGT\<close>, \<open>LAMLP\<close>, \<open>CASTLP\<close>, \<open>RECLP\<close>, \<open>LAMID\<close>) are shown
  as \<open><\<close>, \<open>>\<close> and \<open>(\<close>, the optional trailing separators are left out, the contextual keywords
  are shown as such, and the binary operators are abbreviated by their precedence table, from the
  loosest to the tightest binding: \<open>||\<close>; \<open>&&\<close>; \<open>|\<close>; \<open>^\<close>; \<open>&\<close>; \<open>==\<close>, \<open>!=\<close>; \<open><\<close>, \<open><=\<close>, \<open>>\<close>,
  \<open>>=\<close>, \<open>instanceof\<close>; \<open><<\<close>, \<open>>>\<close>, \<open>>>>\<close>; \<open>+\<close>, \<open>-\<close>; \<open>*\<close>, \<open>/\<close>, \<open>%\<close>; all left-associative,
  below the conditional \<open>?:\<close>, the lambda and the assignments, which are right-associative.

  \<^rail>\<open>
    compilation__unit : ordinary__unit | compact__unit | module__unit
    ;
    ordinary__unit : ((annotation *) 'package' qualified__name ';')? (import__decl *)
                     ((type__decl | ';') *)
    ;
    compact__unit : (import__decl *) ((type__decl | member__decl) *)
    ;
    module__unit : (import__decl *) (annotation *) 'open'? 'module' qualified__name
                   '{' (module__directive *) '}'
    ;
    import__decl : 'import' ('static'? qualified__name ('.' '*')? | 'module' qualified__name) ';'
    ;
    module__directive : 'requires' (('transitive' | 'static') *) qualified__name ';'
                      | ('exports' | 'opens') qualified__name ('to' (qualified__name + ','))? ';'
                      | 'uses' qualified__name ';'
                      | 'provides' qualified__name 'with' (qualified__name + ',') ';'
  \<close>

  \<^rail>\<open>
    type__decl : class__decl | interface__decl | enum__decl | record__decl | annotation__decl
    ;
    class__decl : (modifier *) 'class' identifier type__parameters? ('extends' type)?
                  ('implements' (type + ','))? ('permits' (type + ','))? class__body
    ;
    interface__decl : (modifier *) 'interface' identifier type__parameters?
                      ('extends' (type + ','))? ('permits' (type + ','))? class__body
    ;
    enum__decl : (modifier *) 'enum' identifier ('implements' (type + ','))?
                 '{' ((enum__constant + ',')?) (';' (member__decl *))? '}'
    ;
    enum__constant : (annotation *) identifier ('(' ((expression + ',')?) ')')? class__body?
    ;
    record__decl : (modifier *) 'record' identifier type__parameters?
                   '(' ((record__component + ',')?) ')' ('implements' (type + ','))?
                   '{' (member__decl *) '}'
    ;
    annotation__decl : (modifier *) '@' 'interface' identifier class__body
    ;
    type__parameters : '<' (type__parameter + ',') '>'
    ;
    type__parameter : (annotation *) identifier ('extends' (type + '&'))?
    ;
    class__body : '{' (member__decl *) '}'
  \<close>

  \<^rail>\<open>
    member__decl : field__decl | method__decl | constructor__decl | compact__constructor
                 | initializer | type__decl | ';'
    ;
    field__decl : (modifier *) type (variable__declarator + ',') ';'
    ;
    variable__declarator : identifier (('[' ']') *) ('=' (expression | array__init))?
    ;
    method__decl : (modifier *) type__parameters? type identifier
                   '(' ((formal__parameter + ',')?) ')' (('[' ']') *) ('throws' (type + ','))?
                   (block | ';' | 'default' element__value ';')
    ;
    constructor__decl : (modifier *) type__parameters? identifier
                        '(' ((formal__parameter + ',')?) ')' ('throws' (type + ','))? block
    ;
    compact__constructor : (modifier *) identifier block
    ;
    initializer : 'static'? block
    ;
    formal__parameter : (modifier *) type '...'? identifier (('[' ']') *)
    ;
    modifier : annotation | 'public' | 'protected' | 'private' | 'abstract' | 'static' | 'final'
             | 'sealed' | 'non-sealed' | 'strictfp' | 'default' | 'synchronized' | 'native'
             | 'transient' | 'volatile'
    ;
    annotation : '@' qualified__name ('(' ((element__value | (identifier '=' element__value) + ',')?) ')')?
    ;
    element__value : expression | annotation | '{' ((element__value + ',')?) '}'
  \<close>

  \<^rail>\<open>
    type : (annotation *) (primitive__type | class__type) (('[' ']') *)
    ;
    primitive__type : 'boolean' | 'byte' | 'short' | 'int' | 'long' | 'char' | 'float' | 'double'
    ;
    class__type : ((annotation *) identifier type__arguments?) + '.'
    ;
    type__arguments : '<' ((type | (annotation *) '?' (('extends' | 'super') type)?) + ',')? '>'
    ;
    qualified__name : identifier + '.'
  \<close>

  \<^rail>\<open>
    block : '{' (block__statement *) '}'
    ;
    block__statement : local__variable ';' | type__decl | statement
    ;
    local__variable : (modifier *) (type | 'var') (variable__declarator + ',')
    ;
    statement : block | ';' | identifier ':' statement | expression ';'
              | 'if' '(' expression ')' statement ('else' statement)?
              | 'assert' expression (':' expression)? ';'
              | 'switch' '(' expression ')' switch__block
              | 'while' '(' expression ')' statement
              | 'do' statement 'while' '(' expression ')' ';'
              | 'for' '(' ((local__variable | (expression + ','))? ';' expression? ';'
                           ((expression + ',')?)
                          | (modifier *) (type | 'var') identifier ':' expression) ')' statement
              | 'break' identifier? ';' | 'continue' identifier? ';'
              | 'return' expression? ';' | 'throw' expression ';' | 'yield' expression ';'
              | 'synchronized' '(' expression ')' block
              | 'try' ('(' ((local__variable | expression) + ';') ';'? ')')? block
                (catch__clause *) ('finally' block)?
              | (expression '.')? ('this' | 'super') '(' ((expression + ',')?) ')' ';'
    ;
    catch__clause : 'catch' '(' (modifier *) (type + '|') identifier ')' block
    ;
    switch__block : '{' ((switch__label (('->' (expression ';' | block | 'throw' expression ';'))
                                       | (':' (block__statement *)))) *) '}'
    ;
    switch__label : ('case' ((case__item + ',') ('when' expression)?) | 'default')
    ;
    case__item : expression | pattern | 'null' | 'default'
    ;
    pattern : (modifier *) type identifier | type '(' ((pattern + ',')?) ')' | '_'
  \<close>

  \<^rail>\<open>
    expression : lambda | assignment | conditional
    ;
    lambda : ('(' ((lambda__parameter + ',')?) ')' | identifier) '->' (expression | block)
    ;
    lambda__parameter : identifier | (modifier *) (type | 'var') identifier
    ;
    assignment : unary '=' expression | unary assign__op expression
    ;
    assign__op : '+=' | '-=' | '*=' | '/=' | '%=' | '&=' | '|=' | '^=' | '<<=' | '>>=' | '>>>='
    ;
    conditional : binary ('?' expression ':' (conditional | lambda))?
    ;
    binary : unary | binary binary__op binary | binary 'instanceof' (pattern | type)
    ;
    unary : primary | ('+' | '-' | '!' | '~' | '++' | '--') unary
          | '(' (type + '&') ')' unary
    ;
    primary : primary__prefix (('.' type__arguments? identifier ('(' ((expression + ',')?) ')')?
                                | '[' expression ']' | '++' | '--'
                                | '::' type__arguments? (identifier | 'new')
                                | '.' 'new' type__arguments? class__type
                                  '(' ((expression + ',')?) ')' class__body?) *)
    ;
    primary__prefix : literal | 'this' | 'super' | identifier ('(' ((expression + ',')?) ')')?
                    | '(' expression ')'
                    | 'new' (class__type '(' ((expression + ',')?) ')' class__body?
                            | type__no__dims (('[' expression ']') +) (('[' ']') *)
                            | type (('[' ']') +) array__init)
                    | 'switch' '(' expression ')' switch__block
                    | type '.' 'class' | type '::' (identifier | 'new')
    ;
    array__init : '{' ((variable__init + ',')?) '}'
  \<close>
\<close>

(*<*)
end
(*>*)
