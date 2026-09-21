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

theory C_Ast
  imports Main
begin

text\<open>
  Just the C11 abstract syntax tree (structure \<^verbatim>\<open>C_Ast\<close>, a hand-pruned port of
  the \<^verbatim>\<open>Isabelle_C\<close> AFP entry's own C11 AST - see \<^verbatim>\<open>c_ast.ML\<close> itself for the full
  provenance/pruning notes), with none of the lex/yacc grammar that builds it.
  Kept as its own theory, importing nothing beyond \<^verbatim>\<open>Main\<close>, so that anything
  which only needs the \<^emph>\<open>types\<close> - \<^verbatim>\<open>CEnv.thy\<close>, in particular, which stores
  \<^verbatim>\<open>C_Ast\<close> values but neither parses nor lexes anything - does not have to pull
  in \<^verbatim>\<open>C11_Parser.thy\<close>'s much heavier \<^verbatim>\<open>ml_lex_yacc\<close> machinery just to see them.
  \<^verbatim>\<open>C11_Parser.thy\<close> imports this theory in turn, rather than loading
  \<^verbatim>\<open>c_ast.ML\<close> itself, so the AST is defined in exactly one place.
\<close>

ML_file\<open>c_ast.ML\<close>

end
