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

theory Scala3_Ast
  imports Main
begin

text\<open>
  Just the Scala 3 abstract syntax tree (structure \<^verbatim>\<open>Scala3_Ast\<close>, in
  \<^verbatim>\<open>scala3_ast.ML\<close>) and its pretty-printer (\<^verbatim>\<open>scala3_pp.ML\<close>), with none of the
  lex/yacc grammar that builds it. Kept as its own theory, importing nothing
  beyond \<^verbatim>\<open>Main\<close>, for the same reason \<^verbatim>\<open>C11_Ast.thy\<close> and \<^verbatim>\<open>Occam2_Ast.thy\<close> are:
  anything that only needs the \<^emph>\<open>types\<close> does not have to pull in the heavier
  \<^verbatim>\<open>ml_lex_yacc\<close> machinery just to see them.
\<close>

ML_file\<open>scala3_ast.ML\<close>
ML_file\<open>scala3_pp.ML\<close>

end
