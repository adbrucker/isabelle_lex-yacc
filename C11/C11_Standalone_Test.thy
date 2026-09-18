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

theory C11_Standalone_Test
  imports "C11"
begin

text\<open>
  Regression test for the \<^verbatim>\<open>C11.thy\<close>/\<^verbatim>\<open>C11_Tests.thy\<close> split: this theory
  deliberately imports \<^emph>\<open>only\<close> \<^verbatim>\<open>C11\<close>, not \<^verbatim>\<open>C11_Tests\<close>, to confirm that
  \<^verbatim>\<open>C11.thy\<close> alone - without pulling in the whole test suite - is genuinely
  sufficient for a downstream theory that just wants the \<open>c11\<close>-family
  commands. If a future change to \<^verbatim>\<open>C11.thy\<close> accidentally comes to depend on
  something now living only in \<^verbatim>\<open>C11_Tests.thy\<close> (a registered antiquotation
  handler, a helper only defined there, \<open>\<dots>\<close>), this theory - not
  \<^verbatim>\<open>C11_Tests.thy\<close> itself, which always has everything - is what would catch
  it, by simply failing to build.
\<close>

c11\<open>
int standalone_test(int x) {
  return x + 1;
}
\<close>

c11_ident\<open>standalone_test\<close>

c11_expr\<open>1 + 2\<close>

c11_statement\<open>{ int y = 0; y = y + 1; }\<close>

c11_file \<open>examples/expressions.c\<close>

c11_reject\<open>int + ;\<close>

end
