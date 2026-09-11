# Example C11 sources for `c11_file`

`expressions.c`, `dangling_else.c`, and `declarators.c` are borrowed
unmodified from the [`parser_menhir`](https://github.com/jhjourdan/C11parser)
C11 conformance test suite (via its vendored copy in the
[Isabelle_C](https://www.isa-afp.org/entries/Isabelle_C.html) AFP entry,
`Isabelle_C/src_ext/parser_menhir/tests/`), used there as lexer/parser
stress tests in `C11-FrontEnd/examples/C0.thy`. They are used here for the
same purpose: as non-trivial, real-world input to `c11_file` in `C11.thy`.

Copyright (c) 2016-2017, Inria. BSD 3-clause license, see
`LICENSE.parser_menhir` in this directory.
