# Lex and Yacc for Isabelle/ML

This repository provides a deep integration of ml-lex and ml-yacc into Isabelle/ML (and, hence, Isabelle/HOL). 

## ml-lex and ml-yacc

The work is based on the port of ml-lex and ml-yacc of the sml/nj project to Poly/ML:

* [mllex-polyml](https://github.com/eldesh/mllex-polyml)
* [mlyacc-polyml](https://github.com/eldesh/mlyacc-polyml)

These tools have been modified in several ways. In particular, they have been modified to work "in memory", i.e., taking the lex and yacc specifications as strings and returning the generated lexer and parser as string. They also have been modified to report errors using the error reporting provided by Isabelle/PIDE.

## Authors

* [Achim D. Brucker](http://www.brucker.ch/)
* [Burkhart Wolff](https://usr.lmf.cnrs.fr/~wolff/)

## License

This project is licensed under a 3-clause BSD-style license.

SPDX-License-Identifier: BSD-3-Clause

## Upstream Repository

The upstream git repository, i.e., the single source of truth, for this project is hosted 
by the [Software Assurance & Security Research Team](https://logicalhacking.com) at
<https://git.logicalhacking.com/adbrucker/isabelle_lex-yacc/>.
