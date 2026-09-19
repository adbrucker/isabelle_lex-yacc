chapter AFP

(* The "C11" session (C11/ROOT) is a separate, independent entry, not a
   sub-session of this one - it re-derives its own copy of "LexYacc"/
   "YaccLib" (via "directories .."), since "C11_Parser.thy" imports them by
   relative path. No "ROOTS" file ties the two together on purpose: a
   session's own master directory can never be shared with another
   session's, so declaring both here (or via "ROOTS", which would pull both
   into one build graph the same way) fails with "Duplicate use of
   directory". Build each separately:
     isabelle build -d . Isabelle_Lex-Yacc
     isabelle build -d C11 C11
   This is a consequence of the current, pre-submission, co-located layout;
   once "C11" references this entry as an installed AFP dependency rather
   than via a relative path into this repository, the conflict should not
   arise. *)
session "Isabelle_Lex-Yacc" (AFP) = HOL +
  options [timeout = 600]
  theories [document = false]
    Examples
  theories
    Manual 
  document_files
    "root.tex"
    "root.bib"
