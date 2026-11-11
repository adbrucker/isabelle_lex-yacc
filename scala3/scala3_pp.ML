(* Pretty-printing back to Scala 3 text (the counterpart of "pp_root" in
   occam2_ast.ML).

   Layout is regenerated, not preserved: every block prints its statements one
   per line, two spaces deeper; everything else is printed on one line (long
   lines are never broken). The printer relies on the tree being exactly what
   the parser built: a parenthesized expression is an "EParen" node, so infix
   operators can be printed flat without re-inserting parentheses, and the
   output re-parses to the same tree ("idempotence", the property the test suite
   checks, also on all Scala sources of Isabelle).

   Not preserved: comments, the choice between "_" and "*" for a wildcard
   import, between "as" and "=>" in an import rename, and the distinction
   between "x => stats" as a block statement and "x => { stats }". *)

structure Scala3_Pp = struct

open Scala3_Ast

fun ind n = String.implode (List.tabulate (2 * n, fn _ => #" "))
fun commas f xs = String.concatWith ", " (map f xs)

(* "x_:" would lex as one identifier (an identifier may end in an underscore and
   operator characters), so a colon after a name ending in an underscore needs a
   space *)
fun colon_after s = if String.isSuffix "_" s then s ^ " : " else s ^ ": "

val name = ident_name

fun pp_modifier m = (case m of
    MAbstract => "abstract" | MFinal => "final" | MSealed =>
      "sealed" | MOpen => "open"
  | MImplicit => "implicit" | MLazy => "lazy" | MInline =>
    "inline" | MTransparent => "transparent"
  | MInfix => "infix" | MOverride => "override" | MOpaque => "opaque"
  | MPrivate NONE => "private" | MPrivate (SOME q) => "private[" ^ q ^ "]"
  | MProtected NONE => "protected" | MProtected (SOME q) =>
    "protected[" ^ q ^ "]")

fun pp_lit l = (case l of
    LInt (s, _) => s | LFloat (s, _) => s
  | LChar (s, _) => "'" ^ s ^ "'"
  | LString (s, ml, _) =>
    if ml then "\"\"\"" ^ s ^ "\"\"\"" else "\"" ^ s ^ "\""
  | LInterp (p, s, ml, _) =>
    if ml then p ^ "\"\"\"" ^ s ^ "\"\"\"" else p ^ "\"" ^ s ^ "\""
  | LBool (b, _) => if b then "true" else "false"
  | LNull _ => "null")

(* The mutually recursive printers; "n" is the current indentation level,
   consulted only by the multi-line constructs (blocks and templates). *)
fun pp_type n t = (case t of
    TName id => name id
  | TSelect (t1, id, _) => pp_type n t1 ^ "." ^ name id
  | TSingleton (e, _) => pp_expr n e ^ ".type"
  | TProject (t1, id, _) => pp_type n t1 ^ "#" ^ name id
  | TApply (t1, ts, _) => pp_type n t1 ^ "[" ^ commas (pp_type n) ts ^ "]"
  | TTuple (ts, _) => "(" ^ commas (pp_type n) ts ^ ")"
  | TFun (ctx, ts, r, _) =>
    "(" ^ commas (pp_type n) ts ^ ") " ^ (if ctx then "?=> " else "=> ")
      ^ pp_type n r
  | TByName (t1, _) => "=> " ^ pp_type n t1
  | TRepeated (t1, _) => pp_type n t1 ^ "*"
  | TInfix (t1, op_, t2, _) =>
    pp_type n t1 ^ " " ^ name op_ ^ " " ^ pp_type n t2
  | TWith (t1, t2, _) => pp_type n t1 ^ " with " ^ pp_type n t2
  | TRefine (t1, stats, _) =>
      (case t1 of SOME t => pp_type n t ^ " " | NONE => "") ^ pp_block n stats
  | TAnnot (t1, anns, _) =>
    pp_type n t1 ^ String.concat (map (fn a => " " ^ pp_annot n a) anns)
  | TWild (b, _) => "_" ^ pp_bounds n b
  | TLit (l, _) => pp_lit l
  | TLambda (tps, t1, _) =>
    "[" ^ commas (pp_tparam n) tps ^ "] =>> " ^ pp_type n t1
  | TPolyFun (tps, t1, _) =>
    "[" ^ commas (pp_tparam n) tps ^ "] => " ^ pp_type n t1
  | TMatch (t1, cases, _) =>
      pp_type n t1 ^ " match {\n" ^
      String.concat (map (fn TypeCase (lhs, rhs, _) =>
                     ind (n + 1) ^ "case "
                       ^ (case lhs of SOME t => pp_type n t | NONE => "_") ^
                     " => " ^ pp_type n rhs ^ "\n") cases) ^ ind n ^ "}")

and pp_bounds n (Bounds (lo, hi)) =
  (case lo of SOME t => " >: " ^ pp_type n t | NONE => "") ^
  (case hi of SOME t => " <: " ^ pp_type n t | NONE => "")

and pp_tparam n (TParam (anns, var, id, hk, bounds, ctx, _)) =
  String.concat (map (fn a => pp_annot n a ^ " ") anns) ^
  (case var of 1 => "+" | 2 => "-" | _ => "") ^ name id ^
  (case hk of [] => "" | tps => "[" ^ commas (pp_tparam n) tps ^ "]") ^
  pp_bounds n bounds ^ String.concat (map (fn t => ": " ^ pp_type n t) ctx)

and pp_annot n (Annot (t, argss, _)) =
  "@" ^ pp_type n t
    ^ String.concat (map (fn args => "(" ^ commas (pp_arg n) args ^ ")") argss)

and pp_arg n a = (case a of
    AExpr e => pp_expr n e
  | ANamed (id, e, _) => name id ^ " = " ^ pp_expr n e)

and pp_binding n (Binding (id, t, _)) =
  (case id of SOME i => name i | NONE => "_")
    ^ (case t of SOME t1 => ": " ^ pp_type n t1 | NONE => "")

and pp_expr n e = (case e of
    EIdent id => name id
  | ESelect (e1, id, _) => pp_expr n e1 ^ "." ^ name id
  | EThis (q, _) => (case q of SOME id => name id ^ "." | NONE => "") ^ "this"
  | ESuper (q, mix, _) =>
      (case q of SOME id => name id ^ "." | NONE => "") ^ "super" ^
      (case mix of SOME id => "[" ^ name id ^ "]" | NONE => "")
  | ELit l => pp_lit l
  | EApply (f, args, using_, _) =>
      pp_expr n f ^ "(" ^ (if using_ then "using " else "")
        ^ commas (pp_arg n) args ^ ")"
  | ETypeApply (e1, ts, _) => pp_expr n e1 ^ "[" ^ commas (pp_type n) ts ^ "]"
  | EInfix (e1, op_, e2, _) =>
    pp_expr n e1 ^ " " ^ name op_ ^ " " ^ pp_expr n e2
  | EPrefix (op_, e1, _) => name op_ ^ pp_expr n e1
  | EPostfix (e1, op_, _) => pp_expr n e1 ^ " " ^ name op_
  | EAssign (e1, e2, _) => pp_expr n e1 ^ " = " ^ pp_expr n e2
  | ETyped (e1, t, _) => colon_after (pp_expr n e1) ^ pp_type n t
  | EAnnotated (e1, anns, _) =>
    pp_expr n e1 ^ ":" ^ String.concat (map (fn a => " " ^ pp_annot n a) anns)
  | ESplat (e1, _) => pp_expr n e1 ^ ": _*"
  | ELambda (bs, body, ctx, _) =>
      "(" ^ commas (pp_binding n) bs ^ ") " ^ (if ctx then "?=> " else "=> ")
        ^ pp_expr n body
  | EBlock (stats, _) => pp_block n stats
  | ECases (cases, _) =>
    "{\n" ^ String.concat (map (pp_case n) cases) ^ ind n ^ "}"
  | EIf (c, a, b, _) =>
      "if (" ^ pp_expr n c ^ ") " ^ pp_expr n a
        ^ (case b of SOME e2 => " else " ^ pp_expr n e2 | NONE => "")
  | EWhile (c, b, _) => "while (" ^ pp_expr n c ^ ") " ^ pp_expr n b
  | ETry (b, h, f, _) =>
      "try " ^ pp_expr n b
        ^ (case h of SOME e1 => " catch " ^ pp_expr n e1 | NONE => "") ^
      (case f of SOME e1 => " finally " ^ pp_expr n e1 | NONE => "")
  | EThrow (e1, _) => "throw " ^ pp_expr n e1
  | EReturn (e1, _) =>
    "return" ^ (case e1 of SOME x => " " ^ pp_expr n x | NONE => "")
  | EFor (enums, yield_, body, _) =>
      "for {\n"
        ^ String.concat
          (map (fn en => ind (n + 1) ^ pp_enum n en ^ "\n") enums) ^ ind n
            ^ "} " ^
      (if yield_ then "yield " else "") ^ pp_expr n body
  | EMatch (e1, cases, _) =>
    pp_expr n e1 ^ " match {\n" ^ String.concat (map (pp_case n) cases) ^ ind n
      ^ "}"
  | ENew (parents, body, _) =>
      "new " ^ String.concatWith " with " (map (pp_parent n) parents) ^
      (case body of
         SOME b => (if null parents then "" else " ") ^ pp_template_body n b
       | NONE => "")
  | ETuple (es, _) => "(" ^ commas (pp_expr n) es ^ ")"
  | EParen (e1, _) => "(" ^ pp_expr n e1 ^ ")"
  | EPlaceholder _ => "_")

and pp_enum n en = (case en of
    EnGen (c, p, e1, _) =>
      (if c then "case " else "") ^ pp_pat n p ^ " <- " ^ pp_expr n e1
  | EnGuard (e1, _) => "if " ^ pp_expr n e1
  | EnVal (p, e1, _) => pp_pat n p ^ " = " ^ pp_expr n e1)

and pp_case n (Case (p, g, body, _)) =
  ind (n + 1) ^ "case " ^ pp_pat n p
    ^ (case g of SOME e1 => " if " ^ pp_expr n e1 | NONE => "") ^ " =>" ^
  (case body of
     [] => "\n"
   | _ => "\n" ^ pp_stats (n + 2) body)

and pp_pat n p = (case p of
    PVar id => name id
  | PWild _ => "_"
  | PLit l => pp_lit l
  | PRef e => pp_expr n e
  | PApply (f, ts, ps, _) =>
      pp_expr n f
        ^ (case ts of [] => "" | _ => "[" ^ commas (pp_type n) ts ^ "]") ^ "("
          ^ commas (pp_pat n) ps ^ ")"
  | PTuple (ps, _) => "(" ^ commas (pp_pat n) ps ^ ")"
  | PInfix (p1, op_, p2, _) =>
    pp_pat_atom n p1 ^ " " ^ name op_ ^ " " ^ pp_pat_atom n p2
  | PAlt (ps, _) => String.concatWith " | " (map (pp_pat n) ps)
  | PBind (id, p1, _) => name id ^ " @ " ^ pp_pat_atom n p1
  | PTyped (p1, t, _) => colon_after (pp_pat n p1) ^ pp_type n t
  | PSplat (p1, _) => pp_pat n p1 ^ "*"
  | PGiven (t, _) => "given " ^ pp_type n t)

(* an operand of an infix or "@" pattern: constructs that bind looser are
   parenthesized *)
and pp_pat_atom n p = (case p of
    PTyped _ => "(" ^ pp_pat n p ^ ")"
  | PAlt _ => "(" ^ pp_pat n p ^ ")"
  | PBind _ => "(" ^ pp_pat n p ^ ")"
  | PInfix _ => "(" ^ pp_pat n p ^ ")"
  | _ => pp_pat n p)

and pp_parent n (Parent (t, argss, usings, _)) =
  pp_type n t ^ String.concat (map2 (fn args => fn u =>
    "(" ^ (if u then "using " else "") ^ commas (pp_arg n) args
      ^ ")") argss usings)

and pp_param n (Param (anns, mods, vv, id, t, dflt, _)) =
  String.concat (map (fn a => pp_annot n a ^ " ") anns)
    ^ String.concat (map (fn m => pp_modifier m ^ " ") mods) ^
  (case vv of 1 => "val " | 2 => "var " | _ => "") ^
  (case id of SOME i => colon_after (name i) | NONE => "") ^ pp_type n t ^
  (case dflt of SOME e => " = " ^ pp_expr n e | NONE => "")

and pp_clause n c = (case c of
    PClause (k, ps, _) =>
      "(" ^ (case k of CPlain => "" | CUsing => "using " | CImplicit =>
             "implicit ") ^ commas (pp_param n) ps ^ ")"
  | TClause (tps, _) => "[" ^ commas (pp_tparam n) tps ^ "]")

and pp_template_body n (TemplateBody (self, stats, _)) =
  "{" ^
  (case self of
     SOME (Self (id, t, _)) =>
       " " ^ (case t of SOME t1 =>
              colon_after (name id) ^ pp_type n t1 | NONE => name id) ^ " =>"
   | NONE => "") ^ "\n" ^ pp_stats (n + 1) stats ^ ind n ^ "}"

and pp_template n (Template (parents, derives, body, _)) =
  (case parents of [] => "" | _ =>
   " extends " ^ String.concatWith " with " (map (pp_parent n) parents)) ^
  (case derives of [] => "" | ds => " derives " ^ commas name ds) ^
  (case body of SOME b => " " ^ pp_template_body n b | NONE => "")

and pp_block n stats = "{\n" ^ pp_stats (n + 1) stats ^ ind n ^ "}"

and pp_selector n s = (case s of
    SelName (id, r, _) =>
      name id ^ (case r of SOME id2 => " => " ^ name id2 | NONE => "")
  | SelWild _ => "_"
  | SelGiven (t, _) =>
    "given" ^ (case t of SOME t1 => " " ^ pp_type n t1 | NONE => ""))

and pp_import n (ImportExpr (path, sels, _)) =
  (case sels of
     [] => pp_expr n path
   | [SelWild _] => pp_expr n path ^ "._"
   | [SelName (id, NONE, _)] => pp_expr n path ^ "." ^ name id
   | _ => pp_expr n path ^ ".{" ^ commas (pp_selector n) sels ^ "}")

and pp_stat n s = (case s of
    SExpr (ELambda (bs, EBlock (stats, _), ctx, _)) =>
      (* a lambda in statement position extends to the end of the block, without
         braces *)
      "(" ^ commas (pp_binding n) bs ^ ") " ^ (if ctx then "?=>" else "=>") ^
      (case stats of [] => "" | _ => "\n" ^ pp_stats (n + 1) stats)
  | SExpr e => pp_expr n e
  | SImport (exp, imps, _) =>
    (if exp then "export " else "import ") ^ commas (pp_import n) imps
  | SDef d => pp_def n d)

(* a statement that starts with "{" would, after a single newline, be read as an
   argument of the previous statement (Scala 2 rule: a newline before "{" is
   ignored): such a statement is separated by an explicit semicolon, except at
   the start of a block *)
and pp_stats n stats =
  String.concat (map_index (fn (i, s) =>
    let val text = pp_stat n s
    in ind n ^ (if i > 0 andalso String.isPrefix "{" text then ";" else "")
      ^ text ^ "\n" end) stats)

and pp_prefix n anns mods =
  String.concat (map (fn a => pp_annot n a ^ " ") anns)
    ^ String.concat (map (fn m => pp_modifier m ^ " ") mods)

and pp_def n d = (case d of
    DVal (anns, mods, isvar, pats, t, rhs, _) =>
      pp_prefix n anns mods ^ (if isvar then "var " else "val ") ^
      (case t of SOME t1 =>
       colon_after (commas (pp_pat n) pats) ^ pp_type n t1 | NONE =>
         commas (pp_pat n) pats) ^
      (case rhs of SOME e => " = " ^ pp_expr n e | NONE => "")
  | DDef (anns, mods, id, clauses, t, rhs, _) =>
      pp_prefix n anns mods ^ "def " ^
      (case t of SOME t1 =>
       colon_after (name id ^ String.concat (map (pp_clause n) clauses))
         ^ pp_type n t1
               | NONE => name id ^ String.concat (map (pp_clause n) clauses)) ^
      (case rhs of SOME e => " = " ^ pp_expr n e | NONE => "")
  | DType (anns, mods, id, clauses, bounds, rhs, _) =>
      pp_prefix n anns mods ^ "type " ^ name id
        ^ String.concat (map (pp_clause n) clauses) ^ pp_bounds n bounds ^
      (case rhs of SOME t => " = " ^ pp_type n t | NONE => "")
  | DClass (anns, mods, kind, id, tps, cmods, clauses, tmpl, _) =>
      pp_prefix n anns mods ^
      (case kind of
         KClass => "class " | KTrait => "trait " | KObject =>
           "object " | KEnum => "enum "
       | KCaseClass => "case class " | KCaseObject =>
         "case object " | KPackageObject => "package object ") ^
      name id ^ (case tps of [] => "" | _ =>
                 "[" ^ commas (pp_tparam n) tps ^ "]") ^
      String.concat (map (fn m => " " ^ pp_modifier m) cmods) ^
      String.concat (map (pp_clause n) clauses) ^ pp_template n tmpl
  | DGiven (anns, mods, id, clauses, t, rhs, body, _, _) =>
      pp_prefix n anns mods ^ "given "
        ^ (case id of SOME i => colon_after (name i) | NONE => "") ^
      (case clauses of [] => "" | _ =>
       String.concat (map (pp_clause n) clauses) ^ ": ") ^ pp_type n t ^
      (case rhs of SOME e => " = " ^ pp_expr n e | NONE => "") ^
      (case body of SOME b => " " ^ pp_template_body n b | NONE => "")
  | DExtension (clauses, stats, _) =>
      "extension " ^ String.concat (map (pp_clause n) clauses) ^ " {\n"
        ^ pp_stats (n + 1) stats ^ ind n ^ "}"
  | DEnumCase (anns, mods, ids, tps, clauses, parents, _) =>
      pp_prefix n anns mods ^ "case " ^ commas name ids ^
      (case tps of [] => "" | _ => "[" ^ commas (pp_tparam n) tps ^ "]") ^
      String.concat (map (pp_clause n) clauses) ^
      (case parents of [] => "" | _ =>
       " extends " ^ String.concatWith " with " (map (pp_parent n) parents))
  | DPackage (path, body, _) =>
      "package " ^ pp_expr n path ^
      (case body of SOME stats =>
       " {\n" ^ pp_stats (n + 1) stats ^ ind n ^ "}" | NONE => ""))

fun pp_root r = (case r of
    Id id => name id
  | Expr e => pp_expr 0 e
  | Type t => pp_type 0 t
  | Stat s => pp_stat 0 s
  | Pat p => pp_pat 0 p
  | Unit stats =>
      let val text = pp_stats 0 stats
      in if String.isSuffix "\n" text
        then String.substring (text, 0, size text - 1) else text end)

end
