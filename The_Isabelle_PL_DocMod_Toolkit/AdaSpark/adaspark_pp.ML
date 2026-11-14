(* Printing an AdaSpark AST back as Ada text: canonical layout (three-space
   indentation, one declaration or statement per line, the aspects of a
   subprogram or package on lines of their own, keywords in lower case,
   identifiers as written). Every explicit parenthesis of the source is kept in
   the AST ("EParen", aggregates), so no precedence reasoning is needed here.
   Comments and antiquotations are not printed (they live in the nodeInfo), as
   in the other front-ends. *)

structure AdaSpark_Pp = struct

structure A = AdaSpark_Ast

fun commas xs = space_implode ", " xs
fun opt f x = (case x of NONE => "" | SOME y => f y)

fun ind_str n = replicate_string (3 * n) " "

fun ident_str (A.Ident (s, _, _)) = s

fun binop_str b = (case b of
    A.Plus => " + " | A.Minus => " - " | A.Concat => " & " | A.Mul => " * "
  | A.Div => " / " | A.Mod => " mod " | A.Rem => " rem " | A.Exp => " ** "
  | A.Eq => " = " | A.Ne => " /= " | A.Lt => " < " | A.Le => " <= "
  | A.Gt => " > " | A.Ge => " >= " | A.And => " and " | A.Or => " or "
  | A.Xor => " xor " | A.AndThen => " and then " | A.OrElse => " or else ")

fun unop_str u = (case u of
    A.UPlus => "+" | A.UMinus => "-" | A.Abs => "abs " | A.Not => "not ")

fun mode_str m = (case m of
    A.MDefault => "" | A.MIn => "in " | A.MOut => "out "
  | A.MInOut => "in out " | A.MAccess => "access ")

fun range_str (lo, hi) = " range " ^ expr_str lo ^ " .. " ^ expr_str hi

and expr_str e = (case e of
    A.EId id => ident_str id
  | A.EInt (s, _) => s
  | A.EReal (s, _) => s
  | A.EChar (s, _) => s
  | A.EStr (s, _) => s
  | A.ENull _ => "null"
  | A.ESel (e1, id, _) => expr_str e1 ^ "." ^ ident_str id
  | A.EDeref (e1, _) => expr_str e1 ^ ".all"
  | A.EApply (f, args, _) =>
      expr_str f ^ " (" ^ commas (map assoc_str args) ^ ")"
  | A.EAttr (e1, id, _) => expr_str e1 ^ "'" ^ ident_str id
  | A.EQual (e1, args, _) =>
      expr_str e1 ^ "'(" ^ commas (map assoc_str args) ^ ")"
  | A.EUn (u, e1, _) => unop_str u ^ expr_str e1
  | A.EBin (b, e1, e2, _) => expr_str e1 ^ binop_str b ^ expr_str e2
  | A.EIn (neg, e1, chs, _) =>
      expr_str e1 ^ (if neg then " not in " else " in ") ^
      space_implode " | " (map choice_str chs)
  | A.EParen (e1, _) => "(" ^ expr_str e1 ^ ")"
  | A.EAgg (args, _) => "(" ^ commas (map assoc_str args) ^ ")"
  | A.EExtAgg (e1, args, _) =>
      "(" ^ expr_str e1 ^ " with " ^ commas (map assoc_str args) ^ ")"
  | A.EDeltaAgg (e1, args, _) =>
      "(" ^ expr_str e1 ^ " with delta " ^ commas (map assoc_str args) ^ ")"
  | A.ENew (e1, _) => "new " ^ expr_str e1
  | A.EIf (branches, els, _) =>
      (case branches of
         [] => ""
       | (c, t) :: rest =>
           "if " ^ expr_str c ^ " then " ^ expr_str t ^
           implode (map (fn (c1, t1) =>
                           " elsif " ^ expr_str c1 ^ " then " ^ expr_str t1)
                      rest) ^
           opt (fn e1 => " else " ^ expr_str e1) els)
  | A.ECase (s, alts, _) =>
      "case " ^ expr_str s ^ " is " ^
      commas (map (fn (chs, e1) =>
                     "when " ^ space_implode " | " (map choice_str chs) ^
                     " => " ^ expr_str e1) alts)
  | A.EQuant (all, id, it, p, _) =>
      "for " ^ (if all then "all " else "some ") ^ ident_str id ^
      iter_str it ^ " => " ^ expr_str p)

and assoc_str a = (case a of
    A.APos e => expr_str e
  | A.ARange (lo, hi, _) => expr_str lo ^ " .. " ^ expr_str hi
  | A.ANamed (chs, e, _) =>
      space_implode " | " (map choice_str chs) ^ " => " ^ expr_str e)

and choice_str c = (case c of
    A.ChExpr e => expr_str e
  | A.ChRange (lo, hi, _) => expr_str lo ^ " .. " ^ expr_str hi
  | A.ChOthers _ => "others")

(* A subtype indication without its "not null". *)
and sub_core_str (A.Sub (_, e, rng, _)) = expr_str e ^ opt range_str rng

and sub_str (s as A.Sub (nn, _, _, _)) =
  (if nn then "not null " else "") ^ sub_core_str s

and discrange_str dr = (case dr of
    A.DRRange (lo, hi, _) => expr_str lo ^ " .. " ^ expr_str hi
  | A.DRSub s => sub_str s)

and iter_str it = (case it of
    A.IterIn (rev, dr) =>
      " in " ^ (if rev then "reverse " else "") ^ discrange_str dr
  | A.IterOf (rev, e) =>
      " of " ^ (if rev then "reverse " else "") ^ expr_str e)

fun aspect_str (A.Aspect (id, tick, v, _)) =
  ident_str id ^ opt (fn t => "'" ^ ident_str t) tick ^
  opt (fn e => " => " ^ expr_str e) v

(* The aspects of an object, type or subtype stay on its line ... *)
fun aspects_str asps =
  if null asps then "" else " with " ^ commas (map aspect_str asps)

(* ... those of a subprogram or package go on lines of their own, one per
   aspect, below the declaration at indentation level "n". *)
fun aspects_ln n asps =
  if null asps then ""
  else "\n" ^ ind_str (n + 1) ^ "with " ^
       space_implode (",\n" ^ ind_str (n + 1) ^ "     ")
         (map aspect_str asps)

(* The "is" that opens a body: on its own line after aspects. *)
fun is_str n asps =
  if null asps then " is\n" else "\n" ^ ind_str n ^ "is\n"

fun idx_str i = (case i of
    A.IdxRange (lo, hi, _) => expr_str lo ^ " .. " ^ expr_str hi
  | A.IdxSub e => expr_str e
  | A.IdxUnconstrained (e, _) => expr_str e ^ " range <>")

(* A "not null access T" parameter is the one place where the grammar puts a
   "not null" in front of a mode. *)
fun param_str (A.Param (ids, m, s as A.Sub (nn, _, _, _), d, _)) =
  commas (map ident_str ids) ^ " : " ^
  (case m of
     A.MAccess => (if nn then "not null " else "") ^ "access " ^
                  sub_core_str s
   | _ => mode_str m ^ sub_str s) ^
  opt (fn e => " := " ^ expr_str e) d

fun params_str ps =
  if null ps then "" else " (" ^ space_implode "; " (map param_str ps) ^ ")"

fun spec_str (A.Spec (ov, fn_, name, params, ret, _)) =
  (if ov then "overriding " else "") ^
  (if fn_ then "function " else "procedure ") ^
  ident_str name ^ params_str params ^
  opt (fn s => " return " ^ sub_str s) ret

fun choices_str chs = space_implode " | " (map choice_str chs)

fun comp_str n (A.Comp (ids, aliased, s, d, _)) =
  ind_str n ^ commas (map ident_str ids) ^ " : " ^
  (if aliased then "aliased " else "") ^ sub_str s ^
  opt (fn e => " := " ^ expr_str e) d ^ ";\n"

fun recdef_body n rd = (case rd of
    A.RecNull => ind_str n ^ "null;\n"
  | A.RecComps (comps, vp) =>
      implode (map (comp_str n) comps) ^
      (case vp of
         NONE => ""
       | SOME (A.VariantPart (disc, alts, _)) =>
           ind_str n ^ "case " ^ ident_str disc ^ " is\n" ^
           implode (map (fn (chs, rd1) =>
                           ind_str (n + 1) ^ "when " ^ choices_str chs ^
                           " =>\n" ^ recdef_body (n + 2) rd1) alts) ^
           ind_str n ^ "end case;\n"))

fun flags_str (ab, tg, lim) =
  (if ab then "abstract " else "") ^ (if tg then "tagged " else "") ^
  (if lim then "limited " else "")

fun array_str (idxs, al, s) =
  "array (" ^ commas (map idx_str idxs) ^ ") of " ^
  (if al then "aliased " else "") ^ sub_str s

fun typedef_str n td = (case td of
    A.TEnum ids => "(" ^ commas (map ident_str ids) ^ ")"
  | A.TRange (lo, hi) => "range " ^ expr_str lo ^ " .. " ^ expr_str hi
  | A.TMod e => "mod " ^ expr_str e
  | A.TDigits (e, r) => "digits " ^ expr_str e ^ opt range_str r
  | A.TDelta (e, r) => "delta " ^ expr_str e ^ opt range_str r
  | A.TArray (idxs, al, s) => array_str (idxs, al, s)
  | A.TRecord (ab, tg, lim, rd) =>
      flags_str (ab, tg, lim) ^
      (case rd of
         A.RecNull => "null record"
       | _ => "record\n" ^ recdef_body (n + 1) rd ^ ind_str n ^ "end record")
  | A.TDerived (ab, lim, s, ext) =>
      (if ab then "abstract " else "") ^ (if lim then "limited " else "") ^
      "new " ^ sub_str s ^
      (case ext of
         A.ExtNone => ""
       | A.ExtPrivate => " with private"
       | A.ExtRecord A.RecNull => " with null record"
       | A.ExtRecord rd =>
           " with record\n" ^ recdef_body (n + 1) rd ^ ind_str n ^
           "end record")
  | A.TPrivate (ab, tg, lim) => flags_str (ab, tg, lim) ^ "private"
  | A.TAccess (nn, k, s) =>
      (if nn then "not null " else "") ^ "access " ^
      (case k of
         A.AccPlain => "" | A.AccAll => "all " | A.AccConstant => "constant ")
      ^ sub_str s)

fun scheme_str sc = (case sc of
    A.LoopPlain => ""
  | A.LoopWhile e => "while " ^ expr_str e ^ " "
  | A.LoopFor (id, it) => "for " ^ ident_str id ^ iter_str it ^ " ")

fun pragma_str id args =
  "pragma " ^ ident_str id ^
  (if null args then "" else " (" ^ commas (map assoc_str args) ^ ")") ^ ";"

fun stmts_str n stmts =
  implode (map (fn s => ind_str n ^ stmt_str n s ^ "\n") stmts)

and stmt_str n s = (case s of
    A.SNull _ => "null;"
  | A.SAssign (l, r, _) => expr_str l ^ " := " ^ expr_str r ^ ";"
  | A.SCall (e, _) => expr_str e ^ ";"
  | A.SIf (branches, els, _) =>
      (case branches of
         [] => ""
       | (c, t) :: rest =>
           "if " ^ expr_str c ^ " then\n" ^ stmts_str (n + 1) t ^
           implode (map (fn (c1, t1) =>
                           ind_str n ^ "elsif " ^ expr_str c1 ^ " then\n" ^
                           stmts_str (n + 1) t1) rest) ^
           (case els of
              NONE => ""
            | SOME e => ind_str n ^ "else\n" ^ stmts_str (n + 1) e) ^
           ind_str n ^ "end if;")
  | A.SCase (e, alts, _) =>
      "case " ^ expr_str e ^ " is\n" ^
      implode (map (fn (chs, b) =>
                      ind_str (n + 1) ^ "when " ^ choices_str chs ^ " =>\n" ^
                      stmts_str (n + 2) b) alts) ^
      ind_str n ^ "end case;"
  | A.SLoop (lbl, sc, body, _) =>
      opt (fn l => ident_str l ^ " : ") lbl ^ scheme_str sc ^ "loop\n" ^
      stmts_str (n + 1) body ^ ind_str n ^ "end loop" ^
      opt (fn l => " " ^ ident_str l) lbl ^ ";"
  | A.SBlock (lbl, decls, body, hs, _) =>
      opt (fn l => ident_str l ^ " : ") lbl ^
      (if null decls then ""
       else "declare\n" ^ decls_str (n + 1) decls ^ ind_str n) ^
      "begin\n" ^ stmts_str (n + 1) body ^ handlers_str n hs ^ ind_str n ^
      "end" ^ opt (fn l => " " ^ ident_str l) lbl ^ ";"
  | A.SExit (l, c, _) =>
      "exit" ^ opt (fn e => " " ^ expr_str e) l ^
      opt (fn e => " when " ^ expr_str e) c ^ ";"
  | A.SReturn (e, _) => "return" ^ opt (fn e1 => " " ^ expr_str e1) e ^ ";"
  | A.SRaise (e, m, _) =>
      "raise" ^ opt (fn e1 => " " ^ expr_str e1) e ^
      opt (fn m1 => " with " ^ expr_str m1) m ^ ";"
  | A.SPragma (id, args, _) => pragma_str id args)

and handlers_str n hs =
  if null hs then ""
  else ind_str n ^ "exception\n" ^
       implode (map (fn A.Handler (chs, b, _) =>
                       ind_str (n + 1) ^ "when " ^ choices_str chs ^
                       " =>\n" ^ stmts_str (n + 2) b) hs)

and decls_str n decls =
  implode (map (fn d => ind_str n ^ decl_str n d ^ "\n") decls)

and decl_str n d = (case d of
    A.DObject (ids, al, cst, od, init, asps, _) =>
      commas (map ident_str ids) ^ " : " ^ (if al then "aliased " else "") ^
      (if cst then "constant " else "") ^
      (case od of
         A.OSub s => sub_str s
       | A.OArray (idxs, al1, s) => array_str (idxs, al1, s)) ^
      opt (fn e => " := " ^ expr_str e) init ^ aspects_str asps ^ ";"
  | A.DNumber (ids, e, _) =>
      commas (map ident_str ids) ^ " : constant := " ^ expr_str e ^ ";"
  | A.DException (ids, _) => commas (map ident_str ids) ^ " : exception;"
  | A.DType (id, discs, td, asps, _) =>
      "type " ^ ident_str id ^ params_str discs ^ " is " ^
      typedef_str n td ^ aspects_str asps ^ ";"
  | A.DIncomplete (id, _) => "type " ^ ident_str id ^ ";"
  | A.DSubtype (id, s, asps, _) =>
      "subtype " ^ ident_str id ^ " is " ^ sub_str s ^ aspects_str asps ^ ";"
  | A.DSpec (sp, ab, asps, _) =>
      spec_str sp ^ (if ab then " is abstract" else "") ^ aspects_ln n asps ^
      ";"
  | A.DNullProc (sp, asps, _) =>
      spec_str sp ^ " is null" ^ aspects_ln n asps ^ ";"
  | A.DExprFun (sp, e, asps, _) =>
      spec_str sp ^ " is (" ^ expr_str e ^ ")" ^ aspects_ln n asps ^ ";"
  | A.DBody (sp as A.Spec (_, _, name, _, _, _), asps, decls, body, hs, _) =>
      spec_str sp ^ aspects_ln n asps ^ is_str n asps ^
      decls_str (n + 1) decls ^ ind_str n ^ "begin\n" ^
      stmts_str (n + 1) body ^ handlers_str n hs ^ ind_str n ^ "end " ^
      ident_str name ^ ";"
  | A.DPackage (name, asps, vis, priv, _) =>
      "package " ^ expr_str name ^ aspects_ln n asps ^ is_str n asps ^
      decls_str (n + 1) vis ^
      (if null priv then ""
       else ind_str n ^ "private\n" ^ decls_str (n + 1) priv) ^
      ind_str n ^ "end " ^ expr_str name ^ ";"
  | A.DPackageBody (name, asps, decls, init, _) =>
      "package body " ^ expr_str name ^ aspects_ln n asps ^ is_str n asps ^
      decls_str (n + 1) decls ^
      (case init of
         NONE => ""
       | SOME (stmts, hs) =>
           ind_str n ^ "begin\n" ^ stmts_str (n + 1) stmts ^
           handlers_str n hs) ^
      ind_str n ^ "end " ^ expr_str name ^ ";"
  | A.DUse (ty, names, _) =>
      "use " ^ (if ty then "type " else "") ^ commas (map expr_str names) ^ ";"
  | A.DPragma (id, args, _) => pragma_str id args
  | A.DAttrDef (a, v, _) => "for " ^ expr_str a ^ " use " ^ expr_str v ^ ";")

fun clause_str c = (case c of
    A.CWith (lim, priv, names, _) =>
      (if lim then "limited " else "") ^ (if priv then "private " else "") ^
      "with " ^ commas (map expr_str names) ^ ";"
  | A.CUse (ty, names, _) =>
      "use " ^ (if ty then "type " else "") ^ commas (map expr_str names) ^
      ";")

fun unit_str (A.Unit (clauses, d, _)) =
  implode (map (fn c => clause_str c ^ "\n") clauses) ^ decl_str 0 d

fun trim_nl s =
  if String.isSuffix "\n" s then String.substring (s, 0, size s - 1) else s

fun pp_root r = (case r of
    A.Id id => ident_str id
  | A.Expr e => expr_str e
  | A.Type s => sub_str s
  | A.Stmt s => stmt_str 0 s
  | A.Decl d => decl_str 0 d
  | A.Body stmts => trim_nl (stmts_str 0 stmts)
  | A.Crate units => space_implode "\n\n" (map unit_str units))

end
