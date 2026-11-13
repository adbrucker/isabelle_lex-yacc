(* Printing a Java AST back as Java text: four blanks per level of indentation, braces at the end of
   the line, one statement or member per line, a blank line between the members of a class. Every
   explicit parenthesis of the source is kept in the AST ("EParen"), so no precedence reasoning is
   needed here; binary operators are always surrounded by blanks. Comments and antiquotations are
   not printed (they live in the nodeInfo), as in the other front-ends. What is printed has the
   same tokens as what was parsed (the corpus test of Java_Tests.thy checks this), up to the
   splitting of ">>" in nested type arguments, which the parser undoes. *)

structure Java_Pp = struct

structure A = Java_Ast

fun commas xs = space_implode ", " xs
fun opt f x = (case x of NONE => "" | SOME y => f y)
fun ind n = replicate_string n "    "

fun ident_str (A.Ident (s, _, _)) = s
fun name_str ids = space_implode "." (map ident_str ids)

fun binop_str b = (case b of
    A.LOr => "||" | A.LAnd => "&&" | A.BOr => "|" | A.BXor => "^" | A.BAnd => "&" | A.Eq => "=="
  | A.Ne => "!=" | A.Lt => "<" | A.Gt => ">" | A.Le => "<=" | A.Ge => ">=" | A.Shl => "<<"
  | A.Shr => ">>" | A.UShr => ">>>" | A.Add => "+" | A.Sub => "-" | A.Mul => "*" | A.Div => "/"
  | A.Rem => "%")

fun lit_str l = (case l of
    A.LInt s => s | A.LFloat s => s | A.LChar s => s | A.LString s => s | A.LTextBlock s => s
  | A.LBool true => "true" | A.LBool false => "false" | A.LNull => "null")

(* a prefix operator must not fuse with the first character of its operand ("- -x", "+ ++x") *)
fun prefix_str op_s operand =
  if String.isPrefix (String.substring (op_s, 0, 1)) operand
     andalso (op_s = "-" orelse op_s = "+")
  then op_s ^ " " ^ operand else op_s ^ operand

fun annot_str n (A.Annot (name, args, _)) =
  "@" ^ name_str name
  ^ (case args of
       A.NoArgs => ""
     | A.Single v => "(" ^ elemval_str n v ^ ")"
     | A.Pairs ps =>
         "(" ^ commas (map (fn (id, v) => ident_str id ^ " = " ^ elemval_str n v) ps) ^ ")")

and elemval_str n v = (case v of
    A.EVExpr e => expr_str n e
  | A.EVArray (vs, trail, _) =>
      "{" ^ commas (map (elemval_str n) vs) ^ (if trail then "," else "") ^ "}"
  | A.EVAnnot a => annot_str n a)

and annots_str n al = String.concat (map (fn a => annot_str n a ^ " ") al)

and dim_str n (A.Dim (al, _)) = (if null al then "" else " " ^ annots_str n al) ^ "[]"
and dims_str n ds = String.concat (map (dim_str n) ds)

and type_str n t = (case t of
    A.TPrim (al, s, _) => annots_str n al ^ s
  | A.TClass (al, segs, _) => annots_str n al ^ space_implode "." (map (tseg_str n) segs)
  | A.TArray (e, ds, _) => type_str n e ^ dims_str n ds
  | A.TVar _ => "var")

and tseg_str n (A.TSeg (id, args)) = ident_str id ^ opt (targs_str n) args

and targs_str n (A.TArgs (args, _)) = "<" ^ commas (map (targ_str n) args) ^ ">"

and targ_str n a = (case a of
    A.TAType t => type_str n t
  | A.TAWild (al, b, _) =>
      annots_str n al ^ "?"
      ^ (case b of NONE => "" | SOME (true, t) => " extends " ^ type_str n t
                 | SOME (false, t) => " super " ^ type_str n t))

and tparam_str n (A.TParam (al, id, bounds, _)) =
  annots_str n al ^ ident_str id
  ^ (if null bounds then "" else " extends " ^ space_implode " & " (map (type_str n) bounds))

and tparams_str n tps = if null tps then "" else "<" ^ commas (map (tparam_str n) tps) ^ ">"

and mod_str n m = (case m of
    A.MKw (s, _) => s
  | A.MAnnot a => annot_str n a)

and mods_str n ms = String.concat (map (fn m => mod_str n m ^ " ") ms)

and expr_str n e = (case e of
    A.ELit (l, _) => lit_str l
  | A.EName id => ident_str id
  | A.EField (e1, id, _) => expr_str n e1 ^ "." ^ ident_str id
  | A.EThis _ => "this"
  | A.ESuper _ => "super"
  | A.EQualThis (e1, _) => expr_str n e1 ^ ".this"
  | A.EQualSuper (e1, _) => expr_str n e1 ^ ".super"
  | A.EParen (e1, _) => "(" ^ expr_str n e1 ^ ")"
  | A.EIndex (e1, i, _) => expr_str n e1 ^ "[" ^ expr_str n i ^ "]"
  | A.ECall (recv, targs, id, args, _) =>
      opt (fn r => expr_str n r ^ ".") recv ^ opt (targs_str n) targs ^ ident_str id
      ^ "(" ^ exprs_str n args ^ ")"
  | A.ENew (outer, t, args, body, _) =>
      opt (fn o1 => expr_str n o1 ^ ".") outer ^ "new " ^ type_str n t
      ^ "(" ^ exprs_str n args ^ ")"
      ^ opt (fn ms => " " ^ body_str n ms) body
  | A.ENewArray (t, dimexprs, dims, init, _) =>
      "new " ^ type_str n t
      ^ String.concat (map (fn d => "[" ^ expr_str n d ^ "]") dimexprs)
      ^ dims_str n dims ^ opt (fn i => " " ^ expr_str n i) init
  | A.EArrayInit (es, trail, _) =>
      "{" ^ exprs_str n es ^ (if trail then "," else "") ^ "}"
  | A.EClassLit (t, _) => type_str n t ^ ".class"
  | A.EMethodRef (tg, targs, id, _) =>
      (case tg of A.MRExpr e1 => expr_str n e1 | A.MRType t => type_str n t)
      ^ "::" ^ opt (targs_str n) targs ^ ident_str id
  | A.ELambda (ps, parens, body, _) =>
      (case (ps, parens) of
         ([A.LPInfer id], false) => ident_str id
       | _ => "(" ^ commas (map (lparam_str n) ps) ^ ")")
      ^ " -> "
      ^ (case body of A.LBExpr e1 => expr_str n e1 | A.LBBlock b => block_str n b)
  | A.EUnary (u, e1, _) =>
      (case u of
         A.UPlus => prefix_str "+" (expr_str n e1) | A.UMinus => prefix_str "-" (expr_str n e1)
       | A.UNot => "!" ^ expr_str n e1 | A.UCompl => "~" ^ expr_str n e1
       | A.PreInc => "++" ^ expr_str n e1
       | A.PreDec => "--" ^ expr_str n e1
       | A.PostInc => expr_str n e1 ^ "++" | A.PostDec => expr_str n e1 ^ "--")
  | A.EBinary (b, e1, e2, _) => expr_str n e1 ^ " " ^ binop_str b ^ " " ^ expr_str n e2
  | A.EAssign (l, b, r, _) =>
      expr_str n l ^ " " ^ (case b of NONE => "" | SOME b1 => binop_str b1) ^ "= " ^ expr_str n r
  | A.ECond (c, t, f, _) => expr_str n c ^ " ? " ^ expr_str n t ^ " : " ^ expr_str n f
  | A.ECast (ts, e1, _) => "(" ^ space_implode " & " (map (type_str n) ts) ^ ") " ^ expr_str n e1
  | A.EInstanceof (e1, p, _) => expr_str n e1 ^ " instanceof " ^ pattern_str n p
  | A.ESwitch (e1, cases, _) => switch_str n e1 cases)

and exprs_str n es = commas (map (expr_str n) es)

and lparam_str n p = (case p of
    A.LPInfer id => ident_str id
  | A.LPTyped pr => param_str n pr)

and param_str n (A.Param (ms, t, va, id, ds, _)) =
  mods_str n ms ^ type_str n t ^ (if va then "..." else "") ^ " " ^ ident_str id ^ dims_str n ds

and pattern_str n p = (case p of
    A.PType (ms, t, id, _) => mods_str n ms ^ type_str n t ^ opt (fn i => " " ^ ident_str i) id
  | A.PRecord (t, ps, _) => type_str n t ^ "(" ^ commas (map (pattern_str n) ps) ^ ")"
  | A.PAny _ => "_")

and label_str n l = (case l of
    A.LDefault _ => "default"
  | A.LCase (items, guard, _) =>
      "case " ^ commas (map (fn A.CIExpr e => expr_str n e | A.CIPattern p => pattern_str n p
                              | A.CIDefault => "default") items)
      ^ opt (fn g => " when " ^ expr_str n g) guard)

and switch_str n e cases =
  "switch (" ^ expr_str n e ^ ") {\n" ^ String.concat (map (swcase_str (n + 1)) cases)
  ^ ind n ^ "}"

and swcase_str n c = (case c of
    A.SwRule (l, body, _) =>
      ind n ^ label_str n l ^ " -> "
      ^ (case body of
           A.RBExpr e => expr_str n e ^ ";"
         | A.RBBlock b => block_str n b
         | A.RBThrow s => stmt_str n s) ^ "\n"
  | A.SwGroup (labels, stmts, _) =>
      String.concat (map (fn l => ind n ^ label_str n l ^ ":\n") labels)
      ^ String.concat (map (fn s => ind (n + 1) ^ stmt_str (n + 1) s ^ "\n") stmts))

and block_str n (A.Block (stmts, _)) =
  if null stmts then "{}"
  else "{\n" ^ String.concat (map (fn s => ind (n + 1) ^ stmt_str (n + 1) s ^ "\n") stmts)
       ^ ind n ^ "}"

and vardecl_str n (A.VarDecl (id, ds, init, _)) =
  ident_str id ^ dims_str n ds ^ opt (fn e => " = " ^ expr_str n e) init

and localvar_str n (A.LocalVar (ms, t, vds, _)) =
  mods_str n ms ^ type_str n t ^ " " ^ commas (map (vardecl_str n) vds)

(* a statement as the body of a compound statement: a block stays on the line, anything else
   goes on the next one *)
and sub_str n s = (case s of
    A.SBlock b => " " ^ block_str n b
  | _ => "\n" ^ ind (n + 1) ^ stmt_str (n + 1) s)

and stmt_str n s = (case s of
    A.SBlock b => block_str n b
  | A.SLocal lv => localvar_str n lv ^ ";"
  | A.SClassDecl d => decl_str n d
  | A.SEmpty _ => ";"
  | A.SExpr (e, _) => expr_str n e ^ ";"
  | A.SLabeled (id, s1, _) => ident_str id ^ ": " ^ stmt_str n s1
  | A.SIf (c, t, e, _) =>
      "if (" ^ expr_str n c ^ ")" ^ sub_str n t
      ^ (case e of
           NONE => ""
         | SOME e1 =>
             (case t of A.SBlock _ => " else" | _ => "\n" ^ ind n ^ "else")
             ^ (case e1 of A.SIf _ => " " ^ stmt_str n e1 | _ => sub_str n e1))
  | A.SWhile (c, b, _) => "while (" ^ expr_str n c ^ ")" ^ sub_str n b
  | A.SDo (b, c, _) =>
      "do" ^ sub_str n b ^ (case b of A.SBlock _ => " " | _ => "\n" ^ ind n)
      ^ "while (" ^ expr_str n c ^ ");"
  | A.SFor (init, c, upd, b, _) =>
      "for (" ^ (case init of
                   NONE => ""
                 | SOME (A.FIVars lv) => localvar_str n lv
                 | SOME (A.FIExprs es) => exprs_str n es)
      ^ ";" ^ opt (fn e => " " ^ expr_str n e) c ^ ";"
      ^ (if null upd then "" else " " ^ exprs_str n upd) ^ ")" ^ sub_str n b
  | A.SForEach (ms, t, id, e, b, _) =>
      "for (" ^ mods_str n ms ^ type_str n t ^ " " ^ ident_str id ^ " : " ^ expr_str n e ^ ")"
      ^ sub_str n b
  | A.SBreak (l, _) => "break" ^ opt (fn i => " " ^ ident_str i) l ^ ";"
  | A.SContinue (l, _) => "continue" ^ opt (fn i => " " ^ ident_str i) l ^ ";"
  | A.SReturn (e, _) => "return" ^ opt (fn e1 => " " ^ expr_str n e1) e ^ ";"
  | A.SThrow (e, _) => "throw " ^ expr_str n e ^ ";"
  | A.SYield (e, _) => "yield " ^ expr_str n e ^ ";"
  | A.SAssert (c, m, _) =>
      "assert " ^ expr_str n c ^ opt (fn e => " : " ^ expr_str n e) m ^ ";"
  | A.SSync (e, b, _) => "synchronized (" ^ expr_str n e ^ ") " ^ block_str n b
  | A.STry (res, semi, b, catches, fin, _) =>
      "try"
      ^ (if null res then ""
         else " (" ^ space_implode "; " (map (fn A.RDecl lv => localvar_str n lv
                                              | A.RExpr e => expr_str n e) res)
                    ^ (if semi then ";" else "") ^ ")")
      ^ " " ^ block_str n b
      ^ String.concat (map (catch_str n) catches)
      ^ opt (fn fb => " finally " ^ block_str n fb) fin
  | A.SSwitch (e, cases, _) => switch_str n e cases
  | A.SCtorCall (q, targs, is_super, args, _) =>
      opt (fn q1 => expr_str n q1 ^ ".") q ^ opt (targs_str n) targs
      ^ (if is_super then "super" else "this") ^ "(" ^ exprs_str n args ^ ");")

and catch_str n (A.Catch (ms, ts, id, b, _)) =
  " catch (" ^ mods_str n ms ^ space_implode " | " (map (type_str n) ts) ^ " " ^ ident_str id
  ^ ") " ^ block_str n b

and body_str n ms =
  if null ms then "{}"
  else "{\n" ^ space_implode "\n" (map (fn d => ind (n + 1) ^ decl_str (n + 1) d) ms) ^ "\n"
       ^ ind n ^ "}"

and extends_str n kw ts =
  if null ts then "" else " " ^ kw ^ " " ^ commas (map (type_str n) ts)

and decl_str n d = (case d of
    A.DClass (ms, id, tps, ext, impl, perm, body, _) =>
      mods_str n ms ^ "class " ^ ident_str id ^ tparams_str n tps
      ^ extends_str n "extends" (case ext of NONE => [] | SOME t => [t])
      ^ extends_str n "implements" impl ^ extends_str n "permits" perm ^ " " ^ body_str n body
  | A.DInterface (ms, id, tps, ext, perm, body, _) =>
      mods_str n ms ^ "interface " ^ ident_str id ^ tparams_str n tps
      ^ extends_str n "extends" ext ^ extends_str n "permits" perm ^ " " ^ body_str n body
  | A.DEnum (ms, id, impl, consts, (comma, semi), body, _) =>
      mods_str n ms ^ "enum " ^ ident_str id ^ extends_str n "implements" impl ^ " {\n"
      ^ space_implode ",\n" (map (fn c => ind (n + 1) ^ enumconst_str (n + 1) c) consts)
      ^ (if comma then "," else "")
      ^ (if semi orelse not (null body) then ";" else "") ^ "\n"
      ^ space_implode "\n" (map (fn m => ind (n + 1) ^ decl_str (n + 1) m) body)
      ^ (if null body then "" else "\n") ^ ind n ^ "}"
  | A.DRecord (ms, id, tps, comps, impl, body, _) =>
      mods_str n ms ^ "record " ^ ident_str id ^ tparams_str n tps
      ^ "(" ^ commas (map (param_str n) comps) ^ ")" ^ extends_str n "implements" impl
      ^ " " ^ body_str n body
  | A.DAnnotType (ms, id, body, _) =>
      mods_str n ms ^ "@interface " ^ ident_str id ^ " " ^ body_str n body
  | A.DField (ms, t, vds, _) =>
      mods_str n ms ^ type_str n t ^ " " ^ commas (map (vardecl_str n) vds) ^ ";"
  | A.DMethod (ms, tps, res, id, ps, ds, thr, body, dflt, _) =>
      mods_str n ms ^ (if null tps then "" else tparams_str n tps ^ " ") ^ type_str n res ^ " "
      ^ ident_str id ^ "(" ^ commas (map (param_str n) ps) ^ ")" ^ dims_str n ds
      ^ extends_str n "throws" thr
      ^ opt (fn v => " default " ^ elemval_str n v) dflt
      ^ (case body of NONE => ";" | SOME b => " " ^ block_str n b)
  | A.DCtor (ms, tps, id, ps, thr, b, _) =>
      mods_str n ms ^ (if null tps then "" else tparams_str n tps ^ " ") ^ ident_str id
      ^ "(" ^ commas (map (param_str n) ps) ^ ")" ^ extends_str n "throws" thr ^ " "
      ^ block_str n b
  | A.DCompact (ms, id, b, _) => mods_str n ms ^ ident_str id ^ " " ^ block_str n b
  | A.DInit (st, b, _) => (if st then "static " else "") ^ block_str n b
  | A.DEmpty _ => ";")

and enumconst_str n (A.EnumConst (al, id, args, body, _)) =
  annots_str n al ^ ident_str id ^ opt (fn a => "(" ^ exprs_str n a ^ ")") args
  ^ opt (fn ms => " " ^ body_str n ms) body

fun import_str (A.Import (k, name, _)) =
  "import "
  ^ (case k of
       A.ImSingle => name_str name ^ ";"
     | A.ImDemand => name_str name ^ ".*;"
     | A.ImStaticSingle => "static " ^ name_str name ^ ";"
     | A.ImStaticDemand => "static " ^ name_str name ^ ".*;"
     | A.ImModule => "module " ^ name_str name ^ ";")

fun modnames_str ns = commas (map name_str ns)

fun moddir_str d = (case d of
    A.Requires (ms, name, _) => "requires " ^ String.concat (map (fn m => m ^ " ") ms)
                                ^ name_str name ^ ";"
  | A.Exports (p, tos, _) =>
      "exports " ^ name_str p ^ (if null tos then "" else " to " ^ modnames_str tos) ^ ";"
  | A.Opens (p, tos, _) =>
      "opens " ^ name_str p ^ (if null tos then "" else " to " ^ modnames_str tos) ^ ";"
  | A.Uses (t, _) => "uses " ^ name_str t ^ ";"
  | A.Provides (t, impls, _) => "provides " ^ name_str t ^ " with " ^ modnames_str impls ^ ";")

fun unit_str (A.Unit (pkg, imports, body, _)) =
  opt (fn (al, name) => annots_str 0 al ^ "package " ^ name_str name ^ ";\n\n") pkg
  ^ (if null imports then "" else space_implode "\n" (map import_str imports) ^ "\n\n")
  ^ (case body of
       A.Types ds => space_implode "\n\n" (map (decl_str 0) ds)
     | A.Module (al, is_open, name, dirs, _) =>
         annots_str 0 al ^ (if is_open then "open " else "") ^ "module " ^ name_str name ^ " {\n"
         ^ String.concat (map (fn d => ind 1 ^ moddir_str d ^ "\n") dirs) ^ "}")

fun pp_root r = (case r of
    A.Id id => ident_str id
  | A.Expr e => expr_str 0 e
  | A.Type t => type_str 0 t
  | A.Stmt s => stmt_str 0 s
  | A.Stmts ss => space_implode "\n" (map (stmt_str 0) ss)
  | A.Decl d => decl_str 0 d
  | A.Decls ds => space_implode "\n\n" (map (decl_str 0) ds)
  | A.Source u => unit_str u ^ "\n")

end
