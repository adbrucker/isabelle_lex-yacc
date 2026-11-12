(* Printing a Go AST back as Go text: the layout of gofmt in its essentials (a tab per level of
   indentation, one statement or declaration per line, "case" at the indentation of its "switch",
   a blank line between top-level declarations). Every explicit parenthesis of the source is kept
   in the AST ("EParen"), so no precedence reasoning is needed here; binary operators are always
   surrounded by blanks. Comments and antiquotations are not printed (they live in the nodeInfo),
   as in the other front-ends. *)

structure Go_Pp = struct

structure A = Go_Ast

fun commas xs = space_implode ", " xs
fun opt f x = (case x of NONE => "" | SOME y => f y)

fun ind n = replicate_string n "\t"

fun ident_str (A.Ident (s, _, _)) = s

fun binop_str b = (case b of
    A.LOr => "||" | A.LAnd => "&&" | A.Eq => "==" | A.Ne => "!=" | A.Lt => "<" | A.Le => "<="
  | A.Gt => ">" | A.Ge => ">=" | A.Add => "+" | A.Sub => "-" | A.Or => "|" | A.Xor => "^"
  | A.Mul => "*" | A.Div => "/" | A.Rem => "%" | A.Shl => "<<" | A.Shr => ">>" | A.And => "&"
  | A.AndNot => "&^")

fun unop_str u = (case u of
    A.UPlus => "+" | A.UMinus => "-" | A.Not => "!" | A.UXor => "^" | A.UAnd => "&"
  | A.URecv => "<-")

fun expr_str n e = (case e of
    A.EIdent id => ident_str id
  | A.EInt (s, _) => s
  | A.EFloat (s, _) => s
  | A.EImag (s, _) => s
  | A.ERune (s, _) => s
  | A.EString (s, _) => s
  | A.EParen (e1, _) => "(" ^ expr_str n e1 ^ ")"
  | A.ESelector (e1, id, _) => expr_str n e1 ^ "." ^ ident_str id
  | A.EIndex (e1, args, _) => expr_str n e1 ^ "[" ^ exprs_str n args ^ "]"
  | A.ESlice (e1, lo, hi, mx, _) =>
      expr_str n e1 ^ "[" ^ opt (expr_str n) lo ^ ":" ^ opt (expr_str n) hi
      ^ opt (fn m => ":" ^ expr_str n m) mx ^ "]"
  | A.ETypeAssert (e1, t, _) =>
      expr_str n e1 ^ ".(" ^ (case t of SOME t1 => expr_str n t1 | NONE => "type") ^ ")"
  | A.ECall (f, args, ell, _) =>
      expr_str n f ^ "(" ^ exprs_str n args ^ (if ell then "..." else "") ^ ")"
  | A.EStar (e1, _) => "*" ^ expr_str n e1
  | A.EUnary (u, e1, _) => unop_str u ^ expr_str n e1
  | A.EBinary (b, e1, e2, _) => expr_str n e1 ^ " " ^ binop_str b ^ " " ^ expr_str n e2
  | A.ECompLit (t, elems, _) =>
      opt (expr_str n) t ^ "{" ^ commas (map (element_str n) elems) ^ "}"
  | A.EFuncLit (sg, body, _) => "func" ^ sig_str n sg ^ " " ^ block_str n body
  | A.EArrayType (len, elem, _) =>
      "[" ^ opt (expr_str n) len ^ "]" ^ expr_str n elem
  | A.EEllipsisArray (elem, _) => "[...]" ^ expr_str n elem
  | A.EMapType (k, v, _) => "map[" ^ expr_str n k ^ "]" ^ expr_str n v
  | A.EChanType (d, t, _) =>
      (case d of A.Both => "chan " | A.SendOnly => "chan<- " | A.RecvOnly => "<-chan ")
      ^ expr_str n t
  | A.EFuncType (sg, _) => "func" ^ sig_str n sg
  | A.EStructType ([], _) => "struct{}"
  | A.EStructType (fields, _) =>
      "struct {\n" ^ implode (map (fn f => ind (n + 1) ^ field_str (n + 1) f ^ "\n") fields)
      ^ ind n ^ "}"
  | A.EInterfaceType ([], _) => "interface{}"
  | A.EInterfaceType (elems, _) =>
      "interface {\n" ^ implode (map (fn i => ind (n + 1) ^ ielem_str (n + 1) i ^ "\n") elems)
      ^ ind n ^ "}"
  | A.ETilde (e1, _) => "~" ^ expr_str n e1
  | A.EUnion (es, _) => space_implode " | " (map (expr_str n) es))

and exprs_str n es = commas (map (expr_str n) es)

and element_str n (A.Element (k, v, _)) = opt (fn k1 => expr_str n k1 ^ ": ") k ^ expr_str n v

and param_str n (A.Param (names, t, variadic, _)) =
  (if null names then "" else commas (map ident_str names) ^ " ")
  ^ (if variadic then "..." else "") ^ expr_str n t

and params_str n ps = "(" ^ commas (map (param_str n) ps) ^ ")"

and sig_str n (A.Sig (ps, rs, _)) =
  params_str n ps ^
  (case rs of
     [] => ""
   | [A.Param ([], t, false, _)] => " " ^ expr_str n t
   | _ => " " ^ params_str n rs)

and field_str n (A.Field (names, t, tag, _)) =
  (if null names then "" else commas (map ident_str names) ^ " ") ^ expr_str n t
  ^ opt (fn s => " " ^ s) tag

and ielem_str n i = (case i of
    A.IMethod (id, sg, _) => ident_str id ^ sig_str n sg
  | A.IType (e, _) => expr_str n e)

and block_str n (A.Block (stmts, _)) = "{\n" ^ stmts_str (n + 1) stmts ^ ind n ^ "}"

and stmts_str n stmts = implode (map (fn s => ind n ^ stmt_str n s ^ "\n") stmts)

and simple_str n s = stmt_str n s

and stmt_str n s = (case s of
    A.SEmpty _ => ""
  | A.SExpr (e, _) => expr_str n e
  | A.SSend (c, v, _) => expr_str n c ^ " <- " ^ expr_str n v
  | A.SIncDec (e, inc, _) => expr_str n e ^ (if inc then "++" else "--")
  | A.SAssign (lhs, op1, rhs, _) =>
      exprs_str n lhs ^ " " ^ opt binop_str op1 ^ "= " ^ exprs_str n rhs
  | A.SShortVar (lhs, rhs, _) => exprs_str n lhs ^ " := " ^ exprs_str n rhs
  | A.SDecl d => decl_str n d
  | A.SLabeled (l, A.SEmpty _, _) => ident_str l ^ ":;"
  | A.SLabeled (l, s1, _) => ident_str l ^ ":\n" ^ ind n ^ stmt_str n s1
  | A.SGo (e, _) => "go " ^ expr_str n e
  | A.SDefer (e, _) => "defer " ^ expr_str n e
  | A.SReturn (es, _) => "return" ^ (if null es then "" else " " ^ exprs_str n es)
  | A.SBreak (l, _) => "break" ^ opt (fn l1 => " " ^ ident_str l1) l
  | A.SContinue (l, _) => "continue" ^ opt (fn l1 => " " ^ ident_str l1) l
  | A.SGoto (l, _) => "goto " ^ ident_str l
  | A.SFallthrough _ => "fallthrough"
  | A.SBlock b => block_str n b
  | A.SIf (init, c, thn, els, _) =>
      "if " ^ opt (fn i => simple_str n i ^ "; ") init ^ expr_str n c ^ " " ^ block_str n thn
      ^ opt (fn e1 => " else " ^ stmt_str n e1) els
  | A.SSwitch (init, tag, cases, _) =>
      "switch " ^ opt (fn i => simple_str n i ^ "; ") init ^ opt (fn t => expr_str n t ^ " ") tag
      ^ "{\n" ^ implode (map (case_str n) cases) ^ ind n ^ "}"
  | A.STypeSwitch (init, bind, e, cases, _) =>
      "switch " ^ opt (fn i => simple_str n i ^ "; ") init
      ^ opt (fn b => ident_str b ^ " := ") bind ^ expr_str n e ^ ".(type) {\n"
      ^ implode (map (case_str n) cases) ^ ind n ^ "}"
  | A.SSelect (comms, _) =>
      "select {\n" ^ implode (map (comm_str n) comms) ^ ind n ^ "}"
  | A.SFor (init, c, post, body, _) =>
      (case (init, c, post) of
         (NONE, NONE, NONE) => "for " ^ block_str n body
       | (NONE, SOME c1, NONE) => "for " ^ expr_str n c1 ^ " " ^ block_str n body
       | _ => "for " ^ opt (simple_str n) init ^ "; " ^ opt (expr_str n) c ^ "; "
              ^ opt (simple_str n) post ^ " " ^ block_str n body)
  | A.SRange (k, v, def, e, body, _) =>
      "for " ^
      (case (k, v) of
         (NONE, NONE) => ""
       | (SOME k1, NONE) => expr_str n k1 ^ (if def then " := " else " = ")
       | (SOME k1, SOME v1) =>
           expr_str n k1 ^ ", " ^ expr_str n v1 ^ (if def then " := " else " = ")
       | (NONE, SOME v1) => "_, " ^ expr_str n v1 ^ (if def then " := " else " = "))
      ^ "range " ^ expr_str n e ^ " " ^ block_str n body)

and case_str n (A.Case (guards, stmts, _)) =
  ind n ^ (case guards of NONE => "default:" | SOME es => "case " ^ exprs_str n es ^ ":") ^ "\n"
  ^ stmts_str (n + 1) stmts

and comm_str n (A.Comm (g, stmts, _)) =
  ind n ^ (case g of NONE => "default:" | SOME s => "case " ^ simple_str n s ^ ":") ^ "\n"
  ^ stmts_str (n + 1) stmts

and tparams_str n tps =
  if null tps then ""
  else "[" ^ commas (map (fn A.TParam (names, c, _) =>
                            commas (map ident_str names) ^ " " ^ expr_str n c) tps) ^ "]"

and spec_str n kw spec = (case spec of
    A.ConstSpec (names, t, vals, _) =>
      commas (map ident_str names) ^ opt (fn t1 => " " ^ expr_str n t1) t
      ^ (if null vals then "" else " = " ^ exprs_str n vals)
  | A.VarSpec (names, t, vals, _) =>
      commas (map ident_str names) ^ opt (fn t1 => " " ^ expr_str n t1) t
      ^ (if null vals then "" else " = " ^ exprs_str n vals)
  | A.TypeSpec (name, tps, alias, t, _) =>
      ident_str name ^ tparams_str n tps ^ (if alias then " = " else " ") ^ expr_str n t
  | A.ImportSpec (name, path, _) => opt (fn id => ident_str id ^ " ") name ^ path)

and group_str n kw specs grouped =
  if grouped
  then kw ^ " (\n" ^ implode (map (fn s => ind (n + 1) ^ spec_str (n + 1) kw s ^ "\n") specs)
       ^ ind n ^ ")"
  else kw ^ " " ^ (case specs of [s] => spec_str n kw s | _ => "")

and decl_str n d = (case d of
    A.DConst (specs, grouped, _) => group_str n "const" specs grouped
  | A.DVar (specs, grouped, _) => group_str n "var" specs grouped
  | A.DType (specs, grouped, _) => group_str n "type" specs grouped
  | A.DImport (specs, grouped, _) => group_str n "import" specs grouped
  | A.DFunc (name, tps, sg, body, _) =>
      "func " ^ ident_str name ^ tparams_str n tps ^ sig_str n sg
      ^ opt (fn b => " " ^ block_str n b) body
  | A.DMethod (recv, name, tps, sg, body, _) =>
      "func " ^ params_str n recv ^ " " ^ ident_str name ^ tparams_str n tps ^ sig_str n sg
      ^ opt (fn b => " " ^ block_str n b) body)

fun file_str (A.File (pkg, decls, _)) =
  "package " ^ ident_str pkg ^ "\n"
  ^ implode (map (fn d => "\n" ^ decl_str 0 d ^ "\n") decls)

fun trim_nl s =
  if String.isSuffix "\n" s then String.substring (s, 0, size s - 1) else s

fun pp_root r = (case r of
    A.Id id => ident_str id
  | A.Expr e => expr_str 0 e
  | A.Stmts stmts => trim_nl (stmts_str 0 stmts)
  | A.Decls decls => space_implode "\n\n" (map (decl_str 0) decls)
  | A.Source f => trim_nl (file_str f)
  | A.Stmt s => stmt_str 0 s
  | A.Decl d => decl_str 0 d)

end
