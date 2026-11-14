(* Printing a MicroRust AST back as Rust text: canonical layout (4-space
   indentation, one statement per line, braces always). Every explicit
   parenthesis of the source is kept in the AST ("EParen", "PTuple", ...), so no
   precedence reasoning is needed here. Comments and antiquotations are not
   printed (they live in the nodeInfo), as in the other front-ends. *)

structure MicroRust_Pp = struct

structure A = MicroRust_Ast

fun commas xs = space_implode ", " xs
fun opt f x = (case x of NONE => "" | SOME y => f y)

fun ind_str n = replicate_string (4 * n) " "

fun unop_str u = (case u of
    A.Neg => "-" | A.Not => "!" | A.Deref => "*" | A.Borrow =>
      "&" | A.BorrowMut => "&mut "
  | A.BorrowBorrow => "&&" | A.BorrowBorrowMut => "&&mut ")

fun binop_str b = (case b of
    A.Add => "+" | A.Sub => "-" | A.Mul => "*" | A.Div => "/" | A.Rem =>
      "%" | A.BitAnd => "&"
  | A.BitOr => "|" | A.BitXor => "^" | A.Shl => "<<" | A.Shr => ">>" | A.And =>
    "&&" | A.Or => "||"
  | A.Eq => "==" | A.Ne => "!=" | A.Lt => "<" | A.Le => "<=" | A.Gt =>
    ">" | A.Ge => ">=")

fun assign_str NONE = "=" | assign_str (SOME b) = binop_str b ^ "="

fun ident_str (A.Ident (s, _, _)) = s

fun hol_str (text, subs) = "\092<llangle>" ^ text ^ "\092<rrangle>" ^ subs

fun attr_str (A.Attr (inner, text, _)) = (if inner then "#![" else "#[") ^ text
  ^ "]"
fun attrs_str n attrs =
  implode (map (fn a => attr_str a ^ "\n" ^ ind_str n) attrs)
fun attrs_inline attrs = implode (map (fn a => attr_str a ^ " ") attrs)

fun vis_str A.VPriv = ""
  | vis_str (A.VPub "") = "pub "
  | vis_str (A.VPub s) = "pub(" ^ s ^ ") "

fun lit_str l = (case l of
    A.LInt (s, _) => s | A.LFloat (s, _) => s | A.LChar (s, _) =>
      s | A.LStr (s, _) => s
  | A.LBool (b, _) => if b then "true" else "false")

fun is_block_like e = (case e of
    A.EBlock _ => true | A.EUnsafe _ => true | A.EIf _ => true | A.EWhile _ =>
      true
  | A.ELoop _ => true | A.EFor _ => true | A.EMatch _ => true
  | A.EAttr (_, e1, _) => is_block_like e1
  | _ => false)

fun path_str (A.Path (qself, global, segs, _)) =
  let
    val q = (case qself of
               NONE => ""
             | SOME (t, NONE) => "<" ^ type_str t ^ ">::"
             | SOME (t, SOME tr) =>
               "<" ^ type_str t ^ " as " ^ path_str tr ^ ">::")
    val g = if global then "::" else ""
  in q ^ g ^ space_implode "::" (map seg_str segs) end

and seg_str (A.Seg (id, ga, _)) = ident_str id ^ opt gargs_str ga

and gargs_str (A.GArgs (turbo, args)) = (if turbo then "::<" else "<")
  ^ commas (map garg_str args) ^ ">"

and garg_str g = (case g of
    A.GType t => type_str t
  | A.GLifetime (s, _) => s
  | A.GConst e =>
    (case e of A.ELit _ => expr_str 0 e | _ => "{ " ^ expr_str 0 e ^ " }")
  | A.GBind (id, t) => ident_str id ^ " = " ^ type_str t)

and bound_str b = (case b of
    A.BTrait (q, p, _) => (if q then "?" else "") ^ path_str p
  | A.BLifetime (s, _) => s)

and bounds_str bs = space_implode " + " (map bound_str bs)

and type_str t = (case t of
    A.TPath p => path_str p
  | A.TRef (lt, m, t1, _) =>
    "&" ^ opt (fn l => l ^ " ") lt ^ (if m then "mut " else "") ^ type_str t1
  | A.TPtr (m, t1, _) => (if m then "*mut " else "*const ") ^ type_str t1
  | A.TTuple ([t1], _) => "(" ^ type_str t1 ^ ",)"
  | A.TTuple (ts, _) => "(" ^ commas (map type_str ts) ^ ")"
  | A.TSlice (t1, _) => "[" ^ type_str t1 ^ "]"
  | A.TArray (t1, e, _) => "[" ^ type_str t1 ^ "; " ^ expr_str 0 e ^ "]"
  | A.TInfer _ => "_"
  | A.TNever _ => "!"
  | A.TFn (ts, r, _) =>
    "fn(" ^ commas (map type_str ts) ^ ")"
      ^ opt (fn r1 => " -> " ^ type_str r1) r
  | A.TImpl (bs, _) => "impl " ^ bounds_str bs
  | A.TDyn (bs, _) => "dyn " ^ bounds_str bs
  | A.THol (s, subs, _) => hol_str (s, subs))

and pat_str p = (case p of
    A.PWild _ => "_"
  | A.PRest _ => ".."
  | A.PIdent (r, m, id, sub, _) =>
      (if r then "ref " else "") ^ (if m then "mut " else "") ^ ident_str id
        ^ opt (fn p1 => " @ " ^ pat_str p1) sub
  | A.PLit (neg, l, _) => (if neg then "-" else "") ^ lit_str l
  | A.PRange (lo, hi, incl, _) =>
    opt pat_str lo ^ (if incl then "..=" else "..") ^ opt pat_str hi
  | A.PPath pa => path_str pa
  | A.PTupleStruct (pa, ps, _) =>
    path_str pa ^ "(" ^ commas (map pat_str ps) ^ ")"
  | A.PStruct (pa, fs, rest, _) =>
      let val items = map fieldpat_str fs @ (if rest then [".."] else [])
      in path_str pa
        ^ (if null items then " {}" else " { " ^ commas items ^ " }") end
  | A.PTuple ([p1], _) => "(" ^ pat_str p1 ^ ",)"
  | A.PTuple (ps, _) => "(" ^ commas (map pat_str ps) ^ ")"
  | A.PSlice (ps, _) => "[" ^ commas (map pat_str ps) ^ "]"
  | A.PRef (m, p1, _) => (if m then "&mut " else "&") ^ pat_str p1
  | A.PAlt (ps, _) => space_implode " | " (map pat_str ps)
  | A.PParen (p1, _) => "(" ^ pat_str p1 ^ ")"
  | A.PMut (p1, _) => "mut " ^ pat_str p1
  | A.PHol (s, subs, _) => hol_str (s, subs))

and fieldpat_str (A.FieldPat (id, po, _)) =
  (case po of NONE => ident_str id | SOME p => ident_str id ^ ": " ^ pat_str p)

(* "n" is the indentation level of the line the expression starts on. *)
and expr_str n e = (case e of
    A.ELit l => lit_str l
  | A.EPath p => path_str p
  | A.EHol (s, subs, _) => hol_str (s, subs)
  | A.EEps (s, _) => "\092<epsilon>\092<open>" ^ s ^ "\092<close>"
  | A.ELogLit (s, subs, _) => "l" ^ hol_str (s, subs)
  | A.ESeq (b, _) => "(\n" ^ stmts_str (n + 1) b ^ ind_str n ^ ")"
  | A.EUnary (u, e1, _) => unop_str u ^ expr_str n e1
  | A.EBinary (b, e1, e2, _) =>
    expr_str n e1 ^ " " ^ binop_str b ^ " " ^ expr_str n e2
  | A.EAssign (b, e1, e2, _) =>
    expr_str n e1 ^ " " ^ assign_str b ^ " " ^ expr_str n e2
  | A.ECast (e1, t, _) => expr_str n e1 ^ " as " ^ type_str t
  | A.ETry (e1, _) => expr_str n e1 ^ "?"
  | A.ECall (f, args, _) =>
    expr_str n f ^ "(" ^ commas (map (expr_str n) args) ^ ")"
  | A.EMethod (r, m, ga, args, _) =>
      expr_str n r ^ "." ^ ident_str m ^ opt gargs_str ga ^ "("
        ^ commas (map (expr_str n) args) ^ ")"
  | A.EField (e1, f, _) => expr_str n e1 ^ "." ^ ident_str f
  | A.ETupIdx (e1, i, _) => expr_str n e1 ^ "." ^ i
  | A.EIndex (e1, i, _) => expr_str n e1 ^ "[" ^ expr_str n i ^ "]"
  | A.ERange (lo, hi, incl, _) =>
    opt (expr_str n) lo ^ (if incl then "..=" else "..") ^ opt (expr_str n) hi
  | A.ETuple ([e1], _) => "(" ^ expr_str n e1 ^ ",)"
  | A.ETuple (es, _) => "(" ^ commas (map (expr_str n) es) ^ ")"
  | A.EParen (e1, _) => "(" ^ expr_str n e1 ^ ")"
  | A.EArray (es, _) => "[" ^ commas (map (expr_str n) es) ^ "]"
  | A.ERepeat (e1, c, _) => "[" ^ expr_str n e1 ^ "; " ^ expr_str n c ^ "]"
  | A.EStruct (p, fs, base, _) =>
      let val items = map (fieldinit_str n) fs
        @ (case base of NONE => [] | SOME b => [".." ^ expr_str n b])
      in path_str p
        ^ (if null items then " {}" else " { " ^ commas items ^ " }") end
  | A.EBlock (lbl, b, _) => opt (fn l => l ^ ": ") lbl ^ block_str n b
  | A.EUnsafe (b, _) => "unsafe " ^ block_str n b
  | A.EIf (c, b, els, _) =>
      "if " ^ cond_str n c ^ " " ^ block_str n b ^
      (case els of NONE => "" | SOME e1 => " else " ^ expr_str n e1)
  | A.EWhile (lbl, c, b, _) =>
    opt (fn l => l ^ ": ") lbl ^ "while " ^ cond_str n c ^ " " ^ block_str n b
  | A.ELoop (lbl, b, _) => opt (fn l => l ^ ": ") lbl ^ "loop " ^ block_str n b
  | A.EFor (lbl, p, it, b, _) =>
      opt (fn l => l ^ ": ") lbl ^ "for " ^ pat_str p ^ " in " ^ expr_str n it
        ^ " " ^ block_str n b
  | A.EMatch (s, arms, _) =>
      "match " ^ expr_str n s ^ " {\n" ^ implode (map (arm_str (n + 1)) arms)
        ^ ind_str n ^ "}"
  | A.EClosure (mv, ps, ret, body, _) =>
      (if mv then "move " else "")
        ^ (if null ps then "||" else "|" ^ commas (map cparam_str ps) ^ "|") ^
      (case ret of NONE => " " ^ expr_str n body | SOME t =>
       " -> " ^ type_str t ^ " " ^ expr_str n body)
  | A.EReturn (eo, _) => "return" ^ opt (fn e1 => " " ^ expr_str n e1) eo
  | A.EBreak (lbl, eo, _) =>
    "break" ^ opt (fn l => " " ^ l) lbl ^ opt (fn e1 => " " ^ expr_str n e1) eo
  | A.EContinue (lbl, _) => "continue" ^ opt (fn l => " " ^ l) lbl
  | A.EYield _ => "yield"
  | A.ELog (a, b, _) => "log " ^ expr_str n a ^ " " ^ expr_str n b
  | A.EMacro (p, d, args, _) =>
      path_str p ^ "!" ^ d ^ commas (map (expr_str n) args)
        ^ (if d = "[" then "]" else ")")
  | A.EMacroRepeat (p, e1, c, _) =>
    path_str p ^ "![" ^ expr_str n e1 ^ "; " ^ expr_str n c ^ "]"
  | A.EMatches (e1, p, _) =>
    "matches!(" ^ expr_str n e1 ^ ", " ^ pat_str p ^ ")"
  | A.EAttr (attrs, e1, _) => attrs_inline attrs ^ expr_str n e1)

and fieldinit_str n (A.FieldInit (id, eo, _)) =
  (case eo of NONE => ident_str id | SOME e =>
   ident_str id ^ ": " ^ expr_str n e)

and cond_str n c = (case c of
    A.CExpr e => expr_str n e
  | A.CLet (p, e, _) => "let " ^ pat_str p ^ " = " ^ expr_str n e)

and cparam_str (A.CParam (p, t, _)) = pat_str p
  ^ opt (fn t1 => ": " ^ type_str t1) t

and arm_str n (A.Arm (attrs, p, guard, body, _)) =
  ind_str n ^ attrs_inline attrs ^ pat_str p
    ^ opt (fn g => " if " ^ expr_str n g) guard ^ " => " ^
  expr_str n body ^ ",\n"

(* The statements of a block at indentation level "n" (the statements themselves
   at "n"). *)
and stmts_str n (A.Block (stmts, tail, _)) =
  implode (map (fn s => ind_str n ^ stmt_str n s ^ "\n") stmts) ^
  (case tail of NONE => "" | SOME e => ind_str n ^ expr_str n e ^ "\n")

and block_str n (b as A.Block (stmts, tail, _)) =
  if null stmts andalso not (is_some tail) then "{}"
  else "{\n" ^ stmts_str (n + 1) b ^ ind_str n ^ "}"

and stmt_str n s = (case s of
    A.SLet (is_const, p, t, init, els, _) =>
      (if is_const then "const " else "let ") ^ pat_str p
        ^ opt (fn t1 => ": " ^ type_str t1) t ^
      opt (fn e => " = " ^ expr_str n e) init
        ^ opt (fn b => " else " ^ block_str n b) els ^ ";"
  | A.SExpr (e, semi, _) => expr_str n e ^ (if semi then ";" else "")
  | A.SItem it => item_str n it
  | A.SEmpty _ => ";")

and gparam_str g = (case g of
    A.GPLifetime (l, bs, _) =>
      l ^ (if null bs then "" else ": " ^ space_implode " + " bs)
  | A.GPType (id, bs, def, _) =>
      ident_str id ^ (if null bs then "" else ": " ^ bounds_str bs)
        ^ opt (fn t => " = " ^ type_str t) def
  | A.GPConst (id, t, _) => "const " ^ ident_str id ^ ": " ^ type_str t)

and gparams_str gs = if null gs then "" else "<" ^ commas (map gparam_str gs)
  ^ ">"

and where_str ws =
  if null ws then ""
  else " where " ^ commas (map (fn w => (case w of
         A.WType (t, bs, _) => type_str t ^ ": " ^ bounds_str bs
       | A.WLifetime (l, bs, _) => l ^ ": " ^ space_implode " + " bs)) ws)

and fnparam_str p = (case p of
    A.PSelf (r, lt, m, t, _) =>
      (if r then "&" ^ opt (fn l => l ^ " ") lt else "")
        ^ (if m then "mut " else "") ^ "self" ^
      opt (fn t1 => ": " ^ type_str t1) t
  | A.PParam (attrs, p1, t, _) =>
    attrs_inline attrs ^ pat_str p1 ^ ": " ^ type_str t)

and fielddef_str (A.FieldDef (attrs, vis, name, t, _)) =
  attrs_inline attrs ^ vis_str vis ^ opt (fn id => ident_str id ^ ": ") name
    ^ type_str t

and fields_str n fs = (case fs of
    A.FUnit => ""
  | A.FNamed fds =>
      if null fds then " {}"
      else " {\n"
        ^ implode
          (map (fn fd => ind_str (n + 1) ^ fielddef_str fd ^ ",\n") fds)
            ^ ind_str n ^ "}"
  | A.FTuple fds => "(" ^ commas (map fielddef_str fds) ^ ")")

and variant_str n (A.Variant (attrs, id, fs, disc, _)) =
  ind_str n ^ attrs_inline attrs ^ ident_str id ^ fields_str n fs
    ^ opt (fn e => " = " ^ expr_str n e) disc ^ ",\n"

and use_str u = (case u of
    A.UName (path, alias, _) =>
      space_implode "::" (map ident_str path)
        ^ opt (fn a => " as " ^ ident_str a) alias
  | A.UGlob (path, _) => space_implode "::" (map ident_str path @ ["*"])
  | A.UGroup (path, us, _) =>
      space_implode
        "::" (map ident_str path @ ["{" ^ commas (map use_str us) ^ "}"]))

and items_str n items =
  implode (map (fn it => ind_str n ^ item_str n it ^ "\n") items)

and item_str n (A.MkItem (attrs, vis, kind, _)) =
  attrs_str n attrs ^ vis_str vis ^
  (case kind of
     A.IFn (quals, name, gps, params, ret, wh, body) =>
       implode (map (fn q => q ^ " ") quals) ^ "fn " ^ ident_str name
         ^ gparams_str gps ^
       "(" ^ commas (map fnparam_str params) ^ ")"
         ^ opt (fn t => " -> " ^ type_str t) ret ^ where_str wh ^
       (case body of NONE => ";" | SOME b => " " ^ block_str n b)
   | A.IStruct (name, gps, wh, fs) =>
       "struct " ^ ident_str name ^ gparams_str gps ^
       (case fs of
          A.FNamed _ => where_str wh ^ fields_str n fs
        | A.FTuple _ => fields_str n fs ^ where_str wh ^ ";"
        | A.FUnit => where_str wh ^ ";")
   | A.IEnum (name, gps, wh, vs) =>
       "enum " ^ ident_str name ^ gparams_str gps ^ where_str wh ^
       (if null vs then " {}" else " {\n"
        ^ implode (map (variant_str (n + 1)) vs) ^ ind_str n ^ "}")
   | A.IImpl (uns, gps, tr, t, wh, items) =>
       (if uns then "unsafe " else "") ^ "impl" ^ gparams_str gps ^ " " ^
       opt (fn p => path_str p ^ " for ") tr ^ type_str t ^ where_str wh ^
       (if null items then " {}" else " {\n" ^ items_str (n + 1) items
        ^ ind_str n ^ "}")
   | A.ITrait (uns, name, gps, sups, wh, items) =>
       (if uns then "unsafe " else "") ^ "trait " ^ ident_str name
         ^ gparams_str gps ^
       (if null sups then "" else ": " ^ bounds_str sups) ^ where_str wh ^
       (if null items then " {}" else " {\n" ^ items_str (n + 1) items
        ^ ind_str n ^ "}")
   | A.IConst (name, t, e) =>
     "const " ^ ident_str name ^ ": " ^ type_str t
       ^ opt (fn e1 => " = " ^ expr_str n e1) e ^ ";"
   | A.IStatic (m, name, t, e) =>
       "static " ^ (if m then "mut " else "") ^ ident_str name ^ ": "
         ^ type_str t ^
       opt (fn e1 => " = " ^ expr_str n e1) e ^ ";"
   | A.ITypeAlias (name, gps, bs, t) =>
       "type " ^ ident_str name ^ gparams_str gps
         ^ (if null bs then "" else ": " ^ bounds_str bs) ^
       opt (fn t1 => " = " ^ type_str t1) t ^ ";"
   | A.IUse u => "use " ^ use_str u ^ ";"
   | A.IMod (name, NONE) => "mod " ^ ident_str name ^ ";"
   | A.IMod (name, SOME items) =>
       "mod " ^ ident_str name
         ^ (if null items then " {}" else " {\n" ^ items_str (n + 1) items
            ^ ind_str n ^ "}"))

fun pp_root r = (case r of
    A.Id id => ident_str id
  | A.Expr e => expr_str 0 e
  | A.Type t => type_str t
  | A.Pat p => pat_str p
  | A.Stmt s => stmt_str 0 s
  | A.Item it => item_str 0 it
  | A.Body b =>
    (let val s = stmts_str 0 b in if String.isSuffix "\n" s
     then String.substring (s, 0, size s - 1) else s end)
  | A.Crate items =>
    (let val s = items_str 0 items in if String.isSuffix "\n" s
     then String.substring (s, 0, size s - 1) else s end))

end
