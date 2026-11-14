(* Printing an ARM assembly AST back as GNU assembler text: one statement per line, labels and the
   directives that structure the text (.macro, .if, .rept, their ends) at the first column,
   instructions, other directives and macro calls four blanks in, whatever the nesting of the
   blocks (as macros are written). Every explicit parenthesis of the source is kept in the AST
   ("EParen"), so no precedence reasoning is needed here; binary operators are surrounded by
   blanks. Comments and antiquotations are not printed (they live in the nodeInfo), as in the
   other front-ends. What is printed has the same tokens as what was parsed (the corpus test of
   ARM_Tests.thy checks this), but for the case of the words that end a block (.endm, .endif,
   .else, .endr) and the separators of statements. *)

structure ARM_Pp = struct

structure A = ARM_Ast

fun commas xs = space_implode ", " xs
fun ind n = replicate_string n "    "
(* the nesting of the blocks is not shown: statements that are not labels or structure are at the
   level 1, the others at the level 0 *)

fun ident_str (A.Ident (s, _, _)) = s

fun unop_str u = (case u of A.Neg => "-" | A.Pos => "+" | A.Not => "!" | A.Compl => "~")

fun binop_str b = (case b of
    A.Mul => "*" | A.Div => "/" | A.Mod => "%" | A.Shl => "<<" | A.Shr => ">>" | A.Or => "|"
  | A.And => "&" | A.Xor => "^" | A.Add => "+" | A.Sub => "-" | A.Equal => "==" | A.NotEqual => "!="
  | A.Less => "<" | A.Greater => ">" | A.LessEq => "<=" | A.GreaterEq => ">=" | A.LAnd => "&&"
  | A.LOr => "||")

fun expr_str e = (case e of
    A.ENum (s, _) => s | A.EFloat (s, _) => s | A.EChar (s, _) => s | A.EString (s, _) => s
  | A.ESym id => ident_str id
  | A.EReg (_, s, _) => s
  | A.EDot _ => "."
  | A.ELocal (s, _) => s
  | A.EReloc (e1, id, _) => expr_str e1 ^ "(" ^ ident_str id ^ ")"
  | A.EPart (id, e1, _) => ":" ^ ident_str id ^ ":" ^ expr_str e1
  | A.EUnary (u, e1, _) =>
      let val s = expr_str e1
          val o1 = unop_str u
      in
        if (o1 = "-" orelse o1 = "+") andalso String.isPrefix o1 s then o1 ^ " " ^ s else o1 ^ s
      end
  | A.EBinary (b, e1, e2, _) => expr_str e1 ^ " " ^ binop_str b ^ " " ^ expr_str e2
  | A.EParen (e1, _) => "(" ^ expr_str e1 ^ ")")

fun operand_str o1 = (case o1 of
    A.OExpr e => expr_str e
  | A.OReg (_, s, wb, _) => s ^ (if wb then "!" else "")
  | A.OImm (e, _) => "#" ^ expr_str e
  | A.OShift (_, s, arg, _) => s ^ (case arg of SOME a => " " ^ operand_str a | NONE => "")
  | A.OLiteral (e, _) => "=" ^ expr_str e
  | A.OMem (ops, wb, _) => "[" ^ mem_str ops ^ "]" ^ (if wb then "!" else "")
  | A.OAlign (s, _, _) => ":" ^ s
  | A.OList (ops, hat, _) => "{" ^ commas (map operand_str ops) ^ "}" ^ (if hat then "^" else "")
  | A.ORange (a, b, _) => operand_str a ^ "-" ^ operand_str b
  | A.OPercent (id, _) => "%" ^ ident_str id
  | A.OKeyword (id, e, _) => ident_str id ^ "=" ^ expr_str e
  | A.ORaw (s, _) => s
  | A.OScalar (_, s, e, _) => s ^ "[" ^ expr_str e ^ "]")

(* the operands of a memory reference; an alignment may follow without a comma *)
and mem_str ops =
  let
    fun go acc [] = rev acc
      | go acc (A.OAlign (s, false, _) :: rest) =
          (case acc of
             last :: acc' => go ((last ^ " :" ^ s) :: acc') rest
           | [] => go [" :" ^ s] rest)
      | go acc (x :: rest) = go (operand_str x :: acc) rest
  in commas (go [] ops) end

fun operands_str ops = commas (map operand_str ops)
fun args_str ops = if null ops then "" else " " ^ operands_str ops

fun mparam_str (A.MParam (id, qual, dflt, _, _)) =
  ident_str id ^ (case qual of SOME q => ":" ^ q | NONE => "")
  ^ (case dflt of SOME e => "=" ^ expr_str e | NONE => "")

fun mparams_str ps =
  String.concat (map_index (fn (i, p as A.MParam (_, _, _, comma, _)) =>
                              (if i = 0 then " " else if comma then ", " else " ") ^ mparam_str p)
                            ps)

fun label_str l = (case l of A.LName id => ident_str id ^ ":" | A.LNum (s, _) => s ^ ":")

fun stmt_lines (n : int) s : string list =
  (case s of
     A.SLabel (l, _) => [ind n ^ label_str l]
   | A.SInsn (A.Insn ({text, ...}, ops, _)) => [ind (n + 1) ^ text ^ args_str ops]
   | A.SDir (id, ops, _) => [ind (n + 1) ^ ident_str id ^ args_str ops]
   | A.SAssign (id, e, _) => [ind n ^ ident_str id ^ " = " ^ expr_str e]
   | A.SReq (id, o1, _) => [ind n ^ ident_str id ^ " .req " ^ operand_str o1]
   | A.SCall (id, ops, _) => [ind (n + 1) ^ ident_str id ^ args_str ops]
   | A.SMacro (id, ps, body, _) =>
       [ind n ^ ".macro " ^ ident_str id ^ mparams_str ps] @ stmts_lines n body
       @ [ind n ^ ".endm"]
   | A.SCond (branches, els, _) =>
       maps (fn A.Branch (d, ops, body, _) =>
               (ind n ^ ident_str d ^ args_str ops) :: stmts_lines n body) branches
       @ (case els of SOME b => (ind n ^ ".else") :: stmts_lines n b | NONE => [])
       @ [ind n ^ ".endif"]
   | A.SRep (d, ops, body, _) =>
       (ind n ^ ident_str d ^ args_str ops) :: stmts_lines n body @ [ind n ^ ".endr"]
   | A.SExitm _ => [ind (n + 1) ^ ".exitm"])

and stmts_lines n ss = maps (stmt_lines n) ss

fun pp_stmts ss = cat_lines (stmts_lines 0 ss)

fun pp_root (r : Position.T A.root) : string =
  (case r of
     A.Id id => ident_str id
   | A.Expr e => expr_str e
   | A.Operand o1 => operand_str o1
   | A.Stmts ss => pp_stmts ss
   | A.Source (A.File (ss, _)) => pp_stmts ss ^ (if null ss then "" else "\n")
   | A.Stmt s => pp_stmts [s])

end
