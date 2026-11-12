(* Abstract syntax of Go, following "The Go Programming Language Specification" (go1.27): one
   datatype per syntactic category, one constructor per alternative, close enough to the concrete
   syntax that "pp_root" (go_pp.ML) can print any parsed program back as Go text. What is shared
   with C11 and the other members of the family - the comment/antiquotation attachment mechanism,
   the navigation language, the environment - is the position-annotation machinery ("'a nodeInfo",
   "'a comment", "navi", "'a ident"), identical in shape to its namesakes.

   As in the standard library's go/ast, a type is an expression: Go does not tell a call from a
   conversion, an index from an instantiation, or "*p" from "*T" by syntax, and the type literals
   ("[]int", "map[K]V", "struct{...}", ...) are operands of the expression grammar as well. A type
   is therefore a "gExpr", and the analysis tells what a name denotes. *)

structure Go_Ast = struct

datatype navi = up | Up | right | down

datatype 'a comment = Raw_txt of (string*'a) list
                    | Antiquotation of {tag : string * 'a} * navi list * {level : int}
                                       * {cartouche : string * 'a}

datatype 'a nodeInfo = OnlyPos of 'a | NodeInfo of 'a comment list * 'a

datatype 'a ident = Ident of string * int * 'a nodeInfo

datatype binop =
    LOr | LAnd | Eq | Ne | Lt | Le | Gt | Ge
  | Add | Sub | Or | Xor | Mul | Div | Rem | Shl | Shr | And | AndNot

datatype unop = UPlus | UMinus | Not | UXor | UAnd | URecv     (* + - ! ^ & <- ; "*" is EStar *)

datatype chandir = Both | SendOnly | RecvOnly

datatype 'a gExpr =
    EIdent of 'a ident
  | EInt of string * 'a nodeInfo                     (* the literals, as written *)
  | EFloat of string * 'a nodeInfo
  | EImag of string * 'a nodeInfo
  | ERune of string * 'a nodeInfo
  | EString of string * 'a nodeInfo
  | EParen of 'a gExpr * 'a nodeInfo
  | ESelector of 'a gExpr * 'a ident * 'a nodeInfo   (* x.f, pkg.Name *)
  | EIndex of 'a gExpr * 'a gExpr list * 'a nodeInfo (* a[i], and the instantiation F[T, U] *)
  | ESlice of 'a gExpr * 'a gExpr option * 'a gExpr option * 'a gExpr option * 'a nodeInfo
      (* a[lo:hi], a[lo:hi:max] (the third is present iff the slice has three indices) *)
  | ETypeAssert of 'a gExpr * 'a gExpr option * 'a nodeInfo   (* x.(T); NONE: x.(type) *)
  | ECall of 'a gExpr * 'a gExpr list * bool * 'a nodeInfo    (* f(a, b...): the flag is "..." *)
  | EStar of 'a gExpr * 'a nodeInfo                  (* *p, and the pointer type *T *)
  | EUnary of unop * 'a gExpr * 'a nodeInfo
  | EBinary of binop * 'a gExpr * 'a gExpr * 'a nodeInfo
  | ECompLit of 'a gExpr option * 'a gElement list * 'a nodeInfo
      (* T{...}; NONE: the type is elided, "{...}" inside another literal *)
  | EFuncLit of 'a gSig * 'a gBlock * 'a nodeInfo
  (* the type literals *)
  | EArrayType of 'a gExpr option * 'a gExpr * 'a nodeInfo    (* [N]T; NONE: the slice type []T *)
  | EEllipsisArray of 'a gExpr * 'a nodeInfo                  (* [...]T, in a composite literal *)
  | EMapType of 'a gExpr * 'a gExpr * 'a nodeInfo
  | EChanType of chandir * 'a gExpr * 'a nodeInfo
  | EFuncType of 'a gSig * 'a nodeInfo
  | EStructType of 'a gField list * 'a nodeInfo
  | EInterfaceType of 'a gIElem list * 'a nodeInfo
  | ETilde of 'a gExpr * 'a nodeInfo                          (* ~T, in a constraint *)
  | EUnion of 'a gExpr list * 'a nodeInfo                     (* A | ~B | C, in a constraint *)

and 'a gElement = Element of 'a gExpr option * 'a gExpr * 'a nodeInfo    (* [key :] value *)

and 'a gParam = Param of 'a ident list * 'a gExpr * bool * 'a nodeInfo
    (* names (none: an unnamed parameter), type, variadic ("...T") *)

and 'a gSig = Sig of 'a gParam list * 'a gParam list * 'a nodeInfo    (* parameters, results *)

and 'a gField = Field of 'a ident list * 'a gExpr * string option * 'a nodeInfo
    (* names (none: an embedded field), type, tag as written *)

and 'a gIElem =
    IMethod of 'a ident * 'a gSig * 'a nodeInfo
  | IType of 'a gExpr * 'a nodeInfo        (* a type, a union, a ~T term *)

and 'a gTParam = TParam of 'a ident list * 'a gExpr * 'a nodeInfo     (* names, constraint *)

and 'a gStmt =
    SEmpty of 'a nodeInfo
  | SExpr of 'a gExpr * 'a nodeInfo
  | SSend of 'a gExpr * 'a gExpr * 'a nodeInfo
  | SIncDec of 'a gExpr * bool * 'a nodeInfo                        (* true: ++ *)
  | SAssign of 'a gExpr list * binop option * 'a gExpr list * 'a nodeInfo    (* NONE: plain = *)
  | SShortVar of 'a gExpr list * 'a gExpr list * 'a nodeInfo                 (* := *)
  | SDecl of 'a gDecl
  | SLabeled of 'a ident * 'a gStmt * 'a nodeInfo
  | SGo of 'a gExpr * 'a nodeInfo
  | SDefer of 'a gExpr * 'a nodeInfo
  | SReturn of 'a gExpr list * 'a nodeInfo
  | SBreak of 'a ident option * 'a nodeInfo
  | SContinue of 'a ident option * 'a nodeInfo
  | SGoto of 'a ident * 'a nodeInfo
  | SFallthrough of 'a nodeInfo
  | SBlock of 'a gBlock
  | SIf of 'a gStmt option * 'a gExpr * 'a gBlock * 'a gStmt option * 'a nodeInfo
      (* init, condition, then, else (an SIf or an SBlock) *)
  | SSwitch of 'a gStmt option * 'a gExpr option * 'a gCase list * 'a nodeInfo
  | STypeSwitch of 'a gStmt option * 'a ident option * 'a gExpr * 'a gCase list * 'a nodeInfo
      (* init, the bound name, the x of "x.(type)", the clauses *)
  | SSelect of 'a gComm list * 'a nodeInfo
  | SFor of 'a gStmt option * 'a gExpr option * 'a gStmt option * 'a gBlock * 'a nodeInfo
      (* init, condition, post, body; "for {" and "for cond {" are the special cases *)
  | SRange of 'a gExpr option * 'a gExpr option * bool * 'a gExpr * 'a gBlock * 'a nodeInfo
      (* key, value, the flag is ":=" (otherwise "="), the ranged-over expression, body *)

and 'a gBlock = Block of 'a gStmt list * 'a nodeInfo

and 'a gCase = Case of 'a gExpr list option * 'a gStmt list * 'a nodeInfo   (* NONE: default *)

and 'a gComm = Comm of 'a gStmt option * 'a gStmt list * 'a nodeInfo        (* NONE: default *)

and 'a gSpec =
    ConstSpec of 'a ident list * 'a gExpr option * 'a gExpr list * 'a nodeInfo
  | VarSpec of 'a ident list * 'a gExpr option * 'a gExpr list * 'a nodeInfo
  | TypeSpec of 'a ident * 'a gTParam list * bool * 'a gExpr * 'a nodeInfo   (* true: an alias *)
  | ImportSpec of 'a ident option * string * 'a nodeInfo           (* the path as written *)

and 'a gDecl =
    DConst of 'a gSpec list * bool * 'a nodeInfo        (* the flag: a parenthesised group *)
  | DVar of 'a gSpec list * bool * 'a nodeInfo
  | DType of 'a gSpec list * bool * 'a nodeInfo
  | DImport of 'a gSpec list * bool * 'a nodeInfo
  | DFunc of 'a ident * 'a gTParam list * 'a gSig * 'a gBlock option * 'a nodeInfo
  | DMethod of 'a gParam list * 'a ident * 'a gTParam list * 'a gSig * 'a gBlock option
               * 'a nodeInfo                              (* receiver, name, ... *)

datatype 'a gFile = File of 'a ident * 'a gDecl list * 'a nodeInfo    (* package, declarations *)

(* What a parse produces, by entry point. *)
datatype 'a root =
    Id of 'a ident
  | Expr of 'a gExpr          (* an expression or a type *)
  | Stmts of 'a gStmt list    (* a statement list *)
  | Decls of 'a gDecl list    (* top-level declarations, without a package clause *)
  | Source of 'a gFile        (* a source file *)
  | Stmt of 'a gStmt          (* never produced by a parse: the closest context of a statement *)
  | Decl of 'a gDecl          (* likewise, for a declaration *)

(* --- Positions ---------------------------------------------------------- *)

fun pos_of_NodeInfo (OnlyPos pos) = pos
  | pos_of_NodeInfo (NodeInfo (_, pos)) = pos

fun comments_of_NodeInfo (OnlyPos _) = []
  | comments_of_NodeInfo (NodeInfo (cs, _)) = cs

fun nodeInfo_of_ident (Ident (_, _, ni)) = ni
fun ident_name (Ident (s, _, _)) = s

fun nodeInfo_of_expr e = (case e of
    EIdent id => nodeInfo_of_ident id | EInt (_, ni) => ni | EFloat (_, ni) => ni
  | EImag (_, ni) => ni | ERune (_, ni) => ni | EString (_, ni) => ni | EParen (_, ni) => ni
  | ESelector (_, _, ni) => ni | EIndex (_, _, ni) => ni | ESlice (_, _, _, _, ni) => ni
  | ETypeAssert (_, _, ni) => ni | ECall (_, _, _, ni) => ni | EStar (_, ni) => ni
  | EUnary (_, _, ni) => ni | EBinary (_, _, _, ni) => ni | ECompLit (_, _, ni) => ni
  | EFuncLit (_, _, ni) => ni | EArrayType (_, _, ni) => ni | EEllipsisArray (_, ni) => ni
  | EMapType (_, _, ni) => ni | EChanType (_, _, ni) => ni | EFuncType (_, ni) => ni
  | EStructType (_, ni) => ni | EInterfaceType (_, ni) => ni | ETilde (_, ni) => ni
  | EUnion (_, ni) => ni)

fun nodeInfo_of_block (Block (_, ni)) = ni

fun nodeInfo_of_spec s = (case s of
    ConstSpec (_, _, _, ni) => ni | VarSpec (_, _, _, ni) => ni | TypeSpec (_, _, _, _, ni) => ni
  | ImportSpec (_, _, ni) => ni)

fun nodeInfo_of_decl d = (case d of
    DConst (_, _, ni) => ni | DVar (_, _, ni) => ni | DType (_, _, ni) => ni
  | DImport (_, _, ni) => ni | DFunc (_, _, _, _, ni) => ni | DMethod (_, _, _, _, _, ni) => ni)

fun nodeInfo_of_stmt s = (case s of
    SEmpty ni => ni | SExpr (_, ni) => ni | SSend (_, _, ni) => ni | SIncDec (_, _, ni) => ni
  | SAssign (_, _, _, ni) => ni | SShortVar (_, _, ni) => ni | SDecl d => nodeInfo_of_decl d
  | SLabeled (_, _, ni) => ni | SGo (_, ni) => ni | SDefer (_, ni) => ni | SReturn (_, ni) => ni
  | SBreak (_, ni) => ni | SContinue (_, ni) => ni | SGoto (_, ni) => ni | SFallthrough ni => ni
  | SBlock b => nodeInfo_of_block b | SIf (_, _, _, _, ni) => ni | SSwitch (_, _, _, ni) => ni
  | STypeSwitch (_, _, _, _, ni) => ni | SSelect (_, ni) => ni | SFor (_, _, _, _, ni) => ni
  | SRange (_, _, _, _, _, ni) => ni)

fun pos_of_expr e = pos_of_NodeInfo (nodeInfo_of_expr e)
fun pos_of_decl d = pos_of_NodeInfo (nodeInfo_of_decl d)
fun pos_of_stmt s = pos_of_NodeInfo (nodeInfo_of_stmt s)
fun pos_of_ident id = pos_of_NodeInfo (nodeInfo_of_ident id)

end
