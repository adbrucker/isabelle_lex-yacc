(* Abstract syntax of AdaSpark: the SPARK 2014 subset of Ada 2012, following
   the Ada 2012 Reference Manual (Annex P, the syntax summary) restricted to
   what SPARK uses - packages, subprograms, the scalar, array, record, tagged
   and private types, statements, the full expression language including
   conditional and quantified expressions, and the aspect specifications
   (Pre, Post, Global, Depends, Contract_Cases, ...) in which SPARK states
   its contracts.

   As for the other front-ends there is no pre-existing reference AST to
   port: this is a design of this project's own, one datatype per syntactic
   category, one constructor per alternative, close enough to the concrete
   syntax that "pp_root" (adaspark_pp.ML) can print any parsed program back
   as Ada text. What is shared with C11 and the other members of the family -
   the comment/antiquotation attachment mechanism, the navigation language,
   the environment - is the position-annotation machinery ("'a nodeInfo",
   "'a comment", "navi", "'a ident"), identical in shape to its namesakes.

   Ada makes no difference between names and expressions in its syntax (a
   name is a primary; "F (X)" is a call, an indexing or a conversion
   depending on what "F" is), and neither does this AST: a name is an
   expression, and the analysis tells what it denotes. Ada is case
   insensitive: identifiers and keywords are kept as written, the
   environment compares them in lower case. *)

structure AdaSpark_Ast = struct

datatype navi = up | Up | right | down

datatype 'a comment = Raw_txt of (string*'a) list
                    | Antiquotation
                        of {tag : string * 'a} * navi
                          list * {level : int} * {cartouche : string * 'a}

datatype 'a nodeInfo = OnlyPos of 'a | NodeInfo of 'a comment list * 'a

datatype 'a ident = Ident of string * int * 'a nodeInfo

datatype binop =
    Plus | Minus | Concat | Mul | Div | Mod | Rem | Exp
  | Eq | Ne | Lt | Le | Gt | Ge
  | And | Or | Xor | AndThen | OrElse

datatype unop = UPlus | UMinus | Abs | Not

datatype mode = MDefault | MIn | MOut | MInOut | MAccess

datatype accessKind = AccPlain | AccAll | AccConstant

datatype 'a aExpr =
    EId of 'a ident
  | EInt of string * 'a
      nodeInfo                     (* as written: 16#FF#, 1_000 *)
  | EReal of string * 'a nodeInfo
  | EChar of string * 'a nodeInfo                    (* with its quotes *)
  | EStr of string * 'a nodeInfo                     (* with its quotes *)
  | ENull of 'a nodeInfo
  | ESel of 'a aExpr * 'a ident * 'a nodeInfo        (* P.X *)
  | EDeref of 'a aExpr * 'a nodeInfo                 (* X.all *)
  | EApply of 'a aExpr * 'a aAssoc list * 'a
      nodeInfo  (* F (A, B => C): call, index, slice, conversion *)
  | EAttr of 'a aExpr * 'a ident * 'a nodeInfo       (* X'First *)
  | EQual of 'a aExpr * 'a aAssoc list * 'a nodeInfo (* T'(E), T'(A, B) *)
  | EUn of unop * 'a aExpr * 'a nodeInfo
  | EBin of binop * 'a aExpr * 'a aExpr * 'a nodeInfo
  | EIn of bool * 'a aExpr * 'a aChoice list * 'a
      nodeInfo   (* true: "not in" *)
  | EParen of 'a aExpr * 'a nodeInfo
  | EAgg of 'a aAssoc list * 'a nodeInfo             (* (1, 2, others => 0) *)
  | EExtAgg of 'a aExpr * 'a aAssoc list * 'a nodeInfo   (* (P with A => 1) *)
  | EDeltaAgg
      of 'a aExpr * 'a aAssoc list * 'a nodeInfo (* (X with delta A => 1) *)
  | ENew of 'a aExpr * 'a nodeInfo
  | EIf of ('a aExpr * 'a aExpr) list * 'a aExpr option * 'a nodeInfo
      (* if c then a {elsif c then a} [else b]: conditional expression *)
  | ECase of 'a aExpr * ('a aChoice list * 'a aExpr) list * 'a nodeInfo
  | EQuant of bool * 'a ident * 'a aIter * 'a aExpr * 'a
      nodeInfo   (* true: for all, false: for some *)

and 'a aAssoc =
    APos of 'a aExpr
  | ARange of 'a aExpr * 'a aExpr * 'a
      nodeInfo       (* a slice or range argument: L .. H *)
  | ANamed of 'a aChoice list * 'a aExpr * 'a nodeInfo

and 'a aChoice =
    ChExpr of 'a aExpr
  | ChRange of 'a aExpr * 'a aExpr * 'a nodeInfo
  | ChOthers of 'a nodeInfo

and 'a aIter =
    IterIn of bool * 'a aDiscRange                   (* true: reverse *)
  | IterOf of bool * 'a aExpr                        (* for X of [reverse] A *)

and 'a aDiscRange =
    DRRange of 'a aExpr * 'a aExpr * 'a nodeInfo
  | DRSub of 'a aSub

and 'a aSub = Sub
  of bool * 'a aExpr * ('a aExpr * 'a aExpr) option * 'a nodeInfo
    (* not null?, the subtype mark (possibly with an index or discriminant
       constraint), range constraint *)

and 'a aAspect = Aspect
  of 'a ident * 'a ident option * 'a aExpr option * 'a nodeInfo
    (* Pre'Class => E: name, the attribute, the value *)

and 'a aIdx =
    IdxRange of 'a aExpr * 'a aExpr * 'a nodeInfo    (* constrained: L .. H *)
  | IdxSub of 'a
      aExpr                               (* constrained: a subtype *)
  | IdxUnconstrained of 'a aExpr * 'a nodeInfo       (* T range <> *)

and 'a aComponent = Comp
  of 'a ident list * bool * 'a aSub * 'a aExpr option * 'a nodeInfo

and 'a aRecDef =
    RecNull
  | RecComps of 'a aComponent list * 'a aVariantPart option

and 'a aVariantPart = VariantPart
  of 'a ident * ('a aChoice list * 'a aRecDef) list * 'a nodeInfo

and 'a aExt = ExtNone | ExtRecord of 'a aRecDef | ExtPrivate

and 'a aTypeDef =
    TEnum of 'a ident list
  | TRange of 'a aExpr * 'a aExpr
  | TMod of 'a aExpr
  | TDigits of 'a aExpr * ('a aExpr * 'a aExpr) option
  | TDelta of 'a aExpr * ('a aExpr * 'a aExpr) option
  | TArray of 'a aIdx list * bool * 'a
      aSub          (* indices, aliased components?, component subtype *)
  | TRecord
      of bool * bool * bool * 'a aRecDef       (* abstract, tagged, limited *)
  | TDerived of bool * bool * 'a aSub * 'a aExt      (* abstract, limited *)
  | TPrivate
      of bool * bool * bool                   (* abstract, tagged, limited *)
  | TAccess of bool * accessKind * 'a aSub           (* not null *)

and 'a aParam = Param
  of 'a ident list * mode * 'a aSub * 'a aExpr option * 'a nodeInfo

and 'a aSpec = Spec
  of bool * bool * 'a ident * 'a aParam list * 'a aSub option * 'a nodeInfo
    (* overriding?, function?, designator, parameters, result subtype *)

and 'a aObjDef = OSub of 'a aSub | OArray of 'a aIdx list * bool * 'a aSub

and 'a aDecl =
    DObject of 'a ident list * bool * bool * 'a aObjDef * 'a aExpr option * 'a
      aAspect list * 'a nodeInfo
      (* names, aliased?, constant?, definition, initial value, aspects *)
  | DNumber of 'a ident list * 'a aExpr * 'a nodeInfo
  | DException of 'a ident list * 'a nodeInfo
  | DType of 'a ident * 'a aParam list * 'a aTypeDef * 'a aAspect list * 'a
      nodeInfo
  | DIncomplete of 'a ident * 'a nodeInfo
  | DSubtype of 'a ident * 'a aSub * 'a aAspect list * 'a nodeInfo
  | DSpec of 'a aSpec * bool * 'a aAspect list * 'a
      nodeInfo      (* abstract? *)
  | DNullProc of 'a aSpec * 'a aAspect list * 'a nodeInfo
  | DExprFun of 'a aSpec * 'a aExpr * 'a aAspect list * 'a nodeInfo
  | DBody of 'a aSpec * 'a aAspect list * 'a aDecl list * 'a aStmt list * 'a
      aHandler list * 'a nodeInfo
  | DPackage
      of 'a aExpr * 'a aAspect list * 'a aDecl list * 'a aDecl list * 'a
        nodeInfo   (* visible, private *)
  | DPackageBody
      of 'a aExpr * 'a aAspect list * 'a aDecl
        list * ('a aStmt list * 'a aHandler list) option * 'a nodeInfo
  | DUse of bool * 'a aExpr list * 'a
      nodeInfo                    (* use type? *)
  | DPragma of 'a ident * 'a aAssoc list * 'a nodeInfo
  | DAttrDef
      of 'a aExpr * 'a aExpr * 'a
        nodeInfo                 (* for X'Size use 8; *)

and 'a aScheme =
    LoopPlain
  | LoopWhile of 'a aExpr
  | LoopFor of 'a ident * 'a aIter

and 'a aStmt =
    SNull of 'a nodeInfo
  | SAssign of 'a aExpr * 'a aExpr * 'a nodeInfo
  | SCall of 'a aExpr * 'a nodeInfo
  | SIf of ('a aExpr * 'a aStmt list) list * 'a aStmt list option * 'a nodeInfo
  | SCase of 'a aExpr * ('a aChoice list * 'a aStmt list) list * 'a nodeInfo
  | SLoop of 'a ident option * 'a aScheme * 'a aStmt list * 'a nodeInfo
  | SBlock of 'a ident option * 'a aDecl list * 'a aStmt list * 'a aHandler
      list * 'a nodeInfo
  | SExit of 'a aExpr option * 'a aExpr option * 'a
      nodeInfo     (* loop name, condition *)
  | SReturn of 'a aExpr option * 'a nodeInfo
  | SRaise of 'a aExpr option * 'a aExpr option * 'a
      nodeInfo    (* exception, message *)
  | SPragma of 'a ident * 'a aAssoc list * 'a nodeInfo

and 'a aHandler = Handler of 'a aChoice list * 'a aStmt list * 'a nodeInfo

datatype 'a aClause =
    CWith of bool * bool * 'a aExpr list * 'a
      nodeInfo           (* limited?, private?, units *)
  | CUse of bool * 'a aExpr list * 'a nodeInfo                   (* use type? *)

datatype 'a aUnit = Unit of 'a aClause list * 'a aDecl * 'a nodeInfo

(* What a parse produces, by entry point. *)
datatype 'a root =
    Id of 'a ident
  | Expr of 'a aExpr
  | Type of 'a aSub
  | Stmt of 'a
      aStmt          (* never produced by a parse: the closest context
                      of an annotation on a statement *)
  | Decl of 'a aDecl          (* likewise, for a declaration *)
  | Body of 'a aStmt list     (* a sequence of statements *)
  | Crate of 'a aUnit list    (* a source file: its compilation units *)

(* --- Positions ---------------------------------------------------------- *)

fun pos_of_NodeInfo (OnlyPos pos) = pos
  | pos_of_NodeInfo (NodeInfo (_, pos)) = pos

fun comments_of_NodeInfo (OnlyPos _) = []
  | comments_of_NodeInfo (NodeInfo (cs, _)) = cs

fun nodeInfo_of_ident (Ident (_, _, ni)) = ni
fun ident_name (Ident (s, _, _)) = s

fun nodeInfo_of_expr e = (case e of
    EId id => nodeInfo_of_ident id | EInt (_, ni) => ni | EReal (_, ni) =>
      ni | EChar (_, ni) => ni
  | EStr (_, ni) => ni | ENull ni => ni | ESel (_, _, ni) =>
    ni | EDeref (_, ni) => ni
  | EApply (_, _, ni) => ni | EAttr (_, _, ni) => ni | EQual (_, _, ni) =>
    ni | EUn (_, _, ni) => ni
  | EBin (_, _, _, ni) => ni | EIn (_, _, _, ni) => ni | EParen (_, ni) =>
    ni | EAgg (_, ni) => ni
  | EExtAgg (_, _, ni) => ni | EDeltaAgg (_, _, ni) => ni | ENew (_, ni) =>
    ni | EIf (_, _, ni) => ni
  | ECase (_, _, ni) => ni | EQuant (_, _, _, _, ni) => ni)

fun nodeInfo_of_sub (Sub (_, _, _, ni)) = ni

fun nodeInfo_of_decl d = (case d of
    DObject (_, _, _, _, _, _, ni) => ni | DNumber (_, _, ni) =>
      ni | DException (_, ni) => ni
  | DType (_, _, _, _, ni) => ni | DIncomplete (_, ni) =>
    ni | DSubtype (_, _, _, ni) => ni
  | DSpec (_, _, _, ni) => ni | DNullProc (_, _, ni) =>
    ni | DExprFun (_, _, _, ni) => ni
  | DBody (_, _, _, _, _, ni) => ni | DPackage (_, _, _, _, ni) => ni
  | DPackageBody (_, _, _, _, ni) => ni | DUse (_, _, ni) =>
    ni | DPragma (_, _, ni) => ni
  | DAttrDef (_, _, ni) => ni)

fun nodeInfo_of_stmt s = (case s of
    SNull ni => ni | SAssign (_, _, ni) => ni | SCall (_, ni) =>
      ni | SIf (_, _, ni) => ni
  | SCase (_, _, ni) => ni | SLoop (_, _, _, ni) =>
    ni | SBlock (_, _, _, _, ni) => ni
  | SExit (_, _, ni) => ni | SReturn (_, ni) => ni | SRaise (_, _, ni) =>
    ni | SPragma (_, _, ni) => ni)

fun nodeInfo_of_unit (Unit (_, _, ni)) = ni

fun pos_of_expr e = pos_of_NodeInfo (nodeInfo_of_expr e)
fun pos_of_sub s = pos_of_NodeInfo (nodeInfo_of_sub s)
fun pos_of_decl d = pos_of_NodeInfo (nodeInfo_of_decl d)
fun pos_of_stmt s = pos_of_NodeInfo (nodeInfo_of_stmt s)
fun pos_of_ident id = pos_of_NodeInfo (nodeInfo_of_ident id)

end
