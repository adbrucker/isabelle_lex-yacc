(* Abstract syntax of Java 25, following "The Java Language Specification, Java SE 25 Edition"
   (chapter 19, Syntax): one datatype per syntactic category, one constructor per alternative,
   close enough to the concrete syntax that "pp_root" (java_pp.ML) can print any parsed program
   back as Java text. What is shared with C11 and the other members of the family - the
   comment/antiquotation attachment mechanism, the navigation language, the environment - is the
   position-annotation machinery ("'a nodeInfo", "'a comment", "navi", "'a ident"), identical in
   shape to its namesakes.

   Unlike Go (where a type is an expression) Java keeps types and expressions apart in its
   grammar, and so does this tree - with one exception that the language forces on every parser:
   a dotted name "a.b.c" in an expression can denote a package, a type, a variable or a field, and
   nothing in the syntax tells which; it is read as a chain of "EName" and "EField", as in the
   tree of javac, and the analysis tells what it denotes. The same holds for the target of a method
   reference ("Foo::bar") and for the qualifier of a method call. *)

structure Java_Ast = struct

datatype navi = up | Up | right | down

datatype 'a comment = Raw_txt of (string*'a) list
                    | Antiquotation of {tag : string * 'a} * navi list * {level : int}
                                       * {cartouche : string * 'a}

datatype 'a nodeInfo = OnlyPos of 'a | NodeInfo of 'a comment list * 'a

datatype 'a ident = Ident of string * int * 'a nodeInfo

datatype binop =
    LOr | LAnd | BOr | BXor | BAnd | Eq | Ne | Lt | Gt | Le | Ge
  | Shl | Shr | UShr | Add | Sub | Mul | Div | Rem

datatype unop = UPlus | UMinus | UNot | UCompl | PreInc | PreDec | PostInc | PostDec

datatype lit =
    LInt of string            (* the literals, as written *)
  | LFloat of string
  | LChar of string
  | LString of string
  | LTextBlock of string
  | LBool of bool
  | LNull

datatype 'a jModifier =
    MKw of string * 'a nodeInfo     (* public, static, final, sealed, non-sealed, default, ... *)
  | MAnnot of 'a jAnnot

and 'a jAnnot = Annot of 'a ident list * 'a jAnnotArgs * 'a nodeInfo    (* @a.b.C(...) *)

and 'a jAnnotArgs =
    NoArgs                                                 (* a marker annotation *)
  | Single of 'a jElemValue                                (* @A(v) *)
  | Pairs of ('a ident * 'a jElemValue) list               (* @A(x = v, y = w) *)

and 'a jElemValue =
    EVExpr of 'a jExpr
  | EVArray of 'a jElemValue list * bool * 'a nodeInfo        (* the flag: a trailing comma *)
  | EVAnnot of 'a jAnnot

(* --- Types ----------------------------------------------------------------------------------- *)

and 'a jType =
    TPrim of 'a jAnnot list * string * 'a nodeInfo         (* int, boolean, ..., and void *)
  | TClass of 'a jAnnot list * 'a jTSeg list * 'a nodeInfo (* a.b.C<T>.D: the segments *)
  | TArray of 'a jType * 'a jDim list * 'a nodeInfo        (* the element type, the dimensions *)
  | TVar of 'a nodeInfo                                    (* var *)

and 'a jTSeg = TSeg of 'a ident * 'a jTArgs option

and 'a jTArgs = TArgs of 'a jTArg list * 'a nodeInfo       (* the empty list: the diamond "<>" *)

and 'a jTArg =
    TAType of 'a jType
  | TAWild of 'a jAnnot list * (bool * 'a jType) option * 'a nodeInfo
      (* "?", "? extends T" (true), "? super T" (false) *)

and 'a jDim = Dim of 'a jAnnot list * 'a nodeInfo          (* [] *)

and 'a jTParam = TParam of 'a jAnnot list * 'a ident * 'a jType list * 'a nodeInfo
    (* T extends A & B: the bounds *)

(* --- Expressions ------------------------------------------------------------------------------ *)

and 'a jExpr =
    ELit of lit * 'a nodeInfo
  | EName of 'a ident                                      (* a simple name *)
  | EField of 'a jExpr * 'a ident * 'a nodeInfo            (* e.f, and the qualified name a.b *)
  | EThis of 'a nodeInfo
  | ESuper of 'a nodeInfo                                  (* only as the qualifier of a member *)
  | EQualThis of 'a jExpr * 'a nodeInfo                    (* T.this *)
  | EQualSuper of 'a jExpr * 'a nodeInfo                   (* T.super, as a qualifier *)
  | EParen of 'a jExpr * 'a nodeInfo
  | EIndex of 'a jExpr * 'a jExpr * 'a nodeInfo
  | ECall of 'a jExpr option * 'a jTArgs option * 'a ident * 'a jExpr list * 'a nodeInfo
      (* receiver, explicit type arguments, method name, arguments *)
  | ENew of 'a jExpr option * 'a jType * 'a jExpr list * 'a jDecl list option * 'a nodeInfo
      (* outer.new T(args) { body } *)
  | ENewArray of 'a jType * 'a jExpr list * 'a jDim list * 'a jExpr option * 'a nodeInfo
      (* new T[e1][e2][]..., or new T[]...{init} (the last component, an EArrayInit) *)
  | EArrayInit of 'a jExpr list * bool * 'a nodeInfo     (* {a, b, c}; flag: a trailing comma *)
  | EClassLit of 'a jType * 'a nodeInfo                    (* T.class *)
  | EMethodRef of 'a jMRTarget * 'a jTArgs option * 'a ident * 'a nodeInfo
      (* T::name (name is "new" for a constructor reference) *)
  | ELambda of 'a jLParam list * bool * 'a jLBody * 'a nodeInfo
      (* the flag: the parameters are in parentheses *)
  | EUnary of unop * 'a jExpr * 'a nodeInfo
  | EBinary of binop * 'a jExpr * 'a jExpr * 'a nodeInfo
  | EAssign of 'a jExpr * binop option * 'a jExpr * 'a nodeInfo   (* NONE: plain = *)
  | ECond of 'a jExpr * 'a jExpr * 'a jExpr * 'a nodeInfo
  | ECast of 'a jType list * 'a jExpr * 'a nodeInfo        (* more than one type: an intersection *)
  | EInstanceof of 'a jExpr * 'a jPattern * 'a nodeInfo  (* a plain type: a PType without name *)
  | ESwitch of 'a jExpr * 'a jSwitchCase list * 'a nodeInfo

and 'a jMRTarget = MRExpr of 'a jExpr | MRType of 'a jType

and 'a jLParam =
    LPInfer of 'a ident                                    (* x -> ..., (x, y) -> ... *)
  | LPTyped of 'a jParam

and 'a jLBody = LBExpr of 'a jExpr | LBBlock of 'a jBlock

(* --- Patterns and switch -------------------------------------------------------------------- *)

and 'a jPattern =
    PType of 'a jModifier list * 'a jType * 'a ident option * 'a nodeInfo
      (* "final Foo f"; without a name only as the right side of instanceof *)
  | PRecord of 'a jType * 'a jPattern list * 'a nodeInfo
  | PAny of 'a nodeInfo                                    (* _ *)

and 'a jCaseItem =
    CIExpr of 'a jExpr                                     (* a constant, also null *)
  | CIPattern of 'a jPattern
  | CIDefault                                              (* "case null, default" *)

and 'a jLabel =
    LCase of 'a jCaseItem list * 'a jExpr option * 'a nodeInfo    (* items, guard *)
  | LDefault of 'a nodeInfo

and 'a jSwitchCase =
    SwRule of 'a jLabel * 'a jRuleBody * 'a nodeInfo
  | SwGroup of 'a jLabel list * 'a jStmt list * 'a nodeInfo

and 'a jRuleBody = RBExpr of 'a jExpr | RBBlock of 'a jBlock | RBThrow of 'a jStmt

(* --- Statements ----------------------------------------------------------------------------- *)

and 'a jStmt =
    SBlock of 'a jBlock
  | SLocal of 'a jLocalVar
  | SClassDecl of 'a jDecl
  | SEmpty of 'a nodeInfo
  | SExpr of 'a jExpr * 'a nodeInfo
  | SLabeled of 'a ident * 'a jStmt * 'a nodeInfo
  | SIf of 'a jExpr * 'a jStmt * 'a jStmt option * 'a nodeInfo
  | SWhile of 'a jExpr * 'a jStmt * 'a nodeInfo
  | SDo of 'a jStmt * 'a jExpr * 'a nodeInfo
  | SFor of 'a jForInit option * 'a jExpr option * 'a jExpr list * 'a jStmt * 'a nodeInfo
  | SForEach of 'a jModifier list * 'a jType * 'a ident * 'a jExpr * 'a jStmt * 'a nodeInfo
  | SBreak of 'a ident option * 'a nodeInfo
  | SContinue of 'a ident option * 'a nodeInfo
  | SReturn of 'a jExpr option * 'a nodeInfo
  | SThrow of 'a jExpr * 'a nodeInfo
  | SYield of 'a jExpr * 'a nodeInfo
  | SAssert of 'a jExpr * 'a jExpr option * 'a nodeInfo
  | SSync of 'a jExpr * 'a jBlock * 'a nodeInfo
  | STry of 'a jResource list * bool * 'a jBlock * 'a jCatch list * 'a jBlock option * 'a nodeInfo
      (* resources, whether the last is followed by ";", body, catches, finally *)
  | SSwitch of 'a jExpr * 'a jSwitchCase list * 'a nodeInfo
  | SCtorCall of 'a jExpr option * 'a jTArgs option * bool * 'a jExpr list * 'a nodeInfo
      (* this(...) (false) or [qualifier.]super(...) (true) *)

and 'a jBlock = Block of 'a jStmt list * 'a nodeInfo

and 'a jLocalVar = LocalVar of 'a jModifier list * 'a jType * 'a jVarDecl list * 'a nodeInfo

and 'a jVarDecl = VarDecl of 'a ident * 'a jDim list * 'a jExpr option * 'a nodeInfo

and 'a jForInit = FIVars of 'a jLocalVar | FIExprs of 'a jExpr list

and 'a jResource = RDecl of 'a jLocalVar | RExpr of 'a jExpr

and 'a jCatch = Catch of 'a jModifier list * 'a jType list * 'a ident * 'a jBlock * 'a nodeInfo

(* --- Declarations --------------------------------------------------------------------------- *)

and 'a jParam =
    Param of 'a jModifier list * 'a jType * bool * 'a ident * 'a jDim list * 'a nodeInfo
      (* modifiers, type, variable arity ("T... x"), name ("_" or "this" too), extra dimensions *)

and 'a jEnumConst =
    EnumConst of 'a jAnnot list * 'a ident * 'a jExpr list option * 'a jDecl list option
                 * 'a nodeInfo

and 'a jDecl =
    DClass of 'a jModifier list * 'a ident * 'a jTParam list * 'a jType option * 'a jType list
              * 'a jType list * 'a jDecl list * 'a nodeInfo
      (* modifiers, name, type parameters, extends, implements, permits, body *)
  | DInterface of 'a jModifier list * 'a ident * 'a jTParam list * 'a jType list * 'a jType list
                  * 'a jDecl list * 'a nodeInfo
      (* modifiers, name, type parameters, extends, permits, body *)
  | DEnum of 'a jModifier list * 'a ident * 'a jType list * 'a jEnumConst list * (bool * bool)
             * 'a jDecl list * 'a nodeInfo
      (* the flags: a comma after the last constant, a semicolon after the constants *)
  | DRecord of 'a jModifier list * 'a ident * 'a jTParam list * 'a jParam list * 'a jType list
               * 'a jDecl list * 'a nodeInfo
      (* modifiers, name, type parameters, components, implements, body *)
  | DAnnotType of 'a jModifier list * 'a ident * 'a jDecl list * 'a nodeInfo   (* @interface *)
  | DField of 'a jModifier list * 'a jType * 'a jVarDecl list * 'a nodeInfo
  | DMethod of 'a jModifier list * 'a jTParam list * 'a jType * 'a ident * 'a jParam list
               * 'a jDim list * 'a jType list * 'a jBlock option * 'a jElemValue option
               * 'a nodeInfo
      (* modifiers, type parameters, result, name, parameters, extra dimensions, throws, body,
         the default value of an annotation element *)
  | DCtor of 'a jModifier list * 'a jTParam list * 'a ident * 'a jParam list * 'a jType list
             * 'a jBlock * 'a nodeInfo
  | DCompact of 'a jModifier list * 'a ident * 'a jBlock * 'a nodeInfo    (* of a record *)
  | DInit of bool * 'a jBlock * 'a nodeInfo                              (* true: static *)
  | DEmpty of 'a nodeInfo

datatype importKind = ImSingle | ImDemand | ImStaticSingle | ImStaticDemand | ImModule

datatype 'a jImport = Import of importKind * 'a ident list * 'a nodeInfo

datatype 'a jModDir =
    Requires of string list * 'a ident list * 'a nodeInfo        (* modifiers, module *)
  | Exports of 'a ident list * 'a ident list list * 'a nodeInfo  (* package, to modules *)
  | Opens of 'a ident list * 'a ident list list * 'a nodeInfo
  | Uses of 'a ident list * 'a nodeInfo
  | Provides of 'a ident list * 'a ident list list * 'a nodeInfo

datatype 'a jUnitBody =
    Types of 'a jDecl list      (* classes; with methods and fields: a compact source file *)
  | Module of 'a jAnnot list * bool * 'a ident list * 'a jModDir list * 'a nodeInfo

datatype 'a jUnit =
    Unit of ('a jAnnot list * 'a ident list) option * 'a jImport list * 'a jUnitBody * 'a nodeInfo

(* What a parse produces, by entry point. *)
datatype 'a root =
    Id of 'a ident
  | Expr of 'a jExpr
  | Type of 'a jType
  | Stmts of 'a jStmt list     (* a block statement list *)
  | Decls of 'a jDecl list     (* class body declarations / top-level declarations *)
  | Source of 'a jUnit         (* a compilation unit *)
  | Stmt of 'a jStmt           (* never produced by a parse: the closest context of a statement *)
  | Decl of 'a jDecl           (* likewise, for a declaration *)

(* --- Positions ----------------------------------------------------------------------------- *)

fun pos_of_NodeInfo (OnlyPos pos) = pos
  | pos_of_NodeInfo (NodeInfo (_, pos)) = pos

fun comments_of_NodeInfo (OnlyPos _) = []
  | comments_of_NodeInfo (NodeInfo (cs, _)) = cs

fun nodeInfo_of_ident (Ident (_, _, ni)) = ni
fun ident_name (Ident (s, _, _)) = s

fun nodeInfo_of_annot (Annot (_, _, ni)) = ni

fun nodeInfo_of_type t = (case t of
    TPrim (_, _, ni) => ni | TClass (_, _, ni) => ni | TArray (_, _, ni) => ni | TVar ni => ni)

fun nodeInfo_of_expr e = (case e of
    ELit (_, ni) => ni | EName id => nodeInfo_of_ident id | EField (_, _, ni) => ni
  | EThis ni => ni | ESuper ni => ni | EQualThis (_, ni) => ni | EQualSuper (_, ni) => ni
  | EParen (_, ni) => ni | EIndex (_, _, ni) => ni | ECall (_, _, _, _, ni) => ni
  | ENew (_, _, _, _, ni) => ni | ENewArray (_, _, _, _, ni) => ni | EArrayInit (_, _, ni) => ni
  | EClassLit (_, ni) => ni | EMethodRef (_, _, _, ni) => ni | ELambda (_, _, _, ni) => ni
  | EUnary (_, _, ni) => ni | EBinary (_, _, _, ni) => ni | EAssign (_, _, _, ni) => ni
  | ECond (_, _, _, ni) => ni | ECast (_, _, ni) => ni | EInstanceof (_, _, ni) => ni
  | ESwitch (_, _, ni) => ni)

fun nodeInfo_of_block (Block (_, ni)) = ni

fun nodeInfo_of_pattern p = (case p of
    PType (_, _, _, ni) => ni | PRecord (_, _, ni) => ni | PAny ni => ni)

fun nodeInfo_of_localvar (LocalVar (_, _, _, ni)) = ni

fun nodeInfo_of_decl d = (case d of
    DClass (_, _, _, _, _, _, _, ni) => ni | DInterface (_, _, _, _, _, _, ni) => ni
  | DEnum (_, _, _, _, _, _, ni) => ni | DRecord (_, _, _, _, _, _, ni) => ni
  | DAnnotType (_, _, _, ni) => ni | DField (_, _, _, ni) => ni
  | DMethod (_, _, _, _, _, _, _, _, _, ni) => ni | DCtor (_, _, _, _, _, _, ni) => ni
  | DCompact (_, _, _, ni) => ni | DInit (_, _, ni) => ni | DEmpty ni => ni)

fun nodeInfo_of_stmt s = (case s of
    SBlock b => nodeInfo_of_block b | SLocal lv => nodeInfo_of_localvar lv
  | SClassDecl d => nodeInfo_of_decl d | SEmpty ni => ni | SExpr (_, ni) => ni
  | SLabeled (_, _, ni) => ni | SIf (_, _, _, ni) => ni | SWhile (_, _, ni) => ni
  | SDo (_, _, ni) => ni | SFor (_, _, _, _, ni) => ni | SForEach (_, _, _, _, _, ni) => ni
  | SBreak (_, ni) => ni | SContinue (_, ni) => ni | SReturn (_, ni) => ni | SThrow (_, ni) => ni
  | SYield (_, ni) => ni | SAssert (_, _, ni) => ni | SSync (_, _, ni) => ni
  | STry (_, _, _, _, _, ni) => ni | SSwitch (_, _, ni) => ni | SCtorCall (_, _, _, _, ni) => ni)

fun pos_of_expr e = pos_of_NodeInfo (nodeInfo_of_expr e)
fun pos_of_type t = pos_of_NodeInfo (nodeInfo_of_type t)
fun pos_of_decl d = pos_of_NodeInfo (nodeInfo_of_decl d)
fun pos_of_stmt s = pos_of_NodeInfo (nodeInfo_of_stmt s)
fun pos_of_ident id = pos_of_NodeInfo (nodeInfo_of_ident id)

end
