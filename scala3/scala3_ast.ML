(* Abstract syntax of Scala 3, following the "Scala 3 Syntax Summary"
   (https://docs.scala-lang.org/scala3/reference/syntax.html), restricted to
   what the brace-delimited language needs (see Scala3_Parser.thy for what is
   and is not covered).

   As for occam 2 (occam2_ast.ML) there is no pre-existing reference AST to
   port, so the one below is a design of this project's own: one datatype per
   syntactic category of the syntax summary, one constructor per alternative,
   close enough to the concrete syntax that "pp_root" (below) can print any
   parsed program back as Scala text. What is shared with C11 and occam 2 - and
   so with everything built on them: the comment/antiquotation attachment
   mechanism, the navigation language, the environment - is the
   position-annotation machinery ("'a nodeInfo", "'a comment", "navi", "'a
   ident"), identical in shape to its namesakes.

   Where the grammar is ambiguous without semantic information, the AST follows
   the grammar's syntactic reading and leaves the resolution to later analysis:
   a bare alphanumeric name in a pattern is a variable binder ("PVar") only if
   it starts with a lower-case letter, otherwise a reference to a stable
   identifier ("PRef"), exactly as in the language definition; "f(x)" is an
   application ("EApply") whether "f" is a method, a function value or a
   constructor.

   Layout is not part of the AST. Statements are separated by newlines or
   semicolons in the source; the parser's layout stage (Scala3_Parser.thy)
   infers the separators, and "pp_root" prints canonical, brace-delimited text.
   *)

structure Scala3_Ast = struct

datatype navi = up | Up | right | down

datatype 'a comment = Raw_txt of (string*'a) list
                    | Antiquotation
                        of {tag : string * 'a} * navi
                          list * {level : int} * {cartouche : string * 'a}

datatype 'a nodeInfo = OnlyPos of 'a | NodeInfo of 'a comment list * 'a

datatype 'a ident = Ident of string * int * 'a nodeInfo

(* Modifiers (the "inline"/"opaque"/"open"/"transparent"/"infix" ones are soft
   keywords). *)
datatype modifier =
    MAbstract | MFinal | MSealed | MOpen | MImplicit | MLazy | MInline
      | MTransparent | MInfix
  | MOverride | MOpaque
  | MPrivate of string option | MProtected of string option

datatype classKind = KClass | KTrait | KObject | KEnum | KCaseClass
  | KCaseObject | KPackageObject

datatype clauseKind = CPlain | CUsing | CImplicit

datatype 'a sLit =
    LInt of string * 'a
      nodeInfo                          (* as written, including sign,
                                         base prefix, suffix *)
  | LFloat of string * 'a nodeInfo
  | LChar of string * 'a
      nodeInfo                         (* between the quotes, as written *)
  | LString
      of string * bool * 'a
        nodeInfo                (* between the quotes,
                                 as written; true: """ ... """ *)
  | LInterp
      of string * string * bool * 'a
        nodeInfo       (* prefix, raw body between the quotes, multi-line *)
  | LBool of bool * 'a nodeInfo
  | LNull of 'a nodeInfo

datatype 'a sType =
    TName of 'a ident
  | TSelect of 'a sType * 'a ident * 'a nodeInfo          (* T.id *)
  | TSingleton of 'a sExpr * 'a nodeInfo                  (* p.type *)
  | TProject of 'a sType * 'a ident * 'a nodeInfo         (* T#id *)
  | TApply of 'a sType * 'a sType list * 'a nodeInfo      (* T[A, B] *)
  | TTuple of 'a sType list * 'a nodeInfo                 (* (A, B), also () *)
  | TFun of bool * 'a sType list * 'a sType * 'a nodeInfo
      (* true: context function ?=>; (A, B) => C *)
  | TByName of 'a sType * 'a nodeInfo                     (* => T *)
  | TRepeated of 'a sType * 'a nodeInfo                   (* T* *)
  | TInfix of 'a sType * 'a ident * 'a sType * 'a nodeInfo
  | TWith of 'a sType * 'a sType * 'a nodeInfo            (* A with B *)
  | TRefine of 'a sType option * 'a sStat list * 'a nodeInfo  (* A { decls } *)
  | TAnnot of 'a sType * 'a sAnnot list * 'a nodeInfo     (* T @ann *)
  | TWild of 'a sTypeBounds * 'a nodeInfo                 (* _ >: L <: U, ? *)
  | TLit of 'a sLit * 'a nodeInfo
  | TLambda of 'a sTypeParam list * 'a sType * 'a nodeInfo   (* [X] =>> T *)
  | TPolyFun of 'a sTypeParam list * 'a sType * 'a nodeInfo  (* [X] => T *)
  | TMatch of 'a sType * 'a sTypeCase list * 'a nodeInfo

and 'a sTypeCase = TypeCase
  of 'a sType option * 'a sType * 'a nodeInfo   (* NONE: the case "_" *)

and 'a sTypeBounds = Bounds
  of 'a sType option * 'a sType option           (* >: lower, <: upper *)

and 'a sTypeParam =
    TParam of 'a sAnnot list * int * 'a ident * 'a sTypeParam list * 'a
      sTypeBounds * 'a sType list * 'a nodeInfo
    (* annotations, variance (0 invariant, 1 covariant "+", 2 contravariant
       "-"), name ("_" for an anonymous one), higher-kinded parameters, bounds,
       context bounds *)

and 'a sParam =
    Param of 'a sAnnot list * modifier list * int * 'a ident option * 'a
      sType * 'a sExpr option * 'a nodeInfo
    (* annotations, modifiers, 0 plain / 1 val / 2 var (class parameters), name
       (NONE: a "using" clause of bare types), type, default value *)

and 'a sClause =
    PClause of clauseKind * 'a sParam list * 'a nodeInfo
  | TClause of 'a sTypeParam list * 'a nodeInfo           (* [T, U] *)

and 'a sArg =
    AExpr of 'a sExpr
  | ANamed of 'a ident * 'a sExpr * 'a nodeInfo           (* id = e *)

and 'a sBinding = Binding
  of 'a ident option * 'a sType option * 'a nodeInfo   (* NONE: "_" *)

and 'a sExpr =
    EIdent of 'a ident
  | ESelect of 'a sExpr * 'a ident * 'a nodeInfo          (* e.id *)
  | EThis of 'a ident option * 'a nodeInfo                (* [C.]this *)
  | ESuper of 'a ident option * 'a ident option * 'a
      nodeInfo   (* [C.]super[T] *)
  | ELit of 'a sLit
  | EApply of 'a sExpr * 'a sArg list * bool * 'a
      nodeInfo      (* f(args); true: (using args) *)
  | ETypeApply of 'a sExpr * 'a sType list * 'a nodeInfo        (* e[T] *)
  | EInfix of 'a sExpr * 'a ident * 'a sExpr * 'a nodeInfo
  | EPrefix
      of 'a ident * 'a sExpr * 'a nodeInfo                (* -e, +e, ~e, !e *)
  | EPostfix of 'a sExpr * 'a ident * 'a nodeInfo
  | EAssign of 'a sExpr * 'a sExpr * 'a nodeInfo
  | ETyped of 'a sExpr * 'a sType * 'a nodeInfo                 (* e: T *)
  | EAnnotated of 'a sExpr * 'a sAnnot list * 'a nodeInfo       (* e: @ann *)
  | ESplat of 'a sExpr * 'a nodeInfo                            (* e: _* *)
  | ELambda
      of 'a sBinding list * 'a sExpr * bool * 'a
        nodeInfo  (* (x, y) => e; true: ?=> *)
  | EBlock of 'a sStat list * 'a nodeInfo                       (* { stats } *)
  | ECases of 'a sCase list * 'a
      nodeInfo                       (* { case p => e } *)
  | EIf of 'a sExpr * 'a sExpr * 'a sExpr option * 'a nodeInfo
  | EWhile of 'a sExpr * 'a sExpr * 'a nodeInfo
  | ETry of 'a sExpr * 'a sExpr option * 'a sExpr option * 'a nodeInfo
    (* body, handler (an ECases, or an expression), finalizer *)
  | EThrow of 'a sExpr * 'a nodeInfo
  | EReturn of 'a sExpr option * 'a nodeInfo
  | EFor of 'a sEnum list * bool * 'a sExpr * 'a nodeInfo      (* true: yield *)
  | EMatch of 'a sExpr * 'a sCase list * 'a nodeInfo
  | ENew of 'a sParent list * 'a sTemplateBody option * 'a nodeInfo
  | ETuple of 'a sExpr list * 'a
      nodeInfo                       (* () is ETuple [] *)
  | EParen of 'a sExpr * 'a nodeInfo
  | EPlaceholder of 'a nodeInfo                                 (* _ *)

and 'a sCase = Case
  of 'a sPat * 'a sExpr option * 'a sStat list * 'a
    nodeInfo   (* pattern, guard, body *)

and 'a sEnum =
    EnGen of bool * 'a sPat * 'a sExpr * 'a
      nodeInfo           (* [case] p <- e *)
  | EnGuard of 'a sExpr * 'a nodeInfo                          (* if e *)
  | EnVal of 'a sPat * 'a sExpr * 'a nodeInfo                  (* p = e *)

and 'a sPat =
    PVar of 'a
      ident                                           (* a lower-case binder *)
  | PWild of 'a nodeInfo
  | PLit of 'a sLit
  | PRef of 'a
      sExpr                                           (* a stable
          identifier: A, a.B, `x` *)
  | PApply of 'a sExpr * 'a sType list * 'a sPat list * 'a
      nodeInfo   (* Foo[T](p, q) *)
  | PTuple of 'a sPat list * 'a nodeInfo
  | PInfix of 'a sPat * 'a ident * 'a sPat * 'a nodeInfo
  | PAlt of 'a sPat list * 'a nodeInfo
  | PBind of 'a ident * 'a sPat * 'a nodeInfo                  (* x @ p *)
  | PTyped of 'a sPat * 'a sType * 'a nodeInfo                 (* p: T *)
  | PSplat of 'a sPat * 'a
      nodeInfo                            (* xs* in an argument list *)
  | PGiven of 'a sType * 'a nodeInfo

and 'a sAnnot = Annot of 'a sType * 'a sArg list list * 'a nodeInfo

and 'a sParent = Parent
  of 'a sType * 'a sArg list list * bool list * 'a nodeInfo
    (* the type, the argument lists, and for each list whether it was written
       (using ...) *)

and 'a sSelf = Self of 'a ident * 'a sType option * 'a nodeInfo

and 'a sTemplateBody = TemplateBody
  of 'a sSelf option * 'a sStat list * 'a nodeInfo

and 'a sTemplate = Template
  of 'a sParent list * 'a ident list * 'a sTemplateBody option * 'a nodeInfo
    (* parents, "derives" classes, body *)

and 'a sSelector =
    SelName of 'a ident * 'a ident option * 'a
      nodeInfo        (* a [as b | => b], "_" as target = hiding *)
  | SelWild of 'a nodeInfo                                     (* * or _ *)
  | SelGiven of 'a sType option * 'a nodeInfo

and 'a sImport = ImportExpr of 'a sExpr * 'a sSelector list * 'a nodeInfo

and 'a sStat =
    SExpr of 'a sExpr
  | SImport
      of bool * 'a sImport list * 'a nodeInfo            (* true: export *)
  | SDef of 'a sDef

and 'a sDef =
    DVal of 'a sAnnot list * modifier list * bool * 'a sPat list * 'a sType
      option * 'a sExpr option * 'a nodeInfo
    (* val/var (true: var), patterns (several names: "val a, b: T"), type,
       right-hand side (NONE: a declaration, or "= _" is an EPlaceholder) *)
  | DDef of 'a sAnnot list * modifier list * 'a ident * 'a sClause list * 'a
      sType option * 'a sExpr option * 'a nodeInfo
    (* the name of a secondary constructor is "this" *)
  | DType of 'a sAnnot list * modifier list * 'a ident * 'a sClause list * 'a
      sTypeBounds * 'a sType option * 'a nodeInfo
  | DClass of 'a sAnnot list * modifier list * classKind * 'a ident * 'a
      sTypeParam list
              * modifier list * 'a sClause list * 'a sTemplate * 'a nodeInfo
    (* annotations, modifiers, kind, name, type parameters, constructor
       modifiers (private, annotations are dropped), constructor parameter
       clauses, template *)
  | DGiven of 'a sAnnot list * modifier list * 'a ident option * 'a sClause
      list * 'a sType
              * 'a sExpr option * 'a sTemplateBody option * 'a sParent
                list * 'a nodeInfo
    (* name, parameter clauses of a conditional given, the given type, "= e" or
       a template *)
  | DExtension of 'a sClause list * 'a sStat list * 'a nodeInfo
    (* clauses (type parameters, using clauses, the receiver parameter, further
       using clauses), the extension methods *)
  | DEnumCase
      of 'a sAnnot list * modifier list * 'a ident list * 'a sTypeParam
        list * 'a sClause list
                 * 'a sParent list * 'a nodeInfo
    (* "case A, B" or "case C(x: Int) extends E" *)
  | DPackage of 'a sExpr * 'a sStat list option * 'a nodeInfo
    (* package a.b; or package a.b { ... } *)

(* What a parse produces, by entry point. *)
datatype 'a root =
    Id of 'a ident
  | Expr of 'a sExpr
  | Type of 'a sType
  | Stat of 'a
      sStat          (* never produced by a parse: the closest context
                      of an annotation on a definition *)
  | Pat of 'a sPat            (* likewise *)
  | Unit of 'a sStat list     (* a compilation unit *)

(* --- Positions ---------------------------------------------------------- *)

fun pos_of_NodeInfo (OnlyPos pos) = pos
  | pos_of_NodeInfo (NodeInfo (_, pos)) = pos

fun comments_of_NodeInfo (OnlyPos _) = []
  | comments_of_NodeInfo (NodeInfo (cs, _)) = cs

fun nodeInfo_of_ident (Ident (_, _, ni)) = ni
fun ident_name (Ident (s, _, _)) = s

fun nodeInfo_of_lit l = (case l of
    LInt (_, ni) => ni | LFloat (_, ni) => ni | LChar (_, ni) =>
      ni | LString (_, _, ni) => ni
  | LInterp (_, _, _, ni) => ni | LBool (_, ni) => ni | LNull ni => ni)

fun nodeInfo_of_type t = (case t of
    TName id => nodeInfo_of_ident id | TSelect (_, _, ni) =>
      ni | TSingleton (_, ni) => ni
  | TProject (_, _, ni) => ni | TApply (_, _, ni) => ni | TTuple (_, ni) => ni
  | TFun (_, _, _, ni) => ni | TByName (_, ni) => ni | TRepeated (_, ni) => ni
  | TInfix (_, _, _, ni) => ni | TWith (_, _, ni) => ni | TRefine (_, _, ni) =>
    ni
  | TAnnot (_, _, ni) => ni | TWild (_, ni) => ni | TLit (_, ni) =>
    ni | TLambda (_, _, ni) => ni
  | TPolyFun (_, _, ni) => ni | TMatch (_, _, ni) => ni)

fun nodeInfo_of_expr e = (case e of
    EIdent id => nodeInfo_of_ident id | ESelect (_, _, ni) =>
      ni | EThis (_, ni) => ni
  | ESuper (_, _, ni) => ni | ELit l =>
    nodeInfo_of_lit l | EApply (_, _, _, ni) => ni
  | ETypeApply (_, _, ni) => ni | EInfix (_, _, _, ni) =>
    ni | EPrefix (_, _, ni) => ni
  | EPostfix (_, _, ni) => ni | EAssign (_, _, ni) => ni | ETyped (_, _, ni) =>
    ni
  | EAnnotated (_, _, ni) => ni | ESplat (_, ni) =>
    ni | ELambda (_, _, _, ni) => ni
  | EBlock (_, ni) => ni | ECases (_, ni) => ni | EIf (_, _, _, ni) =>
    ni | EWhile (_, _, ni) => ni
  | ETry (_, _, _, ni) => ni | EThrow (_, ni) => ni | EReturn (_, ni) =>
    ni | EFor (_, _, _, ni) => ni
  | EMatch (_, _, ni) => ni | ENew (_, _, ni) => ni | ETuple (_, ni) =>
    ni | EParen (_, ni) => ni
  | EPlaceholder ni => ni)

fun nodeInfo_of_pat p = (case p of
    PVar id => nodeInfo_of_ident id | PWild ni => ni | PLit l =>
      nodeInfo_of_lit l
  | PRef e => nodeInfo_of_expr e | PApply (_, _, _, ni) =>
    ni | PTuple (_, ni) => ni
  | PInfix (_, _, _, ni) => ni | PAlt (_, ni) => ni | PBind (_, _, ni) => ni
  | PTyped (_, _, ni) => ni | PSplat (_, ni) => ni | PGiven (_, ni) => ni)

fun nodeInfo_of_def d = (case d of
    DVal (_, _, _, _, _, _, ni) => ni | DDef (_, _, _, _, _, _, ni) => ni
  | DType (_, _, _, _, _, _, ni) => ni | DClass (_, _, _, _, _, _, _, _, ni) =>
    ni
  | DGiven (_, _, _, _, _, _, _, _, ni) => ni | DExtension (_, _, ni) => ni
  | DEnumCase (_, _, _, _, _, _, ni) => ni | DPackage (_, _, ni) => ni)

fun nodeInfo_of_stat s = (case s of
    SExpr e => nodeInfo_of_expr e | SImport (_, _, ni) => ni | SDef d =>
      nodeInfo_of_def d)

fun pos_of_expr e = pos_of_NodeInfo (nodeInfo_of_expr e)
fun pos_of_type t = pos_of_NodeInfo (nodeInfo_of_type t)
fun pos_of_pat p = pos_of_NodeInfo (nodeInfo_of_pat p)
fun pos_of_stat s = pos_of_NodeInfo (nodeInfo_of_stat s)
fun pos_of_ident id = pos_of_NodeInfo (nodeInfo_of_ident id)

end
