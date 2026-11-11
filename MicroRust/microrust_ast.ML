(* Abstract syntax of MicroRust: the Rust subset of AutoCorrode's "uRust"
   (https://github.com/awslabs/AutoCorrode, Micro_Rust_Parsing_Frontend/Micro_Rust_Syntax.thy),
   extended by a thin layer of Rust items (fn, struct, enum, impl, trait, const, static, type, use,
   mod) so that a whole source file can be read, not only a function body.

   There is no official, machine-usable grammar of Rust (rustc is the specification; the Rust
   Reference is a PEG-style notation, rust-analyzer's "rust.ungram" describes tree shapes only).
   The reference for this front-end is therefore the explicit syntax table of uRust (which constructs,
   which priorities) completed with the operator precedences of the Rust Reference; see
   MicroRust_Parser.thy for what is and is not covered.

   As for occam 2 and Scala 3 there is no pre-existing AST to port: this is a design of this project's
   own, one datatype per syntactic category, one constructor per alternative, close enough to the
   concrete syntax that "pp_root" (microrust_pp.ML) can print any parsed program back as Rust text.
   What is shared with the other front-ends is the position-annotation machinery ("'a nodeInfo",
   "'a comment", "navi", "'a ident"), identical in shape to its namesakes.

   Where the grammar is ambiguous without name resolution, the AST follows the syntactic reading and
   leaves the decision to the analysis: a lone identifier in a pattern is a "PIdent" (a binder if it
   starts with a lower-case letter or "_", a reference to a constant or a unit variant otherwise,
   Rust's own naming convention). *)

structure MicroRust_Ast = struct

datatype navi = up | Up | right | down

datatype 'a comment = Raw_txt of (string*'a) list
                    | Antiquotation of {tag : string * 'a} * navi list * {level : int} * {cartouche : string * 'a}

datatype 'a nodeInfo = OnlyPos of 'a | NodeInfo of 'a comment list * 'a

datatype 'a ident = Ident of string * int * 'a nodeInfo

datatype 'a rLit =
    LInt of string * 'a nodeInfo        (* as written, with base prefix, underscores and suffix *)
  | LFloat of string * 'a nodeInfo
  | LChar of string * 'a nodeInfo       (* as written, quotes and "b" prefix included *)
  | LStr of string * 'a nodeInfo        (* as written, quotes and "b"/"r#" prefix included *)
  | LBool of bool * 'a nodeInfo

datatype 'a rAttr = Attr of bool * string * 'a nodeInfo   (* inner "#![..]"?; the text between the brackets *)

datatype 'a rVis = VPriv | VPub of string                 (* VPub "": "pub"; VPub "crate": "pub(crate)" *)

datatype unop = Neg | Not | Deref | Borrow | BorrowMut | BorrowBorrow | BorrowBorrowMut

datatype binop =
    Add | Sub | Mul | Div | Rem | BitAnd | BitOr | BitXor | Shl | Shr
  | And | Or | Eq | Ne | Lt | Le | Gt | Ge

(* "NONE": plain assignment; SOME op: compound assignment "lhs op= rhs". *)
type assignop = binop option

datatype 'a rPath = Path of ('a rType * 'a rPath option) option * bool * 'a rSeg list * 'a nodeInfo
    (* <T as Trait>::seg::seg, with a leading "::" if the bool is true *)

and 'a rSeg = Seg of 'a ident * 'a rGArgs option * 'a nodeInfo

and 'a rGArgs = GArgs of bool * 'a rGArg list     (* true: turbofish "::<..>" *)

and 'a rGArg =
    GType of 'a rType
  | GLifetime of string * 'a nodeInfo
  | GConst of 'a rExpr
  | GBind of 'a ident * 'a rType                  (* Item = T *)

and 'a rType =
    TPath of 'a rPath
  | TRef of string option * bool * 'a rType * 'a nodeInfo     (* &'a mut T; true: mut *)
  | TPtr of bool * 'a rType * 'a nodeInfo                     (* *const T / *mut T; true: mut *)
  | TTuple of 'a rType list * 'a nodeInfo                     (* (A, B), (A,), () *)
  | TSlice of 'a rType * 'a nodeInfo
  | TArray of 'a rType * 'a rExpr * 'a nodeInfo
  | TInfer of 'a nodeInfo                                     (* _ *)
  | TNever of 'a nodeInfo                                     (* ! *)
  | TFn of 'a rType list * 'a rType option * 'a nodeInfo      (* fn(A, B) -> C *)
  | TImpl of 'a rBound list * 'a nodeInfo
  | TDyn of 'a rBound list * 'a nodeInfo
  | THol of string * string * 'a nodeInfo                     (* a HOL type escape, the text between the brackets *)

and 'a rBound =
    BTrait of bool * 'a rPath * 'a nodeInfo       (* true: "?Trait" *)
  | BLifetime of string * 'a nodeInfo

and 'a rExpr =
    ELit of 'a rLit
  | EPath of 'a rPath
  | EHol of string * string * 'a nodeInfo         (* the HOL literal escape: text, subscripts as written *)
  | EEps of string * 'a nodeInfo                  (* the HOL term escape *)
  | ELogLit of string * string * 'a nodeInfo      (* uRust: l, llangle text rrangle - the HOL escape of the logging macros *)
  | ESeq of 'a rBlock * 'a nodeInfo               (* uRust: a parenthesized statement sequence "(a; b; c)" *)
  | EUnary of unop * 'a rExpr * 'a nodeInfo
  | EBinary of binop * 'a rExpr * 'a rExpr * 'a nodeInfo
  | EAssign of assignop * 'a rExpr * 'a rExpr * 'a nodeInfo
  | ECast of 'a rExpr * 'a rType * 'a nodeInfo
  | ETry of 'a rExpr * 'a nodeInfo                (* e? *)
  | ECall of 'a rExpr * 'a rExpr list * 'a nodeInfo
  | EMethod of 'a rExpr * 'a ident * 'a rGArgs option * 'a rExpr list * 'a nodeInfo
  | EField of 'a rExpr * 'a ident * 'a nodeInfo
  | ETupIdx of 'a rExpr * string * 'a nodeInfo    (* e.0 *)
  | EIndex of 'a rExpr * 'a rExpr * 'a nodeInfo
  | ERange of 'a rExpr option * 'a rExpr option * bool * 'a nodeInfo   (* true: inclusive *)
  | ETuple of 'a rExpr list * 'a nodeInfo         (* (a, b), (a,), () *)
  | EParen of 'a rExpr * 'a nodeInfo
  | EArray of 'a rExpr list * 'a nodeInfo
  | ERepeat of 'a rExpr * 'a rExpr * 'a nodeInfo  (* [e; n] *)
  | EStruct of 'a rPath * 'a rFieldInit list * 'a rExpr option * 'a nodeInfo
  | EBlock of string option * 'a rBlock * 'a nodeInfo           (* 'label: { .. } *)
  | EUnsafe of 'a rBlock * 'a nodeInfo
  | EIf of 'a rCond * 'a rBlock * 'a rExpr option * 'a nodeInfo  (* the else part: a block or an if *)
  | EWhile of string option * 'a rCond * 'a rBlock * 'a nodeInfo
  | ELoop of string option * 'a rBlock * 'a nodeInfo
  | EFor of string option * 'a rPat * 'a rExpr * 'a rBlock * 'a nodeInfo
  | EMatch of 'a rExpr * 'a rArm list * 'a nodeInfo
  | EClosure of bool * 'a rClosureParam list * 'a rType option * 'a rExpr * 'a nodeInfo   (* move? *)
  | EReturn of 'a rExpr option * 'a nodeInfo
  | EBreak of string option * 'a rExpr option * 'a nodeInfo
  | EContinue of string option * 'a nodeInfo
  | EYield of 'a nodeInfo                         (* uRust: a breakpoint *)
  | ELog of 'a rExpr * 'a rExpr * 'a nodeInfo     (* uRust: log ⟪a⟫ ⟪b⟫ *)
  | EMacro of 'a rPath * string * 'a rExpr list * 'a nodeInfo   (* name!(..), name![..]; the opening delimiter *)
  | EMacroRepeat of 'a rPath * 'a rExpr * 'a rExpr * 'a nodeInfo   (* vec![e; n] *)
  | EMatches of 'a rExpr * 'a rPat * 'a nodeInfo  (* matches!(e, p) *)
  | EAttr of 'a rAttr list * 'a rExpr * 'a nodeInfo

and 'a rFieldInit = FieldInit of 'a ident * 'a rExpr option * 'a nodeInfo   (* NONE: shorthand "x" *)

and 'a rCond = CExpr of 'a rExpr | CLet of 'a rPat * 'a rExpr * 'a nodeInfo

and 'a rClosureParam = CParam of 'a rPat * 'a rType option * 'a nodeInfo

and 'a rArm = Arm of 'a rAttr list * 'a rPat * 'a rExpr option * 'a rExpr * 'a nodeInfo

and 'a rBlock = Block of 'a rStmt list * 'a rExpr option * 'a nodeInfo

and 'a rStmt =
    SLet of bool * 'a rPat * 'a rType option * 'a rExpr option * 'a rBlock option * 'a nodeInfo
      (* "let", or uRust's "const" binding if the bool is true; the block is the "else" of let-else *)
  | SExpr of 'a rExpr * bool * 'a nodeInfo        (* true: followed by ";" *)
  | SItem of 'a rItem
  | SEmpty of 'a nodeInfo                         (* a lone ";" *)

and 'a rPat =
    PWild of 'a nodeInfo
  | PRest of 'a nodeInfo                          (* .. *)
  | PIdent of bool * bool * 'a ident * 'a rPat option * 'a nodeInfo   (* ref? mut? x (@ p)? *)
  | PLit of bool * 'a rLit * 'a nodeInfo          (* true: negated *)
  | PRange of 'a rPat option * 'a rPat option * bool * 'a nodeInfo
  | PPath of 'a rPath
  | PTupleStruct of 'a rPath * 'a rPat list * 'a nodeInfo
  | PStruct of 'a rPath * 'a rFieldPat list * bool * 'a nodeInfo      (* true: "..", the rest *)
  | PTuple of 'a rPat list * 'a nodeInfo
  | PSlice of 'a rPat list * 'a nodeInfo
  | PRef of bool * 'a rPat * 'a nodeInfo          (* &p, &mut p; true: mut *)
  | PAlt of 'a rPat list * 'a nodeInfo
  | PParen of 'a rPat * 'a nodeInfo
  | PMut of 'a rPat * 'a nodeInfo                  (* uRust: "let mut (x, y) = .." *)
  | PHol of string * string * 'a nodeInfo

and 'a rFieldPat = FieldPat of 'a ident * 'a rPat option * 'a nodeInfo

and 'a rGParam =
    GPLifetime of string * string list * 'a nodeInfo
  | GPType of 'a ident * 'a rBound list * 'a rType option * 'a nodeInfo
  | GPConst of 'a ident * 'a rType * 'a nodeInfo

and 'a rWhere =
    WType of 'a rType * 'a rBound list * 'a nodeInfo
  | WLifetime of string * string list * 'a nodeInfo

and 'a rFnParam =
    PSelf of bool * string option * bool * 'a rType option * 'a nodeInfo   (* &'a mut self: ref?, lifetime, mut?, type *)
  | PParam of 'a rAttr list * 'a rPat * 'a rType * 'a nodeInfo

and 'a rFieldDef = FieldDef of 'a rAttr list * 'a rVis * 'a ident option * 'a rType * 'a nodeInfo

and 'a rFields = FNamed of 'a rFieldDef list | FTuple of 'a rFieldDef list | FUnit

and 'a rVariant = Variant of 'a rAttr list * 'a ident * 'a rFields * 'a rExpr option * 'a nodeInfo

and 'a rUse =
    UName of 'a ident list * 'a ident option * 'a nodeInfo      (* a::b::c (as d) *)
  | UGlob of 'a ident list * 'a nodeInfo                        (* a::b::* *)
  | UGroup of 'a ident list * 'a rUse list * 'a nodeInfo        (* a::b::{..} *)

and 'a rItemKind =
    IFn of string list * 'a ident * 'a rGParam list * 'a rFnParam list * 'a rType option
         * 'a rWhere list * 'a rBlock option                    (* qualifiers: const, unsafe *)
  | IStruct of 'a ident * 'a rGParam list * 'a rWhere list * 'a rFields
  | IEnum of 'a ident * 'a rGParam list * 'a rWhere list * 'a rVariant list
  | IImpl of bool * 'a rGParam list * 'a rPath option * 'a rType * 'a rWhere list * 'a rItem list   (* unsafe? *)
  | ITrait of bool * 'a ident * 'a rGParam list * 'a rBound list * 'a rWhere list * 'a rItem list
  | IConst of 'a ident * 'a rType * 'a rExpr option
  | IStatic of bool * 'a ident * 'a rType * 'a rExpr option
  | ITypeAlias of 'a ident * 'a rGParam list * 'a rBound list * 'a rType option
  | IUse of 'a rUse
  | IMod of 'a ident * 'a rItem list option

and 'a rItem = MkItem of 'a rAttr list * 'a rVis * 'a rItemKind * 'a nodeInfo

(* What a parse produces, by entry point. *)
datatype 'a root =
    Id of 'a ident
  | Expr of 'a rExpr
  | Type of 'a rType
  | Pat of 'a rPat
  | Stmt of 'a rStmt          (* never produced by a parse: the closest context of an annotation on a statement *)
  | Item of 'a rItem          (* likewise *)
  | Body of 'a rBlock         (* a uRust function body: statements and a final expression, without braces *)
  | Crate of 'a rItem list    (* a source file *)

(* --- Positions ---------------------------------------------------------- *)

fun pos_of_NodeInfo (OnlyPos pos) = pos
  | pos_of_NodeInfo (NodeInfo (_, pos)) = pos

fun comments_of_NodeInfo (OnlyPos _) = []
  | comments_of_NodeInfo (NodeInfo (cs, _)) = cs

fun nodeInfo_of_ident (Ident (_, _, ni)) = ni
fun ident_name (Ident (s, _, _)) = s

fun nodeInfo_of_lit l = (case l of
    LInt (_, ni) => ni | LFloat (_, ni) => ni | LChar (_, ni) => ni | LStr (_, ni) => ni | LBool (_, ni) => ni)

fun nodeInfo_of_path (Path (_, _, _, ni)) = ni

fun nodeInfo_of_type t = (case t of
    TPath p => nodeInfo_of_path p | TRef (_, _, _, ni) => ni | TPtr (_, _, ni) => ni
  | TTuple (_, ni) => ni | TSlice (_, ni) => ni | TArray (_, _, ni) => ni | TInfer ni => ni
  | TNever ni => ni | TFn (_, _, ni) => ni | TImpl (_, ni) => ni | TDyn (_, ni) => ni
  | THol (_, _, ni) => ni)

fun nodeInfo_of_expr e = (case e of
    ELit l => nodeInfo_of_lit l | EPath p => nodeInfo_of_path p | EHol (_, _, ni) => ni
  | EEps (_, ni) => ni | ELogLit (_, _, ni) => ni | ESeq (_, ni) => ni | EUnary (_, _, ni) => ni | EBinary (_, _, _, ni) => ni
  | EAssign (_, _, _, ni) => ni | ECast (_, _, ni) => ni | ETry (_, ni) => ni
  | ECall (_, _, ni) => ni | EMethod (_, _, _, _, ni) => ni | EField (_, _, ni) => ni
  | ETupIdx (_, _, ni) => ni | EIndex (_, _, ni) => ni | ERange (_, _, _, ni) => ni
  | ETuple (_, ni) => ni | EParen (_, ni) => ni | EArray (_, ni) => ni | ERepeat (_, _, ni) => ni
  | EStruct (_, _, _, ni) => ni | EBlock (_, _, ni) => ni | EUnsafe (_, ni) => ni
  | EIf (_, _, _, ni) => ni | EWhile (_, _, _, ni) => ni | ELoop (_, _, ni) => ni
  | EFor (_, _, _, _, ni) => ni | EMatch (_, _, ni) => ni | EClosure (_, _, _, _, ni) => ni
  | EReturn (_, ni) => ni | EBreak (_, _, ni) => ni | EContinue (_, ni) => ni | EYield ni => ni
  | ELog (_, _, ni) => ni | EMacro (_, _, _, ni) => ni | EMacroRepeat (_, _, _, ni) => ni
  | EMatches (_, _, ni) => ni | EAttr (_, _, ni) => ni)

fun nodeInfo_of_pat p = (case p of
    PWild ni => ni | PRest ni => ni | PIdent (_, _, _, _, ni) => ni | PLit (_, _, ni) => ni
  | PRange (_, _, _, ni) => ni | PPath p => nodeInfo_of_path p | PTupleStruct (_, _, ni) => ni
  | PStruct (_, _, _, ni) => ni | PTuple (_, ni) => ni | PSlice (_, ni) => ni | PRef (_, _, ni) => ni
  | PAlt (_, ni) => ni | PParen (_, ni) => ni | PMut (_, ni) => ni | PHol (_, _, ni) => ni)

fun nodeInfo_of_block (Block (_, _, ni)) = ni

fun nodeInfo_of_item (MkItem (_, _, _, ni)) = ni

fun nodeInfo_of_stmt s = (case s of
    SLet (_, _, _, _, _, ni) => ni | SExpr (_, _, ni) => ni | SItem it => nodeInfo_of_item it
  | SEmpty ni => ni)

fun pos_of_expr e = pos_of_NodeInfo (nodeInfo_of_expr e)
fun pos_of_type t = pos_of_NodeInfo (nodeInfo_of_type t)
fun pos_of_pat p = pos_of_NodeInfo (nodeInfo_of_pat p)
fun pos_of_stmt s = pos_of_NodeInfo (nodeInfo_of_stmt s)
fun pos_of_item i = pos_of_NodeInfo (nodeInfo_of_item i)
fun pos_of_block b = pos_of_NodeInfo (nodeInfo_of_block b)
fun pos_of_ident id = pos_of_NodeInfo (nodeInfo_of_ident id)

end
