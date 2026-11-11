(* Abstract syntax of occam 2, as defined by the INMOS "occam 2 Reference
   Manual" (1988), appendix G ("Syntax summary").

   Unlike C11 (whose AST is a pruned port of the Haskell "language-c" library,
   via the Isabelle_C AFP entry), there is no pre-existing reference AST for
   occam 2 to port, so the one below is an educated design of this project's
   own: one datatype per syntactic category of the manual's BNF, one
   constructor per alternative, close enough to the concrete syntax that
   "pp_root" (below) can print any parsed program back as legal occam 2 text.
   The deliberately shared pieces with C11's AST (and so with everything
   built on it: the comment/antiquotation attachment mechanism, the
   navigation language, the environment) are the position-annotation
   machinery - "'a nodeInfo" (a bare position, or a position plus the
   comments/antiquotations attached to that node), "'a comment", "navi", and
   "'a ident" - which are, by design, identical in shape to their C11
   namesakes, so that a handler or a tool written against one reads the same
   against the other.

   Where the manual's BNF is ambiguous without semantic information, the AST
   follows the grammar's own syntactic reading and leaves the resolution to
   later analysis:
     - "channel ! tag" and "channel ! expression" are the same syntax for a
       tag that is a bare name; both parse as "POutput" with an expression
       item (a bare "ENamed" element) - only the environment can tell a tag
       from a variable.
     - "actual" (a procedure-instance argument) is "element | expression";
       an element is itself an expression, so every actual is stored as an
       "oExpr" (an "EElem" when it is an element).
   Layout (indentation) is not part of the AST: the parser's layout stage
   (Occam2_Parser.thy) turns it into explicit NEWLINE/INDENT/OUTDENT tokens,
   and "pp_root" regenerates the canonical two-space layout. *)

structure Occam2_Ast = struct

datatype navi = up | Up | right | down

datatype 'a comment = Raw_txt of (string*'a) list
                    | Antiquotation
                        of {tag : string * 'a} * navi
                          list * {level : int} * {cartouche : string * 'a}

datatype 'a nodeInfo = OnlyPos of 'a | NodeInfo of 'a comment list * 'a

datatype 'a ident = Ident of string * int * 'a nodeInfo

(* The primitive data types (the manual's "primitive.type" minus the
   channel/timer/port types, which take arguments and so are "oType"
   constructors of their own). *)
datatype primKind = KBool | KByte | KInt | KInt16 | KInt32 | KInt64 | KReal32
  | KReal64

(* Monadic operators: "-" (checked negation) and MINUS (modulo negation), NOT,
   BITNOT ("~" is its symbolic spelling), SIZE. *)
datatype monOp = MNeg | MMinus | MNot | MBitNot | MSize

(* Dyadic operators other than AND/OR, which chain without parentheses and so
   form "EChain" nodes instead. "\" and REM are one operator (remainder), as
   are "/\" and BITAND, "\/" and BITOR. *)
datatype dyOp = DAdd | DSub | DMul | DDiv | DRem | DPlus | DMinus | DTimes
              | DBitAnd | DBitOr | DBitXor | DShl | DShr
              | DEq | DNe | DLt | DGt | DLe | DGe | DAfter

datatype logOp = LAnd | LOr

datatype convMode = ConvPlain | ConvRound | ConvTrunc

datatype 'a oType =
    TPrim of primKind * 'a nodeInfo
  | TChan of 'a oProtocol * 'a nodeInfo                  (* CHAN OF protocol *)
  | TTimer of 'a nodeInfo
  | TPort of 'a oType * 'a nodeInfo                      (* PORT OF type *)
  | TArray of 'a oExpr * 'a oType * 'a nodeInfo          (* [expression] type *)
  | TOpenArray
      of 'a oType * 'a nodeInfo                 (* [] type: specifiers only *)

and 'a oSimpleProt =
    SPType of 'a oType
  | SPCounted of primKind * 'a nodeInfo * 'a oType * 'a nodeInfo
                                                         (* primitive.type :: []
                                                            type *)

and 'a oProtocol =
    PrName of 'a
      ident                                   (* a defined protocol *)
  | PrSeq of 'a oSimpleProt list * 'a
      nodeInfo           (* simple or sequential protocol *)
  | PrAny of 'a nodeInfo                                 (* ANY *)

and 'a oLit =
    LInt of string * 'a
      nodeInfo                         (* digits or #HEXDIGITS, as written *)
  | LByte of string * 'a
      nodeInfo                        (* between the quotes, as written *)
  | LReal of string * 'a nodeInfo
  | LString
      of string * 'a
        nodeInfo                      (* between the quotes, as written *)
  | LTrue of 'a nodeInfo
  | LFalse of 'a nodeInfo
  | LTyped of 'a oLit * 'a oType * 'a nodeInfo           (* literal (type) *)

and 'a oElement =
    ENamed of 'a ident
  | ESub of 'a oElement * 'a oExpr * 'a
      nodeInfo         (* element [ subscript ] *)
  | ESlice of 'a oElement * 'a oExpr * 'a oExpr * 'a nodeInfo
                                                         (* [ element FROM
                                                            subscript FOR count
                                                            ] *)

and 'a oTable =
    TabString
      of string * 'a nodeInfo                    (* "..." used as a table *)
  | TabList of 'a oExpr list * 'a nodeInfo               (* [ e1, ..., en ] *)
  | TabSub of 'a oTable * 'a oExpr * 'a
      nodeInfo         (* table [ subscript ] *)
  | TabSlice of 'a oTable * 'a oExpr * 'a oExpr * 'a nodeInfo
                                                         (* [ table FROM
                                                            subscript FOR count
                                                            ] *)

and 'a oExpr =
    EElem of 'a oElement
  | ELit of 'a oLit
  | ETable of 'a oTable
  | EParen of 'a oExpr * 'a nodeInfo                     (* ( expression ) *)
  | EMon of monOp * 'a oExpr * 'a nodeInfo
  | EBin of 'a oExpr * dyOp * 'a oExpr * 'a nodeInfo
  | EChain of logOp * 'a oExpr list * 'a
      nodeInfo        (* a AND b AND c / a OR b OR c *)
  | EConv of convMode * primKind * 'a oExpr * 'a nodeInfo
  | EMost of bool * 'a oType * 'a
      nodeInfo               (* true: MOSTPOS, false: MOSTNEG *)
  | ECall of 'a ident * 'a oExpr list * 'a nodeInfo      (* function instance *)
  | EValof of 'a oValueProcess * 'a nodeInfo             (* ( value.process ) *)

and 'a oValueProcess =
    VPValof of 'a oProcess * 'a oExpr list * 'a nodeInfo
      (* VALOF process RESULT expression.list *)
  | VPSpec of 'a oSpec * 'a oValueProcess * 'a nodeInfo

and 'a oInputItem =
    IIVar of 'a oElement
  | IICounted
      of 'a oElement * 'a oElement               (* variable :: variable *)

and 'a oOutItem =
    OIExpr of 'a oExpr
  | OICounted
      of 'a oExpr * 'a oExpr                     (* expression :: expression *)

and 'a oInput =
    InVars of 'a oElement * 'a oInputItem list * 'a nodeInfo
                                                         (* channel/timer/port ?
                                                            item ; item ... *)
  | InAfter
      of 'a oElement * 'a oExpr * 'a
        nodeInfo      (* timer ? AFTER expression *)

and 'a oReplicator = Repl of 'a ident * 'a oExpr * 'a oExpr * 'a nodeInfo
                                                         (* name = base FOR
                                                            count *)

and 'a oChoice =
    ChGuarded
      of 'a oExpr * 'a oProcess * 'a
        nodeInfo    (* boolean, then an indented process *)
  | ChNested of 'a oProcess                              (* a nested IF *)
  | ChSpec of 'a oSpec * 'a oChoice * 'a nodeInfo

and 'a oOption =
    OpCases of 'a oExpr list * 'a oProcess * 'a nodeInfo
  | OpElse of 'a oProcess * 'a nodeInfo
  | OpSpec of 'a oSpec * 'a oOption * 'a nodeInfo

and 'a oVariant =
    VaTagged of 'a ident * 'a oInputItem list * 'a oProcess * 'a nodeInfo
  | VaSpec of 'a oSpec * 'a oVariant * 'a nodeInfo

and 'a oGuard =
    GInput of 'a oInput * 'a nodeInfo
  | GCondInput of 'a oExpr * 'a oInput * 'a nodeInfo     (* boolean & input *)
  | GCondSkip of 'a oExpr * 'a nodeInfo                  (* boolean & SKIP *)

and 'a oAlt =
    AlGuarded of 'a oGuard * 'a oProcess * 'a nodeInfo
  | AlCase of 'a oExpr option * 'a oElement * 'a oVariant list * 'a nodeInfo
                                                         (* [boolean &] channel
                                                            ? CASE variants *)
  | AlNested of 'a oProcess                              (* a nested ALT *)
  | AlSpec of 'a oSpec * 'a oAlt * 'a nodeInfo

and 'a oPlaced =
    PlProcessor
      of 'a oExpr * 'a oProcess * 'a
        nodeInfo  (* PROCESSOR expression process *)
  | PlPar of 'a oReplicator option * 'a oPlaced list * 'a nodeInfo
                                                         (* nested PLACED PAR *)

and 'a oFormal = Formal of bool * 'a oType * 'a ident list * 'a nodeInfo
                                                         (* [VAL] specifier
                                                            names *)

and 'a oTagged = Tagged of 'a ident * 'a oSimpleProt list * 'a nodeInfo
                                                         (* tag [;
                                                            sequential.protocol]
                                                            *)

and 'a oSpec =
    SDecl of 'a oType * 'a ident list * 'a nodeInfo      (* type names : *)
  | SAbbrev of 'a oType option * 'a ident * 'a oElement * 'a nodeInfo
                                                         (* [specifier] name IS
                                                            element : *)
  | SValAbbrev of 'a oType option * 'a ident * 'a oExpr * 'a nodeInfo
                                                         (* VAL [specifier] name
                                                            IS expression : *)
  | SRetypes of 'a oType * 'a ident * 'a oElement * 'a nodeInfo
  | SValRetypes of 'a oType * 'a ident * 'a oExpr * 'a nodeInfo
  | SProtocol
      of 'a ident * 'a oProtocol * 'a
        nodeInfo   (* PROTOCOL name IS protocol : *)
  | SProtocolCase of 'a ident * 'a oTagged list * 'a nodeInfo
  | SProc of 'a ident * 'a oFormal list * 'a oProcess * 'a nodeInfo
  | SFunction
      of 'a oType list * 'a ident * 'a oFormal list * 'a oValueProcess * 'a
        nodeInfo
  | SFunctionIs
      of 'a oType list * 'a ident * 'a oFormal list * 'a oExpr list * 'a
        nodeInfo

and 'a oProcess =
    PSkip of 'a nodeInfo
  | PStop of 'a nodeInfo
  | PAssign of 'a oElement list * 'a oExpr list * 'a nodeInfo
  | PInput of 'a oInput * 'a nodeInfo
  | POutput of 'a oElement * 'a oOutItem list * 'a nodeInfo
  | PCaseInput of 'a oElement * 'a oVariant list * 'a nodeInfo
  | PSeq of 'a oReplicator option * 'a oProcess list * 'a nodeInfo
  | PIf of 'a oReplicator option * 'a oChoice list * 'a nodeInfo
  | PCase of 'a oExpr * 'a oOption list * 'a nodeInfo
  | PWhile of 'a oExpr * 'a oProcess * 'a nodeInfo
  | PPar of bool * 'a oReplicator option * 'a oProcess list * 'a nodeInfo
                                                         (* bool: PRI PAR *)
  | PAlt of bool * 'a oReplicator option * 'a oAlt list * 'a nodeInfo
                                                         (* bool: PRI ALT *)
  | PPlacedPar of 'a oReplicator option * 'a oPlaced list * 'a nodeInfo
  | PInstance
      of 'a ident * 'a oExpr list * 'a nodeInfo  (* procedure instance *)
  | PSpecP of 'a oSpec * 'a oProcess * 'a
      nodeInfo       (* specification, then its scope *)
  | PPlace of 'a ident * 'a oExpr * 'a oProcess * 'a nodeInfo
                                                         (* PLACE name AT
                                                            expression : process
                                                            *)

(* What a parse produces, by entry point. "Id": a bare name; "Expr": an
   expression; "Unit": a program unit - a (possibly empty) run of
   specifications followed by at most one process (a "Specs"-only unit, with no
   process after the last specification, is a library-style compilation unit).
   "Spec" is never produced by a parse: it exists so that the analysis pass
   (Occam2_AnaEval.thy) can name a single specification as the "closest
   context" of an antiquotation, exactly like "Expr" and "Proc" do for the
   other two syntactic categories it walks. *)
datatype 'a root =
    Id of 'a ident
  | Expr of 'a oExpr
  | Proc of 'a oProcess
  | Spec of 'a oSpec
  | Specs of 'a oSpec list

(* --- Positions ---------------------------------------------------------- *)

fun pos_of_NodeInfo (OnlyPos pos) = pos
  | pos_of_NodeInfo (NodeInfo (_, pos)) = pos

fun comments_of_NodeInfo (OnlyPos _) = []
  | comments_of_NodeInfo (NodeInfo (cs, _)) = cs

fun nodeInfo_of_ident (Ident (_, _, ni)) = ni

fun nodeInfo_of_type t = (case t of
    TPrim (_, ni) => ni | TChan (_, ni) => ni | TTimer ni =>
      ni | TPort (_, ni) => ni
  | TArray (_, _, ni) => ni | TOpenArray (_, ni) => ni)

fun nodeInfo_of_lit l = (case l of
    LInt (_, ni) => ni | LByte (_, ni) => ni | LReal (_, ni) =>
      ni | LString (_, ni) => ni
  | LTrue ni => ni | LFalse ni => ni | LTyped (_, _, ni) => ni)

fun nodeInfo_of_element e = (case e of
    ENamed id => nodeInfo_of_ident id | ESub (_, _, ni) =>
      ni | ESlice (_, _, _, ni) => ni)

fun nodeInfo_of_table t = (case t of
    TabString (_, ni) => ni | TabList (_, ni) => ni | TabSub (_, _, ni) => ni
  | TabSlice (_, _, _, ni) => ni)

fun nodeInfo_of_expr e = (case e of
    EElem el => nodeInfo_of_element el
  | ELit l => nodeInfo_of_lit l
  | ETable t => nodeInfo_of_table t
  | EParen (_, ni) => ni | EMon (_, _, ni) => ni | EBin (_, _, _, ni) => ni
  | EChain (_, _, ni) => ni | EConv (_, _, _, ni) => ni | EMost (_, _, ni) => ni
  | ECall (_, _, ni) => ni | EValof (_, ni) => ni)

fun nodeInfo_of_spec s = (case s of
    SDecl (_, _, ni) => ni | SAbbrev (_, _, _, ni) =>
      ni | SValAbbrev (_, _, _, ni) => ni
  | SRetypes (_, _, _, ni) => ni | SValRetypes (_, _, _, ni) => ni
  | SProtocol (_, _, ni) => ni | SProtocolCase (_, _, ni) => ni
  | SProc (_, _, _, ni) => ni | SFunction (_, _, _, _, ni) => ni
  | SFunctionIs (_, _, _, _, ni) => ni)

fun nodeInfo_of_process p = (case p of
    PSkip ni => ni | PStop ni => ni | PAssign (_, _, ni) =>
      ni | PInput (_, ni) => ni
  | POutput (_, _, ni) => ni | PCaseInput (_, _, ni) => ni | PSeq (_, _, ni) =>
    ni
  | PIf (_, _, ni) => ni | PCase (_, _, ni) => ni | PWhile (_, _, ni) => ni
  | PPar (_, _, _, ni) => ni | PAlt (_, _, _, ni) =>
    ni | PPlacedPar (_, _, ni) => ni
  | PInstance (_, _, ni) => ni | PSpecP (_, _, ni) =>
    ni | PPlace (_, _, _, ni) => ni)

fun nodeInfo_of_choice c = (case c of
    ChGuarded (_, _, ni) => ni | ChNested p =>
      nodeInfo_of_process p | ChSpec (_, _, ni) => ni)

fun nodeInfo_of_option o_ = (case o_ of
    OpCases (_, _, ni) => ni | OpElse (_, ni) => ni | OpSpec (_, _, ni) => ni)

fun nodeInfo_of_variant v =
  (case v of VaTagged (_, _, _, ni) => ni | VaSpec (_, _, ni) => ni)

fun nodeInfo_of_alt a = (case a of
    AlGuarded (_, _, ni) => ni | AlCase (_, _, _, ni) => ni
  | AlNested p => nodeInfo_of_process p | AlSpec (_, _, ni) => ni)

fun nodeInfo_of_valueprocess v =
  (case v of VPValof (_, _, ni) => ni | VPSpec (_, _, ni) => ni)

fun pos_of_process p = pos_of_NodeInfo (nodeInfo_of_process p)
fun pos_of_expr e = pos_of_NodeInfo (nodeInfo_of_expr e)
fun pos_of_spec s = pos_of_NodeInfo (nodeInfo_of_spec s)
fun pos_of_ident id = pos_of_NodeInfo (nodeInfo_of_ident id)

(* --- Pretty-printing back to occam 2 text --------------------------------

   Layout is regenerated, not preserved: every compound construct prints its
   keyword on one line and its body two spaces deeper (the manual's one
   layout rule); long lines are never broken. Operator spellings are
   normalised to the keyword form where the manual gives both (REM, BITAND,
   BITOR, BITNOT). *)

fun ind n = String.implode (List.tabulate (2 * n, fn _ => #" "))
fun commas f xs = String.concatWith ", " (map f xs)
fun semis f xs = String.concatWith "; " (map f xs)

fun ident_name (Ident (s, _, _)) = s

fun pp_prim k = (case k of
    KBool => "BOOL" | KByte => "BYTE" | KInt => "INT" | KInt16 => "INT16"
  | KInt32 => "INT32" | KInt64 => "INT64" | KReal32 => "REAL32" | KReal64 =>
    "REAL64")

fun pp_monop m = (case m of
    MNeg => "-" | MMinus => "MINUS " | MNot => "NOT " | MBitNot =>
      "BITNOT " | MSize => "SIZE ")

fun pp_dyop d = (case d of
    DAdd => "+" | DSub => "-" | DMul => "*" | DDiv => "/" | DRem => "REM"
  | DPlus => "PLUS" | DMinus => "MINUS" | DTimes => "TIMES"
  | DBitAnd => "BITAND" | DBitOr => "BITOR" | DBitXor => "><"
  | DShl => "<<" | DShr => ">>"
  | DEq => "=" | DNe => "<>" | DLt => "<" | DGt => ">" | DLe => "<=" | DGe =>
    ">="
  | DAfter => "AFTER")

fun pp_logop LAnd = "AND" | pp_logop LOr = "OR"

fun pp_conv ConvPlain = "" | pp_conv ConvRound = "ROUND " | pp_conv ConvTrunc =
  "TRUNC "

(* The "n" parameter of the mutually recursive printers below is the current
   indentation level, only ever consulted by the multi-line constructs (a value
   process inside an expression, and the compound processes). *)
fun pp_type n t = (case t of
    TPrim (k, _) => pp_prim k
  | TChan (p, _) => "CHAN OF " ^ pp_protocol n p
  | TTimer _ => "TIMER"
  | TPort (t, _) => "PORT OF " ^ pp_type n t
  | TArray (e, t, _) => "[" ^ pp_expr n e ^ "]" ^ pp_type n t
  | TOpenArray (t, _) => "[]" ^ pp_type n t)

and pp_simple_prot n sp = (case sp of
    SPType t => pp_type n t
  | SPCounted (k, _, t, _) => pp_prim k ^ " :: []" ^ pp_type n t)

and pp_protocol n p = (case p of
    PrName id => ident_name id
  | PrSeq (sps, _) => String.concatWith "; " (map (pp_simple_prot n) sps)
  | PrAny _ => "ANY")

and pp_lit n l = (case l of
    LInt (s, _) => s
  | LByte (s, _) => "'" ^ s ^ "'"
  | LReal (s, _) => s
  | LString (s, _) => "\"" ^ s ^ "\""
  | LTrue _ => "TRUE"
  | LFalse _ => "FALSE"
  | LTyped (l, t, _) => pp_lit n l ^ " (" ^ pp_type n t ^ ")")

and pp_element n e = (case e of
    ENamed id => ident_name id
  | ESub (e, x, _) => pp_element n e ^ "[" ^ pp_expr n x ^ "]"
  | ESlice (e, a, b, _) =>
      "[" ^ pp_element n e ^ " FROM " ^ pp_expr n a ^ " FOR " ^ pp_expr n b
        ^ "]")

and pp_table n t = (case t of
    TabString (s, _) => "\"" ^ s ^ "\""
  | TabList (es, _) => "[" ^ commas (pp_expr n) es ^ "]"
  | TabSub (t, x, _) => pp_table n t ^ "[" ^ pp_expr n x ^ "]"
  | TabSlice (t, a, b, _) =>
      "[" ^ pp_table n t ^ " FROM " ^ pp_expr n a ^ " FOR " ^ pp_expr n b ^ "]")

and pp_expr n e = (case e of
    EElem el => pp_element n el
  | ELit l => pp_lit n l
  | ETable t => pp_table n t
  | EParen (x, _) => "(" ^ pp_expr n x ^ ")"
  | EMon (m, x, _) => pp_monop m ^ pp_expr n x
  | EBin (a, d, b, _) => pp_expr n a ^ " " ^ pp_dyop d ^ " " ^ pp_expr n b
  | EChain (l, xs, _) =>
    String.concatWith (" " ^ pp_logop l ^ " ") (map (pp_expr n) xs)
  | EConv (m, k, x, _) => pp_prim k ^ " " ^ pp_conv m ^ pp_expr n x
  | EMost (b, t, _) => (if b then "MOSTPOS " else "MOSTNEG ") ^ pp_type n t
  | ECall (id, args, _) => ident_name id ^ "(" ^ commas (pp_expr n) args ^ ")"
  | EValof (vp, _) =>
      "(\n" ^ String.concatWith "\n" (pp_valueprocess (n + 1) vp) ^ "\n"
        ^ ind n ^ ")")

and pp_input_item n i = (case i of
    IIVar e => pp_element n e
  | IICounted (a, b) => pp_element n a ^ " :: " ^ pp_element n b)

and pp_out_item n i = (case i of
    OIExpr e => pp_expr n e
  | OICounted (a, b) => pp_expr n a ^ " :: " ^ pp_expr n b)

and pp_input n i = (case i of
    InVars (c, items, _) =>
      pp_element n c ^ " ? "
        ^ String.concatWith "; " (map (pp_input_item n) items)
  | InAfter (t, e, _) => pp_element n t ^ " ? AFTER " ^ pp_expr n e)

and pp_repl n (Repl (id, a, b, _)) =
    ident_name id ^ " = " ^ pp_expr n a ^ " FOR " ^ pp_expr n b

and pp_repl_opt n NONE = ""
  | pp_repl_opt n (SOME r) = " " ^ pp_repl n r

and pp_formal n (Formal (is_val, t, ids, _)) =
    (if is_val then "VAL " else "") ^ pp_type n t ^ " " ^ commas ident_name ids

and pp_tagged n (Tagged (id, sps, _)) =
    ident_name id
      ^ (if null sps then "" else "; "
         ^ String.concatWith "; " (map (pp_simple_prot n) sps))

and pp_spec n s = (case s of
    SDecl (t, ids, _) =>
      [ind n ^ pp_type n t ^ " " ^ commas ident_name ids ^ ":"]
  | SAbbrev (st, id, el, _) =>
      [ind n ^ (case st of NONE => "" | SOME t => pp_type n t ^ " ")
       ^ ident_name id ^ " IS " ^
        pp_element n el ^ ":"]
  | SValAbbrev (st, id, e, _) =>
      [ind n ^ "VAL " ^ (case st of NONE => "" | SOME t => pp_type n t ^ " ")
       ^ ident_name id ^
        " IS " ^ pp_expr n e ^ ":"]
  | SRetypes (t, id, el, _) =>
      [ind n ^ pp_type n t ^ " " ^ ident_name id ^ " RETYPES "
       ^ pp_element n el ^ ":"]
  | SValRetypes (t, id, e, _) =>
      [ind n ^ "VAL " ^ pp_type n t ^ " " ^ ident_name id ^ " RETYPES "
       ^ pp_expr n e ^ ":"]
  | SProtocol (id, p, _) =>
      [ind n ^ "PROTOCOL " ^ ident_name id ^ " IS " ^ pp_protocol n p ^ ":"]
  | SProtocolCase (id, tags, _) =>
      [ind n ^ "PROTOCOL " ^ ident_name id, ind (n + 1) ^ "CASE"]
      @ map (fn t => ind (n + 2) ^ pp_tagged n t) tags @ [ind n ^ ":"]
  | SProc (id, formals, body, _) =>
      [ind n ^ "PROC " ^ ident_name id ^ " (" ^ commas (pp_formal n) formals
       ^ ")"]
      @ pp_proc (n + 1) body @ [ind n ^ ":"]
  | SFunction (ts, id, formals, vp, _) =>
      [ind n ^ commas (pp_type n) ts ^ " FUNCTION " ^ ident_name id ^ " (" ^
        commas (pp_formal n) formals ^ ")"]
      @ pp_valueprocess (n + 1) vp @ [ind n ^ ":"]
  | SFunctionIs (ts, id, formals, es, _) =>
      [ind n ^ commas (pp_type n) ts ^ " FUNCTION " ^ ident_name id ^ " (" ^
        commas (pp_formal n) formals ^ ") IS " ^ commas (pp_expr n) es ^ ":"])

and pp_valueprocess n vp = (case vp of
    VPValof (p, es, _) =>
      [ind n ^ "VALOF"] @ pp_proc (n + 1) p
        @ [ind n ^ "RESULT " ^ commas (pp_expr n) es]
  | VPSpec (s, vp, _) => pp_spec n s @ pp_valueprocess n vp)

and pp_variants n vs = List.concat (map (pp_variant n) vs)

and pp_variant n v = (case v of
    VaTagged (id, items, p, _) =>
      [ind n ^ ident_name id ^
        (if null items then "" else "; "
         ^ String.concatWith "; " (map (pp_input_item n) items))]
      @ pp_proc (n + 1) p
  | VaSpec (s, v, _) => pp_spec n s @ pp_variant n v)

and pp_choice n c = (case c of
    ChGuarded (e, p, _) => [ind n ^ pp_expr n e] @ pp_proc (n + 1) p
  | ChNested p => pp_proc n p
  | ChSpec (s, c, _) => pp_spec n s @ pp_choice n c)

and pp_option n o_ = (case o_ of
    OpCases (es, p, _) => [ind n ^ commas (pp_expr n) es] @ pp_proc (n + 1) p
  | OpElse (p, _) => [ind n ^ "ELSE"] @ pp_proc (n + 1) p
  | OpSpec (s, o_, _) => pp_spec n s @ pp_option n o_)

and pp_guard n g = (case g of
    GInput (i, _) => pp_input n i
  | GCondInput (e, i, _) => pp_expr n e ^ " & " ^ pp_input n i
  | GCondSkip (e, _) => pp_expr n e ^ " & SKIP")

and pp_alt n a = (case a of
    AlGuarded (g, p, _) => [ind n ^ pp_guard n g] @ pp_proc (n + 1) p
  | AlCase (be, c, vs, _) =>
      [ind n ^ (case be of NONE => "" | SOME e => pp_expr n e ^ " & ")
       ^ pp_element n c ^ " ? CASE"]
      @ pp_variants (n + 1) vs
  | AlNested p => pp_proc n p
  | AlSpec (s, a, _) => pp_spec n s @ pp_alt n a)

and pp_placed n pl = (case pl of
    PlProcessor (e, p, _) =>
      [ind n ^ "PROCESSOR " ^ pp_expr n e] @ pp_proc (n + 1) p
  | PlPar (r, pls, _) =>
      [ind n ^ "PLACED PAR" ^ pp_repl_opt n r]
        @ List.concat (map (pp_placed (n + 1)) pls))

and pp_proc n p = (case p of
    PSkip _ => [ind n ^ "SKIP"]
  | PStop _ => [ind n ^ "STOP"]
  | PAssign (vs, es, _) =>
    [ind n ^ commas (pp_element n) vs ^ " := " ^ commas (pp_expr n) es]
  | PInput (i, _) => [ind n ^ pp_input n i]
  | POutput (c, items, _) =>
      [ind n ^ pp_element n c ^ " ! "
       ^ String.concatWith "; " (map (pp_out_item n) items)]
  | PCaseInput (c, vs, _) =>
    [ind n ^ pp_element n c ^ " ? CASE"] @ pp_variants (n + 1) vs
  | PSeq (r, ps, _) =>
    [ind n ^ "SEQ" ^ pp_repl_opt n r] @ List.concat (map (pp_proc (n + 1)) ps)
  | PIf (r, cs, _) =>
    [ind n ^ "IF" ^ pp_repl_opt n r] @ List.concat (map (pp_choice (n + 1)) cs)
  | PCase (e, os, _) =>
    [ind n ^ "CASE " ^ pp_expr n e] @ List.concat (map (pp_option (n + 1)) os)
  | PWhile (e, p, _) => [ind n ^ "WHILE " ^ pp_expr n e] @ pp_proc (n + 1) p
  | PPar (pri, r, ps, _) =>
      [ind n ^ (if pri then "PRI PAR" else "PAR") ^ pp_repl_opt n r]
      @ List.concat (map (pp_proc (n + 1)) ps)
  | PAlt (pri, r, alts, _) =>
      [ind n ^ (if pri then "PRI ALT" else "ALT") ^ pp_repl_opt n r]
      @ List.concat (map (pp_alt (n + 1)) alts)
  | PPlacedPar (r, pls, _) =>
      [ind n ^ "PLACED PAR" ^ pp_repl_opt n r]
        @ List.concat (map (pp_placed (n + 1)) pls)
  | PInstance (id, args, _) =>
    [ind n ^ ident_name id ^ "(" ^ commas (pp_expr n) args ^ ")"]
  | PSpecP (s, p, _) => pp_spec n s @ pp_proc n p
  | PPlace (id, e, p, _) =>
      [ind n ^ "PLACE " ^ ident_name id ^ " AT " ^ pp_expr n e ^ ":"]
        @ pp_proc n p)

fun pp_process p = String.concatWith "\n" (pp_proc 0 p)
fun pp_expression e = pp_expr 0 e
fun pp_specification s = String.concatWith "\n" (pp_spec 0 s)

fun pp_root (Id id) = ident_name id
  | pp_root (Expr e) = pp_expression e
  | pp_root (Proc p) = pp_process p
  | pp_root (Spec s) = pp_specification s
  | pp_root (Specs ss) = String.concatWith "\n" (map pp_specification ss)

end
