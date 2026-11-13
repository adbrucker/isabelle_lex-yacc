(* Abstract syntax of ARM Thumb-2 assembly in the syntax of the GNU assembler (as), for the
   Cortex-M7 (ARMv7E-M, with the DSP extension and the single and double precision floating point
   unit FPv5): the unified assembler syntax, with the directives, the labels, the macros and the
   conditional assembly of "as".

   The tree is an ML datatype of its own, in the style of a machine model: the registers, the
   instructions (opcodes), the conditions and the shifts are closed enumerations of constructors,
   so that a semantic backend - an interpreter, a translation into HOL - can match on them. What
   is shared with C11 and the other front-ends of the family is the position-annotation
   machinery ("'a nodeInfo", "'a comment", "navi", "'a ident"). A mnemonic is decoded by the
   parser (see "ARM_Isa") into its opcode, its condition, its S flag, its width and its data
   types ("add.w", "adds", "addeq", "vadd.f32"), and also kept as it was written, so that the tree
   prints back to the very text. A word that is at the start of a statement and not a
   mnemonic is a macro call (or an unknown instruction): "SCall". *)

structure ARM_Ast = struct

datatype navi = up | Up | right | down

datatype 'a comment = Raw_txt of (string*'a) list
                    | Antiquotation of {tag : string * 'a} * navi list * {level : int}
                                       * {cartouche : string * 'a}

datatype 'a nodeInfo = OnlyPos of 'a | NodeInfo of 'a comment list * 'a

datatype 'a ident = Ident of string * int * 'a nodeInfo

(* --- the machine ---------------------------------------------------------------------------- *)

(* the core registers; r11 is also fp, r12 ip, r13 sp, r14 lr, r15 pc *)
datatype regcode = R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10 | R11 | R12 | SP | LR | PC

(* a register of any file: core, single precision (s0-s31), double precision (d0-d15), special
   (apsr, msp, primask, fpscr, ...: its name in lower case) *)
datatype reg = Core of regcode | Single of int | Double of int | Special of string

datatype cond = EQ | NE | CS | CC | MI | PL | VS | VC | HI | LS | GE | LT | GT | LE | AL

datatype width = Narrow | Wide

datatype shiftop = Lsl | Lsr | Asr | Ror | Rrx

(* the instructions of ARMv7E-M (Thumb-2 with the DSP extension and the coprocessor instructions)
   and of the floating point unit FPv5, by their base mnemonic *)
datatype opcode =
    ADC | ADD | ADDW | ADR | AND | ASR | B | BFC | BFI | BIC | BKPT | BL | BLX | BX | CBNZ |
    CBZ | CDP | CDP2 | CLREX | CLZ | CMN | CMP | CPSID | CPSIE | DBG | DMB | DSB | EOR | ISB |
    IT | LDC | LDC2 | LDM | LDMDB | LDMEA | LDMFD | LDMIA | LDR | LDRB | LDRBT | LDRD | LDREX |
    LDREXB | LDREXH | LDRH | LDRHT | LDRSB | LDRSBT | LDRSH | LDRSHT | LDRT | LSL | LSR | MCR |
    MCR2 | MCRR | MCRR2 | MLA | MLS | MOV | MOVT | MOVW | MRC | MRC2 | MRRC | MRRC2 | MRS |
    MSR | MUL | MVN | NOP | ORN | ORR | PKHBT | PKHTB | PLD | PLDW | PLI | POP | PUSH | QADD |
    QADD16 | QADD8 | QASX | QDADD | QDSUB | QSAX | QSUB | QSUB16 | QSUB8 | RBIT | REV | REV16 |
    REVSH | ROR | RRX | RSB | SADD16 | SADD8 | SASX | SBC | SBFX | SDIV | SEL | SEV | SHADD16 |
    SHADD8 | SHASX | SHSAX | SHSUB16 | SHSUB8 | SMLABB | SMLABT | SMLATB | SMLATT | SMLAD |
    SMLADX | SMLAL | SMLALBB | SMLALBT | SMLALTB | SMLALTT | SMLALD | SMLALDX | SMLAWB |
    SMLAWT | SMLSD | SMLSDX | SMLSLD | SMLSLDX | SMMLA | SMMLAR | SMMLS | SMMLSR | SMMUL |
    SMMULR | SMUAD | SMUADX | SMULBB | SMULBT | SMULTB | SMULTT | SMULL | SMULWB | SMULWT |
    SMUSD | SMUSDX | SSAT | SSAT16 | SSAX | SSUB16 | SSUB8 | STC | STC2 | STM | STMDB | STMEA |
    STMFD | STMIA | STR | STRB | STRBT | STRD | STREX | STREXB | STREXH | STRH | STRHT | STRT |
    SUB | SUBW | SVC | SXTAB | SXTAB16 | SXTAH | SXTB | SXTB16 | SXTH | TBB | TBH | TEQ | TST |
    UADD16 | UADD8 | UASX | UBFX | UDF | UDIV | UHADD16 | UHADD8 | UHASX | UHSAX | UHSUB16 |
    UHSUB8 | UMAAL | UMLAL | UMULL | UQADD16 | UQADD8 | UQASX | UQSAX | UQSUB16 | UQSUB8 |
    USAD8 | USADA8 | USAT | USAT16 | USAX | USUB16 | USUB8 | UXTAB | UXTAB16 | UXTAH | UXTB |
    UXTB16 | UXTH | WFE | WFI | YIELD | VABS | VADD | VCMP | VCMPE | VCVT | VCVTA | VCVTB |
    VCVTM | VCVTN | VCVTP | VCVTR | VCVTT | VDIV | VFMA | VFMS | VFNMA | VFNMS | VLDM |
    VLDMDB | VLDMIA | VLDR | VMAXNM | VMINNM | VMLA | VMLS | VMOV | VMRS | VMSR | VMUL | VNEG |
    VNMLA | VNMLS | VNMUL | VPOP | VPUSH | VRINTA | VRINTM | VRINTN | VRINTP | VRINTR |
    VRINTX | VRINTZ | VSEL | VSQRT | VSTM | VSTMDB | VSTMIA | VSTR | VSUB

datatype unop = Neg | Pos | Not | Compl

datatype binop =
    Mul | Div | Mod | Shl | Shr | Or | And | Xor | Add | Sub
  | Equal | NotEqual | Less | Greater | LessEq | GreaterEq | LAnd | LOr

(* --- expressions and operands --------------------------------------------------------------- *)

datatype 'a expr =
    ENum of string * 'a nodeInfo                  (* an integer, as written *)
  | EFloat of string * 'a nodeInfo                (* 1.5, 0f1.5 *)
  | EChar of string * 'a nodeInfo                 (* 'a *)
  | EString of string * 'a nodeInfo               (* "...", with the quotes *)
  | ESym of 'a ident                              (* a symbol or a label, a macro argument *)
  | EReg of reg * string * 'a nodeInfo            (* a register, as spelled *)
  | EDot of 'a nodeInfo                           (* the location counter "." *)
  | ELocal of string * 'a nodeInfo                (* a reference "1b" or "1f" to a numeric label *)
  | EReloc of 'a expr * 'a ident * 'a nodeInfo    (* sym(GOT), sym(PLT) *)
  | EPart of 'a ident * 'a expr * 'a nodeInfo     (* :lower16:sym, :upper16:sym *)
  | EUnary of unop * 'a expr * 'a nodeInfo
  | EBinary of binop * 'a expr * 'a expr * 'a nodeInfo
  | EParen of 'a expr * 'a nodeInfo

datatype 'a operand =
    OExpr of 'a expr                              (* a branch target, a symbol, a number *)
  | OReg of reg * string * bool * 'a nodeInfo     (* r0, sp, s3; the flag: "!" (write back) *)
  | OImm of 'a expr * 'a nodeInfo                 (* #expr *)
  | OShift of shiftop * string * 'a operand option * 'a nodeInfo
                                                  (* lsl #2, lsl r1, rrx; spelled as written *)
  | OLiteral of 'a expr * 'a nodeInfo             (* =expr: a literal pool entry *)
  | OMem of 'a operand list * bool * 'a nodeInfo  (* [r0, #4]; the flag: "!" *)
  | OAlign of string * bool * 'a nodeInfo         (* :64 in [r0, :64]; the flag: a comma precedes *)
  | OList of 'a operand list * bool * 'a nodeInfo (* {r0-r3, lr}; the flag: "^" *)
  | ORange of 'a operand * 'a operand * 'a nodeInfo  (* r0-r3 in a register list *)
  | OPercent of 'a ident * 'a nodeInfo            (* %function, %progbits *)
  | OKeyword of 'a ident * 'a expr * 'a nodeInfo  (* name=value: a keyword argument *)
  | ORaw of string * 'a nodeInfo                  (* the rest of a line, as written (.file, .loc) *)
  | OScalar of reg * string * 'a expr * 'a nodeInfo  (* d0[1]: an element of a register *)

(* --- statements ------------------------------------------------------------------------------ *)

datatype 'a insn =
    Insn of {text : string, opc : opcode, cond : cond option, setflags : bool,
             width : width option, dtypes : string list} * 'a operand list * 'a nodeInfo

datatype 'a label = LName of 'a ident | LNum of string * 'a nodeInfo

(* a parameter of a macro: name, a qualifier (:req, :vararg), a default value; whether a comma
   precedes it *)
datatype 'a mparam = MParam of 'a ident * string option * 'a expr option * bool * 'a nodeInfo

datatype 'a stmt =
    SLabel of 'a label * 'a nodeInfo              (* name: *)
  | SInsn of 'a insn
  | SDir of 'a ident * 'a operand list * 'a nodeInfo        (* .word 1, 2 *)
  | SAssign of 'a ident * 'a expr * 'a nodeInfo             (* sym = expr *)
  | SReq of 'a ident * 'a operand * 'a nodeInfo             (* name .req r0 *)
  | SCall of 'a ident * 'a operand list * 'a nodeInfo       (* a macro call, an unknown mnemonic *)
  | SMacro of 'a ident * 'a mparam list * 'a stmt list * 'a nodeInfo        (* .macro ... .endm *)
  | SCond of 'a branch list * 'a stmt list option * 'a nodeInfo             (* .if ... .endif *)
  | SRep of 'a ident * 'a operand list * 'a stmt list * 'a nodeInfo         (* .rept, .irp, .irpc *)
  | SExitm of 'a nodeInfo                                   (* .exitm *)

(* one branch of a conditional: the directive (.if, .ifdef, .elseif, ...), operands and body *)
and 'a branch = Branch of 'a ident * 'a operand list * 'a stmt list * 'a nodeInfo

datatype 'a file = File of 'a stmt list * 'a nodeInfo

datatype 'a root =
    Id of 'a ident
  | Expr of 'a expr
  | Operand of 'a operand
  | Stmts of 'a stmt list      (* the statements of a block *)
  | Source of 'a file          (* an assembly file *)
  | Stmt of 'a stmt            (* never produced by a parse: the closest context of a statement *)

(* --- Positions ------------------------------------------------------------------------------- *)

fun pos_of_NodeInfo (OnlyPos pos) = pos
  | pos_of_NodeInfo (NodeInfo (_, pos)) = pos

fun comments_of_NodeInfo (OnlyPos _) = []
  | comments_of_NodeInfo (NodeInfo (cs, _)) = cs

fun nodeInfo_of_ident (Ident (_, _, ni)) = ni
fun ident_name (Ident (s, _, _)) = s

fun nodeInfo_of_expr e = (case e of
    ENum (_, ni) => ni | EFloat (_, ni) => ni | EChar (_, ni) => ni | EString (_, ni) => ni
  | ESym id => nodeInfo_of_ident id | EReg (_, _, ni) => ni | EDot ni => ni | ELocal (_, ni) => ni
  | EReloc (_, _, ni) => ni | EPart (_, _, ni) => ni | EUnary (_, _, ni) => ni
  | EBinary (_, _, _, ni) => ni | EParen (_, ni) => ni)

fun nodeInfo_of_operand o1 = (case o1 of
    OExpr e => nodeInfo_of_expr e | OReg (_, _, _, ni) => ni | OImm (_, ni) => ni
  | OShift (_, _, _, ni) => ni | OLiteral (_, ni) => ni | OMem (_, _, ni) => ni
  | OAlign (_, _, ni) => ni | OList (_, _, ni) => ni | ORange (_, _, ni) => ni
  | OPercent (_, ni) => ni | OKeyword (_, _, ni) => ni
  | ORaw (_, ni) => ni | OScalar (_, _, _, ni) => ni)

fun nodeInfo_of_insn (Insn (_, _, ni)) = ni

fun nodeInfo_of_stmt s = (case s of
    SLabel (_, ni) => ni | SInsn i => nodeInfo_of_insn i | SDir (_, _, ni) => ni
  | SAssign (_, _, ni) => ni | SReq (_, _, ni) => ni | SCall (_, _, ni) => ni
  | SMacro (_, _, _, ni) => ni | SCond (_, _, ni) => ni | SRep (_, _, _, ni) => ni
  | SExitm ni => ni)

fun pos_of_ident id = pos_of_NodeInfo (nodeInfo_of_ident id)
fun pos_of_expr e = pos_of_NodeInfo (nodeInfo_of_expr e)
fun pos_of_operand o1 = pos_of_NodeInfo (nodeInfo_of_operand o1)
fun pos_of_stmt s = pos_of_NodeInfo (nodeInfo_of_stmt s)

end
