(* The instruction set of the front-end: how a mnemonic is decoded into an opcode with its
   condition, S flag, width and data types, and which words are registers. *)

structure ARM_Isa = struct

structure A = ARM_Ast

val opcodes : (string * A.opcode) list =
  [   ("adc", A.ADC), ("add", A.ADD), ("addw", A.ADDW), ("adr", A.ADR), ("and", A.AND),
   ("asr", A.ASR), ("b", A.B), ("bfc", A.BFC), ("bfi", A.BFI), ("bic", A.BIC),
   ("bkpt", A.BKPT), ("bl", A.BL), ("blx", A.BLX), ("bx", A.BX), ("cbnz", A.CBNZ),
   ("cbz", A.CBZ), ("cdp", A.CDP), ("cdp2", A.CDP2), ("clrex", A.CLREX), ("clz", A.CLZ),
   ("cmn", A.CMN), ("cmp", A.CMP), ("cpsid", A.CPSID), ("cpsie", A.CPSIE), ("dbg", A.DBG),
   ("dmb", A.DMB), ("dsb", A.DSB), ("eor", A.EOR), ("isb", A.ISB), ("it", A.IT),
   ("ldc", A.LDC), ("ldc2", A.LDC2), ("ldm", A.LDM), ("ldmdb", A.LDMDB), ("ldmea", A.LDMEA),
   ("ldmfd", A.LDMFD), ("ldmia", A.LDMIA), ("ldr", A.LDR), ("ldrb", A.LDRB),
   ("ldrbt", A.LDRBT), ("ldrd", A.LDRD), ("ldrex", A.LDREX), ("ldrexb", A.LDREXB),
   ("ldrexh", A.LDREXH), ("ldrh", A.LDRH), ("ldrht", A.LDRHT), ("ldrsb", A.LDRSB),
   ("ldrsbt", A.LDRSBT), ("ldrsh", A.LDRSH), ("ldrsht", A.LDRSHT), ("ldrt", A.LDRT),
   ("lsl", A.LSL), ("lsr", A.LSR), ("mcr", A.MCR), ("mcr2", A.MCR2), ("mcrr", A.MCRR),
   ("mcrr2", A.MCRR2), ("mla", A.MLA), ("mls", A.MLS), ("mov", A.MOV), ("movt", A.MOVT),
   ("movw", A.MOVW), ("mrc", A.MRC), ("mrc2", A.MRC2), ("mrrc", A.MRRC), ("mrrc2", A.MRRC2),
   ("mrs", A.MRS), ("msr", A.MSR), ("mul", A.MUL), ("mvn", A.MVN), ("nop", A.NOP),
   ("orn", A.ORN), ("orr", A.ORR), ("pkhbt", A.PKHBT), ("pkhtb", A.PKHTB), ("pld", A.PLD),
   ("pldw", A.PLDW), ("pli", A.PLI), ("pop", A.POP), ("push", A.PUSH), ("qadd", A.QADD),
   ("qadd16", A.QADD16), ("qadd8", A.QADD8), ("qasx", A.QASX), ("qdadd", A.QDADD),
   ("qdsub", A.QDSUB), ("qsax", A.QSAX), ("qsub", A.QSUB), ("qsub16", A.QSUB16),
   ("qsub8", A.QSUB8), ("rbit", A.RBIT), ("rev", A.REV), ("rev16", A.REV16),
   ("revsh", A.REVSH), ("ror", A.ROR), ("rrx", A.RRX), ("rsb", A.RSB), ("sadd16", A.SADD16),
   ("sadd8", A.SADD8), ("sasx", A.SASX), ("sbc", A.SBC), ("sbfx", A.SBFX), ("sdiv", A.SDIV),
   ("sel", A.SEL), ("sev", A.SEV), ("shadd16", A.SHADD16), ("shadd8", A.SHADD8),
   ("shasx", A.SHASX), ("shsax", A.SHSAX), ("shsub16", A.SHSUB16), ("shsub8", A.SHSUB8),
   ("smlabb", A.SMLABB), ("smlabt", A.SMLABT), ("smlatb", A.SMLATB), ("smlatt", A.SMLATT),
   ("smlad", A.SMLAD), ("smladx", A.SMLADX), ("smlal", A.SMLAL), ("smlalbb", A.SMLALBB),
   ("smlalbt", A.SMLALBT), ("smlaltb", A.SMLALTB), ("smlaltt", A.SMLALTT),
   ("smlald", A.SMLALD), ("smlaldx", A.SMLALDX), ("smlawb", A.SMLAWB), ("smlawt", A.SMLAWT),
   ("smlsd", A.SMLSD), ("smlsdx", A.SMLSDX), ("smlsld", A.SMLSLD), ("smlsldx", A.SMLSLDX),
   ("smmla", A.SMMLA), ("smmlar", A.SMMLAR), ("smmls", A.SMMLS), ("smmlsr", A.SMMLSR),
   ("smmul", A.SMMUL), ("smmulr", A.SMMULR), ("smuad", A.SMUAD), ("smuadx", A.SMUADX),
   ("smulbb", A.SMULBB), ("smulbt", A.SMULBT), ("smultb", A.SMULTB), ("smultt", A.SMULTT),
   ("smull", A.SMULL), ("smulwb", A.SMULWB), ("smulwt", A.SMULWT), ("smusd", A.SMUSD),
   ("smusdx", A.SMUSDX), ("ssat", A.SSAT), ("ssat16", A.SSAT16), ("ssax", A.SSAX),
   ("ssub16", A.SSUB16), ("ssub8", A.SSUB8), ("stc", A.STC), ("stc2", A.STC2), ("stm", A.STM),
   ("stmdb", A.STMDB), ("stmea", A.STMEA), ("stmfd", A.STMFD), ("stmia", A.STMIA),
   ("str", A.STR), ("strb", A.STRB), ("strbt", A.STRBT), ("strd", A.STRD), ("strex", A.STREX),
   ("strexb", A.STREXB), ("strexh", A.STREXH), ("strh", A.STRH), ("strht", A.STRHT),
   ("strt", A.STRT), ("sub", A.SUB), ("subw", A.SUBW), ("svc", A.SVC), ("sxtab", A.SXTAB),
   ("sxtab16", A.SXTAB16), ("sxtah", A.SXTAH), ("sxtb", A.SXTB), ("sxtb16", A.SXTB16),
   ("sxth", A.SXTH), ("tbb", A.TBB), ("tbh", A.TBH), ("teq", A.TEQ), ("tst", A.TST),
   ("uadd16", A.UADD16), ("uadd8", A.UADD8), ("uasx", A.UASX), ("ubfx", A.UBFX),
   ("udf", A.UDF), ("udiv", A.UDIV), ("uhadd16", A.UHADD16), ("uhadd8", A.UHADD8),
   ("uhasx", A.UHASX), ("uhsax", A.UHSAX), ("uhsub16", A.UHSUB16), ("uhsub8", A.UHSUB8),
   ("umaal", A.UMAAL), ("umlal", A.UMLAL), ("umull", A.UMULL), ("uqadd16", A.UQADD16),
   ("uqadd8", A.UQADD8), ("uqasx", A.UQASX), ("uqsax", A.UQSAX), ("uqsub16", A.UQSUB16),
   ("uqsub8", A.UQSUB8), ("usad8", A.USAD8), ("usada8", A.USADA8), ("usat", A.USAT),
   ("usat16", A.USAT16), ("usax", A.USAX), ("usub16", A.USUB16), ("usub8", A.USUB8),
   ("uxtab", A.UXTAB), ("uxtab16", A.UXTAB16), ("uxtah", A.UXTAH), ("uxtb", A.UXTB),
   ("uxtb16", A.UXTB16), ("uxth", A.UXTH), ("wfe", A.WFE), ("wfi", A.WFI), ("yield", A.YIELD),
   ("vabs", A.VABS), ("vadd", A.VADD), ("vcmp", A.VCMP), ("vcmpe", A.VCMPE), ("vcvt", A.VCVT),
   ("vcvta", A.VCVTA), ("vcvtb", A.VCVTB), ("vcvtm", A.VCVTM), ("vcvtn", A.VCVTN),
   ("vcvtp", A.VCVTP), ("vcvtr", A.VCVTR), ("vcvtt", A.VCVTT), ("vdiv", A.VDIV),
   ("vfma", A.VFMA), ("vfms", A.VFMS), ("vfnma", A.VFNMA), ("vfnms", A.VFNMS),
   ("vldm", A.VLDM), ("vldmdb", A.VLDMDB), ("vldmia", A.VLDMIA), ("vldr", A.VLDR),
   ("vmaxnm", A.VMAXNM), ("vminnm", A.VMINNM), ("vmla", A.VMLA), ("vmls", A.VMLS),
   ("vmov", A.VMOV), ("vmrs", A.VMRS), ("vmsr", A.VMSR), ("vmul", A.VMUL), ("vneg", A.VNEG),
   ("vnmla", A.VNMLA), ("vnmls", A.VNMLS), ("vnmul", A.VNMUL), ("vpop", A.VPOP),
   ("vpush", A.VPUSH), ("vrinta", A.VRINTA), ("vrintm", A.VRINTM), ("vrintn", A.VRINTN),
   ("vrintp", A.VRINTP), ("vrintr", A.VRINTR), ("vrintx", A.VRINTX), ("vrintz", A.VRINTZ),
   ("vsel", A.VSEL), ("vsqrt", A.VSQRT), ("vstm", A.VSTM), ("vstmdb", A.VSTMDB),
   ("vstmia", A.VSTMIA), ("vstr", A.VSTR), ("vsub", A.VSUB)]

(* the opcodes that take an S suffix *)
val s_opcodes : string list =
  [   "adc", "add", "and", "asr", "bic", "eor", "lsl", "lsr", "mov", "mul", "mvn", "orn", "orr",
   "ror", "rrx", "rsb", "sbc", "sub"]

val conditions : (string * A.cond) list =
  [("eq", A.EQ), ("ne", A.NE), ("cs", A.CS), ("hs", A.CS), ("cc", A.CC), ("lo", A.CC), ("mi", A.MI),
   ("pl", A.PL), ("vs", A.VS), ("vc", A.VC), ("hi", A.HI), ("ls", A.LS), ("ge", A.GE), ("lt", A.LT),
   ("gt", A.GT), ("le", A.LE), ("al", A.AL)]

fun lower s = String.map Char.toLower s

(* the opcode, condition and S flag of a stem (no dots, lower case) *)
fun decode_stem (stem : string) : (A.opcode * A.cond option * bool) option =
  let
    fun cond_of c = AList.lookup (op =) conditions c
    (* "", "s", a condition, "s" followed by a condition (unified), a condition followed by "s" *)
    fun rest_ok may_s rest =
      if rest = "" then SOME (NONE, false)
      else if rest = "s" andalso may_s then SOME (NONE, true)
      else (case cond_of rest of
              SOME c => SOME (SOME c, false)
            | NONE =>
                if may_s andalso String.size rest = 3 andalso String.sub (rest, 0) = #"s"
                then (case cond_of (String.extract (rest, 1, NONE)) of
                        SOME c => SOME (SOME c, true) | NONE => NONE)
                else if may_s andalso String.size rest = 3 andalso String.sub (rest, 2) = #"s"
                then (case cond_of (String.substring (rest, 0, 2)) of
                        SOME c => SOME (SOME c, true) | NONE => NONE)
                else NONE)
    fun cands () =
      List.mapPartial
        (fn (name, oc) =>
           if String.isPrefix name stem
           then
             (case rest_ok (member (op =) s_opcodes name)
                     (String.extract (stem, String.size name, NONE)) of
                SOME (c, s) => SOME (String.size name, (oc, c, s))
              | NONE => NONE)
           else NONE) opcodes
    (* "it", "ite", "itte", ...: the condition is an operand *)
    fun is_it s =
      String.size s >= 2 andalso String.size s <= 5 andalso String.isPrefix "it" s
      andalso List.all (fn c => c = #"t" orelse c = #"e")
                (String.explode (String.extract (s, 2, NONE)))
  in
    if is_it stem then SOME (A.IT, NONE, false)
    else
      (case cands () of
         [] => NONE
       | cs =>
           let val best = List.foldl (fn ((n, x), (bn, bx)) => if n > bn then (n, x) else (bn, bx))
                            (hd cs) (tl cs)
           in SOME (#2 best) end)
  end

(* a mnemonic as written: the stem, then ".n", ".w" and data types ("vcvt.f32.s32") *)
fun decode (text : string) =
  (case String.fields (fn c => c = #".") text of
     [] => NONE
   | stem :: suffixes =>
       (case decode_stem (lower stem) of
          NONE => NONE
        | SOME (op1, c, s) =>
            let
              val ls = map lower suffixes
              val width = if member (op =) ls "w" then SOME A.Wide
                          else if member (op =) ls "n" then SOME A.Narrow else NONE
              val dts = List.filter (fn x => x <> "w" andalso x <> "n") ls
            in SOME {text = text, opc = op1, cond = c, setflags = s, width = width,
                     dtypes = dts} end))

(* register names *)
fun reg_of (word : string) : A.reg option =
  let
    val w = lower word
    fun num s = Int.fromString s
    fun all_digits s = s <> "" andalso List.all Char.isDigit (String.explode s)
    val core =
      [("r0", A.R0), ("r1", A.R1), ("r2", A.R2), ("r3", A.R3), ("r4", A.R4), ("r5", A.R5),
       ("r6", A.R6), ("r7", A.R7), ("r8", A.R8), ("r9", A.R9), ("r10", A.R10), ("r11", A.R11),
       ("r12", A.R12), ("r13", A.SP), ("r14", A.LR), ("r15", A.PC), ("sb", A.R9), ("sl", A.R10),
       ("fp", A.R11), ("ip", A.R12), ("sp", A.SP), ("lr", A.LR), ("pc", A.PC)]
    val specials =
      ["apsr", "ipsr", "epsr", "iapsr", "eapsr", "iepsr", "xpsr", "msp", "psp", "primask",
       "basepri", "basepri_max", "faultmask", "control", "fpscr", "apsr_nzcvq", "apsr_g",
       "apsr_nzcvqg", "mpsr"]
  in
    case AList.lookup (op =) core w of
      SOME r => SOME (A.Core r)
    | NONE =>
        if member (op =) specials w then SOME (A.Special w)
        else if String.size w >= 2 andalso String.sub (w, 0) = #"s"
                andalso all_digits (String.extract (w, 1, NONE))
        then (case num (String.extract (w, 1, NONE)) of
                SOME n => if n <= 31 then SOME (A.Single n) else NONE | NONE => NONE)
        else if String.size w >= 2 andalso String.sub (w, 0) = #"d"
                andalso all_digits (String.extract (w, 1, NONE))
        then (case num (String.extract (w, 1, NONE)) of
                SOME n => if n <= 31 then SOME (A.Double n) else NONE | NONE => NONE)
        else NONE
  end

fun shift_of (word : string) : A.shiftop option =
  (case lower word of
     "lsl" => SOME A.Lsl | "lsr" => SOME A.Lsr | "asr" => SOME A.Asr | "ror" => SOME A.Ror
   | "rrx" => SOME A.Rrx | _ => NONE)

end
