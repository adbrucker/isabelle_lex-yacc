(* Functional probe for the antiquotation syntax extension: the optional
   "(level)" after the tag, and the double-quoted string alternative to a
   cartouche body. Dumps the actual parsed C_Ast.comment values (tag, level,
   body text) for a handful of representative comments, so the effect of the
   lexer rules in C11_Parser.thy can be inspected directly rather than taken
   on faith. Not part of the regression suite (C11_Tests.thy already carries
   the permanent versions of these test cases) - this is a standalone,
   re-runnable probe kept for manual inspection. *)
theory AntiqProbe
  imports "C11_Tests"
begin

text\<open>A cartouche body with an explicit level.\<close>
c11\<open>
int b;
//@ setup(2) \<open>Include.append "tmp" [\<open>b\<close>]\<close>
int a = b;
\<close>

text\<open>A quoted-string body with an explicit level.\<close>
c11\<open>
/*@ setup(3) "a plain quoted body" */
int a = 0;
\<close>

text\<open>A quoted-string body with no level (defaults to 0).\<close>
c11\<open>
/*@ setup "a plain quoted body, default level" */
int a = 0;
\<close>

text\<open>
  ACSL-style "@ requires \"...\"" / "@ ensures \"...\"": the leading "@" is
  ACSL's own line-continuation marker, which already matches the tag shape,
  so with the quoted-string body extension these become genuine (level-0)
  antiquotation nodes - see the matching note in C11_Tests.thy.
\<close>
c11\<open>
/*@ requires "n >= 0"
  @ ensures "result >= 0"
 */
int abs(int n) {
  if (n < 0) return -n;
  return n;
}
\<close>

text\<open>
  A bare quote with no tag anywhere nearby: the combined tag+string rule
  only fires when a quote genuinely follows a tag, so this stays ordinary
  comment text.
\<close>
c11\<open>
/* just a "quoted" word here, no tag in sight */
int a = 0;
\<close>

ML \<open>
(* Locates this theory's own last 5 stored units - the ones the five "c11"
   blocks above just produced - without hard-coding their counter values,
   since those shift whenever a block is added/removed above. *)
fun this_theory_units n =
  let
    val thy_name = Context.theory_name {long = false} @{theory}
    val store = CEnv.Ast_Store.get (Context.Theory @{theory})
    val prefix = thy_name ^ "#"
    fun suffix_num k =
      Int.fromString (String.extract (k, String.size prefix, NONE))
    val my_keys =
      Symtab.keys store
      |> List.filter (String.isPrefix prefix)
      |> List.mapPartial (fn k => (case suffix_num k of SOME i => SOME (k, i) | NONE => NONE))
      |> sort (fn ((_, a), (_, b)) => Int.compare (a, b))
      |> map #1
  in List.drop (my_keys, length my_keys - n) end

fun pp_comment (C_Ast.Raw_txt frags) =
      "Raw_txt " ^ String.concatWith " | " (map (fn (t, _) => "[" ^ t ^ "]") frags)
  | pp_comment (C_Ast.Antiquotation ({tag = (tag, _)}, {level}, {cartouche = (body, _)})) =
      "Antiquotation tag=" ^ tag ^ " level=" ^ Int.toString level ^ " body=[" ^ body ^ "]"

fun comments_of_ni ni = (case ni of
      C_Ast.OnlyPos _ => [] | C_Ast.NodeInfo (cs, _) => cs)

fun comments_of (C_Ast.CDeclExt d) = comments_of_ni (C_Ast.nodeInfo_of_CDecl d)
  | comments_of (C_Ast.CFDefExt f) = comments_of_ni (C_Ast.nodeInfo_of_CFunDef f)
  | comments_of _ = []

fun dump_unit key =
  let
    val SOME (C_Ast.Units [C_Ast.CTranslUnit (eds, _)]) = CEnv.get_ast key @{theory}
    val all = List.concat (map comments_of eds)
  in String.concatWith "\n" (map pp_comment all) end

val labels =
  ["setup(2), cartouche body", "setup(3), string body",
   "setup, string body, default level", "requires/ensures (ACSL-style)",
   "bare quote, no tag"]

val report =
  ListPair.map (fn (key, label) => "=== " ^ label ^ " (" ^ key ^ ") ===\n" ^ dump_unit key)
    (this_theory_units 5, labels)
  |> String.concatWith "\n"

val _ = writeln report
\<close>

end
