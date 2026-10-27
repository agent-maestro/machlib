import MachLib
open Lean Elab Command

/-! Statement-identity probe for the second 2026-10-27 transition (checks C1, C5 and C7 of
`docs/machsig/transition_2026-10-27b.py`): the removal of the two false Forge-bridge axioms.

Run from `foundations/` on the built branch: `tools/capped_lean.sh --cap 16G lake env lean
docs/machsig/evidence-2026-10-27b/statement_probe.lean`. It writes `statement_probe.tsv` beside itself.

The serializers are byte-for-byte copies of the two gate 14 hashes (as in `evidence-2026-10-27/`):
`serT` = `tools/machsig/extract_statement.lean`'s `ser` (a theorem's digest `d` is the first 32 hex digits of
`sha256(serT type)`), `serA` = `tools/machsig/extract_trust.lean`'s `serExpr` (an axiom's pin is `sha256(serA type)`).
It serializes the three control propositions of `ForgeBridgeControls` (each should be EXACTLY an old statement), the
restated `interval_add_scale` and the statement it is meant to have (`ExpectedNewIntervalAddScale`, written out
below), and unchanged declarations as serializer controls. -/

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque" | .ctorInfo _ => "ctor" | .inductInfo _ => "inductive"
  | .recInfo _ => "rec" | .quotInfo _ => "quot"

partial def serLevel (ps : List Name) : Level → String
  | .zero => "0"
  | .succ l => "(s " ++ serLevel ps l ++ ")"
  | .max a b => "(max " ++ serLevel ps a ++ " " ++ serLevel ps b ++ ")"
  | .imax a b => "(imax " ++ serLevel ps a ++ " " ++ serLevel ps b ++ ")"
  | .param n => match ps.idxOf? n with
    | some i => "u" ++ toString i
    | none => "(free " ++ n.toString ++ ")"
  | .mvar _ => "(?)"

/-- copy of `extract_trust.lean`'s `serExpr` (axiom pins) -/
partial def serA (ps : List Name) : Expr → String
  | .bvar i => "(B " ++ toString i ++ ")"
  | .fvar _ => "(F)"
  | .mvar _ => "(M)"
  | .sort l => "(S " ++ serLevel ps l ++ ")"
  | .const n ls => "(C " ++ n.toString ++ " [" ++ " ".intercalate (ls.map (serLevel ps)) ++ "])"
  | .app f a => "(A " ++ serA ps f ++ " " ++ serA ps a ++ ")"
  | .lam _ t b _ => "(L " ++ serA ps t ++ " " ++ serA ps b ++ ")"
  | .forallE _ t b _ => "(P " ++ serA ps t ++ " " ++ serA ps b ++ ")"
  | .letE _ t v b _ => "(Z " ++ serA ps t ++ " " ++ serA ps v ++ " " ++ serA ps b ++ ")"
  | .lit (.natVal n) => "(N " ++ toString n ++ ")"
  | .lit (.strVal s) => "(T " ++ s.quote ++ ")"
  | .mdata _ e => serA ps e
  | .proj s i e => "(J " ++ s.toString ++ " " ++ toString i ++ " " ++ serA ps e ++ ")"

/-- copy of `extract_statement.lean`'s `ser` (theorem digests) -/
partial def serT : Expr → String
  | .bvar i => "b" ++ toString i
  | .fvar _ => "f"
  | .mvar _ => "m"
  | .sort _ => "s"
  | .const n _ => "c" ++ n.toString
  | .app f a => "(" ++ serT f ++ " " ++ serT a ++ ")"
  | .lam _ t b _ => "L<" ++ serT t ++ ">" ++ serT b
  | .forallE _ t b _ => "P<" ++ serT t ++ ">" ++ serT b
  | .letE _ t v b _ => "E<" ++ serT t ++ "|" ++ serT v ++ ">" ++ serT b
  | .lit (.natVal k) => "n" ++ toString k
  | .lit (.strVal s) => "t" ++ s
  | .mdata _ b => serT b
  | .proj s i b => "j" ++ s.toString ++ toString i ++ serT b


namespace MachLib.Real
/-- What the restated `interval_add_scale` is meant to say: the old statement with `j ≤ 1` and `k ≤ 1` replaced by
`j + k ≤ 1`. -/
def ExpectedNewIntervalAddScale : Prop :=
  ∀ (x y j k : Real), 0 < j → 0 < k → j + k ≤ 1 → 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 →
    (0 : Real) ≤ x * j + y * k ∧ x * j + y * k ≤ 1
end MachLib.Real

def outPath : System.FilePath := "docs/machsig/evidence-2026-10-27b/statement_probe.tsv"

run_cmd do
  let env ← getEnv
  let mut rows : Array String := #[]
  for nm in [`MachLib.Real.ForgeBridgeControls.OldUnitLitLeStatement,
             `MachLib.Real.ForgeBridgeControls.OldWeightSumLeStatement,
             `MachLib.Real.ForgeBridgeControls.OldIntervalAddScaleStatement,
             `MachLib.Real.ExpectedNewIntervalAddScale] do
    match env.find? nm with
    | some (.defnInfo v) => rows := rows.push s!"DEFVAL\t{nm}\t{serA v.levelParams v.value}\t{serT v.value}"
    | _ => rows := rows.push s!"DEFVAL\t{nm}\tABSENT\tABSENT"
  for nm in [`MachLib.Real.interval_add_scale] do
    match env.find? nm with
    | some ci => rows := rows.push s!"THM\t{nm}\t{kindOf ci}\t{serT ci.type}"
    | none => rows := rows.push s!"THM\t{nm}\tABSENT\t-"
  for nm in [`MachLib.Real.interval_scale_unit_lit_le, `MachLib.Real.interval_weight_sum_le] do
    rows := rows.push s!"GONE\t{nm}\t{(env.find? nm).isSome}"
  for nm in [`MachLib.Real.hasDerivAt_continuousAt, `MachLib.Real.HasDerivAt2_comp, `MachLib.Real.floor_le,
             `MachLib.Real.rolle_ct] do
    match env.find? nm with
    | some ci => rows := rows.push s!"CTRL_AX\t{nm}\t{serA ci.levelParams ci.type}"
    | none => rows := rows.push s!"CTRL_AX\t{nm}\tABSENT"
  for nm in [`MachLib.Real.cosh_ge_one, `MachLib.Real.hasDerivAt2_exp_sum, `MachLib.Real.mean_value_theorem_ct] do
    match env.find? nm with
    | some ci => rows := rows.push s!"CTRL_THM\t{nm}\t{serT ci.type}"
    | none => rows := rows.push s!"CTRL_THM\t{nm}\tABSENT"
  let sorted := rows.qsort (· < ·)
  IO.FS.writeFile outPath (String.intercalate "\n" sorted.toList ++ "\n")
  logInfo m!"statement_probe: {sorted.size} rows -> {outPath}"
