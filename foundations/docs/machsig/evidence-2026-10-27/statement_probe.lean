import MachLib
open Lean Elab Command

/-! Statement-identity probe for the 2026-10-27 transition (checks C1, C2 and C6 of
`docs/machsig/transition_2026-10-27.py`).

Run from `foundations/` on the built branch: `tools/capped_lean.sh --cap 16G lake env lean
docs/machsig/evidence-2026-10-27/statement_probe.lean`. It writes `statement_probe.tsv` beside itself.

It carries byte-for-byte copies of the two serializers gate 14 hashes:
  * `serT` = `tools/machsig/extract_statement.lean`'s `ser`: a THEOREM's digest `d` is the first 32 hex digits of
    `sha256(serT type)`;
  * `serA` = `tools/machsig/extract_trust.lean`'s `serExpr`: an AXIOM's pin is `sha256(serA type)`.

For every theorem with a leading hypothesis named `hcont` concluding `MachLib.Real.ContinuousAt` (after that
hypothesis's own leading binders), and every axiom with any such hypothesis, it removes those hypotheses (each must be
unused by the rest of the type), counts them, and serializes what is left: if the change only ADDED the hypothesis, that hash is the old statement's. It also
serializes the two control propositions' definitions (`OldImplicitStatement`, `OldCurveCountStatement`), which should
be EXACTLY the old axiom's and the old theorem's statements, and a few unchanged declarations as serializer controls. -/

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

/-- The conclusion of a hypothesis after its own leading `∀`s: is its head `ContinuousAt`? -/
partial def concludesContinuousAt : Expr → Bool
  | .forallE _ _ b _ => concludesContinuousAt b
  | .mdata _ e => concludesContinuousAt e
  | e => e.getAppFn.isConstOf `MachLib.Real.ContinuousAt

/-- Remove every leading binder of the type that `pick` selects (by name) and whose domain concludes `ContinuousAt`,
when the rest does not use it. Returns the stripped type, the number removed, and the number selected but USED (which
must be 0). Theorems select the binder named `hcont`, the name every added hypothesis has; the two axioms take theirs
anonymously, so for an axiom every such binder is selected. -/
partial def strip (pick : Name → Bool) : Expr → Expr × Nat × Nat
  | .forallE n t b bi =>
    if pick n && concludesContinuousAt t then
      if b.hasLooseBVar 0 then
        let (b', k, u) := strip pick b; (.forallE n t b' bi, k, u + 1)
      else
        let (b', k, u) := strip pick (b.lowerLooseBVars 1 1); (b', k + 1, u)
    else
      let (b', k, u) := strip pick b; (.forallE n t b' bi, k, u)
  | .mdata _ e => strip pick e
  | e => (e, 0, 0)

def outPath : System.FilePath := "docs/machsig/evidence-2026-10-27/statement_probe.tsv"

run_cmd do
  let env ← getEnv
  let mut rows : Array String := #[]
  for (nm, ci) in env.constants.toList do
    let own := (`MachLib).isPrefixOf nm || (match env.getModuleIdxFor? nm with
      | some i => (`MachLib).isPrefixOf (env.header.moduleNames[i.toNat]!) | none => false)
    unless own do continue
    let pick : Name → Bool := match ci with
      | .axiomInfo _ => fun _ => true
      | _ => fun n => n == `hcont
    let (t', k, u) := strip pick ci.type
    if k == 0 && u == 0 then continue
    match ci with
    | .thmInfo _ => rows := rows.push s!"STRIP_THM\t{nm}\t{k}\t{u}\t{serT t'}"
    | .axiomInfo _ => rows := rows.push s!"STRIP_AX\t{nm}\t{k}\t{u}\t{serA ci.levelParams t'}"
    | _ => rows := rows.push s!"STRIP_OTHER\t{nm}\t{k}\t{u}\t-"
  -- the two control propositions: their DEFINITIONS, serialized as an axiom pin and as a theorem digest
  for nm in [`MachLib.Real.BivariateImplicitControls.OldImplicitStatement,
             `MachLib.Real.BivariateImplicitControls.OldCurveCountStatement] do
    match env.find? nm with
    | some (.defnInfo v) => rows := rows.push s!"DEFVAL\t{nm}\t{serA v.levelParams v.value}\t{serT v.value}"
    | _ => rows := rows.push s!"DEFVAL\t{nm}\tABSENT\tABSENT"
  -- serializer controls: unchanged declarations whose pins/digests the baseline already holds
  for nm in [`MachLib.Real.hasDerivAt_continuousAt, `MachLib.Real.HasDerivAt2_comp, `MachLib.Real.floor_le,
             `MachLib.Real.rolle_ct] do
    match env.find? nm with
    | some ci => rows := rows.push s!"CTRL_AX\t{nm}\t{serA ci.levelParams ci.type}"
    | none => rows := rows.push s!"CTRL_AX\t{nm}\tABSENT"
  for nm in [`MachLib.Real.cosh_ge_one, `MachLib.Real.hasDerivAt2_exp_sum,
             `MachLib.Real.mean_value_theorem_ct] do
    match env.find? nm with
    | some ci => rows := rows.push s!"CTRL_THM\t{nm}\t{serT ci.type}"
    | none => rows := rows.push s!"CTRL_THM\t{nm}\tABSENT"
  let sorted := rows.qsort (· < ·)
  IO.FS.writeFile outPath (String.intercalate "\n" sorted.toList ++ "\n")
  logInfo m!"statement_probe: {sorted.size} rows -> {outPath}"
