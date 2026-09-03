/-
  tools/machsig/extract.lean — MachSig Phase 1 declaration-level extractor.

  Emits one tab-separated MSIG row per MachLib declaration. Reuses the audited proof spine
  (`getEnv`, `Lean.collectAxioms`) rather than building a parallel scanner, per Phase 0 Finding 5.

  WHAT THIS DOES *NOT* DO. It censuses DECLARATIONS. The grammar-level features of Phase 0.5
  (eml_node_count, fOcc, trans1_head_counts) are properties of TERMS, and terms are not
  first-class objects in the environment — a declaration does not "have" an EMLTree unless one
  appears inside it. Those need a separate term-level extractor and are absent here, not null.

  Run:  lake env lean tools/machsig/extract.lean
-/
import MachLib
open Lean Elab Command Term Meta

private def isMachLib (n : Name) : Bool := (`MachLib).isPrefixOf n

private def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque" | .ctorInfo _ => "ctor" | .inductInfo _ => "inductive"
  | .recInfo _ => "rec" | .quotInfo _ => "quot"

/-- Constants referenced directly in an expression. DIRECT references only: this is the
    declaration's own surface, not the transitive closure. `collectAxioms` supplies the
    transitive axiom view separately, and the two must not be conflated. -/
private partial def constsIn (e : Expr) (acc : NameSet) : NameSet :=
  match e with
  | .const n _ => acc.insert n
  | .app f a => constsIn a (constsIn f acc)
  | .lam _ t b _ => constsIn b (constsIn t acc)
  | .forallE _ t b _ => constsIn b (constsIn t acc)
  | .letE _ t v b _ => constsIn b (constsIn v (constsIn t acc))
  | .mdata _ b => constsIn b acc
  | .proj _ _ b => constsIn b acc
  | _ => acc

run_cmd Command.liftTermElabM do
  let env ← getEnv
  let mut seen := 0
  IO.println "MSIG_SCHEMA\tname\tkind\tmodule\tbinder_count\tprop_binder_count\taxiom_count\tdepends_on_sorry\ttype_direct_consts\tvalue_direct_consts\thas_value"
  for (nm, ci) in env.constants.toList do
    if isMachLib nm && !nm.isInternal then
      seen := seen + 1
      let (binders, props) ← Meta.forallTelescopeReducing ci.type fun xs _ => do
        let mut p := 0
        for x in xs do
          if ← Meta.isProp (← Meta.inferType x) then p := p + 1
        pure (xs.size, p)
      let ax ← Lean.collectAxioms nm
      let hasSorry := ax.any (· == ``sorryAx)
      let tdeps := (constsIn ci.type {}).size
      -- `ConstantInfo.value?` is NONE for theorems here; destructure explicitly or the proof
      -- layer is silently empty for every theorem in the corpus (found in Phase 2A).
      let valE : Option Expr := match ci with
        | .thmInfo v => some v.value
        | .defnInfo v => some v.value
        | .opaqueInfo v => some v.value
        | _ => none
      let vdeps := match valE with
        | some v => (constsIn v {}).size
        | none => 0
      let hasVal := valE.isSome
      let mod := match env.getModuleIdxFor? nm with
        | some i => (env.header.moduleNames[i.toNat]!).toString
        | none => "<current>"
      IO.println s!"MSIG\t{nm}\t{kindOf ci}\t{mod}\t{binders}\t{props}\t{ax.size}\t{hasSorry}\t{tdeps}\t{vdeps}\t{hasVal}"
  IO.println s!"MSIG_TOTAL\t{seen}"
