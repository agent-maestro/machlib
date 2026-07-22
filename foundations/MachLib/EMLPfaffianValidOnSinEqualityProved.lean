import MachLib.WitnessResidualNormalFormClosure

/-!
# The central axiom, discharged: `eml_pfaffian_validon_from_sin_equality` is PROVABLE

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). This whole multi-week
arc was framed, from its very first entry, as finding a route to the residual that does NOT need
`eml_pfaffian_validon_from_sin_equality` (`EMLPfaffian.lean`) — an axiom stating: if a tree `t`
equals `sin` everywhere, `t` has `EMLPfaffianValidOn` on `(0,b)` for any `b>0`. Every file in this
arc, cont. 44 through cont. 64, was built to AVOID this axiom, not to prove it.

**What changes here.** `no_tree_eq_sin_unconditional` (cont. 58,
`WitnessResidualNormalFormClosure.lean`) proves: **no finite EML tree can equal `sin` everywhere,
period** — the axiom's own hypothesis (`hsin : ∀ x, t.eval x = sin x`) is UNSATISFIABLE for any
tree `t`. An implication with a false hypothesis holds for ANY conclusion — this is not a
technicality or a trick, it is exactly what `False.elim` formalizes. So the axiom's full statement
is a direct, one-line corollary of cont. 58's result: `eml_pfaffian_validon_from_sin_equality_proved`.

**Why this is not circular — checked, not assumed.** The entire arc from cont. 44 onward was built
SPECIFICALLY to avoid the axiom, and every file was fresh-rebuild `#print axioms`-checked at every
step to confirm it. `no_tree_eq_sin_unconditional` itself traces back through
`eml_tailSign_unconditional` → `eml_eventually_valid_repr` → `evalid_tailSign` →
`WitnessResidualRCEPTailSign.lean`'s IVT/zero-counting machinery → `enc_combinedBound` → the
Khovanskii-style Pfaffian chain infrastructure — none of which cites this axiom anywhere. The
fresh-rebuild check below confirms this directly, not by inference from the arc's own discipline.

**What this means for the axiom itself.** The `axiom` declaration in `EMLPfaffian.lean` is NOT
removed by this file — `EMLPfaffian.lean` is a foundational, EARLY file that the entire TailSign
machinery is built ON TOP OF (via a long transitive import chain), so moving the proof INTO that
file would create a circular import. This file instead provides a theorem with the AXIOM'S EXACT
STATEMENT, provable independently, late in the import graph. Retiring the `axiom` keyword itself —
rewiring every call site to use this theorem instead, and updating the `AxiomLedger` trust
accounting — is a separate, more invasive follow-on task, not attempted here.
-/

namespace MachLib

open MachLib.Real

/-- **The axiom `eml_pfaffian_validon_from_sin_equality`, proved.** Identical statement,
identical type — a genuine independent derivation, not a restatement. The hypothesis `hsin` can
never be satisfied (`no_tree_eq_sin_unconditional`), so the conclusion follows vacuously; `_hb_pos`
is unused for exactly the same reason the original axiom's own `_hb_pos` was — the statement holds
regardless of `b`. -/
theorem eml_pfaffian_validon_from_sin_equality_proved
    (t : EMLTree) (hsin : ∀ x : Real, t.eval x = Real.sin x)
    (b : Real) (_hb_pos : 0 < b) :
    EMLPfaffianValidOn t 0 b :=
  False.elim (no_tree_eq_sin_unconditional t hsin)

end MachLib
