import MachLib.WitnessResidualCosTailSign

/-!
# `sin_not_in_eml_any_depth`/`cos_not_in_eml_any_depth`, re-derived as one-line corollaries

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). Cont. 66 flagged a
sharper question about the axiom discharge: does `no_tree_eq_sin_unconditional` (no finite EML
tree equals `sin`, ANY depth, unconditionally) SUBSUME `sin_not_in_eml_any_depth`
(`EMLExplicitBoundSinBarrier.lean`, no tree of depth `≤ k` equals `sin`, one `k` at a time,
citing `eml_pfaffian_validon_from_sin_equality` in its own proof)? Checked directly: yes.

**`InEMLDepth f k := ∃ t, t.depth ≤ k ∧ ∀x, f x = t.eval x`.** `sin_not_in_eml_any_depth k`
unfolds to "no `t` of depth `≤ k` has `t.eval = sin`." `no_tree_eq_sin_unconditional` rules out
EVERY `t`, regardless of depth, matching `sin` — so the depth bound `t.depth ≤ k` is never even
inspected. The corollary is exactly one line, for every `k` simultaneously.

**Why this file, not an edit to the original.** The original `sin_not_in_eml_any_depth`
(`EMLExplicitBoundSinBarrier.lean`) still cites `eml_pfaffian_validon_from_sin_equality` in its
OWN proof body — genuinely fixing that in place would need the same import-graph restructuring
flagged and deferred in cont. 65/66 (that file is transitively imported by this one's own
dependency chain). Twelve other files reference `sin_not_in_eml_any_depth` by name; rewiring
every one to a hypothetically-modified version was not attempted — instead, this file adds an
INDEPENDENT theorem proving the exact same statement, with a genuinely different (and, per
`#print axioms`, strictly cheaper) proof. The original stays as-is, historical/independent route;
this is the route to cite going forward when a caller doesn't specifically need the depth bound
`k` to be inspected (it never is, given the statement below).
-/

namespace MachLib

open Real

/-- **`sin_not_in_eml_any_depth`, re-derived — one line, zero axiom dependence.** The depth bound
`k` is entirely unused; `no_tree_eq_sin_unconditional` already covers every depth at once. -/
theorem sin_not_in_eml_any_depth_unconditional (k : Nat) :
    ¬ InEMLDepth (fun x : Real => Real.sin x) k := by
  intro ⟨t, _htd, hsin⟩
  exact no_tree_eq_sin_unconditional t (fun x => (hsin x).symm)

/-- **`cos_not_in_eml_any_depth`, re-derived — same shape, `cos` in place of `sin`.** -/
theorem cos_not_in_eml_any_depth_unconditional (k : Nat) :
    ¬ InEMLDepth (fun x : Real => Real.cos x) k := by
  intro ⟨t, _htd, hcos⟩
  exact no_tree_eq_cos_unconditional t (fun x => (hcos x).symm)

end MachLib
