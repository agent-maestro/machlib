import MachLib.WitnessResidualSignNecessity

/-! # From "sign-definite" to "quantitatively bounded away" — connecting back to `boundedNonConstantWitness`

`WitnessResidualSignNecessity.lean`'s `eml_A_B_bounded_above_sign_definite` establishes a
QUALITATIVE dichotomy (`B` positive everywhere or non-positive everywhere). Boundedness of
`eml A B` above actually forces something QUANTITATIVE too, essentially for free from the same
algebra: in the positive branch, `B` isn't merely positive — it's bounded AWAY from `0`,
uniformly, by `exp(-M)` where `M` is the tree's own upper bound.

**Why this matters, concretely.** This is EXACTLY the shape `boundedNonConstantWitness`'s own
safe right-child machinery has always used, though never stated this abstractly before:
`boundedNonConstantWitness_Bpos` (`WitnessResidualBoundedNonConstant.lean`) establishes
`0 < exp(exp z) - log c` UNCONDITIONALLY, and the OUTER structures built from it
(`E_BNCW`, `growthCompetitionWitness`, `growthCompetitionWitnessDeep`) all ultimately rely on
right children whose infimum is a POSITIVE constant (`1 - log c`, etc.), not merely "eventually
positive." This file shows that reliance wasn't incidental engineering — it's the QUANTITATIVE
form the sign-necessity dichotomy forces on any bounded compound tree, derived directly rather
than discovered by trial per construction.

**`B_bounded_below_of_eml_bounded_above`**: `eml A B` bounded above by `M`, `B` positive
everywhere ⟹ `∀x, exp(-M) ≤ B.eval x`. Proof: from `exp(A.eval x) - log(B.eval x) ≤ M` and
`exp(A.eval x) ≥ 0` unconditionally, `-M ≤ log(B.eval x)`, then `exp` monotone.

**`A_bounded_above_of_eml_bounded_above_nonpos`**: the dual, degenerate case — if `B ≤ 0`
everywhere, the bound on `eml A B` transfers directly to `exp(A.eval ·)` via the reduction
identity already established (`eml_A_B_eq_exp_A_of_nonpos`).

**`eml_A_B_bounded_above_characterization`**: combines both into the FULL quantitative picture —
exactly one of two mutually exclusive, fully quantified outcomes, for any bounded-above compound
tree in this grammar.

`sorryAx`-free, verified via a genuinely fresh rebuild: same axiom footprint as
`WitnessResidualSignNecessity.lean` (foundational axioms plus `hasDerivAt_continuousAt` and
`sup_exists`) — no dependence on `EMLPfaffianValidOn`. -/

namespace MachLib
namespace Real

/-- If `eml A B` is bounded above by `M` and `B` is positive everywhere, `B` isn't merely
positive — it's bounded AWAY from zero, uniformly, by `exp(-M)`. -/
theorem B_bounded_below_of_eml_bounded_above (A B : EMLTree) (M : Real)
    (hbdd : ∀ x : Real, (EMLTree.eml A B).eval x ≤ M) (hBpos : ∀ x : Real, 0 < B.eval x) :
    ∀ x : Real, Real.exp (-M) ≤ B.eval x := by
  intro x
  have hTx : Real.exp (A.eval x) - Real.log (B.eval x) ≤ M := hbdd x
  have hexpA : (0 : Real) ≤ Real.exp (A.eval x) := le_of_lt (Real.exp_pos _)
  have h1 := add_le_add_left hTx (Real.log (B.eval x))
  have e1 : Real.log (B.eval x) + (Real.exp (A.eval x) - Real.log (B.eval x))
      = Real.exp (A.eval x) := by mach_ring
  rw [e1] at h1
  have step2 : (0 : Real) ≤ Real.log (B.eval x) + M := le_trans hexpA h1
  have h2 := add_le_add_left step2 (-M)
  have e2 : -M + 0 = -M := by mach_ring
  have e3 : -M + (Real.log (B.eval x) + M) = Real.log (B.eval x) := by mach_ring
  rw [e2, e3] at h2
  have h3 := exp_monotone h2
  rwa [Real.exp_log (hBpos x)] at h3

/-- Dual: if `eml A B` is bounded above by `M` and `B` is non-positive everywhere (the
degenerate, dead-branch case), the bound transfers directly to `exp(A.eval ·)`. -/
theorem A_bounded_above_of_eml_bounded_above_nonpos (A B : EMLTree) (M : Real)
    (hbdd : ∀ x : Real, (EMLTree.eml A B).eval x ≤ M) (hBnonpos : ∀ x : Real, B.eval x ≤ 0) :
    ∀ x : Real, Real.exp (A.eval x) ≤ M := by
  intro x
  have h := eml_A_B_eq_exp_A_of_nonpos A B hBnonpos x
  have hTx := hbdd x
  rwa [h] at hTx

/-- **The full quantitative characterization.** `eml A B` bounded above by `M` ⟹ EITHER `B` is
positive everywhere AND bounded away from `0` by `exp(-M)`, OR `B` is non-positive everywhere
(dead branch) AND `exp(A.eval ·) ≤ M` directly. Combines the sign-necessity dichotomy
(`WitnessResidualSignNecessity.lean`) with the quantitative bound each branch actually forces. -/
theorem eml_A_B_bounded_above_characterization (A B : EMLTree)
    (hBdiff : ∀ z : Real, ∃ Bd : Real, HasDerivAt B.eval Bd z)
    (M : Real) (hbdd : ∀ x : Real, (EMLTree.eml A B).eval x ≤ M) :
    (∀ x : Real, 0 < B.eval x ∧ Real.exp (-M) ≤ B.eval x) ∨
    (∀ x : Real, B.eval x ≤ 0 ∧ Real.exp (A.eval x) ≤ M) := by
  rcases eml_A_B_bounded_above_sign_definite A B hBdiff M hbdd with hpos | hnonpos
  · left; intro x; exact ⟨hpos x, B_bounded_below_of_eml_bounded_above A B M hbdd hpos x⟩
  · right; intro x; exact ⟨hnonpos x, A_bounded_above_of_eml_bounded_above_nonpos A B M hbdd hnonpos x⟩

end Real
end MachLib
