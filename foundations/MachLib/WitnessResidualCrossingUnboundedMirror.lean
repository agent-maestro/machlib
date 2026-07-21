import MachLib.WitnessResidualCrossingUnboundedGeneral
import MachLib.SturmNonOscillation

/-! # Completing the crossing-unboundedness picture: both directions

`WitnessResidualCrossingUnboundedGeneral.lean`'s `eml_A_crossing_B_unbounded_above` needs `B`
INCREASING through zero (`B(x0)=0`, `B(x1)>0` for `x0<x1` — zero-then-positive, left to right).
Every crossing subtree actually built anywhere in this arc (`eml var (const c)`, and every
compound tree derived from it) happens to cross in this one direction, so that was never a real
gap for the trees this arc has seen — but the underlying MECHANISM (`exp(A)≥0` can't cancel
`-log(B)→+∞` as `B→0⁺`) is obviously direction-agnostic: the blow-up happens wherever `B` is
small and positive, whether that's approached from the left or the right of the touch point.
Checking that formally (raised while considering whether a DECREASING-through-zero right child —
e.g. built from `boundedNonConstantWitness`, which IS proven decreasing
(`boundedNonConstantWitness_deriv_neg`) — might escape the obstruction) confirms it does not:
the mirror case is just as unbounded, via the same IVT technique with the sign of the auxiliary
function flipped.

**`eml_A_crossing_B_unbounded_above_mirror`**: `B` POSITIVE at an earlier point `x0` and zero at a
LATER point `x1` (decreasing-through-zero) — `eml A B` is still unbounded above, for any `A`.
Same proof shape as the increasing case, with `h(z) := exp(-(M+1)) - B(z)` in place of
`B(z) - exp(-(M+1))` (flips the sign so `intermediate_value_of_hasDerivAt`'s required order,
negative-then-positive left to right, is still met) — otherwise identical: IVT gives an exact hit
`B(c) = exp(-(M+1))` when `exp(-(M+1)) < B(x0)`, or `x0` itself already works directly when it
doesn't.

**Net effect**: between the two directions, EVERY possible genuine, differentiable, finite-point
zero crossing of a right child — regardless of which way it crosses — forces `eml A B`
unbounded, for any `A`. There is no third direction to check (a differentiable real function
crossing zero transversally is locally either increasing or decreasing through it — nothing else
is possible). The tree-depth induction's negative half is now closed exhaustively, not just for
the crossings this arc happened to build. -/

namespace MachLib
namespace Real

/-- Mirror of `eml_A_crossing_B_unbounded_above`: if `B` is POSITIVE at an EARLIER point `x0` and
touches zero at a LATER point `x1` (the opposite direction — decreasing-through-zero rather than
increasing-through-zero), `eml A B` is STILL unbounded above, for any `A`. The blow-up now happens
approaching `x1` from the left (where `B` is still positive, shrinking toward `0`), rather than
approaching `x0` from the right. -/
theorem eml_A_crossing_B_unbounded_above_mirror (A B : EMLTree) (x0 x1 : Real) (hx0x1 : x0 < x1)
    (hBx0pos : 0 < B.eval x0) (hBx1 : B.eval x1 = 0)
    (hBdiff : ∀ z : Real, x0 ≤ z → z ≤ x1 → ∃ Bd : Real, HasDerivAt B.eval Bd z) (M : Real) :
    ∃ x : Real, M < (EMLTree.eml A B).eval x := by
  rcases lt_total (Real.exp (-(M + 1))) (B.eval x0) with hcase | hcase | hcase
  · -- IVT case: find c with B.eval c = exp(-(M+1)) exactly, via h := exp(-(M+1)) - B
    have hdiff2 : ∀ z : Real, x0 ≤ z → z ≤ x1 →
        ∃ h' : Real, HasDerivAt (fun w => Real.exp (-(M + 1)) - B.eval w) h' z := by
      intro z hz0 hz1
      obtain ⟨Bd, hBd⟩ := hBdiff z hz0 hz1
      refine ⟨0 - Bd, HasDerivAt_sub (fun _ => Real.exp (-(M + 1))) B.eval 0 Bd z
        (HasDerivAt_const _ z) hBd⟩
    have hha : (fun w => Real.exp (-(M + 1)) - B.eval w) x0 < 0 := by
      show Real.exp (-(M + 1)) - B.eval x0 < 0
      exact sub_neg_of_lt' hcase
    have hhb : 0 < (fun w => Real.exp (-(M + 1)) - B.eval w) x1 := by
      show 0 < Real.exp (-(M + 1)) - B.eval x1
      rw [hBx1]
      have h1 : Real.exp (-(M + 1)) - 0 = Real.exp (-(M + 1)) := sub_zero _
      rw [h1]
      exact Real.exp_pos _
    obtain ⟨c, hc0, hc1, hBc⟩ := intermediate_value_of_hasDerivAt
      (fun w => Real.exp (-(M + 1)) - B.eval w) x0 x1 hx0x1 hdiff2 hha hhb
    have hBceq : B.eval c = Real.exp (-(M + 1)) := by
      have h1 : Real.exp (-(M + 1)) - B.eval c + B.eval c = 0 + B.eval c := by rw [hBc]
      have h2 : Real.exp (-(M + 1)) - B.eval c + B.eval c = Real.exp (-(M + 1)) := by mach_ring
      have h3 : (0 : Real) + B.eval c = B.eval c := by mach_ring
      rw [h2, h3] at h1
      exact h1.symm
    refine ⟨c, ?_⟩
    show M < Real.exp (A.eval c) - Real.log (B.eval c)
    rw [hBceq, Real.log_exp]
    have hexpA : (0 : Real) ≤ Real.exp (A.eval c) := le_of_lt (Real.exp_pos _)
    have hstep : M + 1 ≤ Real.exp (A.eval c) - -(M + 1) := by
      have h1 : (0 : Real) - -(M + 1) ≤ Real.exp (A.eval c) - -(M + 1) :=
        sub_le_sub_right hexpA (-(M + 1))
      have h2 : (0 : Real) - -(M + 1) = M + 1 := by mach_ring
      rwa [h2] at h1
    have hlt : M < M + 1 := by
      have h := add_lt_add_left zero_lt_one_ax M
      rwa [add_zero] at h
    exact lt_of_lt_of_le hlt hstep
  · -- exp(-(M+1)) = B.eval x0: x0 itself already works
    refine ⟨x0, ?_⟩
    show M < Real.exp (A.eval x0) - Real.log (B.eval x0)
    rw [← hcase, Real.log_exp]
    have hexpA : (0 : Real) ≤ Real.exp (A.eval x0) := le_of_lt (Real.exp_pos _)
    have hstep : M + 1 ≤ Real.exp (A.eval x0) - -(M + 1) := by
      have h1 : (0 : Real) - -(M + 1) ≤ Real.exp (A.eval x0) - -(M + 1) :=
        sub_le_sub_right hexpA (-(M + 1))
      have h2 : (0 : Real) - -(M + 1) = M + 1 := by mach_ring
      rwa [h2] at h1
    have hlt : M < M + 1 := by
      have h := add_lt_add_left zero_lt_one_ax M
      rwa [add_zero] at h
    exact lt_of_lt_of_le hlt hstep
  · -- exp(-(M+1)) < B.eval x0 is FALSE means B.eval x0 < exp(-(M+1)): x0 itself works too
    refine ⟨x0, ?_⟩
    show M < Real.exp (A.eval x0) - Real.log (B.eval x0)
    have hlog_le : Real.log (B.eval x0) ≤ -(M + 1) := by
      have h := log_mono hBx0pos (le_of_lt hcase)
      rwa [Real.log_exp] at h
    have hexpA : (0 : Real) ≤ Real.exp (A.eval x0) := le_of_lt (Real.exp_pos _)
    have hstep1 : Real.exp (A.eval x0) - -(M + 1) ≤ Real.exp (A.eval x0) - Real.log (B.eval x0) :=
      sub_le_sub_left hlog_le _
    have hstep2 : M + 1 ≤ Real.exp (A.eval x0) - -(M + 1) := by
      have h1 : (0 : Real) - -(M + 1) ≤ Real.exp (A.eval x0) - -(M + 1) :=
        sub_le_sub_right hexpA (-(M + 1))
      have h2 : (0 : Real) - -(M + 1) = M + 1 := by mach_ring
      rwa [h2] at h1
    have hlt : M < M + 1 := by
      have h := add_lt_add_left zero_lt_one_ax M
      rwa [add_zero] at h
    exact lt_of_lt_of_le hlt (le_trans hstep2 hstep1)

/-- **Both directions, packaged.** `B` crosses zero SOMEHOW between `p` and `q` (either
increasing or decreasing through it) ⟹ `eml A B` is unbounded above, for any `A`. A caller who
just knows "`B` touches `0` and is positive somewhere else nearby" doesn't need to know which
side is which. -/
theorem eml_A_crossing_B_unbounded_above_either_direction (A B : EMLTree) (p q : Real)
    (hpq : p < q) (hBdiff : ∀ z : Real, p ≤ z → z ≤ q → ∃ Bd : Real, HasDerivAt B.eval Bd z)
    (hcross : (B.eval p = 0 ∧ 0 < B.eval q) ∨ (0 < B.eval p ∧ B.eval q = 0)) (M : Real) :
    ∃ x : Real, M < (EMLTree.eml A B).eval x := by
  rcases hcross with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact eml_A_crossing_B_unbounded_above A B p q hpq h1 h2 hBdiff M
  · exact eml_A_crossing_B_unbounded_above_mirror A B p q hpq h1 h2 hBdiff M

end Real
end MachLib
