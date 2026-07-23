import MachLib.WitnessResidualContinuousTargetMetaLemma
import MachLib.Forge

/-!
# Track C, item C9: the general periodic-target barrier

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). Both external reviews'
own top-ranked frontier: does `no_tree_eq_target_of_not_tailSign` (`WitnessResidualContinuous
TargetMetaLemma.lean`) already cover EVERY nonconstant continuous periodic function "for free"?
The "NEXT OBJECTIVES" round (2026-07-22) checked this directly rather than assuming it, and
concluded the argument needed the infimum of `TARGET` to be ATTAINED (a genuine Extreme Value
Theorem), which this codebase didn't have — `continuousAt_bddAbove_Icc` gave boundedness only.
`ExtremeValueAttainment.lean` (this same round) closes that gap: `continuousAt_attains_max_Icc`/
`continuousAt_attains_min_Icc`, the classical `1/(M−f)` argument, built from scratch.

**Erratum, found while actually building the barrier theorem below, not assumed.** EVT-attainment
turns out NOT to be the binding constraint for THIS specific theorem. Re-examining the mechanism:
`TailSign.pos`/`.neg` are refuted by finding a point, arbitrarily far out, where `TARGET x = L`
EXACTLY — and periodicity makes EVERY value of `TARGET` recur arbitrarily far out, not just the
extremal ones. `L := TARGET x₀` for ANY fixed basepoint `x₀` works exactly as well as `L :=
inf(TARGET)` for this purpose — the already-proven `sin_not_tailSign` (`WitnessResidualTailSign.
lean`) is itself a confirming precedent: it uses `L = sin 0 = 0`, not `inf(sin) = -1`. So the
theorem below uses `x₀ := 0` directly and needs no EVT-attainment at all. `ExtremeValueAttainment.
lean` stands as a genuine, separate, correctly-motivated result (it closes exactly the gap both
reviews flagged, and is real new machinery this codebase lacked) — it is simply not, on inspection,
what THIS particular barrier needs. Recorded here rather than silently dropped, matching this
document's own "checked directly, report deviations" discipline (cf. cont. 76's erratum).

**The mechanism, concretely.** `Periodic f p := ∀x, f(x+p) = f x` extends to `f(x + n·p) = f x` for
every `n : Nat` by induction (`periodic_add_natCast_mul`); combined with the Archimedean axiom,
any basepoint's value can be pushed past any threshold `R` (`periodic_push_past`). Given `L :=
TARGET 0`: pushing `0` itself past `R` gives a point where `TARGET x − L = 0`, refuting both
`TailSign.pos` and `.neg` (whichever threshold `R` either supplies, `TARGET x − L` is neither
`> 0` nor `< 0` there). Nonconstancy (`∃x₁ x₂, TARGET x₁ ≠ TARGET x₂`) gives some point `x'` with
`TARGET x' ≠ L` (at least one of `x₁`, `x₂` must differ from `L`, else they'd agree with each
other); pushing `x'` past `R` refutes `TailSign.zero`. All three `TailSign` cases fall, so
`no_tree_eq_target_of_not_tailSign` applies directly.

`sorryAx`-free, no new axioms — everything here is `natCast`/`archimedean`-derived, both already
load-bearing throughout this arc (`sin_not_tailSign` uses the identical Archimedean-pushing idea,
just hand-specialized to `2π`; this file makes it generic in the period `p`).
-/

namespace MachLib
namespace Real

open MachLib

/-! ## §1 — Periodicity -/

/-- `f` repeats every `p`. -/
def Periodic (f : Real → Real) (p : Real) : Prop := ∀ x : Real, f (x + p) = f x

private theorem periodic_shift_local (x p : Real) (k : Nat) :
    x + natCast (k + 1) * p = (x + natCast k * p) + p := by
  rw [natCast_succ]
  mach_mpoly [x, natCast k, p]

/-- Periodicity extends to every natural multiple of the period, by induction. -/
theorem periodic_add_natCast_mul {f : Real → Real} {p : Real} (hf : Periodic f p) :
    ∀ (n : Nat) (x : Real), f (x + natCast n * p) = f x := by
  intro n
  induction n with
  | zero => intro x; rw [natCast_zero, zero_mul, add_zero]
  | succ k ih =>
      intro x
      rw [periodic_shift_local x p k, hf, ih]

private theorem div_mul_cancel_local3 {a b : Real} (hb : b ≠ 0) : a / b * b = a := by
  rw [div_def a b hb, mul_assoc, mul_comm (1 / b) b, mul_inv b hb, mul_one_ax]

/-- **Push arbitrarily far.** For any basepoint `x0` and any threshold `R`, some natural multiple
of a positive period `p` pushes `x0` past `R`. Pure Archimedean scaling: `n` dominating `(R−x0)/p`
gives `n·p` dominating `R−x0` after cross-multiplying by `p > 0`. -/
theorem periodic_push_past (p : Real) (hp : 0 < p) (x0 R : Real) :
    ∃ n : Nat, R < x0 + natCast n * p := by
  obtain ⟨n, hn⟩ := archimedean ((R - x0) / p)
  refine ⟨n, ?_⟩
  have h2 : R - x0 < natCast n * p := by
    have h1 := mul_lt_mul_of_pos_right hn hp
    rwa [div_mul_cancel_local3 (ne_of_gt hp)] at h1
  have h3 := add_lt_add_left h2 x0
  rwa [show x0 + (R - x0) = R from by mach_mpoly [x0, R]] at h3

/-! ## §2 — The general periodic-target barrier -/

/-- **No finite EML tree equals ANY nonconstant, everywhere-continuous, periodic target.**
Subsumes `no_tree_eq_sin_unconditional_via_continuous_meta` (`sin` is `2π`-periodic, nonconstant)
and `no_tree_eq_nestedTarget_fully_unconditional`-style results uniformly, without re-deriving
the recurrence facts by hand for each target — genuinely reachable via `TARGET 0` as the
reference level, per this file's own header erratum (no EVT-attainment needed). -/
theorem no_tree_eq_periodic_target (TARGET : Real → Real) (p : Real) (hp : 0 < p)
    (hcont : ∀ x : Real, ContinuousAt TARGET x)
    (hperiodic : Periodic TARGET p)
    (hnonconst : ∃ x1 x2 : Real, TARGET x1 ≠ TARGET x2)
    (T : EMLTree) (heq : ∀ x : Real, T.eval x = TARGET x) : False := by
  have hnts : ¬ TailSign (fun x => TARGET x - TARGET 0) := by
    intro htail
    rcases htail with ⟨R, hR⟩ | ⟨R, hR⟩ | ⟨R, hR⟩
    · obtain ⟨n, hn⟩ := periodic_push_past p hp 0 R
      have heqn : TARGET (0 + natCast n * p) = TARGET 0 := periodic_add_natCast_mul hperiodic n 0
      have h := hR (0 + natCast n * p) hn
      rw [heqn, sub_self] at h
      exact lt_irrefl_ax 0 h
    · obtain ⟨n, hn⟩ := periodic_push_past p hp 0 R
      have heqn : TARGET (0 + natCast n * p) = TARGET 0 := periodic_add_natCast_mul hperiodic n 0
      have h := hR (0 + natCast n * p) hn
      rw [heqn, sub_self] at h
      exact lt_irrefl_ax 0 h
    · obtain ⟨x1, x2, hne⟩ := hnonconst
      have hx' : ∃ x' : Real, TARGET x' ≠ TARGET 0 := by
        by_cases hx1 : TARGET x1 = TARGET 0
        · refine ⟨x2, fun hx2 => hne (hx1.trans hx2.symm)⟩
        · exact ⟨x1, hx1⟩
      obtain ⟨x', hx'ne⟩ := hx'
      obtain ⟨n, hn⟩ := periodic_push_past p hp x' R
      have heqn : TARGET (x' + natCast n * p) = TARGET x' := periodic_add_natCast_mul hperiodic n x'
      have h := hR (x' + natCast n * p) hn
      rw [heqn] at h
      exact hx'ne (eq_of_sub_eq_zero_local h)
  exact no_tree_eq_target_of_not_tailSign TARGET (TARGET 0) hcont hnts T heq

/-- **Sanity check: `sin` instantiates cleanly.** Confirms the general theorem genuinely reaches
the same conclusion `no_tree_eq_sin_unconditional_via_continuous_meta` reaches by hand, via
`2π`-periodicity and `sin 0 ≠ sin (π/2)` for nonconstancy. -/
theorem no_tree_eq_sin_via_periodic_barrier (T : EMLTree)
    (heq : ∀ x : Real, T.eval x = Real.sin x) : False := by
  have hcont : ∀ x : Real, ContinuousAt Real.sin x :=
    fun x => hasDerivAt_continuousAt (HasDerivAt_sin x)
  have hperiodic : Periodic Real.sin ((1 + 1) * pi) := sin_periodic
  have hnonconst : ∃ x1 x2 : Real, Real.sin x1 ≠ Real.sin x2 := by
    refine ⟨0, pi / (1 + 1), ?_⟩
    rw [sin_zero, sin_pi_div_two]
    exact zero_ne_one_ax
  exact no_tree_eq_periodic_target Real.sin ((1 + 1) * pi) (mul_pos two_pos pi_pos)
    hcont hperiodic hnonconst T heq

end Real
end MachLib
