import MachLib.Rolle
import MachLib.Lemmas
import MachLib.Ring

/-!
# Continuity + sign preservation — toward the in-model IVT (Gate 2d, IFT gate — brick 1.b.1)

Building the Intermediate Value Theorem in-model from the completeness axiom `sup_exists`. `HasDerivAt` is
an opaque axiom, so continuity is bridged by ONE fundamental, witnessable axiom `hasDerivAt_continuousAt`
(differentiable ⟹ continuous). This file provides the ε-δ `ContinuousAt`, that bridge, and the
**sign-preservation** lemmas the IVT sup-construction turns on: a continuous function positive (negative) at
a point stays positive (negative) on a neighborhood. The IVT itself (brick 1.b.2) then takes
`c = sup {x : f x ≤ 0}` and rules out `f c < 0` and `f c > 0` via these.
-/

namespace MachLib
namespace Real

/-- ε-δ continuity at a point. -/
def ContinuousAt (f : Real → Real) (x : Real) : Prop :=
  ∀ ε : Real, 0 < ε → ∃ δ : Real, 0 < δ ∧ ∀ y : Real, abs (y - x) < δ → abs (f y - f x) < ε

/-- **Differentiable ⟹ continuous** — the one new analytic axiom (witnessable against Mathlib), bridging
the opaque `HasDerivAt` to continuity. -/
axiom hasDerivAt_continuousAt {f : Real → Real} {f' x : Real} :
    HasDerivAt f f' x → ContinuousAt f x

/-! ## abs helpers -/

private theorem neg_neg_of_pos {v : Real} (h : 0 < v) : -v < 0 := by
  have h2 := add_lt_add_left h (-v)
  rw [add_zero, neg_add_self] at h2
  exact h2

private theorem abs_of_neg {t : Real} (h : t < 0) : abs t = -t := by
  unfold abs
  rw [if_neg (fun hle => lt_irrefl_ax t (lt_of_lt_of_le_r h hle))]

/-- `|u − v| < v ⟹ 0 < u`: closeness within `v` of a value at distance `v` keeps `u` positive. -/
theorem pos_of_abs_sub_lt {u v : Real} (h : abs (u - v) < v) : 0 < u := by
  have hv : 0 < v := lt_of_le_of_lt_r (abs_nonneg (u - v)) h
  rcases lt_total 0 u with hu | hu | hu
  · exact hu
  · exfalso
    have hval : abs (u - v) = v := by
      rw [← hu, show (0 : Real) - v = -v from by mach_ring, abs_of_neg (neg_neg_of_pos hv)]
      mach_ring
    rw [hval] at h; exact lt_irrefl_ax v h
  · exfalso
    have hshift : u - v < 0 := by
      have h1 : u - v < -v := by
        have h2 := add_lt_add_left hu (-v)
        rw [show -v + u = u - v from by mach_mpoly [u, v], add_zero] at h2
        exact h2
      exact lt_trans_ax h1 (neg_neg_of_pos hv)
    rw [abs_of_neg hshift] at h
    have h0u : 0 < u := by
      have hnu : -u < 0 := by
        have h3 := add_lt_add_left h (-v)
        rw [show -v + -(u - v) = -u from by mach_mpoly [u, v], neg_add_self] at h3
        exact h3
      have h4 := add_lt_add_left hnu u
      rw [add_neg, add_zero] at h4
      exact h4
    exact lt_irrefl_ax u (lt_trans_ax hu h0u)

/-- **Sign preservation (positive).** A continuous function positive at `x` is positive on a neighborhood. -/
theorem pos_nbhd_of_continuousAt {f : Real → Real} {x : Real}
    (hc : ContinuousAt f x) (hpos : 0 < f x) :
    ∃ δ : Real, 0 < δ ∧ ∀ y : Real, abs (y - x) < δ → 0 < f y := by
  obtain ⟨δ, hδ, hy⟩ := hc (f x) hpos
  exact ⟨δ, hδ, fun y hyδ => pos_of_abs_sub_lt (hy y hyδ)⟩

private theorem abs_neg (t : Real) : abs (-t) = abs t := by
  rcases lt_total t 0 with h | h | h
  · have hpos : 0 < -t := by
      have h2 := add_lt_add_left h (-t); rw [add_zero, neg_add_self] at h2; exact h2
    rw [abs_of_nonneg (le_of_lt_r hpos), abs_of_neg h]
  · rw [h, show -(0 : Real) = 0 from by mach_ring]
  · rw [abs_of_neg (neg_neg_of_pos h), abs_of_nonneg (le_of_lt_r h), show -(-t) = t from by mach_ring]

/-- **Sign preservation (negative).** A continuous function negative at `x` is negative on a neighborhood.
Reduces to the positive case for `−f` (which is continuous). -/
theorem neg_nbhd_of_continuousAt {f : Real → Real} {x : Real}
    (hc : ContinuousAt f x) (hneg : f x < 0) :
    ∃ δ : Real, 0 < δ ∧ ∀ y : Real, abs (y - x) < δ → f y < 0 := by
  have hpos : 0 < -f x := by
    have h2 := add_lt_add_left hneg (-f x); rw [add_zero, neg_add_self] at h2; exact h2
  have hcn : ContinuousAt (fun z => -f z) x := by
    intro ε hε
    obtain ⟨δ, hδ, hy⟩ := hc ε hε
    refine ⟨δ, hδ, fun y hyδ => ?_⟩
    rw [show -f y - -f x = -(f y - f x) from by mach_ring, abs_neg]
    exact hy y hyδ
  obtain ⟨δ, hδ, hy⟩ := pos_nbhd_of_continuousAt hcn hpos
  refine ⟨δ, hδ, fun y hyδ => ?_⟩
  have h3 : 0 < -f y := hy y hyδ
  have h4 := add_lt_add_left h3 (f y)
  rw [add_zero, add_neg] at h4
  exact h4

end Real
end MachLib
