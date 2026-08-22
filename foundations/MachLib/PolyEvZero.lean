import MachLib.PolyPoleCount

/-!
# The bridge: vanishing on a tail means the zero polynomial

**This module is deliberately outside `algebraFootprint`**, and it is the only one in the arc that
is. Everything from `PolyCanonical` through `cleared_relation_impossible` stays inside the field
axioms; this file is where the analysis begins, and the boundary is drawn here on purpose rather
than discovered later.

## Why it must leave

`pnorm L = []` from "`pev L` vanishes on a tail" is **false over a finite field** — over `𝔽₂` the
list `[0, 1, 1]` is `X² + X`, which vanishes at every point and is not the zero polynomial. It is
the third face of the same obstruction this arc kept meeting (`PolyMulDegree` for extensionality,
`PolyDeriv` for characteristic zero), and the missing ingredient is the same one each time:
`algebraFootprint` is the theory of fields, and fields can be finite.

What supplies it here is `exists_ge_notMem` — beyond any bound there is a point outside any finite
list — which is exactly "`ℝ` is infinite", and carries the ordered base.

## What the caller gets

`pnorm_eq_nil_of_evZero` is the step the differential route needs to turn "the eliminated
coefficient vanishes on a tail" into "the eliminated coefficient is the zero polynomial", which is
the hypothesis shape `cleared_relation_impossible` consumes. It is stated once, here, so that
everything downstream of it can be `PEq` reasoning and everything upstream can be `pev` reasoning.
-/

namespace MachLib

open Real

attribute [local instance] Classical.propDecidable

/-! ## Beyond any bound there is a point outside any finite list -/

theorem list_upper_bound : ∀ R : List Real, ∃ B : Real, ∀ y : Real, y ∈ R → y ≤ B := by
  intro R
  induction R with
  | nil => exact ⟨0, fun y hy => absurd hy (by simp)⟩
  | cons r rs ih =>
      obtain ⟨B, hB⟩ := ih
      rcases lt_total r B with h | h | h
      · refine ⟨B, fun y hy => ?_⟩
        rcases List.mem_cons.mp hy with he | hm
        · rw [he]; exact le_of_lt h
        · exact hB y hm
      · refine ⟨B, fun y hy => ?_⟩
        rcases List.mem_cons.mp hy with he | hm
        · rw [he, h]; exact le_refl B
        · exact hB y hm
      · refine ⟨r, fun y hy => ?_⟩
        rcases List.mem_cons.mp hy with he | hm
        · rw [he]; exact le_refl r
        · exact le_trans (hB y hm) (le_of_lt h)

theorem self_lt_succ (M : Real) : M < M + 1 := by
  have h := add_lt_add_left zero_lt_one_ax M
  rw [add_zero] at h
  exact h

/-- **`ℝ` is infinite**, in the form the bridge needs: beyond any bound there is a point avoiding
any finite list. This is the fact that is false over a finite field, and the reason this module
sits outside the algebra spine. -/
theorem exists_ge_notMem (R : List Real) (X : Real) : ∃ x : Real, X ≤ x ∧ x ∉ R := by
  obtain ⟨B, hB⟩ := list_upper_bound R
  rcases lt_total X B with h | h | h
  · refine ⟨B + 1, le_of_lt (lt_of_le_of_lt (le_of_lt h) (self_lt_succ B)), ?_⟩
    intro hx
    exact (ne_of_lt (lt_of_le_of_lt (hB (B + 1) hx) (self_lt_succ B))) rfl
  · refine ⟨B + 1, le_of_lt (lt_of_le_of_lt (le_of_eq h) (self_lt_succ B)), ?_⟩
    intro hx
    exact (ne_of_lt (lt_of_le_of_lt (hB (B + 1) hx) (self_lt_succ B))) rfl
  · refine ⟨X + 1, le_of_lt (self_lt_succ X), ?_⟩
    intro hx
    have hle : X + 1 ≤ B := hB (X + 1) hx
    have hlt : B < X + 1 := lt_of_le_of_lt (le_of_lt h) (self_lt_succ X)
    exact (ne_of_lt (lt_of_le_of_lt hle hlt)) rfl

/-! ## The bridge -/

/-- Identically zero as a function means the zero polynomial. Extracted as its own induction: the
hypothesis mentions the list being inducted on, so it has to be introduced after the split. -/
theorem pnorm_eq_nil_of_all_zero : ∀ L : List Real, (∀ x : Real, pev L x = 0) → pnorm L = [] := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons c cs ih =>
      intro hzero
      have hc : c = 0 := by
        have h0 := hzero 0
        show c = 0
        rw [show pev (c :: cs) 0 = c + 0 * pev cs 0 from rfl] at h0
        have e : c + 0 * pev cs 0 = c := by mach_ring
        rw [e] at h0
        exact h0
      have hcs : ∀ x : Real, pev cs x = 0 := by
        intro x
        rcases pev_zero_or_finite_roots cs with hz | ⟨R', hR'⟩
        · exact hz x
        · exfalso
          obtain ⟨y, hy1, hy2⟩ := exists_ge_notMem (0 :: R') 1
          have hyne : y ≠ 0 := by
            intro h; rw [h] at hy2; exact hy2 (by simp)
          have hz0 := hzero y
          rw [show pev (c :: cs) y = c + y * pev cs y from rfl, hc] at hz0
          have e : (0 : Real) + y * pev cs y = y * pev cs y := by mach_ring
          rw [e] at hz0
          have hcy : pev cs y = 0 := by
            rcases Classical.em (pev cs y = 0) with h | h
            · exact h
            · exact absurd hz0 (mul_ne_zero hyne h)
          exact hy2 (List.mem_cons_of_mem 0 (hR' y hcy))
      show pconsN c (pnorm cs) = []
      rw [ih hcs, hc]
      show (if (0 : Real) = 0 then [] else [(0 : Real)]) = []
      rw [if_pos rfl]

/-- **A coefficient list whose polynomial vanishes on a tail is the zero polynomial.** The step that
turns the differential route's "the eliminated coefficient vanishes eventually" into the `PEq`
hypothesis `cleared_relation_impossible` consumes. -/
theorem pnorm_eq_nil_of_evZero {L : List Real} (hL : EvZeroF (pev L)) : pnorm L = [] := by
  rcases pev_zero_or_finite_roots L with hzero | ⟨R, hR⟩
  · exact pnorm_eq_nil_of_all_zero L hzero
  · exfalso
    obtain ⟨X, hX, hz⟩ := hL
    obtain ⟨y, hy1, hy2⟩ := exists_ge_notMem R X
    exact hy2 (hR y (hz y hy1))

end MachLib
