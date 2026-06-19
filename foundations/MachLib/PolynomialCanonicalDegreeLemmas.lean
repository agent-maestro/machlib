import MachLib.PolynomialCanonical

/-!
# MachLib.PolynomialCanonicalDegreeLemmas — `polyTrueDegree[Strict]` combinators

Structural lemmas about `polyTrueDegree` and `polyTrueDegreeStrict`
under the basic coefficient-list operations.

Zero new axioms. Zero `sorry`.
-/

namespace MachLib
namespace PolynomialCanonical

open MachLib.Real

/-! ## `coeffAt` under list operations -/

theorem coeffAt_listAddR (L1 L2 : List Real) (k : Nat) :
    coeffAt (listAddR L1 L2) k = coeffAt L1 k + coeffAt L2 k := by
  induction L1 generalizing L2 k with
  | nil =>
    rw [listAddR_nil_left]
    show coeffAt L2 k = coeffAt [] k + coeffAt L2 k
    rw [coeffAt_nil, zero_add]
  | cons p ps' ih =>
    cases L2 with
    | nil =>
      rw [listAddR_nil_right]
      show coeffAt (p :: ps') k = coeffAt (p :: ps') k + coeffAt [] k
      rw [coeffAt_nil, add_zero]
    | cons q qs' =>
      rw [listAddR_cons_cons]
      cases k with
      | zero => simp only [coeffAt_cons_zero]
      | succ k' =>
        simp only [coeffAt_cons_succ]
        exact ih qs' k'

theorem coeffAt_listScaleR (c : Real) (L : List Real) (k : Nat) :
    coeffAt (listScaleR c L) k = c * coeffAt L k := by
  induction L generalizing k with
  | nil =>
    rw [listScaleR_nil]
    show coeffAt [] k = c * coeffAt [] k
    rw [coeffAt_nil, mul_zero]
  | cons q qs' ih =>
    rw [listScaleR_cons]
    cases k with
    | zero => simp only [coeffAt_cons_zero]
    | succ k' =>
      simp only [coeffAt_cons_succ]
      exact ih k'

/-! ## Helper: `CanonicallyZero` is preserved under operations -/

theorem canonicallyZero_listAddR_of_both
    (L1 L2 : List Real)
    (h1 : CanonicallyZero L1) (h2 : CanonicallyZero L2) :
    CanonicallyZero (listAddR L1 L2) := by
  rw [canonicallyZero_iff_all_coeffs_zero] at h1 h2 ⊢
  intro c hc
  induction L1 generalizing L2 with
  | nil =>
    rw [listAddR_nil_left] at hc
    exact h2 c hc
  | cons p ps' ih_p =>
    cases L2 with
    | nil =>
      rw [listAddR_nil_right] at hc
      exact h1 c hc
    | cons q qs' =>
      rw [listAddR_cons_cons] at hc
      rcases List.mem_cons.mp hc with h_head | h_tail
      · have hp_zero : p = 0 := h1 p (List.mem_cons_self _ _)
        have hq_zero : q = 0 := h2 q (List.mem_cons_self _ _)
        subst h_head
        rw [hp_zero, hq_zero, add_zero]
      · apply ih_p qs'
        · intro c' hc'; exact h1 c' (List.mem_cons_of_mem _ hc')
        · intro c' hc'; exact h2 c' (List.mem_cons_of_mem _ hc')
        · exact h_tail

theorem canonicallyZero_listScaleR_of_canonicallyZero
    (c : Real) (L : List Real)
    (h : CanonicallyZero L) :
    CanonicallyZero (listScaleR c L) := by
  rw [canonicallyZero_iff_all_coeffs_zero] at h ⊢
  intro c' hc'
  induction L with
  | nil => simp [listScaleR_nil] at hc'
  | cons q qs' ih =>
    rw [listScaleR_cons] at hc'
    rcases List.mem_cons.mp hc' with h_head | h_tail
    · subst h_head
      have hq_zero : q = 0 := h q (List.mem_cons_self _ _)
      rw [hq_zero, mul_zero]
    · apply ih
      · intro c'' hc''; exact h c'' (List.mem_cons_of_mem _ hc'')
      · exact h_tail

/-! ## `polyTrueDegree` under list operations -/

theorem polyDegreeBoundedBy_listAddR (L1 L2 : List Real) (n1 n2 : Nat)
    (h1 : polyDegreeBoundedBy L1 n1) (h2 : polyDegreeBoundedBy L2 n2) :
    polyDegreeBoundedBy (listAddR L1 L2) (max n1 n2) := by
  intro k hk
  rw [coeffAt_listAddR]
  have hk1 : k > n1 := Nat.lt_of_le_of_lt (Nat.le_max_left n1 n2) hk
  have hk2 : k > n2 := Nat.lt_of_le_of_lt (Nat.le_max_right n1 n2) hk
  rw [h1 k hk1, h2 k hk2, add_zero]

theorem polyTrueDegree_add_le (L1 L2 : List Real) :
    polyTrueDegree (listAddR L1 L2) ≤ max (polyTrueDegree L1) (polyTrueDegree L2) := by
  apply polyTrueDegree_le_of_bounded
  exact polyDegreeBoundedBy_listAddR L1 L2
    (polyTrueDegree L1) (polyTrueDegree L2)
    (polyTrueDegree_spec L1) (polyTrueDegree_spec L2)

theorem polyDegreeBoundedBy_listScaleR (c : Real) (L : List Real) (n : Nat)
    (h : polyDegreeBoundedBy L n) :
    polyDegreeBoundedBy (listScaleR c L) n := by
  intro k hk
  rw [coeffAt_listScaleR]
  rw [h k hk, mul_zero]

theorem polyTrueDegree_scale_le (c : Real) (L : List Real) :
    polyTrueDegree (listScaleR c L) ≤ polyTrueDegree L := by
  apply polyTrueDegree_le_of_bounded
  exact polyDegreeBoundedBy_listScaleR c L (polyTrueDegree L) (polyTrueDegree_spec L)

/-! ## Helper: `coeffAt` is zero on canonically-zero lists -/

private theorem coeffAt_of_canonicallyZero (L : List Real)
    (h : CanonicallyZero L) (k : Nat) :
    coeffAt L k = 0 := by
  rw [canonicallyZero_iff_all_coeffs_zero] at h
  by_cases hk_len : k < L.length
  · induction L generalizing k with
    | nil => simp at hk_len
    | cons c cs ih_cs =>
      cases k with
      | zero =>
        rw [coeffAt_cons_zero]
        exact h c (List.mem_cons_self _ _)
      | succ k' =>
        rw [coeffAt_cons_succ]
        apply ih_cs
        · intro c' hc'; exact h c' (List.mem_cons_of_mem _ hc')
        · simp at hk_len; omega
  · exact coeffAt_out_of_range _ k (Nat.not_lt.mp hk_len)

/-! ## `polyTrueDegreeStrict` versions -/

theorem polyTrueDegreeStrict_add_le (L1 L2 : List Real) :
    polyTrueDegreeStrict (listAddR L1 L2) ≤
      max (polyTrueDegreeStrict L1) (polyTrueDegreeStrict L2) := by
  by_cases h_zero : CanonicallyZero (listAddR L1 L2)
  · rw [polyTrueDegreeStrict_of_canonicallyZero _ h_zero]
    exact Nat.zero_le _
  · rw [polyTrueDegreeStrict_of_not_canonicallyZero _ h_zero]
    have h_sum_deg := polyTrueDegree_add_le L1 L2
    by_cases h_z1 : CanonicallyZero L1
    · by_cases h_z2 : CanonicallyZero L2
      · exfalso; exact h_zero (canonicallyZero_listAddR_of_both L1 L2 h_z1 h_z2)
      · rw [polyTrueDegreeStrict_of_canonicallyZero L1 h_z1]
        rw [polyTrueDegreeStrict_of_not_canonicallyZero L2 h_z2]
        rw [Nat.zero_max]
        have h_sum_le_L2 : polyTrueDegree (listAddR L1 L2) ≤ polyTrueDegree L2 := by
          apply polyTrueDegree_le_of_bounded
          intro k hk
          rw [coeffAt_listAddR]
          rw [coeffAt_of_canonicallyZero L1 h_z1 k]
          rw [polyTrueDegree_spec L2 k hk]
          rw [add_zero]
        omega
    · by_cases h_z2 : CanonicallyZero L2
      · rw [polyTrueDegreeStrict_of_not_canonicallyZero L1 h_z1]
        rw [polyTrueDegreeStrict_of_canonicallyZero L2 h_z2]
        rw [Nat.max_zero]
        have h_sum_le_L1 : polyTrueDegree (listAddR L1 L2) ≤ polyTrueDegree L1 := by
          apply polyTrueDegree_le_of_bounded
          intro k hk
          rw [coeffAt_listAddR]
          rw [polyTrueDegree_spec L1 k hk]
          rw [coeffAt_of_canonicallyZero L2 h_z2 k]
          rw [add_zero]
        omega
      · rw [polyTrueDegreeStrict_of_not_canonicallyZero L1 h_z1]
        rw [polyTrueDegreeStrict_of_not_canonicallyZero L2 h_z2]
        omega

theorem polyTrueDegreeStrict_scale_le (c : Real) (L : List Real) :
    polyTrueDegreeStrict (listScaleR c L) ≤ polyTrueDegreeStrict L := by
  by_cases h_zero : CanonicallyZero (listScaleR c L)
  · rw [polyTrueDegreeStrict_of_canonicallyZero _ h_zero]
    exact Nat.zero_le _
  · rw [polyTrueDegreeStrict_of_not_canonicallyZero _ h_zero]
    have h_L_nonzero : ¬ CanonicallyZero L := fun h =>
      h_zero (canonicallyZero_listScaleR_of_canonicallyZero c L h)
    rw [polyTrueDegreeStrict_of_not_canonicallyZero L h_L_nonzero]
    have h := polyTrueDegree_scale_le c L
    omega

end PolynomialCanonical
end MachLib
