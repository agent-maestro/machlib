import MachLib.ChainExp2ExplicitTrim
import MachLib.IterExpDepthNCanonDegree

/-!
# `canonLcYAt` degree bounds (step-3 support for the chain-N explicit bound's `EIrank`)

The `EIrank` recursion (`chainNMeasureEI` linearized by `rankNested`) descends into
`dropLastY (canonLcYAt ⟨top⟩ q)` at each level, so bounding `EIrank` by a global `B` needs the inner
poly's degrees bounded — i.e. `canonLcYAt` must not raise `degreeX` or any `degreeY`. `canonLcYAt i q` is
`const 0` or one of `q`'s `y_i`-coefficients, so its degrees are bounded by `q`'s. `degreeX` reuses the
existing `yCoeffsAt_entries_degreeX_le`; `degreeY` (cross-index) needs the same tower for `degreeY jt`,
built here as a verbatim mirror (the `add→max`, `sub→max`, `mul→sum`, `const→0` structure is identical).

  * `listAddN/SubN/ScaleN/MulN_entries_degreeY_le` + `yCoeffsAt_entries_degreeY_le` — the cross-index tower.
  * `canonLcYAt_mem_or_zero` — `canonLcYAt i q = const 0 ∨ ∈ yCoeffsAt i q`.
  * `degreeX_canonLcYAt_le`, `degreeY_canonLcYAt_le` — the two non-raising bounds.
-/

namespace MachLib.IterExpDepthN

open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.MultiPolyReconstruct
open MachLib.ChainExp2Explicit

/-! ### Cross-index `degreeY jt`-non-raising tower over the `yCoeffsAt` list operations -/

theorem listAddN_entries_degreeY_le {n : Nat} (jt : Fin n) (l1 l2 : List (MultiPoly n)) (D : Nat)
    (h1 : ∀ c ∈ l1, degreeY jt c ≤ D) (h2 : ∀ c ∈ l2, degreeY jt c ≤ D) :
    ∀ c ∈ listAddN l1 l2, degreeY jt c ≤ D := by
  induction l1 generalizing l2 with
  | nil => intro c hc; rw [listAddN_nil_left] at hc; exact h2 c hc
  | cons p ps ih =>
    cases l2 with
    | nil => intro c hc; rw [listAddN_cons_nil] at hc; exact h1 c hc
    | cons q qs =>
      intro c hc; rw [listAddN_cons_cons] at hc
      cases hc with
      | head => exact Nat.max_le.mpr ⟨h1 p (List.mem_cons_self _ _), h2 q (List.mem_cons_self _ _)⟩
      | tail _ hc' =>
        exact ih qs (fun c hc => h1 c (List.mem_cons_of_mem _ hc))
                 (fun c hc => h2 c (List.mem_cons_of_mem _ hc)) c hc'

theorem listSubN_entries_degreeY_le {n : Nat} (jt : Fin n) (l1 l2 : List (MultiPoly n)) (D : Nat)
    (h1 : ∀ c ∈ l1, degreeY jt c ≤ D) (h2 : ∀ c ∈ l2, degreeY jt c ≤ D) :
    ∀ c ∈ listSubN l1 l2, degreeY jt c ≤ D := by
  induction l1 generalizing l2 with
  | nil =>
    induction l2 with
    | nil => intro c hc; exact absurd hc (List.not_mem_nil _)
    | cons q qs ihq =>
      intro c hc
      change c ∈ (sub (const 0) q :: listSubN [] qs) at hc
      cases hc with
      | head => exact Nat.max_le.mpr ⟨Nat.zero_le _, h2 q (List.mem_cons_self _ _)⟩
      | tail _ hc' => exact ihq (fun c hc => h2 c (List.mem_cons_of_mem _ hc)) c hc'
  | cons p ps ih =>
    cases l2 with
    | nil => intro c hc; change c ∈ (p :: ps) at hc; exact h1 c hc
    | cons q qs =>
      intro c hc; change c ∈ (sub p q :: listSubN ps qs) at hc
      cases hc with
      | head => exact Nat.max_le.mpr ⟨h1 p (List.mem_cons_self _ _), h2 q (List.mem_cons_self _ _)⟩
      | tail _ hc' =>
        exact ih qs (fun c hc => h1 c (List.mem_cons_of_mem _ hc))
                 (fun c hc => h2 c (List.mem_cons_of_mem _ hc)) c hc'

theorem listScaleN_entries_degreeY_le {n : Nat} (jt : Fin n) (p : MultiPoly n) (Dp : Nat)
    (hp : degreeY jt p ≤ Dp) (l : List (MultiPoly n)) (D : Nat) (hl : ∀ c ∈ l, degreeY jt c ≤ D) :
    ∀ c ∈ listScaleN p l, degreeY jt c ≤ Dp + D := by
  induction l with
  | nil => intro c hc; rw [listScaleN_nil] at hc; exact absurd hc (List.not_mem_nil _)
  | cons q qs ih =>
    intro c hc; rw [listScaleN_cons] at hc
    cases hc with
    | head =>
      show degreeY jt p + degreeY jt q ≤ Dp + D
      exact Nat.add_le_add hp (hl q (List.mem_cons_self _ _))
    | tail _ hc' => exact ih (fun c hc => hl c (List.mem_cons_of_mem _ hc)) c hc'

theorem listMulN_entries_degreeY_le {n : Nat} (jt : Fin n) (l1 l2 : List (MultiPoly n)) (D1 D2 : Nat)
    (h1 : ∀ c ∈ l1, degreeY jt c ≤ D1) (h2 : ∀ c ∈ l2, degreeY jt c ≤ D2) :
    ∀ c ∈ listMulN l1 l2, degreeY jt c ≤ D1 + D2 := by
  induction l1 with
  | nil => intro c hc; rw [listMulN_nil] at hc; exact absurd hc (List.not_mem_nil _)
  | cons p ps ih =>
    intro c hc; rw [listMulN_cons] at hc
    refine listAddN_entries_degreeY_le jt (listScaleN p l2) (const 0 :: listMulN ps l2) (D1 + D2)
      ?_ ?_ c hc
    · exact listScaleN_entries_degreeY_le jt p D1 (h1 p (List.mem_cons_self _ _)) l2 D2 h2
    · intro c' hc'
      cases hc' with
      | head => exact Nat.zero_le _
      | tail _ hc'' => exact ih (fun c hc => h1 c (List.mem_cons_of_mem _ hc)) c' hc''

/-- **Every `yCoeffsAt i p` entry has `degreeY jt ≤ degreeY jt p`** (cross-index). Structural mirror of
`yCoeffsAt_entries_degreeX_le`. -/
theorem yCoeffsAt_entries_degreeY_le {n : Nat} (jt i : Fin n) (p : MultiPoly n) :
    ∀ c ∈ yCoeffsAt i p, degreeY jt c ≤ degreeY jt p := by
  induction p with
  | const a =>
    intro c hc; change c ∈ [const a] at hc
    rw [List.mem_singleton] at hc; subst hc; exact Nat.le_refl _
  | varX =>
    intro c hc; change c ∈ [varX] at hc
    rw [List.mem_singleton] at hc; subst hc; exact Nat.le_refl _
  | varY j =>
    intro c hc
    by_cases hji : j = i
    · have he : yCoeffsAt i (varY j) = [const 0, const 1] := by
        show (if j = i then _ else _) = _; rw [if_pos hji]
      rw [he] at hc
      rcases List.mem_cons.mp hc with rfl | hc2
      · exact Nat.zero_le _
      · rw [List.mem_singleton] at hc2; subst hc2; exact Nat.zero_le _
    · have he : yCoeffsAt i (varY j) = [varY j] := by
        show (if j = i then _ else _) = _; rw [if_neg hji]
      rw [he, List.mem_singleton] at hc; subst hc; exact Nat.le_refl _
  | add p q ihp ihq =>
    intro c hc
    exact listAddN_entries_degreeY_le jt (yCoeffsAt i p) (yCoeffsAt i q)
      (Nat.max (degreeY jt p) (degreeY jt q))
      (fun c hc => Nat.le_trans (ihp c hc) (Nat.le_max_left _ _))
      (fun c hc => Nat.le_trans (ihq c hc) (Nat.le_max_right _ _)) c hc
  | sub p q ihp ihq =>
    intro c hc
    exact listSubN_entries_degreeY_le jt (yCoeffsAt i p) (yCoeffsAt i q)
      (Nat.max (degreeY jt p) (degreeY jt q))
      (fun c hc => Nat.le_trans (ihp c hc) (Nat.le_max_left _ _))
      (fun c hc => Nat.le_trans (ihq c hc) (Nat.le_max_right _ _)) c hc
  | mul p q ihp ihq =>
    intro c hc
    exact listMulN_entries_degreeY_le jt (yCoeffsAt i p) (yCoeffsAt i q)
      (degreeY jt p) (degreeY jt q) ihp ihq c hc

/-! ### `canonLcYAt` is one of the coefficients (or `const 0`), hence degree-non-raising -/

private theorem mem_of_mem_dropWhile {α : Type} (pr : α → Bool) :
    ∀ (l : List α) (a : α), a ∈ l.dropWhile pr → a ∈ l
  | [], _, h => h
  | b :: bs, a, h => by
      rw [List.dropWhile_cons] at h
      by_cases hpb : pr b = true
      · rw [if_pos hpb] at h
        exact List.mem_cons_of_mem _ (mem_of_mem_dropWhile pr bs a h)
      · rw [if_neg hpb] at h; exact h

/-- `canonLcYAt i q` is either `const 0` (all coefficients canon-zero) or one of the `y_i`-coefficients. -/
theorem canonLcYAt_mem_or_zero {n : Nat} (i : Fin n) (q : MultiPoly n) :
    canonLcYAt i q = MultiPoly.const 0 ∨ canonLcYAt i q ∈ yCoeffsAt i q := by
  unfold canonLcYAt
  cases h : (yCoeffsAt i q).reverse.dropWhile canonZeroB with
  | nil => left; rfl
  | cons a t =>
      right
      have ha_dw : a ∈ (yCoeffsAt i q).reverse.dropWhile canonZeroB := by
        rw [h]; exact List.mem_cons_self a t
      have ha_rev : a ∈ (yCoeffsAt i q).reverse := mem_of_mem_dropWhile canonZeroB _ a ha_dw
      exact List.mem_reverse.mp ha_rev

/-- `canonLcYAt` does not raise `degreeX`. -/
theorem degreeX_canonLcYAt_le {n : Nat} (i : Fin n) (q : MultiPoly n) :
    MultiPoly.degreeX (canonLcYAt i q) ≤ MultiPoly.degreeX q := by
  rcases canonLcYAt_mem_or_zero i q with h | h
  · rw [h]; exact Nat.zero_le _
  · exact yCoeffsAt_entries_degreeX_le i q _ h

/-- `canonLcYAt` does not raise any `degreeY` (cross-index). -/
theorem degreeY_canonLcYAt_le {n : Nat} (i jt : Fin n) (q : MultiPoly n) :
    MultiPoly.degreeY jt (canonLcYAt i q) ≤ MultiPoly.degreeY jt q := by
  rcases canonLcYAt_mem_or_zero i q with h | h
  · rw [h]; exact Nat.zero_le _
  · exact yCoeffsAt_entries_degreeY_le jt i q _ h

end MachLib.IterExpDepthN
