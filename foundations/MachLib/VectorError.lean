import MachLib.OperatorBasisComplete
import MachLib.ErrorAlgebra

/-!
# The n-ary reduction operator — vectors, and an explicit per-operation constant

The scalar certifier (`OperatorBasisComplete.gexpr_sound`) folds a *fixed* expression tree.
The universal kernel shapes, though, are **n-ary reductions** over a vector: `Σ xᵢ`,
`Σ xᵢ·yᵢ` (dot product — the single most recurrent shape across the stdlib's domains),
`Σ xᵢ²` (squared norm). Their length `n` is a *variable*, so they are not one tree but a
*family* — a `List`-fold.

This file certifies that family. A `GRoundedSum` models the standard accumulator loop
`s := 0; for xᵢ: s := fl(s + xᵢ)` over a list of already-certified components, and
`aerr_sum` proves the running sum carries the `AErr` magnitude+error certificate — one
list induction reusing `aerr_add` at each step, no new axiom.

It also turns the **parametric** error *shape* into an **explicit constant**: `sum_const`
proves that for exact inputs the forward error of the n-fold sum is `≤ ((1+w)ⁿ − 1)·Σ|xᵢ|`
— the classic sequential-summation bound (`≈ n·u·Σ|xᵢ|`), now a closed-form constant in
`n` rather than a recursive accumulator. (`n`, not `n−1`: the `s := 0` start rounds on the
first add too — faithful to the loop as written.)

`sorryAx`-free; rests only on MachLib's existing base + `aerr_add`/`npow` (no new axioms).
-/

namespace MachLib.Real

/-- A certified vector component: `(M, E, v, ve)` standing for the fact `AErr M E v ve`
(magnitude bound `M`, error bound `E`, computed `v`, exact `ve`). -/
abbrev Comp := Real × Real × Real × Real

/-- One `List.foldr` carrying `(ΣM, error-bound, Σexact)`. `foldr` reduces definitionally,
so each projection's cons-step holds by `rfl`. The magnitude and exact components ignore
`w`; bundling them with the error bound keeps the recursion single + clean. -/
noncomputable def vecAcc (w : Real) (comps : List Comp) : Real × Real × Real :=
  comps.foldr
    (fun c a => (c.1 + a.1,
                 c.2.1 + a.2.1 + w * (c.1 + c.2.1 + a.1 + a.2.1),
                 c.2.2.2 + a.2.2))
    (0, 0, 0)

/-- Σ of the component magnitude bounds (value is `w`-independent). -/
noncomputable def sumM (w : Real) (comps : List Comp) : Real := (vecAcc w comps).1
/-- Accumulated forward-error bound of the sequentially-rounded sum. -/
noncomputable def sumEbound (w : Real) (comps : List Comp) : Real := (vecAcc w comps).2.1
/-- Σ of the exact component values — the reduction's exact result (`w`-independent). -/
noncomputable def sumExact (w : Real) (comps : List Comp) : Real := (vecAcc w comps).2.2

/-- Every component has a nonneg magnitude bound and is an *exact* input (`E = 0`). The
"fresh sum of exact data" regime where the only error is the summation's own rounding.
(`foldr` form, so the cons step reduces by `rfl`.) -/
def ExactComps (comps : List Comp) : Prop :=
  comps.foldr (fun c acc => 0 ≤ c.1 ∧ c.2.1 = 0 ∧ acc) True

/-- The accumulator loop `s := 0; for (M,E,v,ve) ∈ comps: s := fl(s + v)`. Each component
is certified (`AErr M E v ve`); the running sum is rounded at every `+`. -/
inductive GRoundedSum (w : Real) : List Comp → Real → Prop where
  | nil : GRoundedSum w [] 0
  | cons {M E v ve : Real} {r : List Comp} {s p : Real}
      (hc : AErr M E v ve) (hr : GRoundedSum w r s) (hp : RoundsW w p (v + s)) :
      GRoundedSum w ((M, E, v, ve) :: r) p

/-- **The n-ary reduction certificate.** Any sequentially-rounded sum of certified
components carries the magnitude+error certificate — one list induction folding `aerr_add`.
This is the vector analogue of `gexpr_sound`: a reduction over an arbitrary-length vector,
not a fixed tree. -/
theorem aerr_sum {w : Real} (hw0 : 0 ≤ w) {comps : List Comp} {p : Real}
    (h : GRoundedSum w comps p) :
    AErr (sumM w comps) (sumEbound w comps) p (sumExact w comps) := by
  induction h with
  | nil =>
      have h0 : AErr (0 : Real) 0 0 0 :=
        ⟨le_of_eq abs_zero,
         by rw [show (0 : Real) - 0 = 0 from by mach_ring]; exact le_of_eq abs_zero⟩
      exact h0
  | cons hc hr hp ih =>
      -- sumM/sumEbound/sumExact of `(M,E,v,ve)::r` reduce by `rfl` (foldr) to the
      -- aerr_add shape with the IH on the tail.
      exact aerr_add hw0 hc ih hp

/-- The forward-error corollary for the reduction: `|fl(Σvᵢ) − Σveᵢ| ≤ sumEbound`. -/
theorem aerr_sum_fwd {w : Real} (hw0 : 0 ≤ w) {comps : List Comp} {p : Real}
    (h : GRoundedSum w comps p) :
    abs (p - sumExact w comps) ≤ sumEbound w comps :=
  (aerr_sum hw0 h).err

/-! ## the explicit per-operation constant (for exact inputs) -/

theorem sumM_nonneg {w : Real} {comps : List Comp} (h : ExactComps comps) :
    0 ≤ sumM w comps := by
  induction comps with
  | nil => exact le_of_eq (show (0 : Real) = sumM w [] from rfl)
  | cons c r ih =>
      obtain ⟨hM, _, hr⟩ := h
      show 0 ≤ c.1 + sumM w r
      exact add_nonneg_ea hM (ih hr)

/-- `1 ≤ (1+w)ᵏ` for `0 ≤ w` (base `≥ 1`, any exponent). -/
theorem one_le_npow_one_add {w : Real} (hw0 : 0 ≤ w) (k : Nat) : 1 ≤ npow k (1 + w) := by
  have h1w : (1 : Real) ≤ 1 + w := le_add_of_nonneg_right hw0
  have hmono : npow 0 (1 + w) ≤ npow k (1 + w) := npow_mono_le h1w (Nat.zero_le k)
  rwa [show npow 0 (1 + w) = 1 from rfl] at hmono

/-! Fresh-var ring identities (mach_mpoly dislikes `npow`/recursive atoms, so the algebra
is factored out over plain variables). -/
theorem vs_lhs (s w M S : Real) :
    (0 : Real) + s + w * (M + 0 + S + s) = s * (1 + w) + w * (M + S) := by
  mach_mpoly [s, w, M, S]
theorem vs_mid (P S w M : Real) :
    ((P - 1) * S) * (1 + w) + w * (M + S) = ((1 + w) * P - 1) * S + w * M := by
  mach_mpoly [P, S, w, M]
theorem vs_gap (P w : Real) : (1 + w) * P - 1 - w = (1 + w) * (P - 1) := by
  mach_mpoly [P, w]
theorem vs_fold (Q S M : Real) : Q * S + Q * M = Q * (M + S) := by mach_mpoly [Q, S, M]

/-- **The explicit per-operation constant.** For a sequentially-rounded sum of `n` *exact*
inputs (magnitudes `≥ 0`), the forward error is bounded by `((1+w)ⁿ − 1)·Σ|xᵢ|` — the
classic summation bound `≈ n·u·Σ|xᵢ|`, as a closed-form constant in `n`, not a recursive
accumulator. (Replaces the parametric `sumEbound` *shape* with a numeric constant once `w`
and the input magnitudes are fixed.) -/
theorem sum_const {w : Real} (hw0 : 0 ≤ w) :
    ∀ {comps : List Comp}, ExactComps comps →
      sumEbound w comps ≤ (npow comps.length (1 + w) - 1) * sumM w comps := by
  have h1w : (0 : Real) ≤ 1 + w :=
    le_trans (le_of_lt zero_lt_one_ax) (le_add_of_nonneg_right hw0)
  intro comps
  induction comps with
  | nil =>
      intro _
      rw [show sumEbound w ([] : List Comp) = 0 from rfl,
          show sumM w ([] : List Comp) = 0 from rfl]
      exact le_of_eq (mul_zero _).symm
  | cons c r ih =>
      intro hex
      obtain ⟨hM, hE, hr⟩ := hex
      have hS : 0 ≤ sumM w r := sumM_nonneg hr
      have hP1 : 1 ≤ npow r.length (1 + w) := one_le_npow_one_add hw0 r.length
      have hIH : sumEbound w r ≤ (npow r.length (1 + w) - 1) * sumM w r := ih hr
      -- reshape both sides to their cons-unfolded (rfl) forms
      show c.2.1 + sumEbound w r + w * (c.1 + c.2.1 + sumM w r + sumEbound w r)
            ≤ (npow (r.length + 1) (1 + w) - 1) * (c.1 + sumM w r)
      rw [hE, npow_succ, vs_lhs (sumEbound w r) w c.1 (sumM w r)]
      have step1 : sumEbound w r * (1 + w)
            ≤ ((npow r.length (1 + w) - 1) * sumM w r) * (1 + w) :=
        mul_le_mul_of_nonneg_right hIH h1w
      have step2 := add_le_add_both step1 (le_refl (w * (c.1 + sumM w r)))
      rw [vs_mid (npow r.length (1 + w)) (sumM w r) w c.1] at step2
      have hwle : w ≤ (1 + w) * npow r.length (1 + w) - 1 := by
        apply le_of_sub_nonneg
        rw [vs_gap (npow r.length (1 + w)) w]
        exact mul_nonneg h1w (sub_nonneg_of_le hP1)
      have stepM : w * c.1 ≤ ((1 + w) * npow r.length (1 + w) - 1) * c.1 :=
        mul_le_mul_of_nonneg_right hwle hM
      have step3 := add_le_add_both
        (le_refl (((1 + w) * npow r.length (1 + w) - 1) * sumM w r)) stepM
      rw [vs_fold ((1 + w) * npow r.length (1 + w) - 1) (sumM w r) c.1] at step3
      exact le_trans step2 step3

/-! ## demos — the reduction on concrete vectors -/

/-- **A 3-element sum of exact inputs, with the explicit constant.** The accumulator
`q = fl(x₁ + fl(x₂ + fl(x₃ + 0)))` lands within `((1+w)³ − 1)·(|x₁|+|x₂|+|x₃|)` of the
exact sum — the textbook summation bound, here machine-checked end-to-end from the
operator rules (`aerr_leaf` per input, `aerr_sum` for the fold, `sum_const` for the
constant). -/
theorem sum3_const_certified {w x1 x2 x3 s3 s2 q : Real} (hw0 : 0 ≤ w)
    (hs3 : RoundsW w s3 (x3 + 0)) (hs2 : RoundsW w s2 (x2 + s3)) (hq : RoundsW w q (x1 + s2)) :
    abs (q - (x1 + (x2 + (x3 + 0))))
      ≤ (npow 3 (1 + w) - 1) * (abs x1 + (abs x2 + (abs x3 + 0))) := by
  have g : GRoundedSum w [(abs x1, 0, x1, x1), (abs x2, 0, x2, x2), (abs x3, 0, x3, x3)] q :=
    .cons (aerr_leaf x1) (.cons (aerr_leaf x2) (.cons (aerr_leaf x3) .nil hs3) hs2) hq
  have hex : ExactComps [(abs x1, 0, x1, x1), (abs x2, 0, x2, x2), (abs x3, 0, x3, x3)] :=
    ⟨abs_nonneg x1, rfl, abs_nonneg x2, rfl, abs_nonneg x3, rfl, trivial⟩
  exact le_trans (aerr_sum_fwd hw0 g) (sum_const hw0 hex)

/-- **A 2-element dot product** `x·y = fl(p₁ + fl(p₂ + 0))`, `pᵢ = fl(xᵢ·yᵢ)` — the
universal stdlib shape, certified as `aerr_sum` over the per-component `aerr_mul`
products. The bound is the reduction's `sumEbound` (the products carry the multiply's
rounding, so this is the general `aerr_sum`, not the exact-input `sum_const`). -/
theorem dot2_certified {w x1 y1 x2 y2 p1 p2 s2 q : Real} (hw0 : 0 ≤ w)
    (h1 : RoundsW w p1 (x1 * y1)) (h2 : RoundsW w p2 (x2 * y2))
    (hs2 : RoundsW w s2 (p2 + 0)) (hq : RoundsW w q (p1 + s2)) :
    abs (q - (x1 * y1 + (x2 * y2 + 0)))
      ≤ sumEbound w
          [(abs x1 * abs y1,
            (abs x1 + 0) * 0 + abs y1 * 0 + w * ((abs x1 + 0) * (abs y1 + 0)), p1, x1 * y1),
           (abs x2 * abs y2,
            (abs x2 + 0) * 0 + abs y2 * 0 + w * ((abs x2 + 0) * (abs y2 + 0)), p2, x2 * y2)] :=
  aerr_sum_fwd hw0
    (.cons (aerr_mul hw0 (aerr_leaf x1) (aerr_leaf y1) h1)
      (.cons (aerr_mul hw0 (aerr_leaf x2) (aerr_leaf y2) h2) .nil hs2) hq)

end MachLib.Real
