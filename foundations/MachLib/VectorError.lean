import MachLib.OperatorBasisComplete
import MachLib.ErrorAlgebra
import MachLib.ConditionNumber   -- sumList (List Real → Real), for the ∀N certificate
import MachLib.Trig              -- sin/cos + sin_sq_add_cos_sq, for rotation norm-preservation

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

/-! ### Unit-norm certificate — `|normalize v| = 1`

The first WHOLE-vector predicate (`v·v = 1` about the entire result), as opposed
to the per-component `∀ i` bounds above. This is what a `normalize` kernel's
`@verify(lean)` reduces to: divide each component by `‖v‖ = √(v·v)` and the
squared-norm of the result is exactly `1`. No Mathlib — the whole thing is
`div_def` + `mul_inv` (`a·(1/a)=1`) + `mach_mpoly` ring-normalisation. -/

/-- **The div core.** For ANY `s` with `s² = v·v` and `s ≠ 0`, the 3-vector
`(v₀/s, v₁/s, v₂/s)` has squared-norm `1`. (`s = √(v·v)` is one such witness;
kept general so the caller supplies the sqrt facts.) -/
theorem norm3_of_s (v0 v1 v2 s : Real)
    (hs : s * s = v0 * v0 + v1 * v1 + v2 * v2) (hsne : s ≠ 0) :
    (v0 / s) * (v0 / s) + (v1 / s) * (v1 / s) + (v2 / s) * (v2 / s) = 1 := by
  rw [div_def v0 s hsne, div_def v1 s hsne, div_def v2 s hsne]
  have hinv : s * (1 / s) = 1 := mul_inv s hsne
  calc (v0 * (1/s)) * (v0 * (1/s)) + (v1 * (1/s)) * (v1 * (1/s))
          + (v2 * (1/s)) * (v2 * (1/s))
      = (v0*v0 + v1*v1 + v2*v2) * ((1/s) * (1/s)) := by mach_mpoly [v0, v1, v2, 1/s]
    _ = (s * s) * ((1/s) * (1/s)) := by rw [hs]
    _ = (s * (1/s)) * (s * (1/s)) := by mach_mpoly [s, 1/s]
    _ = 1 * 1 := by rw [hinv]
    _ = 1 := mul_one_ax 1

/-- **`|normalize v|² = 1`** for a nonzero 3-vector, fully self-contained:
dividing each component by `√(v·v)` yields a unit vector. The sqrt facts
(`√(v·v)² = v·v` from `sqrt_sq_nonneg`, `√(v·v) ≠ 0` from `sqrt_pos`) discharge
`norm3_of_s`'s hypotheses. This is the theorem a `normalize`
`@verify(lean, ensures (dot(result,result) == 1.0))` kernel maps onto. -/
theorem norm3_unit (v0 v1 v2 : Real) (hpos : 0 < v0 * v0 + v1 * v1 + v2 * v2) :
    (v0 / sqrt (v0*v0+v1*v1+v2*v2)) * (v0 / sqrt (v0*v0+v1*v1+v2*v2))
  + (v1 / sqrt (v0*v0+v1*v1+v2*v2)) * (v1 / sqrt (v0*v0+v1*v1+v2*v2))
  + (v2 / sqrt (v0*v0+v1*v1+v2*v2)) * (v2 / sqrt (v0*v0+v1*v1+v2*v2)) = 1 :=
  norm3_of_s v0 v1 v2 (sqrt (v0*v0+v1*v1+v2*v2))
    (sqrt_sq_nonneg _ (le_of_lt hpos)) (ne_of_gt (sqrt_pos hpos))

/-! #### The ∀N unit-norm certificate (arbitrary dimension)

`norm3_of_s` is the fixed-arity (3) core; `normList_unit` is the SAME
result for a vector of ANY length, stated over `sumList` (the right-fold
sum, `MachLib.Real.sumList : List Real → Real`). Forge's emitter does NOT
need this — at a concrete N it inlines the norm3_of_s argument and lets
`mach_mpoly` absorb the arity (the unrolled `Σ` is one big polynomial).
The single-theorem ∀N form, by contrast, DOES need induction on the list:
that is the honest boundary — arity-generic *ring algebra* is free, but a
statement quantified over the *length* is not. -/

private theorem sumList_nil : sumList ([] : List Real) = 0 := rfl
private theorem sumList_cons (a : Real) (m : List Real) :
    sumList (a :: m) = a + sumList m := rfl

/-- The cons step, as its own lemma so `mach_mpoly` reifies its atoms in a
plain-hypothesis context (it does not see `induction`-introduced binders). -/
private theorem sumList_div_sq_step (s t : Real) (ts : List Real) (hsne : s ≠ 0)
    (ih : sumList (ts.map (fun x => (x / s) * (x / s)))
        = (sumList (ts.map (fun x => x * x))) * ((1 / s) * (1 / s))) :
    sumList ((t :: ts).map (fun x => (x / s) * (x / s)))
      = (sumList ((t :: ts).map (fun x => x * x))) * ((1 / s) * (1 / s)) := by
  simp only [List.map_cons, sumList_cons]
  rw [ih, div_def t s hsne]
  mach_mpoly [t, sumList (List.map (fun x => x * x) ts), 1 / s]

/-- **A scalar factors out of a sum of scaled squares**, at any length:
`Σ (xᵢ/s)² = (Σ xᵢ²) · (1/s)²`. Induction on the list. -/
theorem sumList_div_sq (s : Real) (hsne : s ≠ 0) (l : List Real) :
    sumList (l.map (fun x => (x / s) * (x / s)))
      = (sumList (l.map (fun x => x * x))) * ((1 / s) * (1 / s)) := by
  induction l with
  | nil => simp only [List.map_nil, sumList_nil, zero_mul]
  | cons t ts ih => exact sumList_div_sq_step s t ts hsne ih

/-- **`|normalize v|² = 1` for a vector of ANY dimension.** For any list
`l` and any `s ≠ 0` with `s² = Σ xᵢ²` (e.g. `s = ‖v‖`), the normalised
vector has unit squared-norm: `Σ (xᵢ/s)² = 1`. The arbitrary-N companion
to `norm3_unit`. -/
theorem normList_unit (s : Real) (hsne : s ≠ 0) (l : List Real)
    (hs : s * s = sumList (l.map (fun x => x * x))) :
    sumList (l.map (fun x => (x / s) * (x / s))) = 1 := by
  rw [sumList_div_sq s hsne l, ← hs]
  have hinv : s * (1 / s) = 1 := mul_inv s hsne
  calc (s * s) * ((1 / s) * (1 / s))
      = (s * (1 / s)) * (s * (1 / s)) := by mach_mpoly [s, 1 / s]
    _ = 1 * 1 := by rw [hinv]
    _ = 1 := mul_one_ax 1

/-! #### Rotation preserves length — `|R(θ)·v|² = |v|²`

The classic verified-geometry theorem: a 2-D rotation
`R(θ)·v = (cos θ·v₀ − sin θ·v₁, sin θ·v₀ + cos θ·v₁)` preserves the
squared norm. The cross-terms `±2·cos·sin·v₀·v₁` cancel and the diagonal
collapses via `sin²θ + cos²θ = 1` (`sin_sq_add_cos_sq`). Covers ANY
rotation angle and vector — the certificate for a `rotate` kernel's
`ensures (dot(result, result) == dot(v, v))`. -/
theorem rotate_preserves_norm (theta v0 v1 : Real) :
    ((cos theta)*v0 - (sin theta)*v1) * ((cos theta)*v0 - (sin theta)*v1)
  + ((sin theta)*v0 + (cos theta)*v1) * ((sin theta)*v0 + (cos theta)*v1)
  = v0*v0 + v1*v1 := by
  have h : sin theta * sin theta + cos theta * cos theta = 1 :=
    sin_sq_add_cos_sq theta
  calc ((cos theta)*v0 - (sin theta)*v1) * ((cos theta)*v0 - (sin theta)*v1)
        + ((sin theta)*v0 + (cos theta)*v1) * ((sin theta)*v0 + (cos theta)*v1)
      = (sin theta * sin theta + cos theta * cos theta) * (v0*v0)
        + (sin theta * sin theta + cos theta * cos theta) * (v1*v1) := by
          mach_mpoly [cos theta, sin theta, v0, v1]
    _ = 1*(v0*v0) + 1*(v1*v1) := by rw [h]
    _ = v0*v0 + v1*v1 := by mach_mpoly [v0, v1]

end MachLib.Real
