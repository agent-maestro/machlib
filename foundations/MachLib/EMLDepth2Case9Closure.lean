import MachLib.EMLDepth2Case9RowU3

/-!
# `u1 × w3`-small — closed by ONE parameter-dependent point

`RESULT_FOUR_POINTS.md` concluded that the next step had to be *"an argument that does not go through
finitely many samples at all."* **This is one.**

`u1`'s master is `x · log (W x) = x · E − K` with `E := exp α > 0`. The right side is **affine in
`x`**; the left grows like **`x²`**, because `log (exp x − L′)` grows like `x`. **So a single
sufficiently large `x` breaks it — and "sufficiently large" is computable from `E` and `K`:**

```
X  :=  E + exp (−K) + 1 + 1
```

> ### `exp (−K) > −K` for every real `K`, so `exp (−K)` is a canonical upper bound for an arbitrary real. **No `abs`, no sign case-split** — which matters in a corpus that has neither to hand.

**No sampling, no second difference.** This module sits at the end of the import chain because it
uses order helpers introduced across several of the row files.
-/

namespace MachLib
namespace Real

open EMLTree

/-! ## `w3`-small by ONE parameter-dependent point — no sampling

The right-hand side of `u1`'s master is **affine in `x`**; the left grows like `x²`, because
`log (exp x − L′)` grows like `x`. **So a single sufficiently large `x` breaks it — and
"sufficiently large" is computable from the parameters.**

> ### `exp (−K) > −K` for every real `K`, so `exp (−K)` is a canonical upper bound for an arbitrary real. **No `abs`, no sign case-split.** -/

/-- `exp X − L′ > exp (X − 1)` for `X ≥ 2` and `L′ ≤ exp 1`.

`exp X − exp (X−1) = exp (X−1)·(exp 1 − 1) ≥ exp 1·(exp 1 − 1) > exp 1 ≥ L′`. -/
theorem child_gt_exp_pred {L X : Real} (hL : L ≤ exp 1) (hX : (1 : Real) + 1 ≤ X) :
    exp (X - 1) < exp X - L := by
  apply lt_of_sub_pos
  have esplit : (exp X - L) - exp (X - 1) = (exp X - exp (X - 1)) - L := by
    mach_mpoly [exp X, exp (X - 1), L]
  rw [esplit]
  apply sub_pos_of_lt
  -- L ≤ exp 1 < exp X − exp (X−1)
  have hfac : exp X - exp (X - 1) = exp (X - 1) * (exp 1 - 1) := by
    have e : exp X = exp (X - 1) * exp 1 := by
      rw [← exp_add]
      have ee : (X - 1) + 1 = X := by mach_ring
      rw [ee]
    rw [e]; mach_mpoly [exp (X - 1), exp 1]
  rw [hfac]
  have hpred : exp 1 ≤ exp (X - 1) := by
    rcases (le_iff_lt_or_eq ((1 : Real) + 1) X).mp hX with h | h
    · exact le_of_lt (exp_lt (by
        apply lt_of_sub_pos
        have e : (X - 1) - 1 = X - (1 + 1) := by mach_ring
        rw [e]; exact sub_pos_of_lt h))
    · rw [← h]
      have e : ((1 : Real) + 1) - 1 = 1 := by mach_ring
      rw [e]; exact le_refl _
  have hgap : (1 : Real) < exp 1 - 1 := by
    apply lt_of_sub_pos
    have e : exp 1 - 1 - 1 = exp 1 - (1 + 1) := by mach_ring
    rw [e]; exact sub_pos_of_lt two_lt_exp_one
  have step1 : exp 1 * 1 < exp 1 * (exp 1 - 1) := mul_lt_mul_pos_left hgap (exp_pos 1)
  have step2 : exp 1 * (exp 1 - 1) ≤ exp (X - 1) * (exp 1 - 1) := by
    rcases (le_iff_lt_or_eq (exp 1) (exp (X - 1))).mp hpred with h | h
    · exact le_of_lt (mul_lt_mul_of_pos_right h (lt_trans_ax zero_lt_one_ax hgap))
    · rw [h]; exact le_refl _
  have e1 : exp 1 * 1 = exp 1 := by mach_ring
  rw [e1] at step1
  exact lt_of_lt_of_le (lt_of_le_of_lt hL step1) step2

/-- **`u1` over `w3` is impossible on the small branch too** (`log c′ ≤ exp 1`) — **from a SINGLE
point**, chosen as a function of the parameters.

`X := E + exp (−K) + 1 + 1` where `E := exp (u.eval ·)`. Then `log (W X) > X − 1`, so
`X·log (W X) > X·(X−1)`, and `X·(X−1) > X·E − K` because `X·(X − 1 − E) = X·(exp(−K) + 1) >
exp(−K) > −K`.

**No sampling, no second difference, no `abs`.** -/
theorem u1_w3_small_absurd {c₁ c₂ c' K : Real} (hc : log c' ≤ exp 1)
    (e : (exp (exp c₁ - log c₂) + exp (-K) + 1 + 1)
          * (EMLTree.eml (EMLTree.eml (EMLTree.const c₁) (EMLTree.const c₂))
              (EMLTree.eml EMLTree.var (EMLTree.const c'))).eval
            (exp (exp c₁ - log c₂) + exp (-K) + 1 + 1) = K) :
    False := by
  have hE : (0 : Real) < exp (exp c₁ - log c₂) := exp_pos _
  have hR : (0 : Real) < exp (-K) := exp_pos _
  have hX2 : (1 : Real) + 1 ≤ exp (exp c₁ - log c₂) + exp (-K) + 1 + 1 := by
    apply le_of_lt
    apply lt_of_sub_pos
    have ee : (exp (exp c₁ - log c₂) + exp (-K) + 1 + 1) - (1 + 1)
        = exp (exp c₁ - log c₂) + exp (-K) := by
      mach_mpoly [exp (exp c₁ - log c₂), exp (-K)]
    rw [ee]
    exact add_pos_real hE hR
  have hX1 : (0 : Real) < exp (exp c₁ - log c₂) + exp (-K) + 1 + 1 :=
    lt_of_lt_of_le one_add_one_pos hX2
  -- master equation at X
  have m := u1_master (α := exp c₁ - log c₂) rfl e
  have wv : (EMLTree.eml EMLTree.var (EMLTree.const c')).eval
      (exp (exp c₁ - log c₂) + exp (-K) + 1 + 1)
      = exp (exp (exp c₁ - log c₂) + exp (-K) + 1 + 1) - log c' := rfl
  rw [wv] at m
  -- log (W X) > X − 1
  have hchild := child_gt_exp_pred hc hX2
  have hlog : (exp (exp c₁ - log c₂) + exp (-K) + 1 + 1) - 1
      < log (exp (exp (exp c₁ - log c₂) + exp (-K) + 1 + 1) - log c') := by
    have h := log_lt_log (exp_pos _) hchild
    rw [log_exp] at h
    exact h
  -- X·log(W X) > X·(X−1)
  have hmul := mul_lt_mul_pos_left hlog hX1
  -- X·(X−1) > X·E − K
  have hbig : (exp (exp c₁ - log c₂) + exp (-K) + 1 + 1)
      * ((exp (exp c₁ - log c₂) + exp (-K) + 1 + 1) - 1)
      > (exp (exp c₁ - log c₂) + exp (-K) + 1 + 1) * exp (exp c₁ - log c₂) - K := by
    apply lt_of_sub_pos
    have esplit : (exp (exp c₁ - log c₂) + exp (-K) + 1 + 1)
        * ((exp (exp c₁ - log c₂) + exp (-K) + 1 + 1) - 1)
        - ((exp (exp c₁ - log c₂) + exp (-K) + 1 + 1) * exp (exp c₁ - log c₂) - K)
        = (exp (exp c₁ - log c₂) + exp (-K) + 1 + 1) * (exp (-K) + 1) + K := by
      mach_mpoly [exp (exp c₁ - log c₂), exp (-K), K]
    rw [esplit]
    -- X·(exp(−K)+1) > exp(−K) > −K
    have h1 : exp (-K) < (exp (exp c₁ - log c₂) + exp (-K) + 1 + 1) * (exp (-K) + 1) := by
      have hone : (1 : Real) * (exp (-K) + 1) ≤
          (exp (exp c₁ - log c₂) + exp (-K) + 1 + 1) * (exp (-K) + 1) := by
        rcases (le_iff_lt_or_eq 1 (exp (exp c₁ - log c₂) + exp (-K) + 1 + 1)).mp
          (le_of_lt (lt_of_lt_of_le one_lt_one_plus_one hX2)) with h | h
        · exact le_of_lt (mul_lt_mul_of_pos_right h (add_pos_real hR zero_lt_one_ax))
        · rw [← h]; exact le_refl _
      have htriv : exp (-K) < (1 : Real) * (exp (-K) + 1) := by
        have e1 : (1 : Real) * (exp (-K) + 1) = exp (-K) + 1 := by mach_ring
        rw [e1]
        exact lt_add_of_pos_right zero_lt_one_ax
      exact lt_of_lt_of_le htriv hone
    have h2 : -K < exp (-K) := exp_grows_strictly_thm (-K)
    apply lt_of_sub_pos
    have e2 : ((exp (exp c₁ - log c₂) + exp (-K) + 1 + 1) * (exp (-K) + 1) + K) - 0
        = ((exp (exp c₁ - log c₂) + exp (-K) + 1 + 1) * (exp (-K) + 1) - exp (-K))
          + (exp (-K) - (-K)) := by
      mach_mpoly [exp (exp c₁ - log c₂), exp (-K), K]
    rw [e2]
    exact add_pos_real (sub_pos_of_lt h1) (sub_pos_of_lt h2)
  -- contradiction
  rw [m] at hmul
  exact lt_irrefl_ax _ (lt_trans_ax hbig hmul)

end Real
end MachLib
