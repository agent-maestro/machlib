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

/-! ## `u3 × w4` — the doubly-exponential cell, also by ONE point

`u3`'s master carries `x · exp (exp x − L)`. For `w4` the child `exp x − log x` has **no parameter**,
so the point is chosen from `L` and `K` alone.

> ### The point is a `def`, not an inlined expression. Written out, it made `mach_mpoly` time out at 200 k heartbeats; as an opaque atom the same goals close instantly — the `sq_mul` lesson again. -/

/-- The point: `4 + exp L + exp K`. **A `def` so the normaliser sees one atom.** -/
noncomputable def u3Point (L K : Real) : Real := (1 + 1) + ((1 + 1) + exp L + exp K)

/-- `2·exp t > t` for every real `t`. Sign cases on `t` alone; **no `abs`**. -/
theorem two_exp_gt_self (t : Real) : t < exp t + exp t := by
  rcases lt_total t 0 with h | h | h
  · exact lt_trans_ax h (add_pos_real (exp_pos t) (exp_pos t))
  · rw [h]; exact add_pos_real (exp_pos 0) (exp_pos 0)
  · exact lt_trans_ax (exp_grows_strictly_thm t) (lt_add_of_pos_right (exp_pos t))

theorem two_lt_u3Point (L K : Real) : (1 : Real) + 1 < u3Point L K := by
  show (1 : Real) + 1 < (1 + 1) + ((1 + 1) + exp L + exp K)
  exact lt_add_of_pos_right (add_pos_real (add_pos_real one_add_one_pos (exp_pos L)) (exp_pos K))

theorem u3Point_pos (L K : Real) : 0 < u3Point L K :=
  lt_trans_ax one_add_one_pos (two_lt_u3Point L K)

theorem one_lt_u3Point (L K : Real) : (1 : Real) < u3Point L K :=
  lt_trans_ax one_lt_one_plus_one (two_lt_u3Point L K)

/-- **`X + X + L < exp X` at the point.** `exp X = exp(1+1)·exp b > 4·b`, and `4b ≥ 4 + 2b + L`
reduces to `2·exp L + 2·exp K ≥ L`, which `two_exp_gt_self` supplies. -/
theorem u3Point_dominates (L K : Real) :
    u3Point L K + u3Point L K + L < exp (u3Point L K) := by
  have hb : (0 : Real) < (1 + 1) + exp L + exp K :=
    add_pos_real (add_pos_real one_add_one_pos (exp_pos L)) (exp_pos K)
  have hsplit : exp (u3Point L K) = exp (1 + 1) * exp ((1 + 1) + exp L + exp K) := by
    show exp ((1 + 1) + ((1 + 1) + exp L + exp K)) = _
    exact exp_add _ _
  rw [hsplit]
  have h4b : ((1 + 1 : Real) * (1 + 1)) * ((1 + 1) + exp L + exp K)
      < exp (1 + 1) * exp ((1 + 1) + exp L + exp K) :=
    lt_trans_ax (mul_lt_mul_of_pos_right exp_two_gt_four hb)
      (mul_lt_mul_pos_left (exp_grows_strictly_thm ((1 + 1) + exp L + exp K)) (exp_pos (1 + 1)))
  apply lt_trans_ax _ h4b
  show u3Point L K + u3Point L K + L < _
  show ((1 + 1) + ((1 + 1) + exp L + exp K)) + ((1 + 1) + ((1 + 1) + exp L + exp K)) + L < _
  apply lt_of_sub_pos
  have e : ((1 + 1 : Real) * (1 + 1)) * ((1 + 1) + exp L + exp K)
      - (((1 + 1 : Real) + ((1 + 1) + exp L + exp K))
        + ((1 + 1 : Real) + ((1 + 1) + exp L + exp K)) + L)
      = ((exp L + exp L) - L) + (exp K + exp K) := by
    mach_mpoly [exp L, exp K, L]
  rw [e]
  exact add_pos_real (sub_pos_of_lt (two_exp_gt_self L)) (add_pos_real (exp_pos K) (exp_pos K))

/-- `X < X²·(X−1)` for `X > 2`. **Symbolic**, so no numerals meet a transcendental atom. -/
theorem lt_cube_of_two_lt {X : Real} (h : (1 : Real) + 1 < X) : X < (X * X) * (X - 1) := by
  have hX : (0 : Real) < X := lt_trans_ax one_add_one_pos h
  have hX1 : (1 : Real) < X := lt_trans_ax one_lt_one_plus_one h
  have hXm1 : (1 : Real) < X - 1 := by
    apply lt_of_sub_pos
    have e : (X - 1) - 1 = X - (1 + 1) := by mach_ring
    rw [e]; exact sub_pos_of_lt h
  have s1 : X * 1 < X * X := mul_lt_mul_pos_left hX1 hX
  have s2 : (X * X) * 1 < (X * X) * (X - 1) := mul_lt_mul_pos_left hXm1 (mul_pos hX hX)
  have e1 : X * 1 = X := by mach_ring
  have e2 : (X * X) * 1 = X * X := by mach_ring
  rw [e1] at s1
  rw [e2] at s2
  exact lt_trans_ax s1 s2

/-- **The assembly, over bare reals.** `X·A − X·B > X³ − X² = X²(X−1) > K`. -/
theorem final_assembly {X A B K : Real} (hX : 0 < X)
    (hbig : X * X < A) (hsmall : B < X) (hK : K < (X * X) * (X - 1)) :
    K < X * A - X * B := by
  apply lt_of_sub_pos
  have e : (X * A - X * B) - K
      = (X * X - X * B) + (X * A - X * (X * X)) + ((X * X) * (X - 1) - K) := by
    mach_mpoly [X, A, B, K]
  rw [e]
  exact add_pos_real (add_pos_real (sub_pos_of_lt (mul_lt_mul_pos_left hsmall hX))
    (sub_pos_of_lt (mul_lt_mul_pos_left hbig hX))) (sub_pos_of_lt hK)

/-- **`u3` over `w4` is impossible** — one point, chosen from `L` and `K`. -/
theorem u3_w4_absurd {c₂ K : Real}
    (e : u3Point (log c₂) K
          * (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const c₂))
              (EMLTree.eml EMLTree.var EMLTree.var)).eval (u3Point (log c₂) K) = K) :
    False := by
  have hX := u3Point_pos (log c₂) K
  have m := u3_master _ e
  have wv : (EMLTree.eml EMLTree.var EMLTree.var).eval (u3Point (log c₂) K)
      = exp (u3Point (log c₂) K) - log (u3Point (log c₂) K) := rfl
  rw [wv] at m
  -- 0 < log X < X < exp X
  have hlogXpos : (0 : Real) < log (u3Point (log c₂) K) := by
    have h := log_lt_log zero_lt_one_ax (one_lt_u3Point (log c₂) K)
    rw [log_one] at h
    exact h
  have hlogXlt : log (u3Point (log c₂) K) < u3Point (log c₂) K := by
    have h := exp_grows_strictly_thm (log (u3Point (log c₂) K))
    rw [exp_log hX] at h
    exact h
  have hWpos : (0 : Real) < exp (u3Point (log c₂) K) - log (u3Point (log c₂) K) :=
    sub_pos_of_lt (lt_trans_ax hlogXlt (exp_grows_strictly_thm (u3Point (log c₂) K)))
  -- log (W X) < X
  have hsmall : log (exp (u3Point (log c₂) K) - log (u3Point (log c₂) K))
      < u3Point (log c₂) K := by
    have hlt : exp (u3Point (log c₂) K) - log (u3Point (log c₂) K) < exp (u3Point (log c₂) K) := by
      apply lt_of_sub_pos
      have ee : exp (u3Point (log c₂) K)
          - (exp (u3Point (log c₂) K) - log (u3Point (log c₂) K))
          = log (u3Point (log c₂) K) := by
        mach_mpoly [exp (u3Point (log c₂) K), log (u3Point (log c₂) K)]
      rw [ee]; exact hlogXpos
    have h := log_lt_log hWpos hlt
    rw [log_exp] at h
    exact h
  -- X·X < exp (exp X − L)
  have hbig : u3Point (log c₂) K * u3Point (log c₂) K
      < exp (exp (u3Point (log c₂) K) - log c₂) := by
    have hgap : u3Point (log c₂) K + u3Point (log c₂) K
        < exp (u3Point (log c₂) K) - log c₂ := by
      apply lt_of_sub_pos
      have ee : (exp (u3Point (log c₂) K) - log c₂)
          - (u3Point (log c₂) K + u3Point (log c₂) K)
          = exp (u3Point (log c₂) K)
            - ((u3Point (log c₂) K + u3Point (log c₂) K) + log c₂) := by
        mach_mpoly [exp (u3Point (log c₂) K), u3Point (log c₂) K, log c₂]
      rw [ee]
      exact sub_pos_of_lt (u3Point_dominates (log c₂) K)
    apply lt_trans_ax _ (exp_lt hgap)
    rw [exp_add]
    exact square_lt_square hX (exp_grows_strictly_thm (u3Point (log c₂) K))
  -- K < X²(X−1)
  have hK : K < (u3Point (log c₂) K * u3Point (log c₂) K) * (u3Point (log c₂) K - 1) := by
    apply lt_trans_ax _ (lt_cube_of_two_lt (two_lt_u3Point (log c₂) K))
    apply lt_trans_ax (exp_grows_strictly_thm K)
    show exp K < (1 + 1) + ((1 + 1) + exp (log c₂) + exp K)
    apply lt_of_sub_pos
    have ee : ((1 + 1 : Real) + ((1 + 1) + exp (log c₂) + exp K)) - exp K
        = (1 + 1) + ((1 + 1) + exp (log c₂)) := by mach_mpoly [exp (log c₂), exp K]
    rw [ee]
    exact add_pos_real one_add_one_pos (add_pos_real one_add_one_pos (exp_pos _))
  have hfinal := final_assembly hX hbig hsmall hK
  rw [m] at hfinal
  exact lt_irrefl_ax _ hfinal

/-! ## `u3 × w3`-small — the LAST cell of the depth-2 table

Its child `W x = exp x − L′` **has a parameter**, and for `L′ < 0` it EXCEEDS `exp x`, so
`u3 × w4`'s parameter-free bound `log (W X) < X` fails. **The fix is a third exponential in the
point and a slack term in the bound.**

> ### ⚠ Closing this settles **depth-2 case 9 ONLY.** Case 9 at depth ≥ 3 is untouched, and `1/x ∉ EML` stays exactly as open. A finite table being finished is not the frontier moving. -/

/-- The point with slack: `4 + exp L + exp K + exp M`. A `def`, so the normaliser sees one atom. -/
noncomputable def u3PointS (L K M : Real) : Real :=
  (1 + 1) + ((1 + 1) + exp L + exp K + exp M)

theorem two_lt_u3PointS (L K M : Real) : (1 : Real) + 1 < u3PointS L K M := by
  show (1 : Real) + 1 < (1 + 1) + ((1 + 1) + exp L + exp K + exp M)
  exact lt_add_of_pos_right (add_pos_real (add_pos_real (add_pos_real one_add_one_pos
    (exp_pos L)) (exp_pos K)) (exp_pos M))

theorem u3PointS_pos (L K M : Real) : 0 < u3PointS L K M :=
  lt_trans_ax one_add_one_pos (two_lt_u3PointS L K M)

theorem one_lt_u3PointS (L K M : Real) : (1 : Real) < u3PointS L K M :=
  lt_trans_ax one_lt_one_plus_one (two_lt_u3PointS L K M)

/-- `X + X + L < exp X` at the slack point. Same shape as `u3Point_dominates`; the extra `exp M`
only helps. -/
theorem u3PointS_dominates (L K M : Real) :
    u3PointS L K M + u3PointS L K M + L < exp (u3PointS L K M) := by
  have hb : (0 : Real) < (1 + 1) + exp L + exp K + exp M :=
    add_pos_real (add_pos_real (add_pos_real one_add_one_pos (exp_pos L)) (exp_pos K)) (exp_pos M)
  have hsplit : exp (u3PointS L K M) = exp (1 + 1) * exp ((1 + 1) + exp L + exp K + exp M) := by
    show exp ((1 + 1) + ((1 + 1) + exp L + exp K + exp M)) = _
    exact exp_add _ _
  rw [hsplit]
  have h4b : ((1 + 1 : Real) * (1 + 1)) * ((1 + 1) + exp L + exp K + exp M)
      < exp (1 + 1) * exp ((1 + 1) + exp L + exp K + exp M) :=
    lt_trans_ax (mul_lt_mul_of_pos_right exp_two_gt_four hb)
      (mul_lt_mul_pos_left (exp_grows_strictly_thm ((1 + 1) + exp L + exp K + exp M))
        (exp_pos (1 + 1)))
  apply lt_trans_ax _ h4b
  show ((1 + 1) + ((1 + 1) + exp L + exp K + exp M))
    + ((1 + 1) + ((1 + 1) + exp L + exp K + exp M)) + L < _
  apply lt_of_sub_pos
  have e : ((1 + 1 : Real) * (1 + 1)) * ((1 + 1) + exp L + exp K + exp M)
      - (((1 + 1 : Real) + ((1 + 1) + exp L + exp K + exp M))
        + ((1 + 1 : Real) + ((1 + 1) + exp L + exp K + exp M)) + L)
      = ((exp L + exp L) - L) + (exp K + exp K) + (exp M + exp M) := by
    mach_mpoly [exp L, exp K, exp M, L]
  rw [e]
  exact add_pos_real (add_pos_real (sub_pos_of_lt (two_exp_gt_self L))
    (add_pos_real (exp_pos K) (exp_pos K))) (add_pos_real (exp_pos M) (exp_pos M))

/-- **`exp X + D < exp (X + D)`** for `0 < D` and `1 < exp X`.

**The strict `1 < exp X` is load-bearing:** at `exp X = 1` the final step reads `D < D` and the
statement fails. Caught by the elaborator, not by review.

`exp (X+D) = exp X · exp D > exp X · (1 + D) = exp X + D·exp X ≥ exp X + D`. **Uses
`exp_gt_one_plus_self` directly** — the disclosed tangent axiom, deliberately. -/
theorem exp_add_slack {X D : Real} (hD : 0 < D) (hX : (1 : Real) < exp X) :
    exp X + D < exp (X + D) := by
  rw [exp_add]
  have h1 : exp X * (1 + D) < exp X * exp D :=
    mul_lt_mul_pos_left (exp_gt_one_plus_self D hD) (exp_pos X)
  apply lt_trans_ax _ h1
  apply lt_of_sub_pos
  have e : exp X * (1 + D) - (exp X + D) = (exp X * D) - D := by
    mach_mpoly [exp X, D]
  rw [e]
  apply sub_pos_of_lt
  have hh := mul_lt_mul_of_pos_right hX hD
  have e1 : (1 : Real) * D = D := by mach_ring
  rw [e1] at hh
  exact hh

/-- **The assembly with slack.** `X·A − X·B > X³ − X² − X·D = X·(X² − X − D) > K`. -/
theorem final_assembly_slack {X A B K D : Real} (hX : 0 < X)
    (hbig : X * X < A) (hsmall : B < X + D) (hK : K < X * ((X * X) - X - D)) :
    K < X * A - X * B := by
  apply lt_of_sub_pos
  have e : (X * A - X * B) - K
      = (X * (X + D) - X * B) + (X * A - X * (X * X)) + (X * ((X * X) - X - D) - K) := by
    mach_mpoly [X, A, B, K, D]
  rw [e]
  exact add_pos_real (add_pos_real (sub_pos_of_lt (mul_lt_mul_pos_left hsmall hX))
    (sub_pos_of_lt (mul_lt_mul_pos_left hbig hX))) (sub_pos_of_lt hK)

/-- **`u3` over `w3` is impossible on the small branch too** — **the last cell of the depth-2 table.**

Point `X := 4 + exp L + exp K + exp (−L′)`. The child may EXCEED `exp X` (when `L′ < 0`), so the
bound carries a slack: `log (W X) < X + exp (−L′)`. -/
theorem u3_w3_small_absurd {c₂ c' K : Real} (hc : log c' ≤ exp 1)
    (e : u3PointS (log c₂) K (-log c')
          * (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const c₂))
              (EMLTree.eml EMLTree.var (EMLTree.const c'))).eval
            (u3PointS (log c₂) K (-log c')) = K) :
    False := by
  have hX := u3PointS_pos (log c₂) K (-log c')
  have hX2 := two_lt_u3PointS (log c₂) K (-log c')
  have hD : (0 : Real) < exp (-log c') := exp_pos _
  have m := u3_master _ e
  have wv : (EMLTree.eml EMLTree.var (EMLTree.const c')).eval (u3PointS (log c₂) K (-log c'))
      = exp (u3PointS (log c₂) K (-log c')) - log c' := rfl
  rw [wv] at m
  -- exp X > 1, and exp X > exp 1 ≥ log c', so the child is positive
  have hexpX1 : (1 : Real) < exp (u3PointS (log c₂) K (-log c')) := by
    have h := exp_lt hX
    rw [exp_zero] at h
    exact h
  have hexpXgt : exp 1 < exp (u3PointS (log c₂) K (-log c')) :=
    exp_lt (one_lt_u3PointS (log c₂) K (-log c'))
  have hWpos : (0 : Real) < exp (u3PointS (log c₂) K (-log c')) - log c' :=
    sub_pos_of_lt (lt_of_le_of_lt hc hexpXgt)
  -- log (W X) < X + D
  have hsmall : log (exp (u3PointS (log c₂) K (-log c')) - log c')
      < u3PointS (log c₂) K (-log c') + exp (-log c') := by
    have hstep : exp (u3PointS (log c₂) K (-log c')) - log c'
        < exp (u3PointS (log c₂) K (-log c') + exp (-log c')) := by
      apply lt_trans_ax _ (exp_add_slack hD hexpX1)
      apply lt_of_sub_pos
      have ee : (exp (u3PointS (log c₂) K (-log c')) + exp (-log c'))
          - (exp (u3PointS (log c₂) K (-log c')) - log c')
          = exp (-log c') + log c' := by
        mach_mpoly [exp (u3PointS (log c₂) K (-log c')), exp (-log c'), log c']
      rw [ee]
      apply lt_of_sub_pos
      have ee2 : (exp (-log c') + log c') - 0 = exp (-log c') - (-log c') := by
        mach_mpoly [exp (-log c'), log c']
      rw [ee2]
      exact sub_pos_of_lt (exp_grows_strictly_thm (-log c'))
    have h := log_lt_log hWpos hstep
    rw [log_exp] at h
    exact h
  -- X·X < exp (exp X − L)
  have hbig : u3PointS (log c₂) K (-log c') * u3PointS (log c₂) K (-log c')
      < exp (exp (u3PointS (log c₂) K (-log c')) - log c₂) := by
    have hgap : u3PointS (log c₂) K (-log c') + u3PointS (log c₂) K (-log c')
        < exp (u3PointS (log c₂) K (-log c')) - log c₂ := by
      apply lt_of_sub_pos
      have ee : (exp (u3PointS (log c₂) K (-log c')) - log c₂)
          - (u3PointS (log c₂) K (-log c') + u3PointS (log c₂) K (-log c'))
          = exp (u3PointS (log c₂) K (-log c'))
            - ((u3PointS (log c₂) K (-log c') + u3PointS (log c₂) K (-log c')) + log c₂) := by
        mach_mpoly [exp (u3PointS (log c₂) K (-log c')), u3PointS (log c₂) K (-log c'), log c₂]
      rw [ee]
      exact sub_pos_of_lt (u3PointS_dominates (log c₂) K (-log c'))
    apply lt_trans_ax _ (exp_lt hgap)
    rw [exp_add]
    exact square_lt_square hX (exp_grows_strictly_thm (u3PointS (log c₂) K (-log c')))
  -- K < X·(X² − X − D)
  have hXgtD : exp (-log c') + (1 + 1) + 1 + 1 < u3PointS (log c₂) K (-log c') := by
    show _ < (1 + 1) + ((1 + 1) + exp (log c₂) + exp K + exp (-log c'))
    apply lt_of_sub_pos
    have ee : ((1 + 1 : Real) + ((1 + 1) + exp (log c₂) + exp K + exp (-log c')))
        - (exp (-log c') + (1 + 1) + 1 + 1) = exp (log c₂) + exp K := by
      mach_mpoly [exp (log c₂), exp K, exp (-log c')]
    rw [ee]
    exact add_pos_real (exp_pos _) (exp_pos K)
  have hcore : (1 : Real) < (u3PointS (log c₂) K (-log c') * u3PointS (log c₂) K (-log c'))
      - u3PointS (log c₂) K (-log c') - exp (-log c') := by
    -- X² > X·(D + 4) ≥ X·D + 4X ≥ D + X + 1 + 1
    have hXbig : exp (-log c') + (1 + 1) + 1 + 1 < u3PointS (log c₂) K (-log c') := hXgtD
    have hsq : u3PointS (log c₂) K (-log c') * (exp (-log c') + (1 + 1) + 1 + 1)
        < u3PointS (log c₂) K (-log c') * u3PointS (log c₂) K (-log c') :=
      mul_lt_mul_pos_left hXbig hX
    apply lt_trans_ax _ (by
      apply lt_of_sub_pos
      have ee : ((u3PointS (log c₂) K (-log c') * u3PointS (log c₂) K (-log c'))
          - u3PointS (log c₂) K (-log c') - exp (-log c'))
          - ((u3PointS (log c₂) K (-log c') * (exp (-log c') + (1 + 1) + 1 + 1))
            - u3PointS (log c₂) K (-log c') - exp (-log c'))
          = (u3PointS (log c₂) K (-log c') * u3PointS (log c₂) K (-log c'))
            - (u3PointS (log c₂) K (-log c') * (exp (-log c') + (1 + 1) + 1 + 1)) := by
        mach_mpoly [u3PointS (log c₂) K (-log c'), exp (-log c')]
      rw [ee]
      exact sub_pos_of_lt hsq)
    -- 1 < X·(D+4) − X − D
    apply lt_of_sub_pos
    have ee : ((u3PointS (log c₂) K (-log c') * (exp (-log c') + (1 + 1) + 1 + 1))
        - u3PointS (log c₂) K (-log c') - exp (-log c')) - 1
        = (u3PointS (log c₂) K (-log c') * exp (-log c') - exp (-log c'))
          + (u3PointS (log c₂) K (-log c') + u3PointS (log c₂) K (-log c'))
          + (u3PointS (log c₂) K (-log c') - 1) := by
      mach_mpoly [u3PointS (log c₂) K (-log c'), exp (-log c')]
    rw [ee]
    have hd1 : exp (-log c') * 1 < exp (-log c') * u3PointS (log c₂) K (-log c') :=
      mul_lt_mul_pos_left (one_lt_u3PointS (log c₂) K (-log c')) hD
    have hd2 : (0 : Real) < u3PointS (log c₂) K (-log c') * exp (-log c') - exp (-log c') := by
      apply sub_pos_of_lt
      have e1 : exp (-log c') * 1 = exp (-log c') := by mach_ring
      have e2 : exp (-log c') * u3PointS (log c₂) K (-log c')
          = u3PointS (log c₂) K (-log c') * exp (-log c') := by mach_ring
      rw [e1, e2] at hd1
      exact hd1
    exact add_pos_real (add_pos_real hd2 (add_pos_real hX hX))
      (sub_pos_of_lt (one_lt_u3PointS (log c₂) K (-log c')))
  have hK : K < u3PointS (log c₂) K (-log c')
      * ((u3PointS (log c₂) K (-log c') * u3PointS (log c₂) K (-log c'))
        - u3PointS (log c₂) K (-log c') - exp (-log c')) := by
    have hKX : K < u3PointS (log c₂) K (-log c') := by
      apply lt_trans_ax (exp_grows_strictly_thm K)
      show exp K < (1 + 1) + ((1 + 1) + exp (log c₂) + exp K + exp (-log c'))
      apply lt_of_sub_pos
      have ee : ((1 + 1 : Real) + ((1 + 1) + exp (log c₂) + exp K + exp (-log c'))) - exp K
          = ((1 + 1) + (1 + 1)) + exp (log c₂) + exp (-log c') := by
        mach_mpoly [exp (log c₂), exp K, exp (-log c')]
      rw [ee]
      exact add_pos_real (add_pos_real (add_pos_real one_add_one_pos one_add_one_pos)
        (exp_pos _)) (exp_pos _)
    apply lt_trans_ax hKX
    have h := mul_lt_mul_pos_left hcore hX
    have e1 : u3PointS (log c₂) K (-log c') * 1 = u3PointS (log c₂) K (-log c') := by mach_ring
    rw [e1] at h
    exact h
  have hfinal := final_assembly_slack hX hbig hsmall hK
  rw [m] at hfinal
  exact lt_irrefl_ax _ hfinal

/-! ## Is the one-point method depth-dependent? — **No.**

Every one-point proof above fixes a shape for `u` and `w`. **Re-reading them, the shapes are used
for nothing except supplying two bounds.** Stripped of the shapes, the argument is
`one_point_generic` below: **arbitrary `u`, arbitrary `w`, arbitrary depth.**

> ### Depth entered the depth-2 proofs only through VERIFYING the bounds — never through the argument. So case 9 at depth ≥ 3 is a **bound-supply problem**, not an argument problem.

⚠ **That is infrastructure, not a depth-3 result.** A lemma that *would* close a cell given bounds is
not a closed cell, and `one_point_generic`'s hypotheses are **not** supplied generically here —
hypothesis 1 needs `u.eval` to grow, hypothesis 2 needs `w.eval ≤ exp X`, and a tree can fail
either. **Whether every case-9 tree admits a point satisfying both is open.** -/

/-- `log` is monotone (non-strict) on the positives. -/
theorem log_le_log_of_le {a b : Real} (ha : 0 < a) (hab : a ≤ b) : log a ≤ log b := by
  rcases (le_iff_lt_or_eq a b).mp hab with h | h
  · exact le_of_lt (log_lt_log ha h)
  · rw [h]; exact le_refl _

/-- **THE ONE-POINT ARGUMENT, DEPTH-INDEPENDENT.**

Arbitrary `u`, arbitrary `w`, arbitrary depth. The only hypotheses about the children are the two
bounds at the single point `X`:

* `X + X ≤ u.eval X` — the left child is at least `2X` there;
* `0 < w.eval X ≤ exp X` — the right child is positive and at most `exp X` there.

Then `exp (u.eval X) ≥ exp X · exp X > X·X` while `log (w.eval X) ≤ X`, so
`X · eval > X·(X·X) − X·X`, which exceeds `K`.

**Every depth-2 cell closed by one point is an instance of this**; `u3PointS_dominates` is exactly
"discharge hypothesis 1 at the chosen point". -/
theorem one_point_generic {u w : EMLTree} {K X : Real}
    (hX : 0 < X)
    (hu : X + X ≤ u.eval X)
    (hwpos : 0 < w.eval X) (hwle : w.eval X ≤ exp X)
    (hK : K < X * (X * X) - X * X)
    (e : X * (EMLTree.eml u w).eval X = K) :
    False := by
  have v : (EMLTree.eml u w).eval X = exp (u.eval X) - log (w.eval X) := rfl
  rw [v] at e
  -- exp (u.eval X) > X·X
  have hbig : X * X < exp (u.eval X) := by
    have h1 : X * X < exp X * exp X := square_lt_square hX (exp_grows_strictly_thm X)
    have h2 : exp X * exp X = exp (X + X) := (exp_add X X).symm
    rw [h2] at h1
    exact lt_of_lt_of_le h1 (exp_monotone hu)
  -- log (w.eval X) ≤ X
  have hsmall : log (w.eval X) ≤ X := by
    have h := log_le_log_of_le hwpos hwle
    rw [log_exp] at h
    exact h
  -- assemble
  have hfinal : K < X * exp (u.eval X) - X * log (w.eval X) := by
    apply lt_of_sub_pos
    have ee : (X * exp (u.eval X) - X * log (w.eval X)) - K
        = (X * X - X * log (w.eval X)) + (X * exp (u.eval X) - X * (X * X))
          + ((X * (X * X) - X * X) - K) := by
      mach_mpoly [X, exp (u.eval X), log (w.eval X), K]
    rw [ee]
    have s1 : X * log (w.eval X) ≤ X * X := by
      rcases (le_iff_lt_or_eq (log (w.eval X)) X).mp hsmall with h | h
      · exact le_of_lt (mul_lt_mul_pos_left h hX)
      · rw [h]; exact le_refl _
    exact add_pos_real (add_pos_of_nonneg_of_pos (sub_nonneg_of_le s1)
      (sub_pos_of_lt (mul_lt_mul_pos_left hbig hX))) (sub_pos_of_lt hK)
  have edist : X * (exp (u.eval X) - log (w.eval X))
      = X * exp (u.eval X) - X * log (w.eval X) := by
    mach_mpoly [X, exp (u.eval X), log (w.eval X)]
  rw [edist] at e
  rw [e] at hfinal
  exact lt_irrefl_ax _ hfinal

/-- **The depth-2 work fits it.** `u3PointS_dominates` says exactly that hypothesis 1 of
`one_point_generic` holds at the chosen point for a `u3`-shaped left child — modulo the `− L` that
`u3`'s own `exp` absorbs. Recorded as a shape-check, not a re-proof. -/
theorem u3PointS_dominates_is_hypothesis_one (L K M : Real) :
    u3PointS L K M + u3PointS L K M < exp (u3PointS L K M) - L :=
  lt_of_sub_pos (by
    have ee : (exp (u3PointS L K M) - L) - (u3PointS L K M + u3PointS L K M)
        = exp (u3PointS L K M) - ((u3PointS L K M + u3PointS L K M) + L) := by
      mach_mpoly [exp (u3PointS L K M), u3PointS L K M, L]
    rw [ee]
    exact sub_pos_of_lt (u3PointS_dominates L K M))

/-! ## The remaining obligation, named — and it is NOT vacuous -/

/-- Hypothesis 1 of `one_point_generic`, named: the left child reaches `2X` at `X`. -/
def LeftGrowsAt (u : EMLTree) (X : Real) : Prop := X + X ≤ u.eval X

/-- Hypothesis 2 of `one_point_generic`, named: the right child is positive and at most `exp X`. -/
def RightBoundedAt (w : EMLTree) (X : Real) : Prop := 0 < w.eval X ∧ w.eval X ≤ exp X

/-- **The one-point argument, in the named form.** Case 9 at any depth reduces to finding a point
where both hold. -/
theorem one_point_of_bounds {u w : EMLTree} {K X : Real}
    (hX : 0 < X) (hL : LeftGrowsAt u X) (hR : RightBoundedAt w X)
    (hK : K < X * (X * X) - X * X)
    (e : X * (EMLTree.eml u w).eval X = K) :
    False :=
  one_point_generic hX hL hR.1 hR.2 hK e

/-- **`RightBoundedAt` FAILS AT EVERY POINT for a perfectly ordinary depth-2 right child.**

`eml (eml var (const 1)) (const 1)` evaluates to `exp (exp x)` — because `log 1 = 0` twice — and
`exp (exp X) > exp X` for every `X`.

> ### So the second obligation is not a formality: a depth-2 subtree can already outrun `exp X` everywhere, and then the one-point method has no point to stand on. **This is exactly why depth ≥ 3 is not "the same argument again".** -/
theorem rightBounded_fails_everywhere (X : Real) :
    ¬ RightBoundedAt (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1))
        (EMLTree.const 1)) X := by
  intro h
  have hval : (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1))
      (EMLTree.const 1)).eval X = exp (exp X) := by
    show exp (exp X - log (1 : Real)) - log (1 : Real) = exp (exp X)
    rw [log_one]
    have e : exp X - (0 : Real) = exp X := by mach_ring
    rw [e]
    have e2 : exp (exp X) - (0 : Real) = exp (exp X) := by mach_ring
    exact e2
  have hgt : exp X < exp (exp X) := exp_lt (exp_grows_strictly_thm X)
  have hle : (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1))
      (EMLTree.const 1)).eval X ≤ exp X := h.2
  rw [hval] at hle
  exact lt_irrefl_ax _ (lt_of_lt_of_le hgt hle)

/-! ## Why the method STALLS: the two obligations are in TENSION

`one_point_generic` needs `LeftGrowsAt u X` **and** `RightBoundedAt w X`. **They are not
independent.** The master equation `X·exp (u.eval X) = X·log (w.eval X) + K` says a large right
child *forces* a large left child — so the easiest route to hypothesis 1 is a large `w`, and that is
exactly what hypothesis 2 forbids.

> ### The very condition that guarantees hypothesis 1 REFUTES hypothesis 2. So "supply the two bounds" is not a plan: **a depth-≥3 argument must get hypothesis 1 from the left child's own structure, not from the balance.** -/

/-- `exp a ≤ exp b → a ≤ b`. -/
theorem le_of_exp_le {a b : Real} (h : exp a ≤ exp b) : a ≤ b := by
  rcases lt_total a b with hab | hab | hab
  · exact le_of_lt hab
  · exact le_of_eq hab
  · exact absurd h (by
      intro hle
      exact lt_irrefl_ax _ (lt_of_lt_of_le (exp_lt hab) hle))

/-- `c·a ≤ c·b → a ≤ b` for `c > 0`. -/
theorem le_of_mul_le_mul_pos_left {a b c : Real} (hc : 0 < c) (h : c * a ≤ c * b) : a ≤ b := by
  rcases lt_total a b with hab | hab | hab
  · exact le_of_lt hab
  · exact le_of_eq hab
  · exact absurd h (by
      intro hle
      exact lt_irrefl_ax _ (lt_of_lt_of_le (mul_lt_mul_pos_left hab hc) hle))

/-- **The balance lemma.** For `K ≥ 0`, `exp T ≤ log (w.eval X)` forces `T ≤ u.eval X`.

**A big right child does not buy the tree freedom; it forces the left child up too.** -/
theorem balance_forces_left {u w : EMLTree} {K X T : Real}
    (hX : 0 < X) (hK : 0 ≤ K)
    (hbig : exp T ≤ log (w.eval X))
    (e : X * (EMLTree.eml u w).eval X = K) :
    T ≤ u.eval X := by
  have v : (EMLTree.eml u w).eval X = exp (u.eval X) - log (w.eval X) := rfl
  rw [v] at e
  have edist : X * (exp (u.eval X) - log (w.eval X))
      = X * exp (u.eval X) - X * log (w.eval X) := by
    mach_mpoly [X, exp (u.eval X), log (w.eval X)]
  rw [edist] at e
  have heq : X * exp (u.eval X) = K + X * log (w.eval X) := by
    have ee : X * exp (u.eval X)
        = (X * exp (u.eval X) - X * log (w.eval X)) + X * log (w.eval X) := by
      mach_mpoly [X, exp (u.eval X), log (w.eval X)]
    rw [ee, e]
  have hstep : X * exp T ≤ X * log (w.eval X) := by
    rcases (le_iff_lt_or_eq (exp T) (log (w.eval X))).mp hbig with h | h
    · exact le_of_lt (mul_lt_mul_pos_left h hX)
    · rw [h]; exact le_refl _
  have hKadd : X * log (w.eval X) ≤ K + X * log (w.eval X) := by
    rcases (le_iff_lt_or_eq 0 K).mp hK with h | h
    · apply le_of_lt
      have hh := lt_add_of_pos_right (a := X * log (w.eval X)) h
      have ec : X * log (w.eval X) + K = K + X * log (w.eval X) := by mach_ring
      rw [ec] at hh
      exact hh
    · rw [← h]
      have ec : (0 : Real) + X * log (w.eval X) = X * log (w.eval X) := by mach_ring
      rw [ec]
      exact le_refl _
  have hge : X * exp T ≤ X * exp (u.eval X) := by
    rw [heq]
    exact le_trans hstep hKadd
  exact le_of_exp_le (le_of_mul_le_mul_pos_left hX hge)

/-- **`LeftGrowsAt` comes free when the right child is big enough.** -/
theorem leftGrows_of_big_right {u w : EMLTree} {K X : Real}
    (hX : 0 < X) (hK : 0 ≤ K)
    (hbig : exp (X + X) ≤ log (w.eval X))
    (e : X * (EMLTree.eml u w).eval X = K) :
    LeftGrowsAt u X :=
  balance_forces_left hX hK hbig e

/-- **…and the SAME hypothesis refutes `RightBoundedAt`.**

`log (w.eval X) ≥ exp (X+X)` gives `w.eval X ≥ exp (exp (X+X)) > exp X`.

> ### The condition that guarantees hypothesis 1 destroys hypothesis 2. The two obligations of `one_point_generic` are in TENSION — which is why the method stalls at depth ≥ 3 rather than merely lacking a lemma. -/
theorem bigRight_refutes_rightBounded {w : EMLTree} {X : Real}
    (hX : 0 < X) (hwpos : 0 < w.eval X)
    (hbig : exp (X + X) ≤ log (w.eval X)) :
    ¬ RightBoundedAt w X := by
  intro h
  have hle : w.eval X ≤ exp X := h.2
  -- w.eval X = exp (log (w.eval X)) ≥ exp (exp (X+X)) > exp X
  have hexp : exp (exp (X + X)) ≤ w.eval X := by
    have h1 : exp (exp (X + X)) ≤ exp (log (w.eval X)) := exp_monotone hbig
    rw [exp_log hwpos] at h1
    exact h1
  have hgt : exp X < exp (exp (X + X)) := by
    apply exp_lt
    apply lt_trans_ax _ (exp_grows_strictly_thm (X + X))
    exact lt_add_of_pos_right hX
  exact lt_irrefl_ax _ (lt_of_lt_of_le (lt_of_lt_of_le hgt hexp) hle)

/-- **The tension, as one statement.** Under the hypothesis that makes `LeftGrowsAt` free,
`RightBoundedAt` is false — so `one_point_generic` cannot be discharged this way. -/
theorem one_point_obligations_in_tension {u w : EMLTree} {K X : Real}
    (hX : 0 < X) (hK : 0 ≤ K) (hwpos : 0 < w.eval X)
    (hbig : exp (X + X) ≤ log (w.eval X))
    (e : X * (EMLTree.eml u w).eval X = K) :
    LeftGrowsAt u X ∧ ¬ RightBoundedAt w X :=
  ⟨leftGrows_of_big_right hX hK hbig e, bigRight_refutes_rightBounded hX hwpos hbig⟩

/-! ## What makes a tree GROW — `LeftGrowsAt` is decided by the left spine

The tension result says `LeftGrowsAt` must come from the left child's own structure. **So: which
trees have it?**

For `u = eml u₁ u₂` the descent is `X + X + log (u₂.eval X) ≤ exp (u₁.eval X)`, and taking `log`
weakens it to `log (X + X) ≤ u₁.eval X`.

> ### The requirement WEAKENS LOGARITHMICALLY at each step down the left spine — `2X`, `log 2X`, `log log 2X`, … — so growth is decided by **where the left spine ENDS**. `var` can meet the weakened form; `const` cannot, once `X` passes it. -/

/-- **`var` never grows.** `X + X ≤ X` is false for every `X > 0`. -/
theorem leftGrowsAt_var_false {X : Real} (hX : 0 < X) : ¬ LeftGrowsAt EMLTree.var X := by
  intro h
  have hv : (EMLTree.var).eval X = X := rfl
  have hle : X + X ≤ X := by rw [← hv]; exact h
  exact lt_irrefl_ax X (lt_of_lt_of_le (lt_add_of_pos_right hX) hle)

/-- **`const c` stops growing once `X` passes `c`.** -/
theorem leftGrowsAt_const_false {c X : Real} (hX : 0 < X) (hc : c ≤ X) :
    ¬ LeftGrowsAt (EMLTree.const c) X := by
  intro h
  have hv : (EMLTree.const c).eval X = c := rfl
  have hle : X + X ≤ c := by rw [← hv]; exact h
  exact lt_irrefl_ax X (lt_of_lt_of_le (lt_of_lt_of_le (lt_add_of_pos_right hX) hle) hc)

/-- **The descent, unconditional.** Growth at a node bounds its LEFT child's `exp` from below. -/
theorem leftGrows_descends {u₁ u₂ : EMLTree} {X : Real}
    (h : LeftGrowsAt (EMLTree.eml u₁ u₂) X) :
    X + X + log (u₂.eval X) ≤ exp (u₁.eval X) := by
  have hv : (EMLTree.eml u₁ u₂).eval X = exp (u₁.eval X) - log (u₂.eval X) := rfl
  have hle : X + X ≤ exp (u₁.eval X) - log (u₂.eval X) := by rw [← hv]; exact h
  rcases (le_iff_lt_or_eq (X + X) (exp (u₁.eval X) - log (u₂.eval X))).mp hle with hlt | heq
  · apply le_of_lt
    apply lt_of_sub_pos
    have ee : exp (u₁.eval X) - (X + X + log (u₂.eval X))
        = (exp (u₁.eval X) - log (u₂.eval X)) - (X + X) := by
      mach_mpoly [exp (u₁.eval X), log (u₂.eval X), X]
    rw [ee]
    exact sub_pos_of_lt hlt
  · apply le_of_eq
    have ee : X + X + log (u₂.eval X)
        = (exp (u₁.eval X) - log (u₂.eval X)) + log (u₂.eval X) := by rw [← heq]
    rw [ee]
    mach_mpoly [exp (u₁.eval X), log (u₂.eval X)]

/-- **And it WEAKENS logarithmically.** When the right child is at least `1`, growth at the node only
requires the left child to reach `log (X + X)` — not `X + X`.

> ### `2X` becomes `log 2X` one level down. That is why a long left spine can carry growth all the way to a `var` leaf. -/
theorem leftGrows_weakens {u₁ u₂ : EMLTree} {X : Real} (hX : 0 < X)
    (hu₂ : (1 : Real) ≤ u₂.eval X)
    (h : LeftGrowsAt (EMLTree.eml u₁ u₂) X) :
    log (X + X) ≤ u₁.eval X := by
  have hlog₂ : (0 : Real) ≤ log (u₂.eval X) := by
    have h1 := log_le_log_of_le zero_lt_one_ax hu₂
    rw [log_one] at h1
    exact h1
  have hd := leftGrows_descends h
  have hmid : X + X ≤ X + X + log (u₂.eval X) := by
    rcases (le_iff_lt_or_eq 0 (log (u₂.eval X))).mp hlog₂ with hl | hl
    · exact le_of_lt (lt_add_of_pos_right hl)
    · rw [← hl]
      have ec : X + X + (0 : Real) = X + X := by mach_ring
      rw [ec]
      exact le_refl _
  have hstep : X + X ≤ exp (u₁.eval X) := le_trans hmid hd
  have h2 := log_le_log_of_le (add_pos_real hX hX) hstep
  rw [log_exp] at h2
  exact h2

/-! ## V4 — this retro-explains the depth-2 table

The table's rows split into "cheap" (`u1`, `u2`) and "doubly-exponential" (`u3`, `u4`). **That split
was never about the row — it was about ONE LEAF, two levels down.** -/

/-- **A `const` at the left-left slot cannot grow**, once `X` passes `exp a`. This is `u1` and `u2`:
both have `const` there, and neither ever grew. -/
theorem leftGrowsAt_const_left_false {a X : Real} {w : EMLTree}
    (hX : 0 < X) (hw : (1 : Real) ≤ w.eval X) (ha : exp a ≤ X) :
    ¬ LeftGrowsAt (EMLTree.eml (EMLTree.const a) w) X := by
  intro h
  have hd := leftGrows_descends h
  have hva : (EMLTree.const a).eval X = a := rfl
  rw [hva] at hd
  have hlog : (0 : Real) ≤ log (w.eval X) := by
    have h1 := log_le_log_of_le zero_lt_one_ax hw
    rw [log_one] at h1
    exact h1
  have hmid : X + X ≤ X + X + log (w.eval X) := by
    rcases (le_iff_lt_or_eq 0 (log (w.eval X))).mp hlog with hl | hl
    · exact le_of_lt (lt_add_of_pos_right hl)
    · rw [← hl]
      have ec : X + X + (0 : Real) = X + X := by mach_ring
      rw [ec]; exact le_refl _
  exact lt_irrefl_ax X (lt_of_lt_of_le (lt_add_of_pos_right hX)
    (le_trans (le_trans hmid hd) ha))

/-- **A `var` at the left-left slot DOES grow** — at the very point the `u3` row already uses. This
is `u3` and `u4`: both have `var` there, and both were the doubly-exponential rows. -/
theorem leftGrowsAt_var_left_holds (c K M : Real) :
    LeftGrowsAt (EMLTree.eml EMLTree.var (EMLTree.const c)) (u3PointS (log c) K M) := by
  show u3PointS (log c) K M + u3PointS (log c) K M
    ≤ exp (u3PointS (log c) K M) - log c
  apply le_of_lt
  apply lt_of_sub_pos
  have ee : (exp (u3PointS (log c) K M) - log c)
      - (u3PointS (log c) K M + u3PointS (log c) K M)
      = exp (u3PointS (log c) K M)
        - ((u3PointS (log c) K M + u3PointS (log c) K M) + log c) := by
    mach_mpoly [exp (u3PointS (log c) K M), u3PointS (log c) K M, log c]
  rw [ee]
  exact sub_pos_of_lt (u3PointS_dominates (log c) K M)

end Real
end MachLib
