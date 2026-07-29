import MachLib.Limits

/-!
# `HasDerivAt` as a definition — feasibility, and six rules that fall out

`MachLib.Real` declares **21 `HasDerivAt*` axioms** because `HasDerivAt` is an **opaque `Prop`**.
There is nothing to prove about an uninterpreted predicate, so every rule had to be assumed — the
same shape as `TendstoTo`, `ballCubeRatio` and `ReplayPacket`, each of which turned out to be a gap
in the *vocabulary* rather than in the argument.

This file tests whether the same fix applies here, and it is a **feasibility result, not a
retirement**: it builds the definition alongside the axiom rather than replacing it. Swapping the
axiom for the definition is a wide, mechanical change across everything that imports
`Differentiation`, and it is not worth making until the definition is known to carry the rules.

## The little-o form, chosen to avoid a division

The usual definition is `lim_{y→x} (f y − f x)/(y − x) = a`, and the quotient drags `divR`,
`mul_inv` and a `y ≠ x` side condition into every proof. The equivalent **linear-approximation**
form does not:

```
    HasDerivAtL f a x  :=  ∀ ε > 0, ∃ δ > 0, ∀ y,
                             |y − x| ≤ δ → |f y − f x − a·(y − x)| ≤ ε·|y − x|
```

Multiplying through by `|y − x|` is what removes the division *and* the side condition — `y = x`
makes both sides zero. **Fourth time this move has paid**: `npow_mul_bernoulli` taking `r(1+h)=1`,
`ekf2_gain_abs_le` keeping `sqrt` out, `affine_recip_secant_id` cleared of denominators, and now
this.

## What falls out, and what does not

Six rules are proved below from the definition alone. `mul` and `comp` need local boundedness of `f`
near `x` — true and derivable, but a further piece of development; the transcendental seeds
(`exp`, `sin`, `cos`, `log`) are genuinely primitive and stay axioms under any definition.

So the honest headline is **not** "21 axioms retired". It is: *the definition carries the structural
rules, so the swap is worth doing, and here is the evidence.*

`sorryAx`-free.
-/

namespace MachLib.Real

private theorem one_add_abs_nonneg (b : Real) : (0 : Real) ≤ 1 + abs b :=
  add_nonneg (le_of_lt zero_lt_one_ax) (abs_nonneg b)

/-- **The derivative, defined.** Linear approximation with a multiplicative error term — no
division, no `y ≠ x` side condition. -/
def HasDerivAtL (f : Real → Real) (a x : Real) : Prop :=
  ∀ ε : Real, 0 < ε → ∃ δ : Real, 0 < δ ∧
    ∀ y : Real, abs (y - x) ≤ δ → abs (f y - f x - a * (y - x)) ≤ ε * abs (y - x)

/-- Constants have derivative `0`. The approximation is exact, so any `δ` works. -/
theorem hasDerivAtL_const (c x : Real) : HasDerivAtL (fun _ => c) 0 x := by
  intro ε hε
  refine ⟨1, zero_lt_one_ax, fun y _ => ?_⟩
  rw [show c - c - 0 * (y - x) = 0 from by mach_ring, abs_zero]
  exact mul_nonneg (le_of_lt hε) (abs_nonneg _)

/-- The identity has derivative `1`, and again exactly. -/
theorem hasDerivAtL_id (x : Real) : HasDerivAtL (fun y => y) 1 x := by
  intro ε hε
  refine ⟨1, zero_lt_one_ax, fun y _ => ?_⟩
  rw [show y - x - 1 * (y - x) = 0 from by mach_ring, abs_zero]
  exact mul_nonneg (le_of_lt hε) (abs_nonneg _)

/-- **Congruence.** Pointwise-equal functions have the same derivative — `HasDerivAt_of_eq`. -/
theorem hasDerivAtL_of_eq (f g : Real → Real) (a x : Real)
    (h : ∀ y, f y = g y) (hf : HasDerivAtL f a x) : HasDerivAtL g a x := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := hf ε hε
  exact ⟨δ, hδ, fun y hy => by rw [← h y, ← h x]; exact hb y hy⟩

/-- **Negation** — `HasDerivAt_neg`, and here it is immediate rather than routed through the
product rule, because the definition makes it an `abs_neg`. -/
theorem hasDerivAtL_neg (f : Real → Real) (a x : Real) (hf : HasDerivAtL f a x) :
    HasDerivAtL (fun y => -f y) (-a) x := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := hf ε hε
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have hid : -f y - -f x - -a * (y - x) = -(f y - f x - a * (y - x)) := by mach_ring
  rw [hid, abs_neg]
  exact hb y hy

/-! ### `min`, proved locally

`min_le_left` and friends live in `Forge.lean`, which imports the whole transcendental stack —
too heavy for a foundational file. Three lines each here instead. -/

private theorem lt_of_not_le' {a b : Real} (h : ¬ a ≤ b) : b < a := by
  rcases lt_total a b with hl | he | hg
  · exact absurd ((le_iff_lt_or_eq a b).mpr (Or.inl hl)) h
  · exact absurd ((le_iff_lt_or_eq a b).mpr (Or.inr he)) h
  · exact hg

private theorem min_cases (a b : Real) : min a b = a ∨ min a b = b := by
  rcases Classical.em (a ≤ b) with h | h
  · exact Or.inl (by unfold min; exact if_pos h)
  · exact Or.inr (by unfold min; exact if_neg h)

private theorem min_pos' {a b : Real} (ha : 0 < a) (hb : 0 < b) : 0 < min a b := by
  rcases min_cases a b with h | h
  · rw [h]; exact ha
  · rw [h]; exact hb

private theorem min_le_l (a b : Real) : min a b ≤ a := by
  rcases Classical.em (a ≤ b) with h | h
  · rw [show min a b = a from by unfold min; exact if_pos h]
    exact le_refl a
  · rw [show min a b = b from by unfold min; exact if_neg h]
    exact le_of_lt (lt_of_not_le' h)

private theorem min_le_r (a b : Real) : min a b ≤ b := by
  rcases Classical.em (a ≤ b) with h | h
  · rw [show min a b = a from by unfold min; exact if_pos h]; exact h
  · rw [show min a b = b from by unfold min; exact if_neg h]
    exact le_refl b

/-- **Sum** — `HasDerivAt_add`. The `ε/2` split is the one division the definition costs, paid once
here rather than in every downstream proof. -/
theorem hasDerivAtL_add (f g : Real → Real) (a b x : Real)
    (hf : HasDerivAtL f a x) (hg : HasDerivAtL g b x) :
    HasDerivAtL (fun y => f y + g y) (a + b) x := by
  intro ε hε
  have h2 : (0 : Real) < 1 + 1 := add_pos one_pos one_pos
  have hhalf : 0 < ε / (1 + 1) := div_pos_of_pos_pos hε h2
  obtain ⟨d1, hd1, hb1⟩ := hf (ε / (1 + 1)) hhalf
  obtain ⟨d2, hd2, hb2⟩ := hg (ε / (1 + 1)) hhalf
  refine ⟨min d1 d2, min_pos' hd1 hd2, fun y hy => ?_⟩
  have k1 := hb1 y (le_trans hy (min_le_l d1 d2))
  have k2 := hb2 y (le_trans hy (min_le_r d1 d2))
  have hid : f y + g y - (f x + g x) - (a + b) * (y - x)
      = (f y - f x - a * (y - x)) + (g y - g x - b * (y - x)) := by mach_ring
  rw [hid]
  refine le_trans (abs_add _ _) ?_
  refine le_trans (add_le_add_both k1 k2) ?_
  have hsum : ε / (1 + 1) * abs (y - x) + ε / (1 + 1) * abs (y - x)
      = (ε / (1 + 1) + ε / (1 + 1)) * abs (y - x) := by mach_ring
  rw [hsum]
  have hhalves : ε / (1 + 1) + ε / (1 + 1) = ε := by
    rw [show ε / (1 + 1) + ε / (1 + 1) = ε / (1 + 1) * (1 + 1) from by mach_ring]
    exact div_mul_cancel (ne_of_gt h2)
  rw [hhalves]
  exact le_refl (ε * abs (y - x))

/-- **Difference** — `HasDerivAt_sub`, from sum and negation. -/
theorem hasDerivAtL_sub (f g : Real → Real) (a b x : Real)
    (hf : HasDerivAtL f a x) (hg : HasDerivAtL g b x) :
    HasDerivAtL (fun y => f y - g y) (a - b) x := by
  have hn := hasDerivAtL_neg g b x hg
  have hs := hasDerivAtL_add f (fun y => -g y) a (-b) x hf hn
  have hv : a + -b = a - b := by mach_ring
  rw [hv] at hs
  exact hasDerivAtL_of_eq (fun y => f y + -g y) (fun y => f y - g y) (a - b) x
    (fun y => by mach_ring) hs

/-! ## Local boundedness — the prerequisite `mul` and `comp` were waiting on

A differentiable function is bounded near the point. Obvious, and it has to be *proved* before the
product rule can be, because the product rule's error term carries a `g y` that must be controlled
uniformly over the neighbourhood. -/

/-- `|u| ≤ |u − v| + |v|`, from the triangle inequality. -/
private theorem abs_le_abs_sub_add (u v : Real) : abs u ≤ abs (u - v) + abs v := by
  have h := abs_add (u - v) v
  rwa [show u - v + v = u from by mach_ring] at h

/-- **The increment bound**, extracted because `mul` needs it directly and the boundedness proof
was already computing it: `|g y − g x| ≤ (1 + |b|)·|y − x|` near `x`. -/
theorem hasDerivAtL_gap_bound {g : Real → Real} {b x : Real} (hg : HasDerivAtL g b x) :
    ∃ δ : Real, 0 < δ ∧ ∀ y, abs (y - x) ≤ δ → abs (g y - g x) ≤ (1 + abs b) * abs (y - x) := by
  obtain ⟨δ, hδ, hb⟩ := hg 1 zero_lt_one_ax
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have h := hb y hy
  rw [one_mul_thm] at h
  refine le_trans (abs_le_abs_sub_add (g y - g x) (b * (y - x))) ?_
  rw [abs_mul]
  have hid : abs (y - x) + abs b * abs (y - x) = (1 + abs b) * abs (y - x) := by mach_ring
  rw [← hid]
  exact add_le_add_both h (le_refl _)

/-- **A differentiable function is bounded on a neighbourhood.** Instantiating the definition at
`ε = 1` gives `|g y − g x| ≤ (1 + |b|)·|y − x|`, and `δ` caps `|y − x|`. -/
theorem hasDerivAtL_bounded_near {g : Real → Real} {b x : Real} (hg : HasDerivAtL g b x) :
    ∃ δ : Real, 0 < δ ∧ ∀ y, abs (y - x) ≤ δ → abs (g y) ≤ abs (g x) + (1 + abs b) * δ := by
  obtain ⟨δ, hδ, hb⟩ := hg 1 zero_lt_one_ax
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have h := hb y hy
  rw [one_mul_thm] at h
  -- |g y - g x| ≤ |g y - g x - b(y-x)| + |b(y-x)| ≤ |y-x| + |b||y-x|
  have hgap : abs (g y - g x) ≤ (1 + abs b) * abs (y - x) := by
    have h1 := abs_le_abs_sub_add (g y - g x) (b * (y - x))
    rw [show g y - g x - b * (y - x) = g y - g x - b * (y - x) from rfl] at h1
    refine le_trans h1 ?_
    rw [abs_mul]
    have : abs (y - x) + abs b * abs (y - x) = (1 + abs b) * abs (y - x) := by mach_ring
    rw [← this]
    exact add_le_add_both h (le_refl _)
  refine le_trans (abs_le_abs_sub_add (g y) (g x)) ?_
  rw [add_comm (abs (g x)) ((1 + abs b) * δ)]
  refine add_le_add_both (le_trans hgap ?_) (le_refl (abs (g x)))
  exact mul_le_mul_of_nonneg_left hy
    (le_trans (le_of_lt zero_lt_one_ax) (le_add_of_nonneg_right (abs_nonneg b)))

/-- **The product rule's error, decomposed.** The whole conceptual content of `mul`, and it is an
identity rather than an estimate:

```
  f y·g y − f x·g x − (a·g x + f x·b)(y−x)
      =  g y · Rf  +  a(y−x)(g y − g x)  +  f x · Rg
```

with `Rf = f y − f x − a(y−x)` and `Rg = g y − g x − b(y−x)` the two residuals the hypotheses bound.
Each of the three pieces is then controlled by something already available: `Rf` and `Rg` by the
hypotheses, `g y` by `hasDerivAtL_bounded_near`, and `g y − g x` by the same `(1+|b|)|y−x|` estimate
that lemma's proof produces.

**What remains for `mul` is ε-bookkeeping, not mathematics** — splitting ε three ways and choosing δ
small enough that the middle term's `|a|(1+|b|)δ` fits. Recorded here so the next attempt starts from
the decomposition rather than rediscovering it. -/
theorem mul_error_decomposition (f g : Real → Real) (a b x y : Real) :
    f y * g y - f x * g x - (a * g x + f x * b) * (y - x)
      = g y * (f y - f x - a * (y - x))
        + a * (y - x) * (g y - g x)
        + f x * (g y - g x - b * (y - x)) := by
  mach_mpoly [f y, f x, g y, g x, a, b, y, x]

/-! ## The product rule

**One division, not three** — and that is not a style choice. Every quotient in this base is a proof
obligation (`C > 0`, the division lemmas, the telescope), so a second quotient is three more places
the positivity side-conditions multiply. `δ ≤ ε/C` does the second quotient's job: the middle term's
`|a|(1+|b|)·δ` is then `≤ |a|(1+|b|)·ε/C`, which is what makes the coefficient **telescope** instead
of forcing a max-of-three-epsilons argument.

**And the constant is NAMED.** A five-term expression written out at ten occurrences does not unify
across them, and `_` asks the elaborator to guess. `set` is a tactic this base lacks; a `def` is term
level and it has always had those. The expansion happens once, inside `mulBound`. -/

/-- Hoisted: `mach_mpoly`'s atom list is elaborated OUTSIDE the tactic block. **Fifth instance in
this library** — the list should simply be treated as top-level scope, always. -/
private theorem collect_three (A B C Q W : Real) :
    A * (Q * W) + B * (Q * W) + C * (Q * W) = (A + B + C) * Q * W := by
  mach_mpoly [A, B, C, Q, W]

private theorem reorder_plus_one (p q r : Real) : p + q + r + 1 - (p + r + q) = 1 := by
  mach_mpoly [p, q, r]

/-- The product rule's constant, named so every occurrence has one unifiable head. The trailing `+ 1`
carries strictness: it makes `mulBound` positive without any hypothesis on `f x` or `a`, and it is
the slack that turns `≤ ε` into the telescope below. -/
private noncomputable def mulBound (Mg fx a b : Real) : Real :=
  Mg + abs fx + abs a * (1 + abs b) + 1

private theorem mulBound_pos {Mg fx a b : Real} (hMg : 0 ≤ Mg) : 0 < mulBound Mg fx a b := by
  unfold mulBound
  refine lt_of_lt_of_le zero_lt_one_ax (le_add_of_nonneg_left ?_)
  exact add_nonneg (add_nonneg hMg (abs_nonneg fx))
    (mul_nonneg (abs_nonneg a) (one_add_abs_nonneg b))

/-- `S ≤ C` and `C > 0` give `S·(e/C) ≤ e`. The only numeric step the product rule needs. -/
private theorem telescope {S C e : Real} (hC : 0 < C) (hS : S ≤ C) (he : 0 ≤ e) :
    S * (e / C) ≤ e := by
  refine le_trans (mul_le_mul_of_nonneg_right hS (div_nonneg_of_nonneg_pos he hC)) ?_
  rw [mul_comm C (e / C), div_mul_cancel (ne_of_gt hC)]
  exact le_refl e

/-- **Product rule.** `mul_error_decomposition` supplies the identity; the three pieces are bounded
by the hypotheses, `hasDerivAtL_bounded_near` and `hasDerivAtL_gap_bound`. -/
theorem hasDerivAtL_mul (f g : Real → Real) (a b x : Real)
    (hf : HasDerivAtL f a x) (hg : HasDerivAtL g b x) :
    HasDerivAtL (fun y => f y * g y) (a * g x + f x * b) x := by
  intro ε hε
  obtain ⟨d0, hd0, hbnd⟩ := hasDerivAtL_bounded_near hg
  obtain ⟨dg, hdg, hgap⟩ := hasDerivAtL_gap_bound hg
  have hMg : (0 : Real) ≤ abs (g x) + (1 + abs b) * d0 :=
    add_nonneg (abs_nonneg _)
      (mul_nonneg (one_add_abs_nonneg b) (le_of_lt hd0))
  have hC : 0 < mulBound (abs (g x) + (1 + abs b) * d0) (f x) a b := mulBound_pos hMg
  have hq : 0 < ε / mulBound (abs (g x) + (1 + abs b) * d0) (f x) a b := div_pos_of_pos_pos hε hC
  obtain ⟨d1, hd1, hb1⟩ := hf _ hq
  obtain ⟨d2, hd2, hb2⟩ := hg _ hq
  refine ⟨min d0 (min dg (min d1 (min d2
      (ε / mulBound (abs (g x) + (1 + abs b) * d0) (f x) a b)))),
    min_pos' hd0 (min_pos' hdg (min_pos' hd1 (min_pos' hd2 hq))), fun y hy => ?_⟩
  have e0 : abs (y - x) ≤ d0 := le_trans hy (min_le_l _ _)
  have eG : abs (y - x) ≤ dg := le_trans hy (le_trans (min_le_r _ _) (min_le_l _ _))
  have e1 : abs (y - x) ≤ d1 :=
    le_trans hy (le_trans (min_le_r _ _) (le_trans (min_le_r _ _) (min_le_l _ _)))
  have e2 : abs (y - x) ≤ d2 :=
    le_trans hy (le_trans (min_le_r _ _) (le_trans (min_le_r _ _)
      (le_trans (min_le_r _ _) (min_le_l _ _))))
  have eQ : abs (y - x) ≤ ε / mulBound (abs (g x) + (1 + abs b) * d0) (f x) a b :=
    le_trans hy (le_trans (min_le_r _ _) (le_trans (min_le_r _ _)
      (le_trans (min_le_r _ _) (min_le_r _ _))))
  have hax : (0 : Real) ≤ abs (y - x) := abs_nonneg _
  rw [mul_error_decomposition f g a b x y]
  refine le_trans (abs_add _ _) (le_trans (add_le_add_both (abs_add _ _) (le_refl _)) ?_)
  -- three pieces
  have hT1 : abs (g y * (f y - f x - a * (y - x)))
      ≤ (abs (g x) + (1 + abs b) * d0)
        * (ε / mulBound (abs (g x) + (1 + abs b) * d0) (f x) a b * abs (y - x)) := by
    rw [abs_mul]
    exact mul_le_mul' (abs_nonneg _) (hbnd y e0) (abs_nonneg _) (hb1 y e1)
  have hT2 : abs (a * (y - x) * (g y - g x))
      ≤ abs a * (1 + abs b)
        * (ε / mulBound (abs (g x) + (1 + abs b) * d0) (f x) a b * abs (y - x)) := by
    rw [abs_mul, abs_mul]
    have step : abs a * abs (y - x) * abs (g y - g x)
        ≤ abs a * abs (y - x) * ((1 + abs b) * abs (y - x)) :=
      mul_le_mul_of_nonneg_left (hgap y eG)
        (mul_nonneg (abs_nonneg a) hax)
    refine le_trans step ?_
    have reassoc : abs a * abs (y - x) * ((1 + abs b) * abs (y - x))
        = abs a * (1 + abs b) * (abs (y - x) * abs (y - x)) := by mach_ring
    rw [reassoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right eQ hax)
      (mul_nonneg (abs_nonneg a) (one_add_abs_nonneg b))
  have hT3 : abs (f x * (g y - g x - b * (y - x)))
      ≤ abs (f x)
        * (ε / mulBound (abs (g x) + (1 + abs b) * d0) (f x) a b * abs (y - x)) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hb2 y e2) (abs_nonneg _)
  refine le_trans (add_le_add_both (add_le_add_both hT1 hT2) hT3) ?_
  -- collect: S * (q * |y-x|) with S = C - 1
  have hcollect := collect_three (abs (g x) + (1 + abs b) * d0) (abs a * (1 + abs b))
    (abs (f x)) (ε / mulBound (abs (g x) + (1 + abs b) * d0) (f x) a b) (abs (y - x))
  rw [hcollect]
  have hSC : (abs (g x) + (1 + abs b) * d0) + abs a * (1 + abs b) + abs (f x)
      ≤ mulBound (abs (g x) + (1 + abs b) * d0) (f x) a b := by
    unfold mulBound
    refine le_of_sub_nonneg ?_
    rw [reorder_plus_one (abs (g x) + (1 + abs b) * d0) (abs (f x)) (abs a * (1 + abs b))]
    exact le_of_lt zero_lt_one_ax
  exact mul_le_mul_of_nonneg_right (telescope hC hSC (le_of_lt hε)) hax

end MachLib.Real
