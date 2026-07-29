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

end MachLib.Real
