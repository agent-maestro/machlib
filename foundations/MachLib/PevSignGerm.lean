import MachLib.PevSign

/-!
# The signed trichotomy, assembled — the germ, not just the polynomial

`pev_eventual_sign` gives the sign of a *coefficient list*. The consumers want the sign of a *germ*,
and the gap between them is the four-way combination for `P/Q`. Closing it makes
`RatGermTrichotomy` emit what the one-sided instruments actually take:

```
FS_not_algebraic_of_ge_linear    needs   c·x ≤ S x        ← the positive branch
FS_not_algebraic_of_le_linear    needs   S x ≤ −(c·x)     ← the negative branch
```

The assembly is bookkeeping. The one thing worth remarking is where the sign comes from: **not from
`f`** — nothing is known about `f` beyond the germ identity — but from `P` and `Q` separately, each
decided by `pev_eventual_sign`, then combined through the quotient. The denominator cannot die (the
germ hypothesis makes it eventually nonvanishing), so exactly four cases arise and each fixes the
sign of `f`.

The `p < 0, q < 0` case is the only one that is not immediate: `p/q = (−p)/(−q)` by cross
multiplication (`div_eq_div_of_cross`, since `p·(−q) = (−p)·q`), and then both arguments are
positive.
-/

namespace MachLib

open Real

-- `neg_of_pos_neg` lives in `EMLGermSign`, which is not upstream of this file; three lines is
-- cheaper than an import that would drag the level-1 branch into the level-0 one.
private theorem neg_of_pos_neg {a : Real} (h : 0 < -a) : a < 0 := by
  have v := add_lt_add_left h a
  have el : a + 0 = a := by mach_ring
  have er : a + -a = 0 := by mach_ring
  rw [el, er] at v; exact v

private theorem neg_pos_of_neg {a : Real} (h : a < 0) : 0 < -a := by
  have v := add_lt_add_left h (-a)
  have el : -a + a = 0 := by mach_ring
  have er : -a + 0 = -a := by mach_ring
  rw [el, er] at v; exact v

private theorem div_neg_of_neg_of_pos {p q : Real} (hp : p < 0) (hq : 0 < q) : p / q < 0 := by
  refine neg_of_pos_neg ?_
  rw [neg_div (ne_of_gt hq)]
  exact div_pos' (neg_pos_of_neg hp) hq

private theorem div_swap_neg {p q : Real} (hq : q ≠ 0) (hqn : -q ≠ 0) : p / q = (-p) / (-q) :=
  div_eq_div_of_cross hq hqn (by mach_ring)

private theorem div_pos_of_neg_of_neg {p q : Real} (hp : p < 0) (hq : q < 0) : 0 < p / q := by
  rw [div_swap_neg (ne_of_lt hq) (ne_of_gt (neg_pos_of_neg hq))]
  exact div_pos' (neg_pos_of_neg hp) (neg_pos_of_neg hq)

private theorem div_neg_of_pos_of_neg {p q : Real} (hp : 0 < p) (hq : q < 0) : p / q < 0 := by
  rw [div_swap_neg (ne_of_lt hq) (ne_of_gt (neg_pos_of_neg hq))]
  refine div_neg_of_neg_of_pos ?_ (neg_pos_of_neg hq)
  refine neg_of_pos_neg ?_
  have e : -(-p) = p := by mach_ring
  rw [e]; exact hp

/-- Turn `pev_eventual_sign`'s dominating bound into a bare sign. -/
private theorem pos_of_dom {c : Real} {d : Nat} {X x : Real} (hc : 0 < c) (hX : 1 ≤ X)
    (hx : X ≤ x) {v : Real} (h : c * powNat x d ≤ v) : 0 < v :=
  lt_of_lt_of_le (mul_pos hc (powNat_pos (lt_of_lt_of_le zero_lt_one_ax (le_trans hX hx)) d)) h

private theorem neg_of_dom {c : Real} {d : Nat} {X x : Real} (hc : 0 < c) (hX : 1 ≤ X)
    (hx : X ≤ x) {v : Real} (h : c * powNat x d ≤ 0 - v) : v < 0 := by
  refine neg_of_pos_neg ?_
  have hv := pos_of_dom hc hX hx h
  have e : (0 : Real) - v = -v := by mach_ring
  rw [e] at hv; exact hv

/-- **A rational germ eventually has a constant sign.** The germ-level companion of
`pev_eventual_sign`. -/
theorem ratGerm_eventual_sign {f : Real → Real} (h : RatGerm f) :
    EvZeroF f
    ∨ (∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → 0 < f x)
    ∨ (∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → f x < 0) := by
  obtain ⟨P, Q, X₀, hX₀, hQ0, he⟩ := h
  rcases pev_eventual_sign Q with ⟨Z, hZ, hzq⟩ | ⟨cQ, dQ, XQ, hcQ, hXQ, hbQ⟩
    | ⟨cQ, dQ, XQ, hcQ, hXQ, hbQ⟩
  · exfalso
    obtain ⟨W, _, hW0, hWZ⟩ := two_bounds' hX₀ hZ
    exact hQ0 W hW0 (hzq W hWZ)
  all_goals
    rcases pev_eventual_sign P with ⟨Z, hZ, hzp⟩ | ⟨cP, dP, XP, hcP, hXP, hbP⟩
      | ⟨cP, dP, XP, hcP, hXP, hbP⟩
  -- Q positive, P dies
  · refine Or.inl ?_
    obtain ⟨W₁, hW₁, hW₁a, hW₁b⟩ := two_bounds' hX₀ hZ
    refine ⟨W₁, hW₁, fun x hx => ?_⟩
    rw [he x (le_trans hW₁a hx), hzp x (le_trans hW₁b hx),
        zero_div_eq (hQ0 x (le_trans hW₁a hx))]
  -- Q positive, P positive
  · obtain ⟨W₁, hW₁, hW₁a, hW₁b⟩ := two_bounds' hX₀ hXQ
    obtain ⟨W, hW, hWW₁, hWP⟩ := two_bounds' hW₁ hXP
    refine Or.inr (Or.inl ⟨W, hW, fun x hx => ?_⟩)
    rw [he x (le_trans (le_trans hW₁a hWW₁) hx)]
    exact div_pos' (pos_of_dom hcP hXP (le_trans hWP hx) (hbP x (le_trans hWP hx)))
      (pos_of_dom hcQ hXQ (le_trans (le_trans hW₁b hWW₁) hx)
        (hbQ x (le_trans (le_trans hW₁b hWW₁) hx)))
  -- Q positive, P negative
  · obtain ⟨W₁, hW₁, hW₁a, hW₁b⟩ := two_bounds' hX₀ hXQ
    obtain ⟨W, hW, hWW₁, hWP⟩ := two_bounds' hW₁ hXP
    refine Or.inr (Or.inr ⟨W, hW, fun x hx => ?_⟩)
    rw [he x (le_trans (le_trans hW₁a hWW₁) hx)]
    exact div_neg_of_neg_of_pos (neg_of_dom hcP hXP (le_trans hWP hx) (hbP x (le_trans hWP hx)))
      (pos_of_dom hcQ hXQ (le_trans (le_trans hW₁b hWW₁) hx)
        (hbQ x (le_trans (le_trans hW₁b hWW₁) hx)))
  -- Q negative, P dies
  · refine Or.inl ?_
    obtain ⟨W₁, hW₁, hW₁a, hW₁b⟩ := two_bounds' hX₀ hZ
    refine ⟨W₁, hW₁, fun x hx => ?_⟩
    rw [he x (le_trans hW₁a hx), hzp x (le_trans hW₁b hx),
        zero_div_eq (hQ0 x (le_trans hW₁a hx))]
  -- Q negative, P positive
  · obtain ⟨W₁, hW₁, hW₁a, hW₁b⟩ := two_bounds' hX₀ hXQ
    obtain ⟨W, hW, hWW₁, hWP⟩ := two_bounds' hW₁ hXP
    refine Or.inr (Or.inr ⟨W, hW, fun x hx => ?_⟩)
    rw [he x (le_trans (le_trans hW₁a hWW₁) hx)]
    exact div_neg_of_pos_of_neg (pos_of_dom hcP hXP (le_trans hWP hx) (hbP x (le_trans hWP hx)))
      (neg_of_dom hcQ hXQ (le_trans (le_trans hW₁b hWW₁) hx)
        (hbQ x (le_trans (le_trans hW₁b hWW₁) hx)))
  -- Q negative, P negative
  · obtain ⟨W₁, hW₁, hW₁a, hW₁b⟩ := two_bounds' hX₀ hXQ
    obtain ⟨W, hW, hWW₁, hWP⟩ := two_bounds' hW₁ hXP
    refine Or.inr (Or.inl ⟨W, hW, fun x hx => ?_⟩)
    rw [he x (le_trans (le_trans hW₁a hWW₁) hx)]
    exact div_pos_of_neg_of_neg (neg_of_dom hcP hXP (le_trans hWP hx) (hbP x (le_trans hWP hx)))
      (neg_of_dom hcQ hXQ (le_trans (le_trans hW₁b hWW₁) hx)
        (hbQ x (le_trans (le_trans hW₁b hWW₁) hx)))

/-! ## The payoff: the trichotomy in the shape the instruments take -/

/-- **The signed trichotomy.** Bounded, or eventually above `c·x`, or eventually below `−c·x` —
which is exactly what `FS_not_algebraic_of_ge_linear` and `FS_not_algebraic_of_le_linear` consume.

`RatGermTrichotomy` gave `c·x ≤ |f x|`, which feeds neither. This is that statement with the
absolute value resolved by `ratGerm_eventual_sign`. -/
def RatGermSignedTrichotomy : Prop :=
  ∀ f : Real → Real, RatGerm f →
    (∃ K X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → abs (f x) ≤ K)
    ∨ (∃ c X : Real, 0 < c ∧ 1 ≤ X ∧ ∀ x : Real, X ≤ x → c * x ≤ f x)
    ∨ (∃ c X : Real, 0 < c ∧ 1 ≤ X ∧ ∀ x : Real, X ≤ x → f x ≤ 0 - (c * x))

theorem ratGermSignedTrichotomy_holds : RatGermSignedTrichotomy := by
  intro f hf
  rcases ratGermTrichotomy_holds f hf with hbdd | ⟨c, X, hc, hX, hlin⟩
  · exact Or.inl hbdd
  rcases ratGerm_eventual_sign hf with ⟨Z, hZ, hzf⟩ | ⟨Z, hZ, hpos⟩ | ⟨Z, hZ, hneg⟩
  · -- the germ dies: bounded by 0
    refine Or.inl ⟨0, Z, hZ, fun x hx => ?_⟩
    rw [hzf x hx, abs_of_nonneg (le_refl (0 : Real))]
    exact le_refl 0
  · obtain ⟨W, hW, hWX, hWZ⟩ := two_bounds' hX hZ
    refine Or.inr (Or.inl ⟨c, W, hc, hW, fun x hx => ?_⟩)
    have hv := hlin x (le_trans hWX hx)
    rw [abs_of_nonneg (le_of_lt (hpos x (le_trans hWZ hx)))] at hv
    exact hv
  · obtain ⟨W, hW, hWX, hWZ⟩ := two_bounds' hX hZ
    refine Or.inr (Or.inr ⟨c, W, hc, hW, fun x hx => ?_⟩)
    have hv := hlin x (le_trans hWX hx)
    rw [abs_of_nonpos (le_of_lt (hneg x (le_trans hWZ hx)))] at hv
    -- `c * x ≤ -(f x)`  ⟹  `f x ≤ 0 - c * x`
    have w := add_le_add_wit hv (le_refl (f x - c * x))
    have el : c * x + (f x - c * x) = f x := by mach_ring
    have er : -(f x) + (f x - c * x) = 0 - c * x := by mach_ring
    rw [el, er] at w; exact w

end MachLib
