import MachLib.PevLeading

/-!
# The signed leading form — because `|f| ≥ c·x` does not feed the instruments

`RatGermTrichotomy` says a rational germ is bounded or satisfies `c·x ≤ |f x|`. That is the right
statement and it is **not yet usable**, which is worth saying plainly: the transcendence instruments
it was built to dispatch onto are **one-sided**.

```
FS_not_algebraic_of_ge_linear    needs   c·x ≤ S x
FS_not_algebraic_of_le_linear    needs   S x ≤ −(c·x)
```

An absolute-value bound feeds neither. Between them sits a fact nobody had needed yet: **a rational
germ eventually has a constant sign.**

## Why it is not borrowed from analysis

The tempting route: `pev_leading_form` gives `|pev L x| ≥ c·x^d > 0` on a tail, so `pev L` does not
vanish there, and a nonvanishing continuous function has constant sign. That needs the intermediate
value theorem, which would put an analytic axiom into the footprint of every consumer — and the whole
level-0 development has been built without one.

The algebraic route is one induction, and it is `pev_dichotomy`'s absorption with the absolute value
simply not taken: at `a :: as` the tail term `x·pev as x` eventually exceeds `|a|` in magnitude, so it
**decides the sign** of `a + x·pev as x`. Sign propagates outward from the top coefficient, which is
what "eventually the leading term wins" actually means.
-/

namespace MachLib

open Real

private theorem neg_abs_le' (a : Real) : 0 - abs a ≤ a := by
  rcases lt_total a 0 with h | h | h
  · rw [abs_of_nonpos (le_of_lt h)]
    have e : (0 : Real) - -a = a := by mach_ring
    rw [e]; exact le_refl a
  · rw [h, abs_of_nonneg (le_refl (0 : Real))]
    have e : (0 : Real) - 0 = 0 := by mach_ring
    rw [e]; exact le_refl 0
  · rw [abs_of_nonneg (le_of_lt h)]
    have v := add_le_add_wit (le_of_lt h) (le_of_lt h)
    have e : (0 : Real) + 0 = 0 := by mach_ring
    rw [e] at v
    have w := add_le_add_wit v (le_refl (0 - a))
    have el : (0 : Real) + (0 - a) = 0 - a := by mach_ring
    have er : a + a + (0 - a) = a := by mach_ring
    rw [el, er] at w; exact w

private theorem abs_zero_sub (a : Real) : abs (0 - a) = abs a := by
  rcases lt_total a 0 with h | h | h
  · have hn : (0 : Real) ≤ 0 - a := by
      have v := add_lt_add_left h (0 - a)
      have el : 0 - a + a = 0 := by mach_ring
      have er : 0 - a + 0 = 0 - a := by mach_ring
      rw [el, er] at v; exact le_of_lt v
    rw [abs_of_nonneg hn, abs_of_nonpos (le_of_lt h)]
    mach_ring
  · rw [h]; have e : (0 : Real) - 0 = 0 := by mach_ring
    rw [e]
  · have hn : (0 : Real) - a ≤ 0 := by
      have v := add_lt_add_left h (0 - a)
      have el : 0 - a + 0 = 0 - a := by mach_ring
      have er : 0 - a + a = 0 := by mach_ring
      rw [el, er] at v; exact le_of_lt v
    rw [abs_of_nonpos hn, abs_of_nonneg (le_of_lt h)]
    mach_ring

/-- **The absorption step, signed.** Once `x` is past `2|a|/c₀`, the tail term decides the sign:
`a + x·P ≥ (c₀/2)·x^{d+1}` whenever `P ≥ c₀·x^d`. `pev_dichotomy` proves this inside an absolute
value; the point here is that it never needed to. -/
private theorem absorb_head (a c₀ P x : Real) (d : Nat) (hc₀ : 0 < c₀) (hx1 : 1 ≤ x)
    (hbig : (1 + 1) * abs a ≤ c₀ * x) (hlo : c₀ * powNat x d ≤ P) :
    c₀ / (1 + 1) * powNat x (d + 1) ≤ a + x * P := by
  have h2 : (0 : Real) < 1 + 1 := add_pos zero_lt_one_ax zero_lt_one_ax
  have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx1
  have hxP : c₀ * powNat x (d + 1) ≤ x * P := by
    have v := mul_le_mul_of_nonneg_left hlo hx0
    have e : x * (c₀ * powNat x d) = c₀ * powNat x (d + 1) := by
      show x * (c₀ * powNat x d) = c₀ * (x * powNat x d)
      mach_mpoly [x, c₀, powNat x d]
    rw [e] at v; exact v
  have hxk : x ≤ powNat x (d + 1) := by
    show x ≤ x * powNat x d
    have v := mul_le_mul_of_nonneg_left (one_le_powNat hx1 d) hx0
    have e : x * 1 = x := by mach_ring
    rw [e] at v; exact v
  have habs : (1 + 1) * abs a ≤ c₀ * powNat x (d + 1) :=
    le_trans hbig (mul_le_mul_of_nonneg_left hxk (le_of_lt hc₀))
  have hkey : c₀ / (1 + 1) * powNat x (d + 1) + c₀ / (1 + 1) * powNat x (d + 1)
      = c₀ * powNat x (d + 1) := by
    have e : c₀ / (1 + 1) * powNat x (d + 1) + c₀ / (1 + 1) * powNat x (d + 1)
        = (c₀ / (1 + 1) * (1 + 1)) * powNat x (d + 1) := by
      mach_mpoly [c₀ / (1 + 1), powNat x (d + 1)]
    rw [e, div_mul_self' (ne_of_gt h2)]
  have hhalf : abs a ≤ c₀ / (1 + 1) * powNat x (d + 1) := by
    refine le_of_mul_le_mul_left' h2 ?_
    have e : (1 + 1) * (c₀ / (1 + 1) * powNat x (d + 1))
        = (c₀ / (1 + 1) * (1 + 1)) * powNat x (d + 1) := by
      mach_mpoly [c₀ / (1 + 1), powNat x (d + 1)]
    rw [e, div_mul_self' (ne_of_gt h2)]; exact habs
  have hstep := add_le_add_wit (neg_abs_le' a) hxP
  refine le_trans ?_ hstep
  have hneg : 0 - c₀ / (1 + 1) * powNat x (d + 1) ≤ 0 - abs a := by
    have v := add_le_add_wit (le_refl (0 - abs a - c₀ / (1 + 1) * powNat x (d + 1))) hhalf
    have el : 0 - abs a - c₀ / (1 + 1) * powNat x (d + 1) + abs a
        = 0 - c₀ / (1 + 1) * powNat x (d + 1) := by mach_ring
    have er : 0 - abs a - c₀ / (1 + 1) * powNat x (d + 1) + c₀ / (1 + 1) * powNat x (d + 1)
        = 0 - abs a := by mach_ring
    rw [el, er] at v; exact v
  have v := add_le_add_wit hneg (le_refl (c₀ * powNat x (d + 1)))
  refine le_trans ?_ v
  rw [← hkey]
  have e : 0 - c₀ / (1 + 1) * powNat x (d + 1)
      + (c₀ / (1 + 1) * powNat x (d + 1) + c₀ / (1 + 1) * powNat x (d + 1))
      = c₀ / (1 + 1) * powNat x (d + 1) := by mach_ring
  rw [e]
  exact le_refl _

/-- **Eventually, a coefficient list has a constant sign** — with a dominating bound on that side.
Three-way where `pev_dichotomy` is two-way. -/
theorem pev_eventual_sign : ∀ L : List Real,
    EvZeroF (pev L)
    ∨ (∃ (c : Real) (d : Nat) (X : Real), 0 < c ∧ 1 ≤ X ∧
        ∀ x : Real, X ≤ x → c * powNat x d ≤ pev L x)
    ∨ (∃ (c : Real) (d : Nat) (X : Real), 0 < c ∧ 1 ≤ X ∧
        ∀ x : Real, X ≤ x → c * powNat x d ≤ 0 - pev L x) := by
  intro L
  induction L with
  | nil => exact Or.inl ⟨1, le_refl 1, fun _ _ => rfl⟩
  | cons a as ih =>
      have h2 : (0 : Real) < 1 + 1 := add_pos zero_lt_one_ax zero_lt_one_ax
      rcases ih with ⟨X, hX, hz⟩ | ⟨c₀, d, X, hc₀, hX, hb⟩ | ⟨c₀, d, X, hc₀, hX, hb⟩
      · rcases lt_total a 0 with ha | ha | ha
        · refine Or.inr (Or.inr ⟨0 - a, 0, X, ?_, hX, fun x hx => ?_⟩)
          · have v := add_lt_add_left ha (0 - a)
            have el : 0 - a + a = 0 := by mach_ring
            have er : 0 - a + 0 = 0 - a := by mach_ring
            rw [el, er] at v; exact v
          · have e : pev (a :: as) x = a := by
              show a + x * pev as x = a
              rw [hz x hx]; mach_ring
            rw [e, powNat_zero]
            have e2 : (0 - a) * 1 = 0 - a := by mach_ring
            rw [e2]; exact le_refl _
        · refine Or.inl ⟨X, hX, fun x hx => ?_⟩
          show a + x * pev as x = 0
          rw [hz x hx, ha]; mach_ring
        · refine Or.inr (Or.inl ⟨a, 0, X, ha, hX, fun x hx => ?_⟩)
          have e : pev (a :: as) x = a := by
            show a + x * pev as x = a
            rw [hz x hx]; mach_ring
          rw [e, powNat_zero]
          have e2 : a * 1 = a := by mach_ring
          rw [e2]; exact le_refl _
      · obtain ⟨X', hX', hXX', hbig⟩ := big_threshold a c₀ hc₀ X hX
        refine Or.inr (Or.inl ⟨c₀ / (1 + 1), d + 1, X', div_pos' hc₀ h2, hX', fun x hx => ?_⟩)
        have hbigx : (1 + 1) * abs a ≤ c₀ * x :=
          le_trans hbig (mul_le_mul_of_nonneg_left hx (le_of_lt hc₀))
        exact absorb_head a c₀ (pev as x) x d hc₀ (le_trans hX' hx) hbigx
          (hb x (le_trans hXX' hx))
      · obtain ⟨X', hX', hXX', hbig⟩ := big_threshold a c₀ hc₀ X hX
        refine Or.inr (Or.inr ⟨c₀ / (1 + 1), d + 1, X', div_pos' hc₀ h2, hX', fun x hx => ?_⟩)
        have hbigx : (1 + 1) * abs a ≤ c₀ * x :=
          le_trans hbig (mul_le_mul_of_nonneg_left hx (le_of_lt hc₀))
        have hbig' : (1 + 1) * abs (0 - a) ≤ c₀ * x := by rw [abs_zero_sub]; exact hbigx
        have hmir := absorb_head (0 - a) c₀ (0 - pev as x) x d hc₀ (le_trans hX' hx) hbig'
          (hb x (le_trans hXX' hx))
        have e : 0 - a + x * (0 - pev as x) = 0 - (a + x * pev as x) := by
          mach_mpoly [a, x, pev as x]
        rw [e] at hmir
        exact hmir

end MachLib
