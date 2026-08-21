import MachLib.PevRoots

/-!
# The sharp leading form — one exponent, both sides

`pev_dichotomy` gives *some* `k` with `c·xᵏ ≤ |P|`; `pev_envelope` gives *some* `N` with
`|P| ≤ C·xᴺ`. Neither is the degree, and `k ≤ N` in general. That looseness is exactly what has
blocked `RatGermTrichotomy` in three separate arcs: with two different exponents, the quotient
`|P|/|Q|` is trapped between `x^{k_P − N_Q}` and `x^{N_P − k_Q}`, and when those straddle zero the
germ is neither shown bounded nor shown linear.

This file closes the gap the only way it can be closed: **one exponent, both bounds.**

```
pev L is eventually zero,  or  ∃ c C d,  c·x^d ≤ |pev L x| ≤ C·x^d  eventually
```

The lower half is `pev_dichotomy`'s argument unchanged — absorb the head once `x ≥ 2|a|/c₀`. The
upper half is free on the same induction, because `|a + x·P| ≤ |a| + C·x^{d+1} ≤ (|a| + C)·x^{d+1}`
whenever `x ≥ 1`. **The two were always provable together; they had simply been proved apart**, and
the cost of that was three arcs routing around the consequence.

No degree is ever *defined*. `d` is produced by the induction — incremented at each `cons` whose tail
dominates, reset to `0` where the tail dies and the head does not — which is the degree, arrived at
without a `List.length`-style detour or any trailing-zero bookkeeping.
-/

namespace MachLib

open Real

private theorem leading_head_upper (a C x : Real) (hx : 1 ≤ x) (d : Nat)
    (h : abs x * abs (pev [] x) ≤ C) : True := trivial

private theorem abs_add_le' (a b : Real) : abs (a + b) ≤ abs a + abs b := abs_add a b

/-- **The sharp leading form.** Either the list dies, or its magnitude is pinned between two
constant multiples of a **single** power of `x`. -/
theorem pev_leading_form : ∀ L : List Real,
    EvZeroF (pev L) ∨ ∃ (c C : Real) (d : Nat) (X : Real), 0 < c ∧ 1 ≤ X ∧
      ∀ x : Real, X ≤ x → c * powNat x d ≤ abs (pev L x) ∧ abs (pev L x) ≤ C * powNat x d := by
  intro L
  induction L with
  | nil => exact Or.inl ⟨1, le_refl 1, fun _ _ => rfl⟩
  | cons a as ih =>
      rcases ih with ⟨X, hX, hz⟩ | ⟨c₀, C₀, d, X, hc₀, hX, hb⟩
      · -- the tail dies: the head decides, at degree 0
        rcases lt_total a 0 with ha | ha | ha
        · refine Or.inr ⟨abs a, abs a, 0, X, abs_pos_of_ne (ne_of_lt ha), hX, fun x hx => ?_⟩
          have e : pev (a :: as) x = a := by
            show a + x * pev as x = a
            rw [hz x hx]; mach_ring
          rw [e, powNat_zero]
          have e2 : abs a * 1 = abs a := by mach_ring
          rw [e2]
          exact ⟨le_refl _, le_refl _⟩
        · refine Or.inl ⟨X, hX, fun x hx => ?_⟩
          show a + x * pev as x = 0
          rw [hz x hx, ha]; mach_ring
        · refine Or.inr ⟨abs a, abs a, 0, X, abs_pos_of_ne (ne_of_gt ha), hX, fun x hx => ?_⟩
          have e : pev (a :: as) x = a := by
            show a + x * pev as x = a
            rw [hz x hx]; mach_ring
          rw [e, powNat_zero]
          have e2 : abs a * 1 = abs a := by mach_ring
          rw [e2]
          exact ⟨le_refl _, le_refl _⟩
      · -- the tail dominates: multiply through by `x`, absorb the head on both sides
        have h2 : (0 : Real) < 1 + 1 := add_pos zero_lt_one_ax zero_lt_one_ax
        obtain ⟨X', hX', hXX', hbig⟩ := big_threshold a c₀ hc₀ X hX
        refine Or.inr ⟨c₀ / (1 + 1), abs a + C₀, d + 1, X', div_pos' hc₀ h2, hX', fun x hx => ?_⟩
        have hx1 : (1 : Real) ≤ x := le_trans hX' hx
        have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx1
        obtain ⟨hlo, hhi⟩ := hb x (le_trans hXX' hx)
        have hxp : c₀ * powNat x (d + 1) ≤ abs (x * pev as x) := by
          rw [abs_mul, abs_of_nonneg hx0]
          have v := mul_le_mul_of_nonneg_left hlo hx0
          have e : x * (c₀ * powNat x d) = c₀ * powNat x (d + 1) := by
            show x * (c₀ * powNat x d) = c₀ * (x * powNat x d)
            mach_mpoly [x, c₀, powNat x d]
          rw [e] at v; exact v
        have hxq : abs (x * pev as x) ≤ C₀ * powNat x (d + 1) := by
          rw [abs_mul, abs_of_nonneg hx0]
          have v := mul_le_mul_of_nonneg_left hhi hx0
          have e : x * (C₀ * powNat x d) = C₀ * powNat x (d + 1) := by
            show x * (C₀ * powNat x d) = C₀ * (x * powNat x d)
            mach_mpoly [x, C₀, powNat x d]
          rw [e] at v; exact v
        constructor
        · -- lower: exactly `pev_dichotomy`'s absorption
          have habs : (1 + 1) * abs a ≤ c₀ * powNat x (d + 1) := by
            have hxk : x ≤ powNat x (d + 1) := by
              show x ≤ x * powNat x d
              have v := mul_le_mul_of_nonneg_left (one_le_powNat hx1 d) hx0
              have e : x * 1 = x := by mach_ring
              rw [e] at v; exact v
            exact le_trans (le_trans hbig (mul_le_mul_of_nonneg_left hx (le_of_lt hc₀)))
              (mul_le_mul_of_nonneg_left hxk (le_of_lt hc₀))
          have hhalf : c₀ / (1 + 1) * powNat x (d + 1) + abs a ≤ c₀ * powNat x (d + 1) := by
            have hkey : c₀ / (1 + 1) * powNat x (d + 1) + c₀ / (1 + 1) * powNat x (d + 1)
                = c₀ * powNat x (d + 1) := by
              have e : c₀ / (1 + 1) * powNat x (d + 1) + c₀ / (1 + 1) * powNat x (d + 1)
                  = (c₀ / (1 + 1) * (1 + 1)) * powNat x (d + 1) := by
                mach_mpoly [c₀ / (1 + 1), powNat x (d + 1)]
              rw [e, div_mul_self' (ne_of_gt h2)]
            rw [← hkey]
            refine add_le_add_wit (le_refl _) ?_
            have hd2 : (1 + 1) * abs a ≤ (1 + 1) * (c₀ / (1 + 1) * powNat x (d + 1)) := by
              have e : (1 + 1) * (c₀ / (1 + 1) * powNat x (d + 1))
                  = (c₀ / (1 + 1) * (1 + 1)) * powNat x (d + 1) := by
                mach_mpoly [c₀ / (1 + 1), powNat x (d + 1)]
              rw [e, div_mul_self' (ne_of_gt h2)]; exact habs
            exact le_of_mul_le_mul_left' h2 hd2
          show c₀ / (1 + 1) * powNat x (d + 1) ≤ abs (a + x * pev as x)
          refine le_trans ?_ abs_add_ge
          have w := add_le_add_wit hhalf (le_refl (-(abs a)))
          have el : c₀ / (1 + 1) * powNat x (d + 1) + abs a + -(abs a)
              = c₀ / (1 + 1) * powNat x (d + 1) := by mach_ring
          rw [el] at w
          have hsub : c₀ * powNat x (d + 1) + -(abs a) ≤ abs (x * pev as x) - abs a := by
            have u := add_le_add_wit hxp (le_refl (-(abs a)))
            have e2 : abs (x * pev as x) + -(abs a) = abs (x * pev as x) - abs a := by mach_ring
            rw [e2] at u; exact u
          exact le_trans w hsub
        · -- upper: free, and this is the half that was missing
          show abs (a + x * pev as x) ≤ (abs a + C₀) * powNat x (d + 1)
          refine le_trans (abs_add_le' a (x * pev as x)) ?_
          have hone : abs a ≤ abs a * powNat x (d + 1) := by
            have v := mul_le_mul_of_nonneg_left (one_le_powNat hx1 (d + 1)) (abs_nonneg a)
            have e : abs a * 1 = abs a := by mach_ring
            rw [e] at v; exact v
          have hsum := add_le_add_wit hone hxq
          have e : abs a * powNat x (d + 1) + C₀ * powNat x (d + 1)
              = (abs a + C₀) * powNat x (d + 1) := by
            mach_mpoly [abs a, C₀, powNat x (d + 1)]
          rw [← e]
          exact hsum

/-! ## The trichotomy, discharged

Three arcs have wanted this and each routed around it. With one exponent on both sides it is a
comparison of two `Nat`s:

* `d_P ≤ d_Q` — then `x^{d_P} ≤ x^{d_Q}` for `x ≥ 1`, the quotient is at most `C_P/c_Q`, **bounded**;
* `d_Q + 1 ≤ d_P` — then `x·x^{d_Q} ≤ x^{d_P}`, the quotient is at least `(c_P/C_Q)·x`, **linear**.

`Nat.le_or_lt` splits them and no subtraction of exponents ever appears.
-/

private theorem cancel_inv (A q : Real) (hq : q ≠ 0) : A * q * (1 / q) = A := by
  have e : A * q * (1 / q) = A * (q * (1 / q)) := by mach_mpoly [A, q, (1 : Real) / q]
  rw [e, mul_inv q hq]; mach_ring

private theorem div_ge_of_mul_le {p q A : Real} (hq : 0 < q) (h : A * q ≤ p) : A ≤ p / q := by
  rw [div_def p q (ne_of_gt hq)]
  have v := mul_le_mul_of_nonneg_right h (le_of_lt (one_div_pos_of_pos hq))
  rw [cancel_inv A q (ne_of_gt hq)] at v; exact v

private theorem div_le_of_le_mul {p q A : Real} (hq : 0 < q) (h : p ≤ A * q) : p / q ≤ A := by
  rw [div_def p q (ne_of_gt hq)]
  have v := mul_le_mul_of_nonneg_right h (le_of_lt (one_div_pos_of_pos hq))
  rw [cancel_inv A q (ne_of_gt hq)] at v; exact v

/-- **`RatGermTrichotomy`, discharged.** A rational germ is eventually bounded, or eventually grows
at least linearly. Nothing between.

The ledger row named this on its third sighting; the fix was not a new idea but a sharper statement
of an old one — `pev_dichotomy` and `pev_envelope` proved on the *same* induction instead of two. -/
theorem ratGermTrichotomy_holds : RatGermTrichotomy := by
  intro f ⟨P, Q, X₀, hX₀, hQ0, he⟩
  -- the denominator cannot die: it is eventually nonzero by hypothesis
  rcases pev_leading_form Q with ⟨Z, hZ, hzq⟩ | ⟨cQ, CQ, dQ, XQ, hcQ, hXQ, hbQ⟩
  · exfalso
    obtain ⟨W, _, hW0, hWZ⟩ := two_bounds' hX₀ hZ
    exact hQ0 W hW0 (hzq W hWZ)
  rcases pev_leading_form P with ⟨Z, hZ, hzp⟩ | ⟨cP, CP, dP, XP, hcP, hXP, hbP⟩
  · -- numerator dies: the germ is eventually 0, hence bounded
    refine Or.inl ⟨1, ?_⟩
    obtain ⟨W, hW, hW0, hWZ⟩ := two_bounds' hX₀ hZ
    refine ⟨W, hW, fun x hx => ?_⟩
    rw [he x (le_trans hW0 hx), hzp x (le_trans hWZ hx),
        zero_div_eq (hQ0 x (le_trans hW0 hx)), abs_of_nonneg (le_refl (0 : Real))]
    exact le_of_lt zero_lt_one_ax
  obtain ⟨W₁, hW₁, hW₁a, hW₁b⟩ := two_bounds' hX₀ hXQ
  obtain ⟨W, hW, hWW₁, hWP⟩ := two_bounds' hW₁ hXP
  have hkey : ∀ x : Real, W ≤ x →
      abs (f x) = abs (pev P x) / abs (pev Q x) ∧ (0 : Real) < abs (pev Q x)
      ∧ (cP * powNat x dP ≤ abs (pev P x) ∧ abs (pev P x) ≤ CP * powNat x dP)
      ∧ (cQ * powNat x dQ ≤ abs (pev Q x) ∧ abs (pev Q x) ≤ CQ * powNat x dQ) := by
    intro x hx
    have hx0 : X₀ ≤ x := le_trans (le_trans hW₁a hWW₁) hx
    have hqne : pev Q x ≠ 0 := hQ0 x hx0
    refine ⟨by rw [he x hx0]; exact abs_div_eq hqne, abs_pos_of_ne hqne,
            hbP x (le_trans hWP hx), hbQ x (le_trans (le_trans hW₁b hWW₁) hx)⟩
  have hx1W : (1 : Real) ≤ W := hW
  -- both upper constants are positive, from the two bounds meeting at one point
  have hposP : (0 : Real) < CP := by
    obtain ⟨_, _, ⟨hlo, hhi⟩, _⟩ := hkey W (le_refl W)
    have hp : (0 : Real) < powNat W dP := powNat_pos (lt_of_lt_of_le zero_lt_one_ax hx1W) dP
    refine lt_of_lt_of_le hcP (le_of_mul_le_mul_left' hp ?_)
    have e1 : powNat W dP * cP = cP * powNat W dP := by mach_mpoly [cP, powNat W dP]
    have e2 : powNat W dP * CP = CP * powNat W dP := by mach_mpoly [CP, powNat W dP]
    rw [e1, e2]; exact le_trans hlo hhi
  have hposQ : (0 : Real) < CQ := by
    obtain ⟨_, _, _, ⟨hlo, hhi⟩⟩ := hkey W (le_refl W)
    have hp : (0 : Real) < powNat W dQ := powNat_pos (lt_of_lt_of_le zero_lt_one_ax hx1W) dQ
    refine lt_of_lt_of_le hcQ (le_of_mul_le_mul_left' hp ?_)
    have e1 : powNat W dQ * cQ = cQ * powNat W dQ := by mach_mpoly [cQ, powNat W dQ]
    have e2 : powNat W dQ * CQ = CQ * powNat W dQ := by mach_mpoly [CQ, powNat W dQ]
    rw [e1, e2]; exact le_trans hlo hhi
  rcases Nat.lt_or_ge dP (dQ + 1) with hle | hlt
  · -- degree of numerator strictly larger: BOUNDED by CP / cQ
    refine Or.inl ⟨CP / cQ, W, hW, fun x hx => ?_⟩
    obtain ⟨hfx, hqpos, ⟨_, hPhi⟩, ⟨hQlo, _⟩⟩ := hkey x hx
    have hx1 : (1 : Real) ≤ x := le_trans hW hx
    rw [hfx]
    refine div_le_of_le_mul hqpos ?_
    have step1 : abs (pev P x) ≤ CP * powNat x dQ :=
      le_trans hPhi (mul_le_mul_of_nonneg_left (powNat_mono_exp hx1 (Nat.le_of_lt_succ hle)) (le_of_lt hposP))
    have step2 : CP * powNat x dQ ≤ CP / cQ * (cQ * powNat x dQ) := by
      have e : CP / cQ * (cQ * powNat x dQ) = (CP / cQ * cQ) * powNat x dQ := by
        mach_mpoly [CP / cQ, cQ, powNat x dQ]
      rw [e, div_mul_self' (ne_of_gt hcQ)]
      exact le_refl _
    exact le_trans (le_trans step1 step2)
      (mul_le_mul_of_nonneg_left hQlo (le_of_lt (div_pos' hposP hcQ)))
  · -- degree of numerator strictly larger: AT LEAST LINEAR, rate cP / CQ
    refine Or.inr ⟨cP / CQ, W, div_pos' hcP hposQ, hW, fun x hx => ?_⟩
    obtain ⟨hfx, hqpos, ⟨hPlo, _⟩, ⟨_, hQhi⟩⟩ := hkey x hx
    have hx1 : (1 : Real) ≤ x := le_trans hW hx
    have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx1
    rw [hfx]
    refine div_ge_of_mul_le hqpos ?_
    have hstep : cP / CQ * x * (CQ * powNat x dQ) = cP * (x * powNat x dQ) := by
      have e : cP / CQ * x * (CQ * powNat x dQ)
          = (cP / CQ * CQ) * (x * powNat x dQ) := by
        mach_mpoly [cP / CQ, CQ, x, powNat x dQ]
      rw [e, div_mul_self' (ne_of_gt hposQ)]
    have hmono : cP * (x * powNat x dQ) ≤ cP * powNat x dP := by
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hcP)
      show x * powNat x dQ ≤ powNat x dP
      exact powNat_mono_exp hx1 hlt
    refine le_trans ?_ hPlo
    refine le_trans (mul_le_mul_of_nonneg_left hQhi ?_) ?_
    · exact mul_nonneg (le_of_lt (div_pos' hcP hposQ)) hx0
    · rw [hstep]; exact hmono

end MachLib
