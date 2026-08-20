import MachLib.EMLZeroQueryBarrier

/-!
# Toward the `C₀` normal form: the polynomial dichotomy, and the first strict query separation

Two things, both on the critical path to characterising `C₀ = {f : computable with 0 F-queries}`.

## The keystone

Envelopes break on cancellation: `x` and `−x + 1/x` sum to `1/x`, and leading-order data of the
summands does not predict the order of the sum. The escape is not a better envelope but an **exact**
representation — an eventual rational germ `P/Q` — where cancellation happens in the polynomial
arithmetic and needs no asymptotic prediction.

The one genuinely new supporting result that programme needs is that a polynomial is *eventually*
zero or *eventually* nonzero. `pev_dichotomy` proves it in the sharper form the germ argument
consumes:

```
either  P ≡ 0 eventually,  or  ∃ c > 0, k, X:  c · xᵏ ≤ |P(x)|  for x ≥ X
```

by leading-term domination, with no root-counting theorem. That is banked here; the germ compilation
itself is not built yet, and the inventory of what remains is at the end of the file.

## The first strict separation

`C₀ ⊊ C₁`, on the division-free fragment, and the witness is **`F` itself** rather than `exp` —
`F` costs one query by definition, whereas `exp` currently costs two. Since `log x ≥ 0` for `x ≥ 1`,

```
F(x) = exp x + log x ≥ exp x      (x ≥ 1)
```

so `F` outgrows every polynomial envelope and cannot be zero-query.
-/

namespace MachLib

open Real

/-! ## Horner evaluation of a coefficient list -/

/-- `pev [c₀, c₁, …] x = c₀ + x·(c₁ + x·(…))`. -/
noncomputable def pev : List Real → Real → Real
  | [], _ => 0
  | c :: cs, x => c + x * pev cs x

/-- Eventually the zero function. -/
def EvZeroF (f : Real → Real) : Prop := ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → f x = 0

/-- Eventually bounded below by `c·xᵏ` in absolute value, with `c > 0`. -/
def EvDom (f : Real → Real) : Prop :=
  ∃ (c : Real) (k : Nat) (X : Real), 0 < c ∧ 1 ≤ X ∧
    ∀ x : Real, X ≤ x → c * powNat x k ≤ abs (f x)

theorem le_add_nonneg' {a b : Real} (hb : 0 ≤ b) : a ≤ a + b := by
  have v := add_le_add_wit (le_refl a) hb
  have e : a + 0 = a := by mach_ring
  rw [e] at v; exact v

private theorem div_mul_self' {a c : Real} (hc : c ≠ 0) : a / c * c = a := by
  rw [div_def a c hc]
  have e : a * (1 / c) * c = a * (c * (1 / c)) := by mach_mpoly [a, c, (1 : Real) / c]
  rw [e, mul_inv c hc]; mach_ring

private theorem nonneg_of_scaled_nonneg {c z : Real} (hc : 0 < c) (h : 0 ≤ c * z) : 0 ≤ z := by
  rcases lt_total 0 z with hz | hz | hz
  · exact le_of_lt hz
  · exact le_of_eq hz
  · exfalso
    have v := add_lt_add_left hz (-z)
    have l : -z + z = 0 := by mach_ring
    have r : -z + 0 = -z := by mach_ring
    rw [l, r] at v
    have hp := mul_pos hc v
    have e : c * -z = -(c * z) := by mach_ring
    rw [e] at hp
    have w := add_lt_add_left hp (c * z)
    have el : c * z + 0 = c * z := by mach_ring
    have er : c * z + -(c * z) = 0 := by mach_ring
    rw [el, er] at w
    exact absurd (lt_of_le_of_lt h w) (lt_irrefl_ax 0)

private theorem le_of_mul_le_mul_left' {a b c : Real} (hc : 0 < c) (h : c * a ≤ c * b) : a ≤ b := by
  refine le_of_sub_nonneg (nonneg_of_scaled_nonneg hc ?_)
  have e : c * (b - a) = c * b - c * a := by mach_mpoly [c, a, b]
  rw [e]
  have v := add_le_add_wit h (le_refl (-(c * a)))
  have el : c * a + -(c * a) = 0 := by mach_ring
  have er : c * b + -(c * a) = c * b - c * a := by mach_ring
  rw [el, er] at v; exact v

private theorem div_pos' {a b : Real} (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [div_def a b (ne_of_gt hb)]
  exact mul_pos ha (one_div_pos_of_pos hb)

private theorem abs_pos_of_ne {c : Real} (h : c ≠ 0) : 0 < abs c := by
  rcases lt_total 0 c with hc | hc | hc
  · rw [abs_of_nonneg (le_of_lt hc)]; exact hc
  · exact absurd hc.symm h
  · have hn : (0 : Real) ≤ -c := by
      have v := add_lt_add_left hc (-c)
      have l : -c + c = 0 := by mach_ring
      have r : -c + 0 = -c := by mach_ring
      rw [l, r] at v; exact le_of_lt v
    rw [← abs_neg, abs_of_nonneg hn]
    have v := add_lt_add_left hc (-c)
    have l : -c + c = 0 := by mach_ring
    have r : -c + 0 = -c := by mach_ring
    rw [l, r] at v; exact v

/-- `|b| − |a| ≤ |a + b|`, the reverse triangle inequality in the form the induction uses. -/
private theorem abs_add_ge {a b : Real} : abs b - abs a ≤ abs (a + b) := by
  have h : abs b ≤ abs (a + b) + abs a := by
    have h2 := abs_add (a + b) (-a)
    rw [abs_neg] at h2
    have e : a + b + -a = b := by mach_mpoly [a, b]
    rw [e] at h2
    exact h2
  have v := add_le_add_wit h (le_refl (-(abs a)))
  have el : abs b + -(abs a) = abs b - abs a := by mach_ring
  have er : abs (a + b) + abs a + -(abs a) = abs (a + b) := by mach_ring
  rw [el, er] at v; exact v

/-- **The polynomial dichotomy.** Every coefficient list is either eventually zero, or eventually
dominates `c·xᵏ` for some `c > 0`.

Proved by leading-term domination, by induction on the list: a nonzero constant term dominates when
the tail dies, and otherwise `|c + x·P(x)| ≥ c₀xᵏ⁺¹ − |c| ≥ (c₀/2)xᵏ⁺¹` once `x ≥ 2|c|/c₀`. No
root-counting theorem is used. -/
theorem pev_dichotomy : ∀ L : List Real, EvZeroF (pev L) ∨ EvDom (pev L) := by
  intro L
  induction L with
  | nil => exact Or.inl ⟨1, le_refl 1, fun _ _ => rfl⟩
  | cons c cs ih =>
      rcases ih with ⟨X, hX, hz⟩ | ⟨c₀, k, X, hc₀, hX, hd⟩
      · -- tail dies: the head decides
        rcases lt_total c 0 with hc | hc | hc
        · refine Or.inr ⟨abs c, 0, X, abs_pos_of_ne (ne_of_lt hc), hX, fun x hx => ?_⟩
          have e : pev (c :: cs) x = c := by
            show c + x * pev cs x = c
            rw [hz x hx]; mach_ring
          rw [e, powNat_zero]
          have e2 : abs c * 1 = abs c := by mach_ring
          rw [e2]; exact le_refl _
        · refine Or.inl ⟨X, hX, fun x hx => ?_⟩
          show c + x * pev cs x = 0
          rw [hz x hx, hc]; mach_ring
        · refine Or.inr ⟨abs c, 0, X, abs_pos_of_ne (ne_of_gt hc), hX, fun x hx => ?_⟩
          have e : pev (c :: cs) x = c := by
            show c + x * pev cs x = c
            rw [hz x hx]; mach_ring
          rw [e, powNat_zero]
          have e2 : abs c * 1 = abs c := by mach_ring
          rw [e2]; exact le_refl _
      · -- tail dominates: multiply by `x` and absorb the head
        have h2 : (0 : Real) < 1 + 1 := add_pos zero_lt_one_ax zero_lt_one_ax
        obtain ⟨X', hX', hXX', hbig⟩ :
            ∃ X' : Real, 1 ≤ X' ∧ X ≤ X' ∧ (1 + 1) * abs c ≤ c₀ * X' := by
          rcases lt_total X ((1 + 1) * abs c / c₀ + 1) with hcmp | hcmp | hcmp
          · refine ⟨(1 + 1) * abs c / c₀ + 1, ?_, le_of_lt hcmp, ?_⟩
            · have hq : (0 : Real) ≤ (1 + 1) * abs c / c₀ :=
                div_nonneg (mul_nonneg (le_of_lt h2) (abs_nonneg c)) (le_of_lt hc₀)
              have v := add_le_add_wit hq (le_refl (1 : Real))
              have e : (0 : Real) + 1 = 1 := by mach_ring
              rw [e] at v; exact v
            · have hkey : c₀ * ((1 + 1) * abs c / c₀) = (1 + 1) * abs c := by
                rw [div_def _ _ (ne_of_gt hc₀)]
                have e : c₀ * ((1 + 1) * abs c * (1 / c₀))
                    = (1 + 1) * abs c * (c₀ * (1 / c₀)) := by
                  mach_mpoly [c₀, (1 + 1) * abs c, (1 : Real) / c₀]
                rw [e, mul_inv _ (ne_of_gt hc₀)]; mach_ring
              have hle : c₀ * ((1 + 1) * abs c / c₀)
                  ≤ c₀ * ((1 + 1) * abs c / c₀ + 1) := by
                have v := add_le_add_wit (le_refl ((1 + 1) * abs c / c₀))
                  (le_of_lt zero_lt_one_ax)
                have e : (1 + 1) * abs c / c₀ + 0 = (1 + 1) * abs c / c₀ := by mach_ring
                rw [e] at v
                exact mul_le_mul_of_nonneg_left v (le_of_lt hc₀)
              rw [hkey] at hle; exact hle
          · exact ⟨X, hX, le_refl X, by
              rw [hcmp] at *
              have hq : (0 : Real) ≤ (1 + 1) * abs c / c₀ :=
                div_nonneg (mul_nonneg (le_of_lt h2) (abs_nonneg c)) (le_of_lt hc₀)
              have hkey : c₀ * ((1 + 1) * abs c / c₀) = (1 + 1) * abs c := by
                rw [div_def _ _ (ne_of_gt hc₀)]
                have e : c₀ * ((1 + 1) * abs c * (1 / c₀))
                    = (1 + 1) * abs c * (c₀ * (1 / c₀)) := by
                  mach_mpoly [c₀, (1 + 1) * abs c, (1 : Real) / c₀]
                rw [e, mul_inv _ (ne_of_gt hc₀)]; mach_ring
              have hle : c₀ * ((1 + 1) * abs c / c₀)
                  ≤ c₀ * ((1 + 1) * abs c / c₀ + 1) := by
                have v := add_le_add_wit (le_refl ((1 + 1) * abs c / c₀))
                  (le_of_lt zero_lt_one_ax)
                have e : (1 + 1) * abs c / c₀ + 0 = (1 + 1) * abs c / c₀ := by mach_ring
                rw [e] at v
                exact mul_le_mul_of_nonneg_left v (le_of_lt hc₀)
              rw [hkey] at hle; exact hle⟩
          · refine ⟨X, hX, le_refl X, ?_⟩
            have hq : (0 : Real) ≤ (1 + 1) * abs c / c₀ :=
              div_nonneg (mul_nonneg (le_of_lt h2) (abs_nonneg c)) (le_of_lt hc₀)
            have hkey : c₀ * ((1 + 1) * abs c / c₀) = (1 + 1) * abs c := by
              rw [div_def _ _ (ne_of_gt hc₀)]
              have e : c₀ * ((1 + 1) * abs c * (1 / c₀))
                  = (1 + 1) * abs c * (c₀ * (1 / c₀)) := by
                mach_mpoly [c₀, (1 + 1) * abs c, (1 : Real) / c₀]
              rw [e, mul_inv _ (ne_of_gt hc₀)]; mach_ring
            have hstep : c₀ * ((1 + 1) * abs c / c₀) ≤ c₀ * X := by
              refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hc₀)
              have v := add_le_add_wit (le_refl ((1 + 1) * abs c / c₀)) (le_of_lt zero_lt_one_ax)
              have e : (1 + 1) * abs c / c₀ + 0 = (1 + 1) * abs c / c₀ := by mach_ring
              rw [e] at v
              exact le_trans v (le_of_lt hcmp)
            rw [hkey] at hstep; exact hstep
        refine Or.inr ⟨c₀ / (1 + 1), k + 1, X', div_pos' hc₀ h2, hX', fun x hx => ?_⟩
        have hx1 : (1 : Real) ≤ x := le_trans hX' hx
        have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx1
        have hdx := hd x (le_trans hXX' hx)
        -- `|x · P(x)| ≥ c₀ x^(k+1)`
        have hxp : c₀ * powNat x (k + 1) ≤ abs (x * pev cs x) := by
          rw [abs_mul, abs_of_nonneg hx0]
          have v := mul_le_mul_of_nonneg_left hdx hx0
          have e : x * (c₀ * powNat x k) = c₀ * powNat x (k + 1) := by
            show x * (c₀ * powNat x k) = c₀ * (x * powNat x k)
            mach_mpoly [x, c₀, powNat x k]
          rw [e] at v; exact v
        -- absorb the head: `c₀ x^(k+1) − |c| ≥ (c₀/2) x^(k+1)`
        have habs : (1 + 1) * abs c ≤ c₀ * powNat x (k + 1) := by
          have hxk : x ≤ powNat x (k + 1) := by
            show x ≤ x * powNat x k
            have v := mul_le_mul_of_nonneg_left (one_le_powNat hx1 k) hx0
            have e : x * 1 = x := by mach_ring
            rw [e] at v; exact v
          exact le_trans (le_trans hbig (mul_le_mul_of_nonneg_left hx (le_of_lt hc₀)))
            (mul_le_mul_of_nonneg_left hxk (le_of_lt hc₀))
        have hhalf : c₀ / (1 + 1) * powNat x (k + 1) + abs c ≤ c₀ * powNat x (k + 1) := by
          have hkey : c₀ / (1 + 1) * powNat x (k + 1) + c₀ / (1 + 1) * powNat x (k + 1)
              = c₀ * powNat x (k + 1) := by
            have e : c₀ / (1 + 1) * powNat x (k + 1) + c₀ / (1 + 1) * powNat x (k + 1)
                = (c₀ / (1 + 1) * (1 + 1)) * powNat x (k + 1) := by
              mach_mpoly [c₀ / (1 + 1), powNat x (k + 1)]
            rw [e, div_mul_self' (ne_of_gt h2)]
          rw [← hkey]
          refine add_le_add_wit (le_refl _) ?_
          have hd2 : (1 + 1) * abs c ≤ (1 + 1) * (c₀ / (1 + 1) * powNat x (k + 1)) := by
            have e : (1 + 1) * (c₀ / (1 + 1) * powNat x (k + 1))
                = (c₀ / (1 + 1) * (1 + 1)) * powNat x (k + 1) := by
              mach_mpoly [c₀ / (1 + 1), powNat x (k + 1)]
            rw [e, div_mul_self' (ne_of_gt h2)]; exact habs
          exact le_of_mul_le_mul_left' h2 hd2
        show c₀ / (1 + 1) * powNat x (k + 1) ≤ abs (c + x * pev cs x)
        refine le_trans ?_ abs_add_ge
        have v : c₀ / (1 + 1) * powNat x (k + 1) ≤ abs (x * pev cs x) - abs c := by
          have w := add_le_add_wit hhalf (le_refl (-(abs c)))
          have el : c₀ / (1 + 1) * powNat x (k + 1) + abs c + -(abs c)
              = c₀ / (1 + 1) * powNat x (k + 1) := by mach_ring
          rw [el] at w
          have hsub : c₀ * powNat x (k + 1) + -(abs c) ≤ abs (x * pev cs x) - abs c := by
            have u := add_le_add_wit hxp (le_refl (-(abs c)))
            have e2 : abs (x * pev cs x) + -(abs c) = abs (x * pev cs x) - abs c := by mach_ring
            rw [e2] at u; exact u
          exact le_trans w hsub
        exact v

/-- Every coefficient list is polynomially bounded — the easy half, recorded because the germ
argument needs both directions. -/
theorem pev_envelope : ∀ L : List Real, PolyEnvelope (pev L) := by
  intro L
  induction L with
  | nil =>
      refine ⟨0, 0, 1, le_refl 0, le_refl 1, fun x _ => ?_⟩
      show abs (0 : Real) ≤ 0 * powNat x 0
      rw [abs_of_nonneg (le_refl (0 : Real)), powNat_zero]
      have e : (0 : Real) * 1 = 0 := by mach_ring
      rw [e]; exact le_refl _
  | cons c cs ih =>
      obtain ⟨C, N, X, hC, hX, hb⟩ := ih
      refine ⟨abs c + C, N + 1, X, add_nonneg (abs_nonneg c) hC, hX, fun x hx => ?_⟩
      have hx1 : (1 : Real) ≤ x := le_trans hX hx
      have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx1
      have hstep : abs (x * pev cs x) ≤ C * powNat x (N + 1) := by
        rw [abs_mul, abs_of_nonneg hx0]
        have v := mul_le_mul_of_nonneg_left (hb x hx) hx0
        have e : x * (C * powNat x N) = C * powNat x (N + 1) := by
          show x * (C * powNat x N) = C * (x * powNat x N)
          mach_mpoly [x, C, powNat x N]
        rw [e] at v; exact v
      show abs (c + x * pev cs x) ≤ (abs c + C) * powNat x (N + 1)
      have htri := abs_add c (x * pev cs x)
      have hone : abs c ≤ abs c * powNat x (N + 1) := by
        have v := mul_le_mul_of_nonneg_left (one_le_powNat hx1 (N + 1)) (abs_nonneg c)
        have e : abs c * 1 = abs c := by mach_ring
        rw [e] at v; exact v
      have hsum := add_le_add_wit hone hstep
      have e : abs c * powNat x (N + 1) + C * powNat x (N + 1)
          = (abs c + C) * powNat x (N + 1) := by
        mach_mpoly [abs c, C, powNat x (N + 1)]
      rw [← e]
      exact le_trans htri hsum

/-! ## The first strict query separation, `C₀ ⊊ C₁` -/

/-- Anything that eventually dominates `exp` has no polynomial envelope. Generalises
`polyEnvelope_ne_exp`, whose target was only `exp` itself. -/
theorem not_polyEnvelope_of_ge_exp {f : Real → Real}
    (h : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → exp x ≤ f x) : ¬ PolyEnvelope f := by
  rintro ⟨C, N, X₀, hC, hX₀, hb⟩
  obtain ⟨X, hX, hge⟩ := h
  obtain ⟨x, hxX, hx1, hlt⟩ := exp_beats_powNat N C (X₀ + X + C + 1)
  have hXpos : (0 : Real) ≤ X₀ := le_trans (le_of_lt zero_lt_one_ax) hX₀
  have hXpos' : (0 : Real) ≤ X := le_trans (le_of_lt zero_lt_one_ax) hX
  have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx1
  have hle0 : X₀ ≤ x := by
    have e : X₀ + X + C + 1 = X₀ + (X + C + 1) := by mach_ring
    have h1 : X₀ ≤ X₀ + X + C + 1 := by
      rw [e]; exact le_add_nonneg' (add_nonneg (add_nonneg hXpos' hC) (le_of_lt zero_lt_one_ax))
    exact le_trans h1 hxX
  have hleX : X ≤ x := by
    have e : X₀ + X + C + 1 = X + (X₀ + C + 1) := by mach_ring
    have h1 : X ≤ X₀ + X + C + 1 := by
      rw [e]; exact le_add_nonneg' (add_nonneg (add_nonneg hXpos hC) (le_of_lt zero_lt_one_ax))
    exact le_trans h1 hxX
  have hCx : C ≤ x := by
    have e : X₀ + X + C + 1 = C + (X₀ + X + 1) := by mach_ring
    have h1 : C ≤ X₀ + X + C + 1 := by
      rw [e]; exact le_add_nonneg' (add_nonneg (add_nonneg hXpos hXpos') (le_of_lt zero_lt_one_ax))
    exact le_trans h1 hxX
  have hpn : (0 : Real) ≤ powNat x N := le_of_lt (powNat_pos (lt_of_lt_of_le zero_lt_one_ax hx1) N)
  have hstep : C * powNat x N ≤ powNat x (N + 2) := by
    have hCxx : C ≤ x * x := by
      have h3 : x ≤ x * x := by
        have v := mul_le_mul_of_nonneg_left hx1 hx0
        have e : x * 1 = x := by mach_ring
        rw [e] at v; exact v
      exact le_trans hCx h3
    have v := mul_le_mul_of_nonneg_right hCxx hpn
    have e : x * x * powNat x N = powNat x (N + 2) := by
      rw [powNat_add]
      show x * x * powNat x N = powNat x N * (x * (x * 1))
      mach_mpoly [x, powNat x N]
    rw [e] at v; exact v
  have hle : powNat x (N + 2) ≤ powNat x (N + 2) + x + C := by
    have e : powNat x (N + 2) + x + C = powNat x (N + 2) + (x + C) := by mach_ring
    rw [e]; exact le_add_nonneg' (add_nonneg hx0 hC)
  have hfx : exp x ≤ f x := hge x hleX
  have hchain : abs (f x) < exp x :=
    lt_of_le_of_lt (le_trans (hb x hle0) (le_trans hstep hle)) hlt
  exact absurd (lt_of_le_of_lt (le_trans hfx (le_abs_self _)) hchain) (lt_irrefl_ax _)

/-- `F(x) = exp x + log x ≥ exp x` for `x ≥ 1`, because `log` is non-negative there. -/
theorem exp_le_Fbasis {x : Real} (hx : 1 ≤ x) : exp x ≤ Fbasis x := by
  have hl1 : log (1 : Real) = 0 := by
    have hz : exp (0 : Real) = 1 := exp_zero
    rw [← hz, log_exp]
  have hlog : (0 : Real) ≤ log x := by
    have hm := log_le_log zero_lt_one_ax hx
    rw [hl1] at hm; exact hm
  show exp x ≤ exp x + log x
  exact le_add_nonneg' hlog

/-- **`F` has no polynomial envelope**, so it is not computed by any zero-query term. -/
theorem not_polyEnvelope_Fbasis : ¬ PolyEnvelope Fbasis :=
  not_polyEnvelope_of_ge_exp ⟨1, le_refl 1, fun _ hx => exp_le_Fbasis hx⟩

/-- **`C₀ ⊊ C₁`, on the division-free fragment.** The generator is its own separating witness: it
costs exactly one query by definition, and no zero-query division-free term computes it.

Cleaner than separating with `exp`, which currently costs *two* queries — here the upper bound is
definitional. -/
theorem zero_query_lt_one_query :
    (∀ T : FTerm, divFree T → (∀ x : Real, FTerm.eval T x = Fbasis x) → 1 ≤ fOcc T)
    ∧ fOcc (FTerm.F FTerm.var) = 1
    ∧ (∀ x : Real, FTerm.eval (FTerm.F FTerm.var) x = Fbasis x) := by
  refine ⟨fun T hd h => ?_, rfl, fun _ => rfl⟩
  rcases Nat.eq_zero_or_pos (fOcc T) with h0 | hp
  · exfalso
    obtain ⟨C, N, X, hC, hX, hb⟩ := polyEnvelope_of_zero_query T h0 hd
    exact not_polyEnvelope_Fbasis ⟨C, N, X, hC, hX, fun x hx => by rw [← h x]; exact hb x hx⟩
  · exact hp

/-! ## What remains for the `C₀` normal form

`pev_dichotomy` is the keystone; the compilation of an `F`-free term to an eventual germ `P/Q` is
not built. What it needs, in order:

* coefficient-list `padd`/`pmul` with their `pev` homomorphism lemmas (the corpus has `listAddR` /
  `listMulR` and `polyCoeffs_eval`, but in a different namespace and phrased for the `Poly`
  expression tree — worth reusing rather than duplicating);
* the fraction identities `P₁/Q₁ ± P₂/Q₂ = (P₁Q₂ ± P₂Q₁)/(Q₁Q₂)` and `(P₁/Q₁)/(P₂/Q₂) = P₁Q₂/(Q₁P₂)`,
  each valid where the denominators are nonzero — which `pev_dichotomy` supplies eventually;
* the division envelope `|P/Q| ≤ (C/c)·x^N`, needing `abs_div` and a monotonicity lemma for
  reciprocals. **Neither exists in the corpus** — that is the concrete missing infrastructure.

The `÷` case then splits on `pev_dichotomy` applied to the *numerator* of the divisor: eventually
zero makes the quotient eventually `0` by the `div_zero` axiom, and eventually nonzero puts ordinary
fraction algebra back in force. Note that this argument **depends on division being totalised**:
`div_zero : a / 0 = 0` is an axiom of `MachLib.Real`. Without it `x ↦ a x / 0` would be an
unconstrained function and `FQueryLowerBound` would not merely be unproved, it would be independent.
-/

end MachLib
