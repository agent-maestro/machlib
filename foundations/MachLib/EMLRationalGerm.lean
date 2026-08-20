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

/-! ## Field infrastructure the corpus did not have

`abs_div` and reciprocal monotonicity were named as the missing pieces. Here they are, together with
the four fraction identities the germ compilation consumes. Everything is derived from `div_def`,
`mul_inv` and `div_zero`; nothing new is assumed. -/

theorem abs_one_div {b : Real} (hb : b ≠ 0) : abs (1 / b) = 1 / abs b := by
  have hab : abs b ≠ 0 := ne_of_gt (abs_pos_of_ne hb)
  refine (div_of_eq_mul hab ?_).symm
  have h : abs b * abs (1 / b) = abs (b * (1 / b)) := (abs_mul b (1 / b)).symm
  rw [mul_inv b hb, abs_of_nonneg (le_of_lt zero_lt_one_ax)] at h
  exact h.symm

theorem abs_div_eq {a b : Real} (hb : b ≠ 0) : abs (a / b) = abs a / abs b := by
  have hab : abs b ≠ 0 := ne_of_gt (abs_pos_of_ne hb)
  rw [div_def a b hb, abs_mul, abs_one_div hb, div_def (abs a) (abs b) hab]

theorem one_div_le_one_div_of_le {a b : Real} (ha : 0 < a) (hab : a ≤ b) : 1 / b ≤ 1 / a := by
  have hb : (0 : Real) < b := lt_of_lt_of_le ha hab
  refine le_of_mul_le_mul_left' (mul_pos ha hb) ?_
  have e1 : a * b * (1 / b) = a := by
    have e : a * b * (1 / b) = a * (b * (1 / b)) := by mach_mpoly [a, b, (1 : Real) / b]
    rw [e, mul_inv b (ne_of_gt hb)]; mach_ring
  have e2 : a * b * (1 / a) = b := by
    have e : a * b * (1 / a) = b * (a * (1 / a)) := by mach_mpoly [a, b, (1 : Real) / a]
    rw [e, mul_inv a (ne_of_gt ha)]; mach_ring
  rw [e1, e2]; exact hab

theorem div_one_eq (a : Real) : a / 1 = a := by
  rw [div_def a 1 (ne_of_gt zero_lt_one_ax)]
  have e : (1 : Real) * (1 / 1) = 1 / 1 := by mach_ring
  have h := mul_inv (1 : Real) (ne_of_gt zero_lt_one_ax)
  rw [e] at h
  rw [h]; mach_ring

theorem zero_div_eq {q : Real} (hq : q ≠ 0) : (0 : Real) / q = 0 := by
  rw [div_def 0 q hq]; mach_ring

theorem div_add_div_eq (p q r s : Real) (hq : q ≠ 0) (hs : s ≠ 0) :
    p / q + r / s = (p * s + r * q) / (q * s) := by
  refine (div_of_eq_mul (mul_ne_zero hq hs) ?_).symm
  rw [div_def p q hq, div_def r s hs]
  have e : q * s * (p * (1 / q) + r * (1 / s))
      = s * p * (q * (1 / q)) + q * r * (s * (1 / s)) := by
    mach_mpoly [p, q, r, s, (1 : Real) / q, (1 : Real) / s]
  rw [e, mul_inv q hq, mul_inv s hs]; mach_ring

theorem div_mul_div_eq (p q r s : Real) (hq : q ≠ 0) (hs : s ≠ 0) :
    p / q * (r / s) = p * r / (q * s) := by
  refine (div_of_eq_mul (mul_ne_zero hq hs) ?_).symm
  rw [div_def p q hq, div_def r s hs]
  have e : q * s * (p * (1 / q) * (r * (1 / s)))
      = p * r * (q * (1 / q)) * (s * (1 / s)) := by
    mach_mpoly [p, q, r, s, (1 : Real) / q, (1 : Real) / s]
  rw [e, mul_inv q hq, mul_inv s hs]; mach_ring

theorem eq_of_mul_eq_mul_right' {a b c : Real} (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  have ea : a * c * (1 / c) = a := by
    have e : a * c * (1 / c) = a * (c * (1 / c)) := by mach_mpoly [a, c, (1 : Real) / c]
    rw [e, mul_inv c hc]; mach_ring
  have eb : b * c * (1 / c) = b := by
    have e : b * c * (1 / c) = b * (c * (1 / c)) := by mach_mpoly [b, c, (1 : Real) / c]
    rw [e, mul_inv c hc]; mach_ring
  rw [← ea, ← eb, h]

theorem div_eq_div_of_cross {a b c d : Real} (hb : b ≠ 0) (hd : d ≠ 0) (h : a * d = c * b) :
    a / b = c / d := by
  rw [div_def a b hb, div_def c d hd]
  refine eq_of_mul_eq_mul_right' (mul_ne_zero hb hd) ?_
  have e1 : a * (1 / b) * (b * d) = a * d * (b * (1 / b)) := by
    mach_mpoly [a, b, d, (1 : Real) / b]
  have e2 : c * (1 / d) * (b * d) = c * b * (d * (1 / d)) := by
    mach_mpoly [b, c, d, (1 : Real) / d]
  rw [e1, e2, mul_inv b hb, mul_inv d hd, h]

theorem div_div_div_eq (p q r s : Real) (hq : q ≠ 0) (hs : s ≠ 0) (hr : r ≠ 0) :
    p / q / (r / s) = p * s / (q * r) := by
  have hrs : r / s ≠ 0 := by
    intro h
    have e : r / s * s = r := div_mul_self' hs
    rw [h] at e
    have e0 : (0 : Real) * s = 0 := by mach_ring
    rw [e0] at e
    exact absurd e.symm hr
  refine div_of_eq_mul hrs ?_
  rw [div_mul_div_eq r s (p * s) (q * r) hs (mul_ne_zero hq hr)]
  refine div_eq_div_of_cross hq (mul_ne_zero hs (mul_ne_zero hq hr)) ?_
  mach_mpoly [p, q, r, s]

theorem div_sub_div_eq (p q r s : Real) (hq : q ≠ 0) (hs : s ≠ 0) :
    p / q - r / s = (p * s - r * q) / (q * s) := by
  refine (div_of_eq_mul (mul_ne_zero hq hs) ?_).symm
  rw [div_def p q hq, div_def r s hs]
  have e : q * s * (p * (1 / q) - r * (1 / s))
      = s * p * (q * (1 / q)) - q * r * (s * (1 / s)) := by
    mach_mpoly [p, q, r, s, (1 : Real) / q, (1 : Real) / s]
  rw [e, mul_inv q hq, mul_inv s hs]; mach_ring

/-! ## Coefficient-list arithmetic -/

noncomputable def padd : List Real → List Real → List Real
  | [], M => M
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: padd as bs

noncomputable def pscale (r : Real) : List Real → List Real
  | [] => []
  | a :: as => (r * a) :: pscale r as

noncomputable def pmul : List Real → List Real → List Real
  | [], _ => []
  | a :: as, M => padd (pscale a M) (0 :: pmul as M)

noncomputable def psub (L M : List Real) : List Real := padd L (pscale (0 - 1) M)

theorem pev_padd : ∀ (L M : List Real) (x : Real), pev (padd L M) x = pev L x + pev M x := by
  intro L
  induction L with
  | nil => intro M x; show pev M x = 0 + pev M x; mach_ring
  | cons a as ih =>
      intro M x
      cases M with
      | nil => show pev (a :: as) x = pev (a :: as) x + 0; mach_ring
      | cons b bs =>
          show a + b + x * pev (padd as bs) x = a + x * pev as x + (b + x * pev bs x)
          rw [ih bs x]; mach_ring

theorem pev_pscale : ∀ (r : Real) (L : List Real) (x : Real),
    pev (pscale r L) x = r * pev L x := by
  intro r L
  induction L with
  | nil => intro x; show (0 : Real) = r * 0; mach_ring
  | cons a as ih =>
      intro x
      show r * a + x * pev (pscale r as) x = r * (a + x * pev as x)
      rw [ih x]; mach_ring

theorem pev_pmul : ∀ (L M : List Real) (x : Real), pev (pmul L M) x = pev L x * pev M x := by
  intro L
  induction L with
  | nil => intro M x; show (0 : Real) = 0 * pev M x; mach_ring
  | cons a as ih =>
      intro M x
      show pev (padd (pscale a M) (0 :: pmul as M)) x = (a + x * pev as x) * pev M x
      rw [pev_padd, pev_pscale]
      show a * pev M x + (0 + x * pev (pmul as M) x) = (a + x * pev as x) * pev M x
      rw [ih M x]; mach_ring

theorem pev_psub (L M : List Real) (x : Real) : pev (psub L M) x = pev L x - pev M x := by
  rw [psub, pev_padd, pev_pscale]; mach_ring

/-! ## The eventual rational germ -/

/-- `f` agrees with a quotient of two polynomials from some point on, the denominator nonvanishing
there. The *eventual* form is the point: with totalised division a global `P/Q` identity would be
false at the denominator's zeros, and at `+∞` those are all behind us. -/
def RatGerm (f : Real → Real) : Prop :=
  ∃ (P Q : List Real) (X : Real), 1 ≤ X ∧ (∀ x : Real, X ≤ x → pev Q x ≠ 0)
    ∧ ∀ x : Real, X ≤ x → f x = pev P x / pev Q x

private theorem two_bounds' {X₁ X₂ : Real} (h₁ : 1 ≤ X₁) (h₂ : 1 ≤ X₂) :
    ∃ X : Real, 1 ≤ X ∧ X₁ ≤ X ∧ X₂ ≤ X := by
  rcases lt_total X₁ X₂ with h | h | h
  · exact ⟨X₂, h₂, le_of_lt h, le_refl X₂⟩
  · exact ⟨X₂, h₂, le_of_eq h, le_refl X₂⟩
  · exact ⟨X₁, h₁, le_refl X₁, le_of_lt h⟩

private theorem ne_zero_of_abs_pos {y : Real} (h : 0 < abs y) : y ≠ 0 := by
  intro hy
  rw [hy, abs_of_nonneg (le_refl (0 : Real))] at h
  exact absurd h (lt_irrefl_ax 0)

private theorem pev_one_ne (x : Real) : pev [(1 : Real)] x ≠ 0 := by
  show (1 : Real) + x * 0 ≠ 0
  have e : (1 : Real) + x * 0 = 1 := by mach_ring
  rw [e]; exact ne_of_gt zero_lt_one_ax

/-- **`C₀` is the class of eventual rational germs.** Every `F`-free `L_F` term — division
included — agrees from some point on with a quotient of polynomials whose denominator does not
vanish there.

The `÷` case is where the dichotomy earns its place: applied to the divisor's *numerator* it splits
into "eventually zero", where `div_zero` makes the whole quotient eventually `0`, and "eventually
nonzero", where ordinary fraction algebra is back in force. Cancellation under `+` is no longer
predicted from leading-order data — it happens inside `padd`/`pmul`. -/
theorem ratGerm_of_zero_query : ∀ T : FTerm, fOcc T = 0 → RatGerm (FTerm.eval T) := by
  intro T
  induction T with
  | const c =>
      intro _
      refine ⟨[c], [1], 1, le_refl 1, fun x _ => pev_one_ne x, fun x _ => ?_⟩
      show c = pev [c] x / pev [(1 : Real)] x
      have e1 : pev [c] x = c := by show c + x * 0 = c; mach_ring
      have e2 : pev [(1 : Real)] x = 1 := by show (1 : Real) + x * 0 = 1; mach_ring
      rw [e1, e2, div_one_eq]
  | var =>
      intro _
      refine ⟨[0, 1], [1], 1, le_refl 1, fun x _ => pev_one_ne x, fun x _ => ?_⟩
      show x = pev [(0 : Real), 1] x / pev [(1 : Real)] x
      have e1 : pev [(0 : Real), 1] x = x := by
        show (0 : Real) + x * (1 + x * 0) = x; mach_ring
      have e2 : pev [(1 : Real)] x = 1 := by show (1 : Real) + x * 0 = 1; mach_ring
      rw [e1, e2, div_one_eq]
  | add a b iha ihb =>
      intro h
      have ha : fOcc a = 0 := by simp only [fOcc] at h; omega
      have hb : fOcc b = 0 := by simp only [fOcc] at h; omega
      obtain ⟨P₁, Q₁, X₁, hX₁, hQ₁, he₁⟩ := iha ha
      obtain ⟨P₂, Q₂, X₂, hX₂, hQ₂, he₂⟩ := ihb hb
      obtain ⟨X, hX, hXa, hXb⟩ := two_bounds' hX₁ hX₂
      refine ⟨padd (pmul P₁ Q₂) (pmul P₂ Q₁), pmul Q₁ Q₂, X, hX, fun x hx => ?_, fun x hx => ?_⟩
      · rw [pev_pmul]
        exact mul_ne_zero (hQ₁ x (le_trans hXa hx)) (hQ₂ x (le_trans hXb hx))
      · show FTerm.eval a x + FTerm.eval b x
            = pev (padd (pmul P₁ Q₂) (pmul P₂ Q₁)) x / pev (pmul Q₁ Q₂) x
        rw [he₁ x (le_trans hXa hx), he₂ x (le_trans hXb hx), pev_padd, pev_pmul, pev_pmul,
            pev_pmul]
        exact div_add_div_eq _ _ _ _ (hQ₁ x (le_trans hXa hx)) (hQ₂ x (le_trans hXb hx))
  | sub a b iha ihb =>
      intro h
      have ha : fOcc a = 0 := by simp only [fOcc] at h; omega
      have hb : fOcc b = 0 := by simp only [fOcc] at h; omega
      obtain ⟨P₁, Q₁, X₁, hX₁, hQ₁, he₁⟩ := iha ha
      obtain ⟨P₂, Q₂, X₂, hX₂, hQ₂, he₂⟩ := ihb hb
      obtain ⟨X, hX, hXa, hXb⟩ := two_bounds' hX₁ hX₂
      refine ⟨psub (pmul P₁ Q₂) (pmul P₂ Q₁), pmul Q₁ Q₂, X, hX, fun x hx => ?_, fun x hx => ?_⟩
      · rw [pev_pmul]
        exact mul_ne_zero (hQ₁ x (le_trans hXa hx)) (hQ₂ x (le_trans hXb hx))
      · show FTerm.eval a x - FTerm.eval b x
            = pev (psub (pmul P₁ Q₂) (pmul P₂ Q₁)) x / pev (pmul Q₁ Q₂) x
        rw [he₁ x (le_trans hXa hx), he₂ x (le_trans hXb hx), pev_psub, pev_pmul, pev_pmul,
            pev_pmul]
        exact div_sub_div_eq _ _ _ _ (hQ₁ x (le_trans hXa hx)) (hQ₂ x (le_trans hXb hx))
  | mul a b iha ihb =>
      intro h
      have ha : fOcc a = 0 := by simp only [fOcc] at h; omega
      have hb : fOcc b = 0 := by simp only [fOcc] at h; omega
      obtain ⟨P₁, Q₁, X₁, hX₁, hQ₁, he₁⟩ := iha ha
      obtain ⟨P₂, Q₂, X₂, hX₂, hQ₂, he₂⟩ := ihb hb
      obtain ⟨X, hX, hXa, hXb⟩ := two_bounds' hX₁ hX₂
      refine ⟨pmul P₁ P₂, pmul Q₁ Q₂, X, hX, fun x hx => ?_, fun x hx => ?_⟩
      · rw [pev_pmul]
        exact mul_ne_zero (hQ₁ x (le_trans hXa hx)) (hQ₂ x (le_trans hXb hx))
      · show FTerm.eval a x * FTerm.eval b x = pev (pmul P₁ P₂) x / pev (pmul Q₁ Q₂) x
        rw [he₁ x (le_trans hXa hx), he₂ x (le_trans hXb hx), pev_pmul, pev_pmul]
        exact div_mul_div_eq _ _ _ _ (hQ₁ x (le_trans hXa hx)) (hQ₂ x (le_trans hXb hx))
  | div a b iha ihb =>
      intro h
      have ha : fOcc a = 0 := by simp only [fOcc] at h; omega
      have hb : fOcc b = 0 := by simp only [fOcc] at h; omega
      obtain ⟨P₁, Q₁, X₁, hX₁, hQ₁, he₁⟩ := iha ha
      obtain ⟨P₂, Q₂, X₂, hX₂, hQ₂, he₂⟩ := ihb hb
      obtain ⟨Y, hY, hYa, hYb⟩ := two_bounds' hX₁ hX₂
      rcases pev_dichotomy P₂ with ⟨Z, hZ, hzero⟩ | ⟨c, k, Z, hc, hZ, hdom⟩
      · -- the divisor is eventually `0`; totalised division makes the quotient eventually `0`
        obtain ⟨X, hX, hXY, hXZ⟩ := two_bounds' hY hZ
        refine ⟨[], [1], X, hX, fun x _ => pev_one_ne x, fun x hx => ?_⟩
        have hbz : FTerm.eval b x = 0 := by
          rw [he₂ x (le_trans (le_trans hYb hXY) hx), hzero x (le_trans hXZ hx)]
          exact zero_div_eq (hQ₂ x (le_trans (le_trans hYb hXY) hx))
        show FTerm.eval a x / FTerm.eval b x = pev [] x / pev [(1 : Real)] x
        rw [hbz, div_zero]
        have e1 : pev ([] : List Real) x = 0 := rfl
        have e2 : pev [(1 : Real)] x = 1 := by show (1 : Real) + x * 0 = 1; mach_ring
        rw [e1, e2, div_one_eq]
      · -- the divisor's numerator is eventually nonzero; ordinary fraction algebra applies
        obtain ⟨X, hX, hXY, hXZ⟩ := two_bounds' hY hZ
        have hP₂ : ∀ x : Real, X ≤ x → pev P₂ x ≠ 0 := by
          intro x hx
          refine ne_zero_of_abs_pos (lt_of_lt_of_le ?_ (hdom x (le_trans hXZ hx)))
          exact mul_pos hc (powNat_pos (lt_of_lt_of_le zero_lt_one_ax (le_trans hX hx)) k)
        refine ⟨pmul P₁ Q₂, pmul Q₁ P₂, X, hX, fun x hx => ?_, fun x hx => ?_⟩
        · rw [pev_pmul]
          exact mul_ne_zero (hQ₁ x (le_trans (le_trans hYa hXY) hx)) (hP₂ x hx)
        · show FTerm.eval a x / FTerm.eval b x = pev (pmul P₁ Q₂) x / pev (pmul Q₁ P₂) x
          rw [he₁ x (le_trans (le_trans hYa hXY) hx), he₂ x (le_trans (le_trans hYb hXY) hx),
              pev_pmul, pev_pmul]
          exact div_div_div_eq _ _ _ _ (hQ₁ x (le_trans (le_trans hYa hXY) hx))
            (hQ₂ x (le_trans (le_trans hYb hXY) hx)) (hP₂ x hx)
  | F a iha => intro h; simp only [fOcc] at h; omega

/-! ## The chain closes: `FQueryLowerBound`, with no division-free hypothesis -/

/-- A rational germ is polynomially bounded. The denominator's lower bound comes from
`pev_dichotomy`: it cannot be eventually zero, since it is eventually *nonzero*, so it must
eventually dominate `c·xᵏ` — and `xᵏ ≥ 1` collapses that to the constant `c`. -/
theorem polyEnvelope_of_ratGerm {f : Real → Real} (h : RatGerm f) : PolyEnvelope f := by
  obtain ⟨P, Q, X, hX, hQ, he⟩ := h
  obtain ⟨C, N, XP, hC, hXP, hbP⟩ := pev_envelope P
  rcases pev_dichotomy Q with ⟨Z, hZ, hzero⟩ | ⟨c, k, Z, hc, hZ, hdom⟩
  · exfalso
    obtain ⟨W, _, hWX, hWZ⟩ := two_bounds' hX hZ
    exact hQ W hWX (hzero W hWZ)
  · obtain ⟨W1, hW1, hW1X, hW1Z⟩ := two_bounds' hX hZ
    obtain ⟨W, hW, hWW1, hWXP⟩ := two_bounds' hW1 hXP
    refine ⟨C * (1 / c), N, W, mul_nonneg hC (le_of_lt (one_div_pos_of_pos hc)), hW,
      fun x hx => ?_⟩
    have hx1 : (1 : Real) ≤ x := le_trans hW hx
    have hQx : pev Q x ≠ 0 := hQ x (le_trans (le_trans hW1X hWW1) hx)
    have hdx := hdom x (le_trans (le_trans hW1Z hWW1) hx)
    have hcxk : (0 : Real) < c * powNat x k :=
      mul_pos hc (powNat_pos (lt_of_lt_of_le zero_lt_one_ax hx1) k)
    have hck : c ≤ c * powNat x k := by
      have v := mul_le_mul_of_nonneg_left (one_le_powNat hx1 k) (le_of_lt hc)
      have e : c * 1 = c := by mach_ring
      rw [e] at v; exact v
    have hinv : 1 / abs (pev Q x) ≤ 1 / c :=
      le_trans (one_div_le_one_div_of_le hcxk hdx) (one_div_le_one_div_of_le hc hck)
    rw [he x (le_trans (le_trans hW1X hWW1) hx), abs_div_eq hQx,
        div_def _ _ (ne_of_gt (abs_pos_of_ne hQx))]
    have s1 : abs (pev P x) * (1 / abs (pev Q x)) ≤ abs (pev P x) * (1 / c) :=
      mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
    have s2 : abs (pev P x) * (1 / c) ≤ C * powNat x N * (1 / c) :=
      mul_le_mul_of_nonneg_right (hbP x (le_trans hWXP hx)) (le_of_lt (one_div_pos_of_pos hc))
    have e : C * powNat x N * (1 / c) = C * (1 / c) * powNat x N := by
      mach_mpoly [C, powNat x N, (1 : Real) / c]
    rw [← e]
    exact le_trans s1 s2

/-- **`FQueryLowerBound`, discharged.** Computing `exp` costs at least one `F`-query — no
division-free hypothesis, no restriction of any kind on the term.

This is where `div_zero : a / 0 = 0` is load-bearing. Without that axiom `x ↦ a x / 0` would be an
unconstrained function of `x`, a model could set `divR y 0 = exp y`, and `div var (sub var var)`
would be a zero-query term computing `exp`. The statement would then be independent, not merely
unproved. -/
theorem fQueryLowerBound_holds : FQueryLowerBound := by
  intro T h
  rcases Nat.eq_zero_or_pos (fOcc T) with h0 | hp
  · exact absurd h (polyEnvelope_ne_exp (polyEnvelope_of_ratGerm (ratGerm_of_zero_query T h0)))
  · exact hp

/-- **`C₀ ⊊ C₁`, in the full language.** The division-free hypothesis of
`zero_query_lt_one_query` is gone. -/
theorem zero_query_lt_one_query_full :
    (∀ T : FTerm, (∀ x : Real, FTerm.eval T x = Fbasis x) → 1 ≤ fOcc T)
    ∧ fOcc (FTerm.F FTerm.var) = 1
    ∧ (∀ x : Real, FTerm.eval (FTerm.F FTerm.var) x = Fbasis x) := by
  refine ⟨fun T h => ?_, rfl, fun _ => rfl⟩
  rcases Nat.eq_zero_or_pos (fOcc T) with h0 | hp
  · exfalso
    obtain ⟨C, N, X, hC, hX, hb⟩ := polyEnvelope_of_ratGerm (ratGerm_of_zero_query T h0)
    exact not_polyEnvelope_Fbasis ⟨C, N, X, hC, hX, fun x hx => by rw [← h x]; exact hb x hx⟩
  · exact hp

/-- **Discrimination: the germ theorem covers terms the previous one could not.** A tower of nested
divisions, including one whose denominator vanishes identically — the totalised branch — is still a
rational germ, and still not `exp`. -/
noncomputable def divTower : FTerm :=
  FTerm.div (FTerm.div FTerm.var (FTerm.sub FTerm.var FTerm.var))
    (FTerm.add (FTerm.mul FTerm.var FTerm.var) (FTerm.const 1))

theorem divTower_ratGerm : RatGerm (FTerm.eval divTower) :=
  ratGerm_of_zero_query divTower rfl

theorem divTower_ne_exp : ¬ (∀ x : Real, FTerm.eval divTower x = exp x) :=
  polyEnvelope_ne_exp (polyEnvelope_of_ratGerm divTower_ratGerm)

end MachLib
