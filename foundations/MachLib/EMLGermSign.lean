import MachLib.EMLOneQueryForm

/-!
# `C₀` is eventually sign-definite — unconditionally

`SignHardCase` asks whether every EML expression is eventually of constant sign. It is open, and it
is the cancellation statement the EML depth programme keeps running into.

**The same question for `C₀` is closed here.** Every zero-query `L_F` term is eventually strictly
positive, eventually strictly negative, or eventually zero — no hypothesis, no ray supplied from
outside. The reason is structural rather than clever: `C₀` has a *normal form*, so the sign of a
quotient is read off from the signs of a numerator and a denominator, and each of those is settled by
a signed refinement of the polynomial dichotomy.

That contrast is the useful content. Sign-definiteness is not hard *in general* — it is hard when the
representation offers no normal form to read it from. Which is a reason to expect `OneQueryDichotomy`
to hinge on whether `C₁` admits one, not on transcendence.

## The regime split this sets up

With the trichotomy in hand, a rational germ `S` feeding a single `F` falls into cases the totalised
logarithm treats very differently:

* `S` eventually **negative** — `log₀ S = 0`, so `F(S) = exp S`, and `0 < F(S) < 1`. The logarithm
  is gone entirely and `F(S)` is *bounded*.
* `S` eventually **zero** — `F(S) = F(0) = 1`, a constant.
* `S` eventually **positive** — `F(S) = exp S + log S`, and the sign genuinely depends on the scale:
  `F(S) < 0` for small `S`, `> 0` for large. This is the branch that still needs work.

Two of the three collapse. Only the positive branch carries the level-1 cancellation problem.
-/

namespace MachLib

open Real

/-! ## A signed dichotomy -/

/-- Eventually bounded below by `c·xᵏ`, `c > 0`. -/
def EvPos (f : Real → Real) : Prop :=
  ∃ (c : Real) (k : Nat) (X : Real), 0 < c ∧ 1 ≤ X ∧ ∀ x : Real, X ≤ x → c * powNat x k ≤ f x

/-- Eventually bounded above by `−c·xᵏ`, `c > 0`. -/
def EvNeg (f : Real → Real) : Prop :=
  ∃ (c : Real) (k : Nat) (X : Real), 0 < c ∧ 1 ≤ X ∧ ∀ x : Real, X ≤ x → f x ≤ -(c * powNat x k)

private theorem neg_pos' {a : Real} (h : a < 0) : 0 < -a := by
  have v := add_lt_add_left h (-a)
  have l : -a + a = 0 := by mach_ring
  have r : -a + 0 = -a := by mach_ring
  rw [l, r] at v; exact v

private theorem neg_of_neg_pos' {a : Real} (h : 0 < -a) : a < 0 := by
  have v := add_lt_add_left h a
  have l : a + 0 = a := by mach_ring
  have r : a + -a = 0 := by mach_ring
  rw [l, r] at v; exact v

/-- **The signed polynomial dichotomy.** Eventually zero, eventually dominating `+c·xᵏ`, or
eventually dominating `−c·xᵏ`. Same leading-term induction as `pev_dichotomy`, tracking the sign. -/
theorem pev_signed_dichotomy :
    ∀ L : List Real, EvZeroF (pev L) ∨ EvPos (pev L) ∨ EvNeg (pev L) := by
  intro L
  induction L with
  | nil => exact Or.inl ⟨1, le_refl 1, fun _ _ => rfl⟩
  | cons c cs ih =>
      have h2 : (0 : Real) < 1 + 1 := add_pos zero_lt_one_ax zero_lt_one_ax
      rcases ih with ⟨X, hX, hz⟩ | ⟨c₀, k, X, hc₀, hX, hd⟩ | ⟨c₀, k, X, hc₀, hX, hd⟩
      · -- tail dies: the head decides
        have hconst : ∀ x : Real, X ≤ x → pev (c :: cs) x = c := by
          intro x hx
          show c + x * pev cs x = c
          rw [hz x hx]; mach_ring
        rcases lt_total c 0 with hc | hc | hc
        · refine Or.inr (Or.inr ⟨-c, 0, X, neg_pos' hc, hX, fun x hx => ?_⟩)
          rw [hconst x hx, powNat_zero]
          have e : -(-c * 1) = c := by mach_ring
          rw [e]; exact le_refl _
        · refine Or.inl ⟨X, hX, fun x hx => ?_⟩
          rw [hconst x hx, hc]
        · refine Or.inr (Or.inl ⟨c, 0, X, hc, hX, fun x hx => ?_⟩)
          rw [hconst x hx, powNat_zero]
          have e : c * 1 = c := by mach_ring
          rw [e]; exact le_refl _
      · -- tail dominates positively
        obtain ⟨X', hX', hXX', hbig⟩ := big_threshold c c₀ hc₀ X hX
        refine Or.inr (Or.inl ⟨c₀ / (1 + 1), k + 1, X', div_pos' hc₀ h2, hX', fun x hx => ?_⟩)
        have hx1 : (1 : Real) ≤ x := le_trans hX' hx
        have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx1
        have hxp : c₀ * powNat x (k + 1) ≤ x * pev cs x := by
          have v := mul_le_mul_of_nonneg_left (hd x (le_trans hXX' hx)) hx0
          have e : x * (c₀ * powNat x k) = c₀ * powNat x (k + 1) := by
            show x * (c₀ * powNat x k) = c₀ * (x * powNat x k)
            mach_mpoly [x, c₀, powNat x k]
          rw [e] at v; exact v
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
                = c₀ / (1 + 1) * (1 + 1) * powNat x (k + 1) := by
              mach_mpoly [c₀ / (1 + 1), powNat x (k + 1)]
            rw [e, div_mul_self' (ne_of_gt h2)]
          rw [← hkey]
          refine add_le_add_wit (le_refl _) ?_
          have hd2 : (1 + 1) * abs c ≤ (1 + 1) * (c₀ / (1 + 1) * powNat x (k + 1)) := by
            have e : (1 + 1) * (c₀ / (1 + 1) * powNat x (k + 1))
                = c₀ / (1 + 1) * (1 + 1) * powNat x (k + 1) := by
              mach_mpoly [c₀ / (1 + 1), powNat x (k + 1)]
            rw [e, div_mul_self' (ne_of_gt h2)]; exact habs
          exact le_of_mul_le_mul_left' h2 hd2
        show c₀ / (1 + 1) * powNat x (k + 1) ≤ c + x * pev cs x
        have hneg : -(abs c) ≤ c := by
          have v := le_abs_self (-c)
          rw [abs_neg] at v
          have w := add_le_add_wit v (le_refl (c + -(abs c)))
          have el : -c + (c + -(abs c)) = -(abs c) := by mach_ring
          have er : abs c + (c + -(abs c)) = c := by mach_ring
          rw [el, er] at w; exact w
        have step : c₀ / (1 + 1) * powNat x (k + 1) ≤ -(abs c) + x * pev cs x := by
          have chain : c₀ / (1 + 1) * powNat x (k + 1) + abs c ≤ x * pev cs x :=
            le_trans hhalf hxp
          have w := add_le_add_wit chain (le_refl (-(abs c)))
          have el : c₀ / (1 + 1) * powNat x (k + 1) + abs c + -(abs c)
              = c₀ / (1 + 1) * powNat x (k + 1) := by mach_ring
          have er : x * pev cs x + -(abs c) = -(abs c) + x * pev cs x := by mach_ring
          rw [el, er] at w; exact w
        exact le_trans step (add_le_add_wit hneg (le_refl (x * pev cs x)))
      · -- tail dominates negatively: mirror the positive case through `−`
        obtain ⟨X', hX', hXX', hbig⟩ := big_threshold c c₀ hc₀ X hX
        refine Or.inr (Or.inr ⟨c₀ / (1 + 1), k + 1, X', div_pos' hc₀ h2, hX', fun x hx => ?_⟩)
        have hx1 : (1 : Real) ≤ x := le_trans hX' hx
        have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx1
        have hxp : x * pev cs x ≤ -(c₀ * powNat x (k + 1)) := by
          have v := mul_le_mul_of_nonneg_left (hd x (le_trans hXX' hx)) hx0
          have e : x * -(c₀ * powNat x k) = -(c₀ * powNat x (k + 1)) := by
            show x * -(c₀ * powNat x k) = -(c₀ * (x * powNat x k))
            mach_mpoly [x, c₀, powNat x k]
          rw [e] at v; exact v
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
                = c₀ / (1 + 1) * (1 + 1) * powNat x (k + 1) := by
              mach_mpoly [c₀ / (1 + 1), powNat x (k + 1)]
            rw [e, div_mul_self' (ne_of_gt h2)]
          rw [← hkey]
          refine add_le_add_wit (le_refl _) ?_
          have hd2 : (1 + 1) * abs c ≤ (1 + 1) * (c₀ / (1 + 1) * powNat x (k + 1)) := by
            have e : (1 + 1) * (c₀ / (1 + 1) * powNat x (k + 1))
                = c₀ / (1 + 1) * (1 + 1) * powNat x (k + 1) := by
              mach_mpoly [c₀ / (1 + 1), powNat x (k + 1)]
            rw [e, div_mul_self' (ne_of_gt h2)]; exact habs
          exact le_of_mul_le_mul_left' h2 hd2
        show c + x * pev cs x ≤ -(c₀ / (1 + 1) * powNat x (k + 1))
        have hcle : c ≤ abs c := le_abs_self c
        have step : c + x * pev cs x ≤ abs c + -(c₀ * powNat x (k + 1)) :=
          add_le_add_wit hcle hxp
        refine le_trans step ?_
        have w := add_le_add_wit hhalf (le_refl (-(c₀ * powNat x (k + 1))))
        have el : c₀ / (1 + 1) * powNat x (k + 1) + abs c + -(c₀ * powNat x (k + 1))
            = abs c + -(c₀ * powNat x (k + 1)) + c₀ / (1 + 1) * powNat x (k + 1) := by mach_ring
        have er : c₀ * powNat x (k + 1) + -(c₀ * powNat x (k + 1)) = 0 := by mach_ring
        rw [el, er] at w
        have v := add_le_add_wit w (le_refl (-(c₀ / (1 + 1) * powNat x (k + 1))))
        have el2 : abs c + -(c₀ * powNat x (k + 1)) + c₀ / (1 + 1) * powNat x (k + 1)
            + -(c₀ / (1 + 1) * powNat x (k + 1)) = abs c + -(c₀ * powNat x (k + 1)) := by mach_ring
        have er2 : (0 : Real) + -(c₀ / (1 + 1) * powNat x (k + 1))
            = -(c₀ / (1 + 1) * powNat x (k + 1)) := by mach_ring
        rw [el2, er2] at v; exact v

/-! ## Signs of quotients -/

theorem one_div_neg_of_neg {b : Real} (hb : b < 0) : 1 / b < 0 := by
  have hnb : (0 : Real) < -b := neg_pos' hb
  have e : 1 / b = -(1 / -b) := by
    refine div_of_eq_mul (ne_of_lt hb) ?_
    have e2 : b * -(1 / -b) = -b * (1 / -b) := by mach_ring
    rw [e2, mul_inv _ (ne_of_gt hnb)]
  rw [e]
  refine neg_of_neg_pos' ?_
  have e3 : -(-(1 / -b)) = 1 / -b := by mach_ring
  rw [e3]; exact one_div_pos_of_pos hnb

theorem div_pos_of_neg_neg {a b : Real} (ha : a < 0) (hb : b < 0) : 0 < a / b := by
  rw [div_def a b (ne_of_lt hb)]
  have hp := mul_pos (neg_pos' ha) (neg_pos' (one_div_neg_of_neg hb))
  have e : -a * -(1 / b) = a * (1 / b) := by mach_ring
  rw [e] at hp; exact hp

theorem div_neg_of_pos_neg {a b : Real} (ha : 0 < a) (hb : b < 0) : a / b < 0 := by
  rw [div_def a b (ne_of_lt hb)]
  refine neg_of_neg_pos' ?_
  have hp := mul_pos ha (neg_pos' (one_div_neg_of_neg hb))
  have e : a * -(1 / b) = -(a * (1 / b)) := by mach_ring
  rw [e] at hp; exact hp

theorem div_neg_of_neg_pos {a b : Real} (ha : a < 0) (hb : 0 < b) : a / b < 0 := by
  rw [div_def a b (ne_of_gt hb)]
  refine neg_of_neg_pos' ?_
  have hp := mul_pos (neg_pos' ha) (one_div_pos_of_pos hb)
  have e : -a * (1 / b) = -(a * (1 / b)) := by mach_ring
  rw [e] at hp; exact hp

/-! ## The trichotomy -/

/-- Eventually strictly positive, eventually strictly negative, or eventually zero. The **strict**
trichotomy — "eventually non-negative" is a different and weaker statement. -/
def EvSignDef (f : Real → Real) : Prop :=
  EvZeroF f
  ∨ (∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → 0 < f x)
  ∨ (∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → f x < 0)

private theorem three_bounds {X₁ X₂ X₃ : Real} (h₁ : 1 ≤ X₁) (h₂ : 1 ≤ X₂) (h₃ : 1 ≤ X₃) :
    ∃ X : Real, 1 ≤ X ∧ X₁ ≤ X ∧ X₂ ≤ X ∧ X₃ ≤ X := by
  obtain ⟨Y, hY, hY1, hY2⟩ := two_bounds' h₁ h₂
  obtain ⟨X, hX, hXY, hX3⟩ := two_bounds' hY h₃
  exact ⟨X, hX, le_trans hY1 hXY, le_trans hY2 hXY, hX3⟩

/-- **Every rational germ is eventually sign-definite.** The sign of a quotient is read off from the
signs of its numerator and denominator, each settled by `pev_signed_dichotomy`. -/
theorem ratGerm_evSignDef {f : Real → Real} (h : RatGerm f) : EvSignDef f := by
  obtain ⟨P, Q, X, hX, hQ, he⟩ := h
  have hQnz : ¬ EvZeroF (pev Q) := by
    rintro ⟨Z, hZ, hz⟩
    obtain ⟨W, _, hWX, hWZ⟩ := two_bounds' hX hZ
    exact hQ W hWX (hz W hWZ)
  have hposP : ∀ (c : Real) (k : Nat) (x : Real), 0 < c → 1 ≤ x →
      c * powNat x k ≤ pev P x → 0 < pev P x := by
    intro c k x hc hx hle
    exact lt_of_lt_of_le (mul_pos hc (powNat_pos (lt_of_lt_of_le zero_lt_one_ax hx) k)) hle
  have hnegP : ∀ (c : Real) (k : Nat) (x : Real), 0 < c → 1 ≤ x →
      pev P x ≤ -(c * powNat x k) → pev P x < 0 := by
    intro c k x hc hx hle
    refine lt_of_le_of_lt hle (neg_of_neg_pos' ?_)
    have e : -(-(c * powNat x k)) = c * powNat x k := by mach_ring
    rw [e]
    exact mul_pos hc (powNat_pos (lt_of_lt_of_le zero_lt_one_ax hx) k)
  have hposQ : ∀ (c : Real) (k : Nat) (x : Real), 0 < c → 1 ≤ x →
      c * powNat x k ≤ pev Q x → 0 < pev Q x := by
    intro c k x hc hx hle
    exact lt_of_lt_of_le (mul_pos hc (powNat_pos (lt_of_lt_of_le zero_lt_one_ax hx) k)) hle
  have hnegQ : ∀ (c : Real) (k : Nat) (x : Real), 0 < c → 1 ≤ x →
      pev Q x ≤ -(c * powNat x k) → pev Q x < 0 := by
    intro c k x hc hx hle
    refine lt_of_le_of_lt hle (neg_of_neg_pos' ?_)
    have e : -(-(c * powNat x k)) = c * powNat x k := by mach_ring
    rw [e]
    exact mul_pos hc (powNat_pos (lt_of_lt_of_le zero_lt_one_ax hx) k)
  rcases pev_signed_dichotomy P with ⟨ZP, hZP, hzP⟩ | ⟨cP, kP, ZP, hcP, hZP, hdP⟩
    | ⟨cP, kP, ZP, hcP, hZP, hdP⟩
  · -- numerator dies
    obtain ⟨W, hW, hWX, hWP⟩ := two_bounds' hX hZP
    refine Or.inl ⟨W, hW, fun x hx => ?_⟩
    rw [he x (le_trans hWX hx), hzP x (le_trans hWP hx)]
    exact zero_div_eq (hQ x (le_trans hWX hx))
  all_goals
    rcases pev_signed_dichotomy Q with hQz | ⟨cQ, kQ, ZQ, hcQ, hZQ, hdQ⟩
      | ⟨cQ, kQ, ZQ, hcQ, hZQ, hdQ⟩
  · exact absurd hQz hQnz
  · obtain ⟨W, hW, hWX, hWP, hWQ⟩ := three_bounds hX hZP hZQ
    refine Or.inr (Or.inl ⟨W, hW, fun x hx => ?_⟩)
    rw [he x (le_trans hWX hx)]
    exact div_pos' (hposP cP kP x hcP (le_trans hW hx) (hdP x (le_trans hWP hx)))
      (hposQ cQ kQ x hcQ (le_trans hW hx) (hdQ x (le_trans hWQ hx)))
  · obtain ⟨W, hW, hWX, hWP, hWQ⟩ := three_bounds hX hZP hZQ
    refine Or.inr (Or.inr ⟨W, hW, fun x hx => ?_⟩)
    rw [he x (le_trans hWX hx)]
    exact div_neg_of_pos_neg (hposP cP kP x hcP (le_trans hW hx) (hdP x (le_trans hWP hx)))
      (hnegQ cQ kQ x hcQ (le_trans hW hx) (hdQ x (le_trans hWQ hx)))
  · exact absurd hQz hQnz
  · obtain ⟨W, hW, hWX, hWP, hWQ⟩ := three_bounds hX hZP hZQ
    refine Or.inr (Or.inr ⟨W, hW, fun x hx => ?_⟩)
    rw [he x (le_trans hWX hx)]
    exact div_neg_of_neg_pos (hnegP cP kP x hcP (le_trans hW hx) (hdP x (le_trans hWP hx)))
      (hposQ cQ kQ x hcQ (le_trans hW hx) (hdQ x (le_trans hWQ hx)))
  · obtain ⟨W, hW, hWX, hWP, hWQ⟩ := three_bounds hX hZP hZQ
    refine Or.inr (Or.inl ⟨W, hW, fun x hx => ?_⟩)
    rw [he x (le_trans hWX hx)]
    exact div_pos_of_neg_neg (hnegP cP kP x hcP (le_trans hW hx) (hdP x (le_trans hWP hx)))
      (hnegQ cQ kQ x hcQ (le_trans hW hx) (hdQ x (le_trans hWQ hx)))

/-- **`C₀` is eventually sign-definite. Unconditionally.**

`SignHardCase` is this statement for EML and it is open. Here it is a theorem, and the reason is
structural: `C₀` has a normal form, so the sign is read off a numerator and a denominator instead of
having to survive nested transcendental cancellation. -/
theorem zero_query_evSignDef (T : FTerm) (h : fOcc T = 0) : EvSignDef (FTerm.eval T) :=
  ratGerm_evSignDef (ratGerm_of_zero_query T h)

/-! ## What the trichotomy buys at level 1

A rational germ `S` feeding the single `F` of a one-query term now falls into cases the totalised
logarithm treats very differently. Three of the four collapse. -/

/-- `S < 0`: **the logarithm is gone and the generator is bounded** — `F(S) = exp S ∈ (0,1)`. -/
theorem Fbasis_of_neg {y : Real} (hy : y < 0) : Fbasis y = exp y ∧ 0 < Fbasis y ∧ Fbasis y < 1 := by
  have he : Fbasis y = exp y := Fbasis_of_nonpos (le_of_lt hy)
  refine ⟨he, ?_, ?_⟩
  · rw [he]; exact exp_pos y
  · rw [he]
    have h := exp_lt hy
    rw [exp_zero] at h; exact h

/-- `S = 0`: the generator is the **constant** `1`. -/
theorem Fbasis_zero : Fbasis (0 : Real) = 1 := by
  rw [Fbasis_of_nonpos (le_refl (0 : Real)), exp_zero]

/-- `S ≥ 1`: the exponential component dominates, so `F(S) ≥ exp S > 0`. -/
theorem Fbasis_ge_exp_of_one_le {y : Real} (hy : 1 ≤ y) : exp y ≤ Fbasis y ∧ 0 < Fbasis y :=
  ⟨exp_le_Fbasis hy, lt_of_lt_of_le (exp_pos y) (exp_le_Fbasis hy)⟩

/-! ### The remaining branch is a bounded WINDOW, not an interval

On `0 < S < 1` the sign of `F(S) = exp S + log S` is a contest between `exp S ∈ (1, e)` and
`log S < 0`, and the contest is decided everywhere except on a bounded window with explicit
transcendental endpoints.

* `S > e⁻¹` forces `log S > −1` while `exp S > 1`, so `F(S) > 0` — and this needs no upper bound on
  `S` at all.
* `0 < S ≤ e^(−e)` forces `log S ≤ −e` while `exp S < e`, so `F(S) < 0`.

Neither bound is numeric: both are comparisons against `exp` of something, so no decimal enters and
the `sqrt`/numeral discipline is untouched. What is left is `e^(−e) < S ≤ e⁻¹`. -/

/-- `F(y) > 0` whenever `y > e⁻¹` — no upper bound on `y` needed. -/
theorem Fbasis_pos_of_gt_expNegOne {y : Real} (hy : exp (-1) < y) : 0 < Fbasis y := by
  have hy0 : (0 : Real) < y := lt_trans_ax (exp_pos (-1)) hy
  have hlog : (-1 : Real) < log y := by
    have h := log_lt_log (exp_pos (-1)) hy
    rw [log_exp] at h; exact h
  have hexp : (1 : Real) < exp y := one_lt_exp hy0
  show (0 : Real) < exp y + log y
  have s1 : (0 : Real) < exp y + -1 := by
    have v := add_lt_add_left hexp (-1 : Real)
    have el : (-1 : Real) + 1 = 0 := by mach_ring
    have er : (-1 : Real) + exp y = exp y + -1 := by mach_ring
    rw [el, er] at v; exact v
  have s2 : exp y + -1 < exp y + log y := add_lt_add_left hlog (exp y)
  exact lt_trans_ax s1 s2

/-- `F(y) < 0` whenever `0 < y ≤ e^(−e)`. -/
theorem Fbasis_neg_of_le_tiny {y : Real} (hy0 : 0 < y) (hy : y ≤ exp (-(exp 1))) :
    Fbasis y < 0 := by
  have hne : -(exp 1) < (0 : Real) := neg_of_neg_pos' (by
    have e : -(-(exp 1)) = exp 1 := by mach_ring
    rw [e]; exact exp_pos 1)
  have htiny : exp (-(exp 1)) < 1 := by
    have h := exp_lt hne
    rw [exp_zero] at h; exact h
  have hy1 : y < 1 := lt_of_le_of_lt hy htiny
  have hlog : log y ≤ -(exp 1) := by
    have h := log_le_log hy0 hy
    rw [log_exp] at h; exact h
  have hexp : exp y < exp 1 := exp_lt hy1
  show exp y + log y < 0
  have s1 : exp y + log y < exp 1 + log y := by
    have v := add_lt_add_left hexp (log y)
    have el : log y + exp y = exp y + log y := by mach_ring
    have er : log y + exp 1 = exp 1 + log y := by mach_ring
    rw [el, er] at v; exact v
  have s2 : exp 1 + log y ≤ 0 := by
    have v := add_le_add_wit (le_refl (exp 1)) hlog
    have e : exp 1 + -(exp 1) = 0 := by mach_ring
    rw [e] at v; exact v
  exact lt_of_lt_of_le s1 s2

/-- **`F` genuinely changes sign on `(0, ∞)`.** This is the source of the level-1 difficulty, stated
rather than left implicit: at `e^(−e)` the generator is negative, at `1` it is `exp 1 > 0`. -/
theorem Fbasis_sign_changes : Fbasis (exp (-(exp 1))) < 0 ∧ 0 < Fbasis 1 := by
  refine ⟨Fbasis_neg_of_le_tiny (exp_pos _) (le_refl _), ?_⟩
  show (0 : Real) < exp 1 + log 1
  have hl1 : log (1 : Real) = 0 := by
    have hz : exp (0 : Real) = 1 := exp_zero
    rw [← hz, log_exp]
  rw [hl1]
  have e : exp 1 + 0 = exp 1 := by mach_ring
  rw [e]; exact exp_pos 1

/-- Rational germs are closed under subtracting a constant: `P/Q − c = (P − c·Q)/Q`. -/
theorem ratGerm_sub_const {f : Real → Real} (h : RatGerm f) (c : Real) :
    RatGerm (fun x => f x - c) := by
  obtain ⟨P, Q, X, hX, hQ, he⟩ := h
  refine ⟨psub P (pscale c Q), Q, X, hX, hQ, fun x hx => ?_⟩
  show f x - c = pev (psub P (pscale c Q)) x / pev Q x
  rw [he x hx, pev_psub, pev_pscale]
  refine (div_of_eq_mul (hQ x hx) ?_).symm
  rw [div_def (pev P x) (pev Q x) (hQ x hx)]
  have e : pev Q x * (pev P x * (1 / pev Q x) - c)
      = pev P x * (pev Q x * (1 / pev Q x)) - c * pev Q x := by
    mach_mpoly [pev P x, pev Q x, c, (1 : Real) / pev Q x]
  rw [e, mul_inv _ (hQ x hx)]; mach_ring

/-- The residual case: the germ is eventually trapped in `(e^(−e), e⁻¹]`. -/
def InWindow (S : Real → Real) : Prop :=
  ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → exp (-(exp 1)) < S x ∧ S x ≤ exp (-1)

/-- **`F ∘ S` is eventually sign-definite for every rational germ `S`, unless `S` is trapped in the
window.**

Every regime except one is decided, and the exception is a *bounded* window with explicit endpoints
rather than the open interval `(0,1)`. That is a much smaller residue than the branch it replaces,
and it is where `OneQueryDichotomy` now lives. -/
theorem FS_evSignDef_or_window {S : Real → Real} (h : RatGerm S) :
    EvSignDef (fun x => Fbasis (S x)) ∨ InWindow S := by
  have hconst : ∀ (c : Real) (X : Real), 1 ≤ X → (∀ x : Real, X ≤ x → S x = c) →
      EvSignDef (fun x => Fbasis (S x)) := by
    intro c X hX hS
    rcases lt_total 0 (Fbasis c) with hc | hc | hc
    · exact Or.inr (Or.inl ⟨X, hX, fun x hx => by show 0 < Fbasis (S x); rw [hS x hx]; exact hc⟩)
    · exact Or.inl ⟨X, hX, fun x hx => by show Fbasis (S x) = 0; rw [hS x hx, ← hc]⟩
    · exact Or.inr (Or.inr ⟨X, hX, fun x hx => by show Fbasis (S x) < 0; rw [hS x hx]; exact hc⟩)
  have hsub : ∀ (c : Real), EvSignDef (fun x => S x - c) :=
    fun c => ratGerm_evSignDef (ratGerm_sub_const h c)
  rcases hsub (exp (-1)) with ⟨X, hX, hz⟩ | ⟨X, hX, hp⟩ | ⟨X, hX, hn⟩
  · -- `S ≡ e⁻¹`
    exact Or.inl (hconst (exp (-1)) X hX (fun x hx => by
      have hz0 : S x - exp (-1) = 0 := hz x hx
      have v : S x - exp (-1) + exp (-1) = 0 + exp (-1) := by rw [hz0]
      have el : S x - exp (-1) + exp (-1) = S x := by mach_ring
      have er : (0 : Real) + exp (-1) = exp (-1) := by mach_ring
      rw [el, er] at v; exact v))
  · -- `S > e⁻¹`
    refine Or.inl (Or.inr (Or.inl ⟨X, hX, fun x hx => ?_⟩))
    show 0 < Fbasis (S x)
    refine Fbasis_pos_of_gt_expNegOne ?_
    have v := add_lt_add_left (hp x hx) (exp (-1))
    have el : exp (-1) + 0 = exp (-1) := by mach_ring
    have er : exp (-1) + (S x - exp (-1)) = S x := by mach_ring
    rw [el, er] at v; exact v
  · -- `S < e⁻¹`; now compare against `e^(−e)`
    have hSle : ∀ x : Real, X ≤ x → S x ≤ exp (-1) := by
      intro x hx
      have v := add_lt_add_left (hn x hx) (exp (-1))
      have el : exp (-1) + (S x - exp (-1)) = S x := by mach_ring
      have er : exp (-1) + 0 = exp (-1) := by mach_ring
      rw [el, er] at v; exact le_of_lt v
    rcases hsub (exp (-(exp 1))) with ⟨Y, hY, hz2⟩ | ⟨Y, hY, hp2⟩ | ⟨Y, hY, hn2⟩
    · exact Or.inl (hconst (exp (-(exp 1))) Y hY (fun x hx => by
        have hz0 : S x - exp (-(exp 1)) = 0 := hz2 x hx
        have v : S x - exp (-(exp 1)) + exp (-(exp 1)) = 0 + exp (-(exp 1)) := by rw [hz0]
        have el : S x - exp (-(exp 1)) + exp (-(exp 1)) = S x := by mach_ring
        have er : (0 : Real) + exp (-(exp 1)) = exp (-(exp 1)) := by mach_ring
        rw [el, er] at v; exact v))
    · -- trapped in the window
      obtain ⟨W, hW, hWX, hWY⟩ := two_bounds' hX hY
      refine Or.inr ⟨W, hW, fun x hx => ⟨?_, hSle x (le_trans hWX hx)⟩⟩
      have v := add_lt_add_left (hp2 x (le_trans hWY hx)) (exp (-(exp 1)))
      have el : exp (-(exp 1)) + 0 = exp (-(exp 1)) := by mach_ring
      have er : exp (-(exp 1)) + (S x - exp (-(exp 1))) = S x := by mach_ring
      rw [el, er] at v; exact v
    · -- `S < e^(−e)`; the sign of `S` itself now finishes it
      have hSlt : ∀ x : Real, Y ≤ x → S x ≤ exp (-(exp 1)) := by
        intro x hx
        have v := add_lt_add_left (hn2 x hx) (exp (-(exp 1)))
        have el : exp (-(exp 1)) + (S x - exp (-(exp 1))) = S x := by mach_ring
        have er : exp (-(exp 1)) + 0 = exp (-(exp 1)) := by mach_ring
        rw [el, er] at v; exact le_of_lt v
      rcases ratGerm_evSignDef h with ⟨Z, hZ, hSz⟩ | ⟨Z, hZ, hSp⟩ | ⟨Z, hZ, hSn⟩
      · exact Or.inl (hconst 0 Z hZ hSz)
      · obtain ⟨W, hW, hWY, hWZ⟩ := two_bounds' hY hZ
        refine Or.inl (Or.inr (Or.inr ⟨W, hW, fun x hx => ?_⟩))
        exact Fbasis_neg_of_le_tiny (hSp x (le_trans hWZ hx)) (hSlt x (le_trans hWY hx))
      · refine Or.inl (Or.inr (Or.inl ⟨Z, hZ, fun x hx => ?_⟩))
        show 0 < Fbasis (S x)
        rw [Fbasis_of_nonpos (le_of_lt (hSn x hx))]
        exact exp_pos _

/-! ### Where `OneQueryDichotomy` now lives

The residue is not "the interval `(0,1)`" but the bounded window `(e^(−e), e⁻¹]`, and a rational germ
trapped there is a strong constraint: it converges, and its limit lies in that window. `F` has
exactly one zero in it, so the delicate case is a germ approaching that zero — a coincidence, but one
that has to be excluded rather than waved away.

Which also says what the level-1 problem is *not*. It is not about `F` being transcendental; on every
regime outside a bounded window the sign is settled by comparisons against `exp` of a constant. -/

end MachLib
