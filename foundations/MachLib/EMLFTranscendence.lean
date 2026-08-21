import MachLib.EMLGermSign

/-!
# `F` satisfies no polynomial relation over the polynomial coefficients

The level-1 residue is no longer about `F ∘ S`'s sign — that is settled. It is whether a nonzero
algebraic expression in `x` and `F(S(x))` can vanish on a tail. After clearing denominators that is
a polynomial relation

```
Σⱼ pⱼ(x) · F(S(x))ʲ = 0      eventually
```

and the smallest instance is `S = x`. This file settles that instance, and it costs **no new
axioms** — the `C₀` lower-bound instrument built for `FQueryLowerBound` pays for it directly.

## The argument

If `aₘ(x)·F(x)ᵐ = −Σ_{i<m} aᵢ(x)·F(x)ⁱ` then, since the right side has degree `< m` in `F`, dividing
by `F(x)ᵐ⁻¹` bounds `F(x)` itself by a ratio of polynomials — hence by a polynomial. But
`F(x) ≥ exp x` for `x ≥ 1`, and `not_polyEnvelope_Fbasis` says no polynomial envelope contains that.

The degree drop is carried as `y · |Σ_{i<m} aᵢ yⁱ| ≤ B(x) · yᵐ`, which avoids `Nat` subtraction and
makes the induction one line per constructor.

## What this is and is not

It is **functional** transcendence in the elementary sense — `F` satisfies no polynomial relation
with polynomial coefficients — not a number-theoretic statement about values. And it is the `S = x`
case only; whether it transports along a nonconstant rational substitution is a separate question,
deliberately not assumed here.
-/

namespace MachLib

open Real

/-- `bipev [c₀, c₁, …] x y = c₀(x) + y·(c₁(x) + y·(…))` — Horner in `y`, polynomial coefficients. -/
noncomputable def bipev : List (List Real) → Real → Real → Real
  | [], _, _ => 0
  | L :: Ls, x, y => pev L x + y * bipev Ls x y

/-- A polynomial in `y` of degree exactly `Ls.length`, with leading coefficient `pev A`. -/
noncomputable def bipevLead (A : List Real) (Ls : List (List Real)) (x y : Real) : Real :=
  pev A x * powNat y Ls.length + bipev Ls x y

/-- **The degree drop**, stated multiplied through by `y` so no `Nat` subtraction appears:
`y · |P(x,y)| ≤ B(x) · y^(deg+1)` where `deg + 1 = Ls.length`. -/
theorem bipev_degree_drop : ∀ Ls : List (List Real),
    ∃ (B : Real) (M : Nat) (X : Real), 0 ≤ B ∧ 1 ≤ X ∧
      ∀ x y : Real, X ≤ x → 1 ≤ y →
        y * abs (bipev Ls x y) ≤ B * powNat x M * powNat y Ls.length := by
  intro Ls
  induction Ls with
  | nil =>
      refine ⟨0, 0, 1, le_refl 0, le_refl 1, fun x y _ hy => ?_⟩
      show y * abs (0 : Real) ≤ 0 * powNat x 0 * powNat y 0
      rw [abs_of_nonneg (le_refl (0 : Real))]
      have e : y * 0 = 0 := by mach_ring
      have e2 : (0 : Real) * powNat x 0 * powNat y 0 = 0 := by mach_ring
      rw [e, e2]; exact le_refl _
  | cons L Ls ih =>
      obtain ⟨B, M, X, hB, hX, hb⟩ := ih
      obtain ⟨C, N, XL, hC, hXL, hbL⟩ := pev_envelope L
      obtain ⟨W, hW, hWX, hWL⟩ := two_bounds' hX hXL
      refine ⟨B + C, max M N, W, add_nonneg hB hC, hW, fun x y hx hy => ?_⟩
      have hx1 : (1 : Real) ≤ x := le_trans hW hx
      have hy0 : (0 : Real) ≤ y := le_trans (le_of_lt zero_lt_one_ax) hy
      have hyk : (0 : Real) ≤ powNat y Ls.length :=
        le_of_lt (powNat_pos (lt_of_lt_of_le zero_lt_one_ax hy) _)
      -- split the head off
      have htri : abs (pev L x + y * bipev Ls x y)
          ≤ abs (pev L x) + y * abs (bipev Ls x y) := by
        have h := abs_add (pev L x) (y * bipev Ls x y)
        rw [abs_mul, abs_of_nonneg hy0] at h
        exact h
      have hmul : y * abs (pev L x + y * bipev Ls x y)
          ≤ y * (abs (pev L x) + y * abs (bipev Ls x y)) :=
        mul_le_mul_of_nonneg_left htri hy0
      -- bound each piece by `(B + C) · x^max · y^(len+1)`
      have h1 : y * abs (pev L x) ≤ C * powNat x (max M N) * powNat y (Ls.length + 1) := by
        have hL := hbL x (le_trans hWL hx)
        have s1 : y * abs (pev L x) ≤ y * (C * powNat x N) :=
          mul_le_mul_of_nonneg_left hL hy0
        have s2 : C * powNat x N ≤ C * powNat x (max M N) :=
          mul_le_mul_of_nonneg_left (powNat_mono_exp hx1 (Nat.le_max_right M N)) hC
        have s3 : y * (C * powNat x N) ≤ y * (C * powNat x (max M N)) :=
          mul_le_mul_of_nonneg_left s2 hy0
        have s4 : y * (C * powNat x (max M N))
            ≤ powNat y (Ls.length + 1) * (C * powNat x (max M N)) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hC (le_of_lt
            (powNat_pos (lt_of_lt_of_le zero_lt_one_ax hx1) _)))
          show y ≤ y * powNat y Ls.length
          have v := mul_le_mul_of_nonneg_left (one_le_powNat hy Ls.length) hy0
          have e : y * 1 = y := by mach_ring
          rw [e] at v; exact v
        have e : powNat y (Ls.length + 1) * (C * powNat x (max M N))
            = C * powNat x (max M N) * powNat y (Ls.length + 1) := by
          mach_mpoly [C, powNat x (max M N), powNat y (Ls.length + 1)]
        rw [← e]
        exact le_trans (le_trans s1 s3) s4
      have h2 : y * (y * abs (bipev Ls x y))
          ≤ B * powNat x (max M N) * powNat y (Ls.length + 1) := by
        have hbb := hb x y (le_trans hWX hx) hy
        have s1 : y * (y * abs (bipev Ls x y)) ≤ y * (B * powNat x M * powNat y Ls.length) :=
          mul_le_mul_of_nonneg_left hbb hy0
        have s2 : B * powNat x M ≤ B * powNat x (max M N) :=
          mul_le_mul_of_nonneg_left (powNat_mono_exp hx1 (Nat.le_max_left M N)) hB
        have s3 : y * (B * powNat x M * powNat y Ls.length)
            ≤ y * (B * powNat x (max M N) * powNat y Ls.length) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right s2 hyk) hy0
        have e : y * (B * powNat x (max M N) * powNat y Ls.length)
            = B * powNat x (max M N) * powNat y (Ls.length + 1) := by
          show y * (B * powNat x (max M N) * powNat y Ls.length)
              = B * powNat x (max M N) * (y * powNat y Ls.length)
          mach_mpoly [y, B, powNat x (max M N), powNat y Ls.length]
        rw [← e]
        exact le_trans s1 s3
      show y * abs (pev L x + y * bipev Ls x y)
          ≤ (B + C) * powNat x (max M N) * powNat y (Ls.length + 1)
      have hsum := add_le_add_wit h1 h2
      have e : C * powNat x (max M N) * powNat y (Ls.length + 1)
          + B * powNat x (max M N) * powNat y (Ls.length + 1)
          = (B + C) * powNat x (max M N) * powNat y (Ls.length + 1) := by
        mach_mpoly [B, C, powNat x (max M N), powNat y (Ls.length + 1)]
      rw [← e]
      refine le_trans hmul (le_trans (le_of_eq ?_) hsum)
      mach_mpoly [y, abs (pev L x), abs (bipev Ls x y)]

/-! ## Rescaling the envelope

`exp(r·x)` outgrows every polynomial for **any** `r > 0`, not just `r ≥ 1`: substituting `x = t/r`
turns a polynomial envelope for it into one for `exp` itself. This is what lets the theorems below
take `c·x ≤ S x` rather than the artificially strong `x ≤ S x`. -/

theorem powNat_mul (a b : Real) : ∀ n : Nat, powNat (a * b) n = powNat a n * powNat b n := by
  intro n
  induction n with
  | zero => show (1 : Real) = 1 * 1; mach_ring
  | succ k ih =>
      show a * b * powNat (a * b) k = a * powNat a k * (b * powNat b k)
      rw [ih]; mach_mpoly [a, b, powNat a k, powNat b k]

theorem not_polyEnvelope_of_ge_exp_scaled {g : Real → Real} {r : Real} (hr : 0 < r)
    (h : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → exp (r * x) ≤ g x) : ¬ PolyEnvelope g := by
  rintro ⟨C, N, X₀, hC, hX₀, hb⟩
  obtain ⟨X, hX, hge⟩ := h
  obtain ⟨W, hW, hWX, hWX₀⟩ := two_bounds' hX hX₀
  obtain ⟨T, hT, _, hTW⟩ := two_bounds' (le_refl (1 : Real))
    (show (1 : Real) ≤ 1 + abs (r * W) from le_add_nonneg' (abs_nonneg _))
  have hrne : r ≠ 0 := ne_of_gt hr
  refine not_polyEnvelope_of_ge_exp ⟨1, le_refl 1, fun t _ => le_refl (exp t)⟩
    ⟨C * powNat (1 / r) N, N, T, mul_nonneg hC
      (le_of_lt (powNat_pos (one_div_pos_of_pos hr) N)), hT, fun t ht => ?_⟩
  have hxt : r * (t / r) = t := by
    have e : r * (t / r) = t / r * r := by mach_ring
    rw [e]; exact div_mul_self' hrne
  have hrW : r * W ≤ t := by
    have h1 : r * W ≤ 1 + abs (r * W) := by
      refine le_trans (le_abs_self _) ?_
      have v := add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl (abs (r * W)))
      have e : (0 : Real) + abs (r * W) = abs (r * W) := by mach_ring
      rw [e] at v; exact v
    exact le_trans (le_trans h1 hTW) ht
  have hWle : W ≤ t / r := by
    refine le_of_mul_le_mul_left' hr ?_
    rw [hxt]; exact hrW
  have hgle := hge (t / r) (le_trans hWX hWle)
  have hble := hb (t / r) (le_trans hWX₀ hWle)
  rw [hxt] at hgle
  show abs (exp t) ≤ C * powNat (1 / r) N * powNat t N
  rw [abs_of_nonneg (le_of_lt (exp_pos t))]
  refine le_trans (le_trans hgle (le_abs_self _)) (le_trans hble (le_of_eq ?_))
  rw [div_def t r hrne, powNat_mul]
  mach_mpoly [C, powNat t N, powNat (1 / r) N]

/-! ## `F` is not algebraic over the polynomial coefficients -/

/-- **No nonzero polynomial in `F(x)` with polynomial coefficients vanishes on a tail.**

The leading coefficient is required to be eventually dominating — which, by `pev_dichotomy`, is the
same as not being eventually zero, i.e. the relation is genuinely of degree `Ls.length`. -/
theorem not_algebraic_of_dominates_exp {g : Real → Real} {r : Real} (hr : 0 < r)
    (hg : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → exp (r * x) ≤ g x)
    (A : List Real) (Ls : List (List Real)) (hA : EvDom (pev A))
    (hrel : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → bipevLead A Ls x (g x) = 0) : False := by
  obtain ⟨Xg, hXg, hge⟩ := hg
  obtain ⟨X₀', hX₀', hz'⟩ := hrel
  obtain ⟨X₀, hX₀, hX₀a, hX₀b⟩ := two_bounds' hXg hX₀'
  have hz : ∀ x : Real, X₀ ≤ x → bipevLead A Ls x (g x) = 0 :=
    fun x hx => hz' x (le_trans hX₀b hx)
  obtain ⟨c, k, X₁, hc, hX₁, hdom⟩ := hA
  obtain ⟨B, M, X₂, hB, hX₂, hdeg⟩ := bipev_degree_drop Ls
  obtain ⟨Y, hY, hY0, hY1⟩ := two_bounds' hX₀ hX₁
  obtain ⟨X, hX, hXY, hX2⟩ := two_bounds' hY hX₂
  refine not_polyEnvelope_of_ge_exp_scaled hr ⟨X, hX, fun x hx =>
      hge x (le_trans (le_trans (le_trans hX₀a hY0) hXY) hx)⟩
    ⟨B * (1 / c), M, X, mul_nonneg hB (le_of_lt (one_div_pos_of_pos hc)), hX, fun x hx => ?_⟩
  have hx1 : (1 : Real) ≤ x := le_trans hX hx
  have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx1
  have hF1 : (1 : Real) ≤ g x := by
    refine le_trans ?_ (hge x (le_trans (le_trans (le_trans hX₀a hY0) hXY) hx))
    exact le_trans (le_add_nonneg' (mul_nonneg (le_of_lt hr) hx0)) (one_add_le_exp (r * x))
  have hF0 : (0 : Real) < g x := lt_of_lt_of_le zero_lt_one_ax hF1
  have hpow : (0 : Real) < powNat (g x) Ls.length := powNat_pos hF0 _
  -- the relation, in absolute value
  have hrel0 : pev A x * powNat (g x) Ls.length = -(bipev Ls x (g x)) := by
    have h : pev A x * powNat (g x) Ls.length + bipev Ls x (g x) = 0 :=
      hz x (le_trans (le_trans hY0 hXY) hx)
    have v : pev A x * powNat (g x) Ls.length + bipev Ls x (g x)
        + -(bipev Ls x (g x)) = 0 + -(bipev Ls x (g x)) := by rw [h]
    have el : pev A x * powNat (g x) Ls.length + bipev Ls x (g x)
        + -(bipev Ls x (g x)) = pev A x * powNat (g x) Ls.length := by
      mach_mpoly [pev A x * powNat (g x) Ls.length, bipev Ls x (g x)]
    have er : (0 : Real) + -(bipev Ls x (g x)) = -(bipev Ls x (g x)) := by
      mach_mpoly [bipev Ls x (g x)]
    rw [el, er] at v; exact v
  have habs : abs (pev A x) * powNat (g x) Ls.length = abs (bipev Ls x (g x)) := by
    have h : abs (pev A x * powNat (g x) Ls.length) = abs (bipev Ls x (g x)) := by
      rw [hrel0, abs_neg]
    rw [abs_mul, abs_of_nonneg (le_of_lt hpow)] at h; exact h
  -- multiply by `F` and use the degree drop
  have hkey : powNat (g x) Ls.length * (abs (pev A x) * g x)
      ≤ powNat (g x) Ls.length * (B * powNat x M) := by
    have hd := hdeg x (g x) (le_trans hX2 hx) hF1
    rw [← habs] at hd
    have e1 : g x * (abs (pev A x) * powNat (g x) Ls.length)
        = powNat (g x) Ls.length * (abs (pev A x) * g x) := by
      mach_mpoly [g x, abs (pev A x), powNat (g x) Ls.length]
    have e2 : B * powNat x M * powNat (g x) Ls.length
        = powNat (g x) Ls.length * (B * powNat x M) := by
      mach_mpoly [B, powNat x M, powNat (g x) Ls.length]
    rw [e1, e2] at hd; exact hd
  have hcancel : abs (pev A x) * g x ≤ B * powNat x M :=
    le_of_mul_le_mul_left' hpow hkey
  -- the leading coefficient is bounded below by `c`
  have hcA : c ≤ abs (pev A x) := by
    refine le_trans ?_ (hdom x (le_trans (le_trans hY1 hXY) hx))
    have v := mul_le_mul_of_nonneg_left (one_le_powNat hx1 k) (le_of_lt hc)
    have e : c * 1 = c := by mach_ring
    rw [e] at v; exact v
  have hstep : c * g x ≤ B * powNat x M :=
    le_trans (mul_le_mul_of_nonneg_right hcA (le_of_lt hF0)) hcancel
  -- divide by `c`
  show abs (g x) ≤ B * (1 / c) * powNat x M
  rw [abs_of_nonneg (le_of_lt hF0)]
  refine le_of_mul_le_mul_left' hc ?_
  have e : c * (B * (1 / c) * powNat x M) = B * powNat x M * (c * (1 / c)) := by
    mach_mpoly [c, B, powNat x M, (1 : Real) / c]
  rw [e, mul_inv c (ne_of_gt hc)]
  have e2 : B * powNat x M * 1 = B * powNat x M := by mach_ring
  rw [e2]; exact hstep

/-- **`F` itself is not algebraic** — the original statement, now a corollary of the general one. -/
theorem Fbasis_not_algebraic (A : List Real) (Ls : List (List Real)) (hA : EvDom (pev A))
    (hrel : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → bipevLead A Ls x (Fbasis x) = 0) : False :=
  not_algebraic_of_dominates_exp zero_lt_one_ax
    ⟨1, le_refl 1, fun x hx => by
      have e : (1 : Real) * x = x := by mach_ring
      rw [e]; exact exp_le_Fbasis hx⟩ A Ls hA hrel

/-! ## A specimen that is not a linear relation

`(x² + 1)·F³ + (7 − x⁵)·F² + x·F − 3 ≠ 0` on any tail. Degree 3 in `F`, coefficients of degree 0, 1
and 5 in `x`, one of them with a negative leading term — nothing about the shape is special.

The coefficients are spelled `1 + 1 + 1` rather than `3` because `MachLib.Real` carries `OfNat`
instances for `0` and `1` only. That is the numeral discipline doing its job: a decimal literal
cannot enter a statement by accident. -/

private theorem specimenA_evDom : EvDom (pev [1, 0, 1]) := by
  rcases pev_dichotomy [(1 : Real), 0, 1] with ⟨X, hX, hz⟩ | hd
  · exfalso
    have hx0 : (0 : Real) < X := lt_of_lt_of_le zero_lt_one_ax hX
    have h0 : pev [(1 : Real), 0, 1] X = 0 := hz X (le_refl X)
    have e : pev [(1 : Real), 0, 1] X = 1 + X * X := by
      show (1 : Real) + X * (0 + X * (1 + X * 0)) = 1 + X * X
      mach_mpoly [X]
    rw [e] at h0
    have hpos : (0 : Real) < 1 + X * X := add_pos zero_lt_one_ax (mul_pos hx0 hx0)
    rw [h0] at hpos
    exact absurd hpos (lt_irrefl_ax 0)
  · exact hd

theorem Fbasis_nasty_relation_impossible :
    ¬ ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x →
      bipevLead [1, 0, 1]
        [[0 - (1 + 1 + 1)], [0, 1], [1 + 1 + 1 + 1 + 1 + 1 + 1, 0, 0, 0, 0, 0 - 1]]
        x (Fbasis x) = 0 :=
  fun h => Fbasis_not_algebraic _ _ specimenA_evDom h

/-! ## The lowest-power dual: when the generator is super-polynomially *small*

`S → −∞` makes the totalised logarithm vanish, so `F(S) = exp S → 0` faster than any polynomial. The
same argument runs upside down: split off the **constant** coefficient instead of the leading one,
and a tiny `F(S)` forces that constant to be tiny — which a nonzero polynomial cannot be. -/

/-- Envelope for `|y| ≤ 1`: the degree in `y` no longer matters. -/
theorem bipev_bounded_envelope : ∀ Ls : List (List Real),
    ∃ (B : Real) (M : Nat) (X : Real), 0 ≤ B ∧ 1 ≤ X ∧
      ∀ x y : Real, X ≤ x → abs y ≤ 1 → abs (bipev Ls x y) ≤ B * powNat x M := by
  intro Ls
  induction Ls with
  | nil =>
      refine ⟨0, 0, 1, le_refl 0, le_refl 1, fun x _ _ _ => ?_⟩
      show abs (0 : Real) ≤ 0 * powNat x 0
      rw [abs_of_nonneg (le_refl (0 : Real))]
      have e : (0 : Real) * powNat x 0 = 0 := by mach_ring
      rw [e]; exact le_refl _
  | cons L Ls ih =>
      obtain ⟨B, M, X, hB, hX, hb⟩ := ih
      obtain ⟨C, N, XL, hC, hXL, hbL⟩ := pev_envelope L
      obtain ⟨W, hW, hWX, hWL⟩ := two_bounds' hX hXL
      refine ⟨B + C, max M N, W, add_nonneg hB hC, hW, fun x y hx hy => ?_⟩
      have hx1 : (1 : Real) ≤ x := le_trans hW hx
      have hsmall : abs (y * bipev Ls x y) ≤ B * powNat x M := by
        rw [abs_mul]
        have s1 : abs y * abs (bipev Ls x y) ≤ 1 * abs (bipev Ls x y) :=
          mul_le_mul_of_nonneg_right hy (abs_nonneg _)
        have e : (1 : Real) * abs (bipev Ls x y) = abs (bipev Ls x y) := by mach_ring
        rw [e] at s1
        exact le_trans s1 (hb x y (le_trans hWX hx) hy)
      have hhead := hbL x (le_trans hWL hx)
      have m1 : C * powNat x N ≤ C * powNat x (max M N) :=
        mul_le_mul_of_nonneg_left (powNat_mono_exp hx1 (Nat.le_max_right M N)) hC
      have m2 : B * powNat x M ≤ B * powNat x (max M N) :=
        mul_le_mul_of_nonneg_left (powNat_mono_exp hx1 (Nat.le_max_left M N)) hB
      show abs (pev L x + y * bipev Ls x y) ≤ (B + C) * powNat x (max M N)
      have e : C * powNat x (max M N) + B * powNat x (max M N)
          = (B + C) * powNat x (max M N) := by
        mach_mpoly [B, C, powNat x (max M N)]
      rw [← e]
      exact le_trans (abs_add _ _)
        (add_le_add_wit (le_trans hhead m1) (le_trans hsmall m2))

/-- **A super-polynomially small generator is not algebraic either.** `A` is the *constant*
coefficient here, split off by the `A :: Ls` shape. -/
theorem not_algebraic_of_dominated_by_exp {g : Real → Real} {r : Real} (hr : 0 < r)
    (hg : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → abs (g x) * exp (r * x) ≤ 1)
    (A : List Real) (Ls : List (List Real)) (hA : EvDom (pev A))
    (hrel : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → bipev (A :: Ls) x (g x) = 0) : False := by
  obtain ⟨Xg, hXg, hsm⟩ := hg
  obtain ⟨X₀, hX₀, hz⟩ := hrel
  obtain ⟨c, k, X₁, hc, hX₁, hdom⟩ := hA
  obtain ⟨B, M, X₂, hB, hX₂, hbd⟩ := bipev_bounded_envelope Ls
  obtain ⟨Y, hY, hY0, hY1⟩ := two_bounds' hXg hX₀
  obtain ⟨Z, hZ, hZY, hZ1⟩ := two_bounds' hY hX₁
  obtain ⟨X, hX, hXZ, hX2⟩ := two_bounds' hZ hX₂
  refine not_polyEnvelope_of_ge_exp_scaled hr
      ⟨1, le_refl 1, fun x _ => le_refl (exp (r * x))⟩
    ⟨B * (1 / c), M, X, mul_nonneg hB (le_of_lt (one_div_pos_of_pos hc)), hX, fun x hx => ?_⟩
  have hx1 : (1 : Real) ≤ x := le_trans hX hx
  have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx1
  have hex : (1 : Real) ≤ exp (r * x) :=
    le_trans (le_add_nonneg' (mul_nonneg (le_of_lt hr) hx0)) (one_add_le_exp (r * x))
  have hgs := hsm x (le_trans (le_trans (le_trans hY0 hZY) hXZ) hx)
  have hg1 : abs (g x) ≤ 1 := by
    refine le_trans ?_ hgs
    have v := mul_le_mul_of_nonneg_left hex (abs_nonneg (g x))
    have e : abs (g x) * 1 = abs (g x) := by mach_ring
    rw [e] at v; exact v
  -- the constant coefficient equals `−g · (rest)`
  have hrel0 : pev A x = -(g x * bipev Ls x (g x)) := by
    have h : pev A x + g x * bipev Ls x (g x) = 0 :=
      hz x (le_trans (le_trans (le_trans hY1 hZY) hXZ) hx)
    have v : pev A x + g x * bipev Ls x (g x) + -(g x * bipev Ls x (g x))
        = 0 + -(g x * bipev Ls x (g x)) := by rw [h]
    have el : pev A x + g x * bipev Ls x (g x) + -(g x * bipev Ls x (g x)) = pev A x := by
      mach_mpoly [pev A x, g x * bipev Ls x (g x)]
    have er : (0 : Real) + -(g x * bipev Ls x (g x)) = -(g x * bipev Ls x (g x)) := by
      mach_mpoly [g x * bipev Ls x (g x)]
    rw [el, er] at v; exact v
  have habs : abs (pev A x) = abs (g x) * abs (bipev Ls x (g x)) := by
    rw [hrel0, abs_neg, abs_mul]
  -- `c ≤ |A| = |g|·|rest| ≤ |g|·B x^M`
  have hcA : c ≤ abs (pev A x) := by
    refine le_trans ?_ (hdom x (le_trans (le_trans hZ1 hXZ) hx))
    have v := mul_le_mul_of_nonneg_left (one_le_powNat hx1 k) (le_of_lt hc)
    have e : c * 1 = c := by mach_ring
    rw [e] at v; exact v
  have hstep : c ≤ abs (g x) * (B * powNat x M) := by
    rw [habs] at hcA
    exact le_trans hcA (mul_le_mul_of_nonneg_left
      (hbd x (g x) (le_trans hX2 hx) hg1) (abs_nonneg _))
  -- multiply by `exp x` and use `|g|·exp x ≤ 1`
  have hBM : (0 : Real) ≤ B * powNat x M :=
    mul_nonneg hB (le_of_lt (powNat_pos (lt_of_lt_of_le zero_lt_one_ax hx1) M))
  have hfin : c * exp (r * x) ≤ B * powNat x M := by
    have v := mul_le_mul_of_nonneg_right hstep (le_of_lt (exp_pos (r * x)))
    have e : abs (g x) * (B * powNat x M) * exp (r * x)
        = abs (g x) * exp (r * x) * (B * powNat x M) := by
      mach_mpoly [abs (g x), B * powNat x M, exp (r * x)]
    rw [e] at v
    have w := mul_le_mul_of_nonneg_right hgs hBM
    have e2 : (1 : Real) * (B * powNat x M) = B * powNat x M := by mach_ring
    rw [e2] at w
    exact le_trans v w
  show abs (exp (r * x)) ≤ B * (1 / c) * powNat x M
  rw [abs_of_nonneg (le_of_lt (exp_pos (r * x)))]
  refine le_of_mul_le_mul_left' hc ?_
  have e : c * (B * (1 / c) * powNat x M) = B * powNat x M * (c * (1 / c)) := by
    mach_mpoly [c, B, powNat x M, (1 : Real) / c]
  rw [e, mul_inv c (ne_of_gt hc)]
  have e2 : B * powNat x M * 1 = B * powNat x M := by mach_ring
  rw [e2]; exact hfin

/-! ## Both unbounded regimes of a substituted germ -/

/-- **`S` growing at least like `x`**: `F(S(x)) ≥ exp(S(x)) ≥ exp x`, so the leading-coefficient
argument applies verbatim. -/
theorem FS_not_algebraic_of_ge_id {S : Real → Real}
    (hS : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → x ≤ S x)
    (A : List Real) (Ls : List (List Real)) (hA : EvDom (pev A))
    (hrel : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x →
      bipevLead A Ls x (Fbasis (S x)) = 0) : False := by
  obtain ⟨X, hX, hs⟩ := hS
  refine not_algebraic_of_dominates_exp zero_lt_one_ax ⟨X, hX, fun x hx => ?_⟩ A Ls hA hrel
  have hx1 : (1 : Real) ≤ x := le_trans hX hx
  have hone : (1 : Real) * x = x := by mach_ring
  rw [hone]
  have h1 : (1 : Real) ≤ S x := le_trans hx1 (hs x hx)
  have h2 : exp x ≤ exp (S x) := by
    rcases lt_total x (S x) with h | h | h
    · exact le_of_lt (exp_lt h)
    · exact le_of_eq (congrArg exp h)
    · exact absurd (lt_of_lt_of_le h (hs x hx)) (lt_irrefl_ax _)
  exact le_trans h2 (exp_le_Fbasis h1)

/-- **`S` decreasing at least like `−x`**: the totalised logarithm vanishes, `F(S) = exp S`, and
`|F(S(x))|·exp x = exp(S x + x) ≤ 1`. The lowest-power argument applies. -/
theorem FS_not_algebraic_of_le_negId {S : Real → Real}
    (hS : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → S x ≤ -x)
    (A : List Real) (Ls : List (List Real)) (hA : EvDom (pev A))
    (hrel : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x →
      bipev (A :: Ls) x (Fbasis (S x)) = 0) : False := by
  obtain ⟨X, hX, hs⟩ := hS
  refine not_algebraic_of_dominated_by_exp zero_lt_one_ax ⟨X, hX, fun x hx => ?_⟩ A Ls hA hrel
  have hx1 : (1 : Real) ≤ x := le_trans hX hx
  have hone : (1 : Real) * x = x := by mach_ring
  rw [hone]
  have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx1
  have hnx : -x < 0 := neg_of_neg_pos' (by
    have e : -(-x) = x := by mach_ring
    rw [e]; exact hx0)
  have hneg : S x < 0 := lt_of_le_of_lt (hs x hx) hnx
  have hsum : S x + x ≤ 0 := by
    have v := add_le_add_wit (hs x hx) (le_refl x)
    have e : -x + x = 0 := by mach_ring
    rw [e] at v; exact v
  rw [Fbasis_of_nonpos (le_of_lt hneg), abs_of_nonneg (le_of_lt (exp_pos _)), ← exp_add]
  rcases lt_total (S x + x) 0 with h | h | h
  · have hlt := exp_lt h
    rw [exp_zero] at hlt; exact le_of_lt hlt
  · rw [h, exp_zero]; exact le_refl _
  · exact absurd (lt_of_lt_of_le h hsum) (lt_irrefl_ax _)

/-! ## Correction: `x ≤ S x` is a sufficient condition, not "unbounded"

The two corollaries above take `x ≤ S x` and `S x ≤ −x`. **Those are not the unbounded regimes.**
`S(x) = x/2` tends to `+∞` and satisfies neither. A rational germ tending to `±∞` behaves like
`a·xᵏ` with `k ≥ 1`, so what it does satisfy is `c·x ≤ S x` for some `c > 0`, which is strictly
weaker whenever `c < 1`.

With the rescaled envelope that gap closes, at any positive rate. -/

/-- **`S` growing at least linearly, at any positive rate.** -/
theorem FS_not_algebraic_of_ge_linear {S : Real → Real} {c : Real} (hc : 0 < c)
    (hS : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → c * x ≤ S x)
    (A : List Real) (Ls : List (List Real)) (hA : EvDom (pev A))
    (hrel : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x →
      bipevLead A Ls x (Fbasis (S x)) = 0) : False := by
  obtain ⟨X, hX, hs⟩ := hS
  obtain ⟨W, hW, hWX, hWc⟩ := two_bounds' hX
    (show (1 : Real) ≤ 1 + abs (1 / c) from le_add_nonneg' (abs_nonneg _))
  refine not_algebraic_of_dominates_exp hc ⟨W, hW, fun x hx => ?_⟩ A Ls hA hrel
  have hcx : c * x ≤ S x := hs x (le_trans hWX hx)
  have hxc : 1 / c ≤ x := by
    refine le_trans (le_trans (le_abs_self _) ?_) (le_trans hWc hx)
    have v := add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl (abs (1 / c)))
    have e : (0 : Real) + abs (1 / c) = abs (1 / c) := by mach_ring
    rw [e] at v; exact v
  have h1 : (1 : Real) ≤ S x := by
    refine le_trans ?_ hcx
    have v := mul_le_mul_of_nonneg_left hxc (le_of_lt hc)
    rw [mul_inv c (ne_of_gt hc)] at v; exact v
  have h2 : exp (c * x) ≤ exp (S x) := by
    rcases lt_total (c * x) (S x) with h | h | h
    · exact le_of_lt (exp_lt h)
    · exact le_of_eq (congrArg exp h)
    · exact absurd (lt_of_lt_of_le h hcx) (lt_irrefl_ax _)
  exact le_trans h2 (exp_le_Fbasis h1)

/-- **`S` decreasing at least linearly, at any positive rate.** -/
theorem FS_not_algebraic_of_le_linear {S : Real → Real} {c : Real} (hc : 0 < c)
    (hS : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → S x ≤ -(c * x))
    (A : List Real) (Ls : List (List Real)) (hA : EvDom (pev A))
    (hrel : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x →
      bipev (A :: Ls) x (Fbasis (S x)) = 0) : False := by
  obtain ⟨X, hX, hs⟩ := hS
  refine not_algebraic_of_dominated_by_exp hc ⟨X, hX, fun x hx => ?_⟩ A Ls hA hrel
  have hx1 : (1 : Real) ≤ x := le_trans hX hx
  have hcxpos : (0 : Real) < c * x := mul_pos hc (lt_of_lt_of_le zero_lt_one_ax hx1)
  have hneg : S x < 0 := lt_of_le_of_lt (hs x hx) (neg_of_neg_pos' (by
    have e : -(-(c * x)) = c * x := by mach_ring
    rw [e]; exact hcxpos))
  have hsum : S x + c * x ≤ 0 := by
    have v := add_le_add_wit (hs x hx) (le_refl (c * x))
    have e : -(c * x) + c * x = 0 := by mach_ring
    rw [e] at v; exact v
  rw [Fbasis_of_nonpos (le_of_lt hneg), abs_of_nonneg (le_of_lt (exp_pos _)), ← exp_add]
  rcases lt_total (S x + c * x) 0 with h | h | h
  · have hlt := exp_lt h
    rw [exp_zero] at hlt; exact le_of_lt hlt
  · rw [h, exp_zero]; exact le_refl _
  · exact absurd (lt_of_lt_of_le h hsum) (lt_irrefl_ax _)

/-! ## The constant exception is real, not defensive

Nonconstancy is not a hypothesis added out of caution. For constant `S` the statement is **false**,
and one line exhibits it: `F(0) = 1`, so `Y − 1` vanishes on it with leading coefficient `1`. A
constant germ collapses the one-query expression back into `C₀`, where a polynomial relation is
exactly what one should expect. -/

theorem constant_germ_is_algebraic :
    ∃ (A : List Real) (Ls : List (List Real)),
      EvDom (pev A) ∧ ∀ x : Real, bipevLead A Ls x (Fbasis 0) = 0 := by
  refine ⟨[1], [[0 - 1]], ⟨1, 0, 1, zero_lt_one_ax, le_refl 1, fun x _ => ?_⟩, fun x => ?_⟩
  · show (1 : Real) * powNat x 0 ≤ abs (pev [(1 : Real)] x)
    have e1 : pev [(1 : Real)] x = 1 := by show (1 : Real) + x * 0 = 1; mach_ring
    have e2 : (1 : Real) * powNat x 0 = 1 := by show (1 : Real) * 1 = 1; mach_ring
    rw [e1, e2, abs_of_nonneg (le_of_lt zero_lt_one_ax)]
    exact le_refl _
  · show pev [(1 : Real)] x * powNat (Fbasis 0) 1 + bipev [[(0 : Real) - 1]] x (Fbasis 0) = 0
    rw [Fbasis_zero]
    show (1 + x * 0) * (1 * 1) + ((0 - 1) + x * 0 + 1 * 0) = 0
    mach_mpoly [x]

end MachLib
