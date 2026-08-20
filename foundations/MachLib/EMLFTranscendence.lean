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

/-! ## `F` is not algebraic over the polynomial coefficients -/

/-- **No nonzero polynomial in `F(x)` with polynomial coefficients vanishes on a tail.**

The leading coefficient is required to be eventually dominating — which, by `pev_dichotomy`, is the
same as not being eventually zero, i.e. the relation is genuinely of degree `Ls.length`. -/
theorem Fbasis_not_algebraic (A : List Real) (Ls : List (List Real)) (hA : EvDom (pev A))
    (hrel : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → bipevLead A Ls x (Fbasis x) = 0) : False := by
  obtain ⟨X₀, hX₀, hz⟩ := hrel
  obtain ⟨c, k, X₁, hc, hX₁, hdom⟩ := hA
  obtain ⟨B, M, X₂, hB, hX₂, hdeg⟩ := bipev_degree_drop Ls
  obtain ⟨Y, hY, hY0, hY1⟩ := two_bounds' hX₀ hX₁
  obtain ⟨X, hX, hXY, hX2⟩ := two_bounds' hY hX₂
  refine not_polyEnvelope_Fbasis ⟨B * (1 / c), M, X, mul_nonneg hB
    (le_of_lt (one_div_pos_of_pos hc)), hX, fun x hx => ?_⟩
  have hx1 : (1 : Real) ≤ x := le_trans hX hx
  have hx0 : (0 : Real) ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx1
  have hF1 : (1 : Real) ≤ Fbasis x := by
    refine le_trans ?_ (exp_le_Fbasis hx1)
    have h := one_add_le_exp x
    exact le_trans (le_add_nonneg' hx0) h
  have hF0 : (0 : Real) < Fbasis x := lt_of_lt_of_le zero_lt_one_ax hF1
  have hpow : (0 : Real) < powNat (Fbasis x) Ls.length := powNat_pos hF0 _
  -- the relation, in absolute value
  have hrel0 : pev A x * powNat (Fbasis x) Ls.length = -(bipev Ls x (Fbasis x)) := by
    have h : pev A x * powNat (Fbasis x) Ls.length + bipev Ls x (Fbasis x) = 0 :=
      hz x (le_trans (le_trans hY0 hXY) hx)
    have v : pev A x * powNat (Fbasis x) Ls.length + bipev Ls x (Fbasis x)
        + -(bipev Ls x (Fbasis x)) = 0 + -(bipev Ls x (Fbasis x)) := by rw [h]
    have el : pev A x * powNat (Fbasis x) Ls.length + bipev Ls x (Fbasis x)
        + -(bipev Ls x (Fbasis x)) = pev A x * powNat (Fbasis x) Ls.length := by
      mach_mpoly [pev A x * powNat (Fbasis x) Ls.length, bipev Ls x (Fbasis x)]
    have er : (0 : Real) + -(bipev Ls x (Fbasis x)) = -(bipev Ls x (Fbasis x)) := by
      mach_mpoly [bipev Ls x (Fbasis x)]
    rw [el, er] at v; exact v
  have habs : abs (pev A x) * powNat (Fbasis x) Ls.length = abs (bipev Ls x (Fbasis x)) := by
    have h : abs (pev A x * powNat (Fbasis x) Ls.length) = abs (bipev Ls x (Fbasis x)) := by
      rw [hrel0, abs_neg]
    rw [abs_mul, abs_of_nonneg (le_of_lt hpow)] at h; exact h
  -- multiply by `F` and use the degree drop
  have hkey : powNat (Fbasis x) Ls.length * (abs (pev A x) * Fbasis x)
      ≤ powNat (Fbasis x) Ls.length * (B * powNat x M) := by
    have hd := hdeg x (Fbasis x) (le_trans hX2 hx) hF1
    rw [← habs] at hd
    have e1 : Fbasis x * (abs (pev A x) * powNat (Fbasis x) Ls.length)
        = powNat (Fbasis x) Ls.length * (abs (pev A x) * Fbasis x) := by
      mach_mpoly [Fbasis x, abs (pev A x), powNat (Fbasis x) Ls.length]
    have e2 : B * powNat x M * powNat (Fbasis x) Ls.length
        = powNat (Fbasis x) Ls.length * (B * powNat x M) := by
      mach_mpoly [B, powNat x M, powNat (Fbasis x) Ls.length]
    rw [e1, e2] at hd; exact hd
  have hcancel : abs (pev A x) * Fbasis x ≤ B * powNat x M :=
    le_of_mul_le_mul_left' hpow hkey
  -- the leading coefficient is bounded below by `c`
  have hcA : c ≤ abs (pev A x) := by
    refine le_trans ?_ (hdom x (le_trans (le_trans hY1 hXY) hx))
    have v := mul_le_mul_of_nonneg_left (one_le_powNat hx1 k) (le_of_lt hc)
    have e : c * 1 = c := by mach_ring
    rw [e] at v; exact v
  have hstep : c * Fbasis x ≤ B * powNat x M :=
    le_trans (mul_le_mul_of_nonneg_right hcA (le_of_lt hF0)) hcancel
  -- divide by `c`
  show abs (Fbasis x) ≤ B * (1 / c) * powNat x M
  rw [abs_of_nonneg (le_of_lt hF0)]
  refine le_of_mul_le_mul_left' hc ?_
  have e : c * (B * (1 / c) * powNat x M) = B * powNat x M * (c * (1 / c)) := by
    mach_mpoly [c, B, powNat x M, (1 : Real) / c]
  rw [e, mul_inv c (ne_of_gt hc)]
  have e2 : B * powNat x M * 1 = B * powNat x M := by mach_ring
  rw [e2]; exact hstep

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

/-! ## Scope, and what it does not give

This is the `S = x` case. Whether it transports along a nonconstant rational substitution — `F(S(x))`
transcendental over the polynomial coefficients for every nonconstant rational germ `S` — is a
separate question and is **not** assumed here. The abstract reason to expect it (`ℝ(S(x)) ⊆ ℝ(x)` is
algebraic for nonconstant rational `S`, so algebraicity would push down) is a statement about
function fields, and these objects are eventual real functions, not yet elements of one.

Two branches of that question look reachable with the machinery already present, and one does not:

* `S → +∞`: `F(S) ≥ exp S` with `S` of rational power scale, so the same polynomial-envelope
  contradiction should apply.
* `S → −∞`: the totalised logarithm vanishes and `F(S) = exp S` is super-polynomially *small* — a
  lowest-power dual of the same argument.
* `S → c` finite: `F(S)` is **bounded**, so growth cannot distinguish it from an algebraic function.
  This is where function-field or differential-algebra infrastructure would actually be needed.

Also worth keeping separate: even the full composed statement would give the **normal form** for `C₁`
(cancellation is algebraically forced), *not* the lower bound `exp ∉ C₁`. The latter asks about an
algebraic relation over `ℝ(x, exp x)`, whose coefficient field already contains `exp` — a strictly
stronger question. -/

end MachLib
