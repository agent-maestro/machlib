import MachLib.EMLDepthTameness
import MachLib.EMLZeroQueryBarrier
import MachLib.Forge
import MachLib.EMLFTranscendence
import MachLib.DivisionError
import MachLib.EMLGermSign

/-!
# `exp` beats every power, eventually — and so does `Fbasis` of a growing argument

## The gap

The corpus had two growth lemmas and neither was the one a polynomial comparison needs:

* `exp_beats_powNat` exhibits **one point** where `x^(k+2) < exp x`;
* `exp_beats_linear_eventually` is the ∀-form for a **line**.

A threshold past which `exp` dominates a POWER was missing, so every argument against a polynomial
had to stop at linear.

## The route, which needs no induction and no division

For `x > 0`,

    powNat x N = powNat (exp (log x)) N = exp (natMul N (log x))

by `exp_natMul` and `exp_log` — a power of `x` **is** an exponential of a multiple of `log x`. So
`exp` beating a POWER at `x` is `exp` beating a LINE at `log x`, which is exactly
`exp_beats_linear_eventually`. `exp_beats_powNat`'s own proof hints at this by working at the point
`exp w`; read backwards it gives the ∀-form directly.

A leading constant costs one extra power rather than a sharper estimate: `K·yᴺ ≤ y·yᴺ = yᴺ⁺¹ ≤ exp y`
once `y ≥ K`.

## What it is for

`fbasis_beats_powNat_of_linear_growth` is the engine for the **growing** branch of
`RatGermTrichotomy` in the degree-1 fragment recorded in `EMLOneQueryMobius`: if the query argument
`w` eventually exceeds `c·x`, then `Fbasis ∘ w` outruns every `C·xᴺ`, so it cannot be a polynomial —
nor, after dividing by a polynomial bounded away from zero, a rational function.

That leaves the trichotomy's **bounded** branch, which is where the genuine transcendence lives:
both sides stay bounded, asymptotics say nothing, and exact equality has to be excluded rather than
merely made implausible. Nothing here touches it, and the fragment stays open.
-/

namespace MachLib
open Real

/-- **`exp` eventually dominates every power** — the ∀-form the corpus lacked.

`exp_beats_powNat` exhibits ONE point where `x^(k+2) < exp x`; `exp_beats_linear_eventually` is the
∀-form for a LINE. Neither gives a threshold past which `exp` beats a POWER, which is what any
growth argument against a polynomial needs.

The route is the one `exp_beats_powNat`'s own proof hints at, read backwards: for `x > 0`,

    powNat x N = powNat (exp (log x)) N = exp (natMul N (log x))

so a power of `x` IS an exponential of a multiple of `log x` — and `exp` beating a line at `log x`
is exactly `exp_beats_linear_eventually`. No division, no induction on `N`. -/
theorem exp_beats_powNat_eventually (N : Nat) :
    ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → powNat x N ≤ exp x := by
  obtain ⟨X₀, hX₀, hlin⟩ := exp_beats_linear_eventually (natMul N 1)
  refine ⟨exp X₀, ?_, fun x hx => ?_⟩
  · have h : exp 0 ≤ exp X₀ := exp_monotone (le_trans (le_of_lt zero_lt_one_ax) hX₀)
    rw [exp_zero] at h; exact h
  · have hxpos : (0 : Real) < x := lt_of_lt_of_le (exp_pos X₀) hx
    have hlogx : X₀ ≤ log x := by
      have h := log_le_log (exp_pos X₀) hx
      rw [log_exp] at h; exact h
    have hle : natMul N 1 * log x ≤ x := by
      have h := hlin (log x) hlogx
      rw [exp_log hxpos] at h; exact h
    have hpow : powNat x N = exp (natMul N (log x)) := by
      rw [exp_natMul (log x) N, exp_log hxpos]
    rw [hpow, natMul_eq (log x) N]
    exact exp_monotone hle

/-- Two lower bounds, one ray. (`two_bounds'` in the corpus is `private`.) -/
private theorem bnd2 {A B : Real} (hA : 1 ≤ A) (hB : 1 ≤ B) :
    ∃ X : Real, 1 ≤ X ∧ A ≤ X ∧ B ≤ X := by
  rcases lt_total A B with h | h | h
  · exact ⟨B, hB, le_of_lt h, le_refl B⟩
  · exact ⟨B, hB, le_of_eq h, le_refl B⟩
  · exact ⟨A, hA, le_refl A, le_of_lt h⟩

/-- Raise any real to at least 1, keeping it as an upper bound. -/
private theorem ge_one_and (v : Real) : ∃ M : Real, 1 ≤ M ∧ v ≤ M := by
  rcases lt_total v 1 with h | h | h
  · exact ⟨1, le_refl 1, le_of_lt h⟩
  · exact ⟨1, le_refl 1, le_of_eq h⟩
  · exact ⟨v, le_of_lt h, le_refl v⟩

/-- With a constant in front. `K · yᴺ ≤ y · yᴺ = yᴺ⁺¹ ≤ exp y` once `y ≥ K`, so the constant is
absorbed by one extra power rather than by a sharper estimate. -/
theorem const_mul_powNat_le_exp (K : Real) (N : Nat) :
    ∃ Y : Real, 1 ≤ Y ∧ ∀ y : Real, Y ≤ y → K * powNat y N ≤ exp y := by
  obtain ⟨Y₀, hY₀, hbeat⟩ := exp_beats_powNat_eventually (N + 1)
  -- a ray past `Y₀` and past `K` (and past 1, so `powNat` is positive there)
  obtain ⟨M, hM, hKM⟩ := ge_one_and K
  obtain ⟨Y, hY, hY0, hMY⟩ := bnd2 hY₀ hM
  refine ⟨Y, hY, fun y hy => ?_⟩
  have hy1 : (1 : Real) ≤ y := le_trans hY hy
  have hKy : K ≤ y := le_trans hKM (le_trans hMY hy)
  have hpn : (0 : Real) ≤ powNat y N :=
    le_of_lt (powNat_pos (lt_of_lt_of_le zero_lt_one_ax hy1) N)
  have step : K * powNat y N ≤ y * powNat y N := mul_le_mul_of_nonneg_right hKy hpn
  have e : y * powNat y N = powNat y (N + 1) := rfl
  rw [e] at step
  exact le_trans step (hbeat y (le_trans hY0 hy))

/-- **`Fbasis` of a linearly growing argument beats every polynomial.**

The engine for the GROWING branch of `RatGermTrichotomy` in the degree-1 fragment: if the query
argument `w` eventually exceeds `c·x` for some `c > 0`, then `Fbasis ∘ w` outruns `C·xᴺ` for every
`C` and `N`, so it cannot be a polynomial — nor, after dividing by a polynomial bounded away from
zero, a rational function.

`Fbasis y = exp y + log y ≥ exp y` once `y ≥ 1`, and the constant `C` and slope `c` are absorbed by
`const_mul_powNat_le_exp` at `K = C / cᴺ` evaluated at `c·x`. -/
theorem fbasis_beats_powNat_of_linear_growth
    {w : Real → Real} {c X : Real} (hc : 0 < c) (hX : 1 ≤ X)
    (hw : ∀ x : Real, X ≤ x → c * x ≤ w x) (C : Real) (N : Nat) :
    ∃ Y : Real, 1 ≤ Y ∧ ∀ x : Real, Y ≤ x → C * powNat x N ≤ Fbasis (w x) := by
  have hcN : (0 : Real) < powNat c N := powNat_pos hc N
  have hcNne : powNat c N ≠ 0 := fun h => lt_irrefl_ax 0 (h ▸ hcN)
  obtain ⟨Y₁, hY₁, hbeat⟩ := const_mul_powNat_le_exp (C / powNat c N) N
  -- a threshold past `X`, and large enough that `c * x` clears both `Y₁` and `1`
  obtain ⟨T, hT, hTY₁, hT1⟩ := bnd2 hY₁ (le_refl (1 : Real))
  obtain ⟨D, hD, hTcD⟩ := ge_one_and (T / c)
  obtain ⟨Y, hY, hYX, hYT⟩ := bnd2 hX hD
  refine ⟨Y, hY, fun x hx => ?_⟩
  have hx1 : (1 : Real) ≤ x := le_trans hY hx
  have hxX : X ≤ x := le_trans hYX hx
  have hTcx : T ≤ c * x := by
    have hstep : T / c ≤ x := le_trans hTcD (le_trans hYT hx)
    have u := mul_le_mul_of_nonneg_left hstep (le_of_lt hc)
    have e : c * (T / c) = T := mul_div_cancel_left (fun h => lt_irrefl_ax 0 (h ▸ hc))
    rw [e] at u; exact u
  have hcx1 : (1 : Real) ≤ c * x := le_trans hT1 hTcx
  have hwx1 : (1 : Real) ≤ w x := le_trans hcx1 (hw x hxX)
  -- C·xᴺ = (C/cᴺ)·(c·x)ᴺ  ≤  exp (c·x)  ≤  exp (w x)  ≤  Fbasis (w x)
  have hrw : C * powNat x N = (C / powNat c N) * powNat (c * x) N := by
    rw [powNat_mul]
    have e : C / powNat c N * (powNat c N * powNat x N)
           = (C / powNat c N * powNat c N) * powNat x N := by
      mach_mpoly [C / powNat c N, powNat c N, powNat x N]
    rw [e, div_mul_cancel hcNne]
  rw [hrw]
  refine le_trans (hbeat (c * x) (le_trans hTY₁ hTcx)) ?_
  exact le_trans (exp_monotone (hw x hxX)) (Fbasis_ge_exp_of_one_le hwx1).1

end MachLib