import MachLib.Limits

/-!
# `rⁿ → 0` for every `r ∈ [0,1)` — and the cube's boundary shell

`Limits.lean` proved `(1/2)ⁿ → 0` via `npow_half_mul_succ_le`. That was enough for `bcRatio`, whose
recurrence hands you a factor of exactly `1/2`. It is **not** enough for the boundary-shell
probability, where the ratio is `1 − ε` for an arbitrary `ε ∈ (0,1)`, so the general lemma is the
piece that has to exist.

This is the first genuinely **mathematical** item in the `HighDimensional` audit. The previous three
passes retired *vocabulary* — placeholder axioms whose referents already existed in Forge. These two
do not have that character: `cubeBoundaryShellProbability_tends_one` is **concentration of measure**,
and it needs a proof rather than a definition.

## The Bernoulli step, stated without division

The textbook route is `r = 1/(1+h)`, then `(1+h)ⁿ ≥ 1 + nh` and `rⁿ ≤ 1/(1+nh) → 0`. Carrying that
into MachLib would drag `divR` and `mul_inv` through every downstream statement.

`npow_mul_bernoulli` instead takes **`r·(1+h) = 1` as a hypothesis**, which says the same thing and
mentions no division at all:

```
    r^n · (1 + n·h) ≤ 1
```

The induction is three lines of algebra and one inequality:

```
  r^(n+1)·(1+(n+1)h) = r^n · [r·(1 + (n+1)h)]
                     = r^n · [r(1+h) + r·n·h]
                     = r^n · [1 + r·n·h]
                    ≤ r^n · [1 + n·h]          (r ≤ 1, n·h ≥ 0)
                    ≤ 1                        (induction hypothesis)
```

The caller supplies `h` — for `0 < r < 1` that is `(1−r)/r`, one division performed **once, at the
call site**, exactly as `ekf2_gain_abs_le` keeps `sqrt` out of its statement.

`sorryAx`-free, zero new axioms.
-/

namespace MachLib.Real

private theorem half_pos' : (0 : Real) < 1 + 1 := add_pos one_pos one_pos

/-- Hoisted: `mach_mpoly`'s atom list is elaborated OUTSIDE the tactic block, so variables bound by
an `intro` are not in scope there. Stating these generically also keeps each goal small — the
documented failure mode is size, not difficulty. -/
private theorem eps_distrib_id (a b c : Real) : a * (1 + b * c) - b * (a * c) = a := by
  mach_mpoly [a, b, c]

private theorem mul_one_add_id (a b : Real) : a * (1 + b) = a + b * a := by
  mach_mpoly [a, b]

/-- **Bernoulli, division-free.** With `r·(1+h) = 1`, `r ≤ 1` and `h ≥ 0`, the product
`rⁿ·(1+n·h)` never exceeds 1. This is the whole content of geometric decay. -/
theorem npow_mul_bernoulli {r h : Real} (hr : 0 ≤ r) (hr1 : r ≤ 1) (hh : 0 ≤ h)
    (hrh : r * (1 + h) = 1) :
    ∀ n : Nat, npow n r * (1 + natCast n * h) ≤ 1
  | 0 => by
      rw [show npow 0 r = (1 : Real) from rfl, natCast_zero,
          show (1 : Real) * (1 + (0 : Real) * h) = 1 from by mach_ring]
      exact le_refl 1
  | n + 1 => by
      have ih := npow_mul_bernoulli hr hr1 hh hrh n
      have hnh : 0 ≤ natCast n * h := mul_nonneg (natCast_nonneg n) hh
      -- r·(1 + (n+1)h) = r(1+h) + r·n·h = 1 + r·n·h
      have hstep : npow (n + 1) r * (1 + natCast (n + 1) * h)
          = npow n r * (r * (1 + h) + r * (natCast n * h)) := by
        rw [npow_succ, natCast_succ]
        mach_mpoly [npow n r, r, h, natCast n]
      rw [hstep, hrh]
      -- 1 + r·n·h ≤ 1 + n·h, since r ≤ 1
      have hcmp : (1 : Real) + r * (natCast n * h) ≤ 1 + natCast n * h := by
        refine add_le_add_left ?_ 1
        have := mul_le_mul_of_nonneg_right hr1 hnh
        rwa [one_mul_thm] at this
      exact le_trans (mul_le_mul_of_nonneg_left hcmp (npow_nonneg hr n)) ih

/-- **`rⁿ → 0` for `0 ≤ r < 1`.** The general form of `npow_half_tendsto_zero`.

`h` is supplied by the caller as `(1−r)/r` — the one division, taken once, outside the statement. -/
theorem npow_tendsto_zero {r h : Real} (hr : 0 < r) (hr1 : r ≤ 1) (hh : 0 < h)
    (hrh : r * (1 + h) = 1) :
    TendstoTo (fun n => npow n r) 0 := by
  intro ε hε
  obtain ⟨m, hm⟩ := archimedean (1 / (ε * h))
  refine ⟨m, fun n hn => ?_⟩
  have hpow_nonneg : 0 ≤ npow n r := npow_nonneg (le_of_lt hr) n
  rw [show npow n r - 0 = npow n r from by mach_ring, abs_of_nonneg hpow_nonneg]
  -- rⁿ·(1 + n·h) ≤ 1 and 1 ≤ ε·(1 + n·h) once n ≥ m, so rⁿ ≤ ε
  have hb := npow_mul_bernoulli (le_of_lt hr) hr1 (le_of_lt hh) hrh n
  have hden : (0 : Real) < 1 + natCast n * h :=
    lt_of_lt_of_le one_pos (le_add_of_nonneg_right (mul_nonneg (natCast_nonneg n) (le_of_lt hh)))
  refine le_of_mul_le_mul_right_pos ?_ hden
  refine le_trans hb ?_
  -- 1 ≤ ε·(1 + n·h): from archimedean, 1/(ε·h) < m ≤ n
  have hmn : natCast m ≤ natCast n := natCast_le_of_le hn
  have hεh : (0 : Real) < ε * h := mul_pos hε hh
  have h1 : (1 : Real) / (ε * h) < natCast n := lt_of_lt_of_le hm hmn
  have h2 : (1 : Real) < natCast n * (ε * h) := by
    have := mul_lt_mul_of_pos_right h1 hεh
    rwa [div_mul_cancel (ne_of_gt hεh)] at this
  have h3 : natCast n * (ε * h) ≤ ε * (1 + natCast n * h) := by
    have := eps_distrib_id ε (natCast n) h
    exact le_of_sub_nonneg (by rw [this]; exact le_of_lt hε)
  exact le_trans (le_of_lt h2) h3

/-! ## The cube's boundary shell

For a unit cube in `d` dimensions, the fraction of the volume lying **within `ε` of the boundary**
is `1 − (1−ε)^d`: the complement is the concentric cube of side `1−ε`. As `d → ∞` that tends to 1 —
**essentially all of a high-dimensional cube is near its surface**, which is the fact the
`HighDimensional` program is built on. -/

/-- Volume fraction of the `ε`-boundary shell of a unit `d`-cube. -/
noncomputable def cubeShell (eps : Real) (d : Nat) : Real :=
  1 - npow d (1 - eps)

/-- **The shell fills the cube.** `cubeShell ε d → 1` for every fixed `ε ∈ (0,1)`. -/
theorem cubeShell_tendsto_one {eps : Real} (h0 : 0 < eps) (h1 : eps < 1) :
    TendstoTo (cubeShell eps) 1 := by
  have hr : 0 < 1 - eps := sub_pos_of_lt h1
  have hr1 : 1 - eps ≤ 1 := by
    refine le_of_sub_nonneg ?_
    rw [show (1 : Real) - (1 - eps) = eps from by mach_ring]
    exact le_of_lt h0
  -- h = eps/(1-eps), the single division, taken here
  have hh : 0 < eps / (1 - eps) := div_pos_of_pos_pos h0 hr
  have hrh : (1 - eps) * (1 + eps / (1 - eps)) = 1 := by
    have hcancel : eps / (1 - eps) * (1 - eps) = eps := div_mul_cancel (ne_of_gt hr)
    have hexp := mul_one_add_id (1 - eps) (eps / (1 - eps))
    rw [hexp, hcancel]
    mach_ring
  have hz := npow_tendsto_zero hr hr1 hh hrh
  intro ε hε
  obtain ⟨N, hN⟩ := hz ε hε
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn
  rw [show npow n (1 - eps) - 0 = npow n (1 - eps) from by mach_ring] at this
  rw [show cubeShell eps n - 1 = -(npow n (1 - eps)) from by
        rw [cubeShell]; mach_ring, abs_neg]
  exact this

end MachLib.Real
