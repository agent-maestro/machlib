import MachLib.Geometry.Apollonius.Examples

/-!
# The flagship coordinates, checked

The exhibit at `monogate.org/proofs/apollonius` carried, per solution, a row reading
**Lean-checked point — NOT YET**, under the disclaimer:

> **NOT PROVED — the eight coordinates below.** COMPUTED here in exact arithmetic and verified to
> have zero tangency residuals; NOT checked in Lean. MachLib proves the COUNT and its structure,
> not these particular coordinates.

This file closes that for the flagship, `d = 4`, `ρ = 1` — three unit circles at `(0,0)`, `(4,0)`,
`(0,4)`. **All eight** solutions are stated as an explicit centre and radius in closed form and
discharged against `Circle.lean`'s **geometric** predicates `TangentExt` / `TangentInt`, not against
the algebraic enumeration equation. Twenty-four tangencies, zero residual, symbolically.

## The one technique that made it possible

Six of the eight have irrational centres with denominators, and written naively every identity dies
in `Lean.Meta.acLt` — the associative-commutative term ordering `simp` uses — because distribution
generates nested `(1+1)` constant trees. Raising `maxHeartbeats` to four million does not help; the
growth is in the ordering, not the arithmetic.

**Compress the constant into the variable.** Instead of `3 + 3h` with `h = √2/2`, write `3 + v` with
`v = 3h` and carry the single fact `2v² = 9`. The `3` vanishes from the distribution, no constant
above `4` survives, and the identity closes immediately. Same move for the `√21` quartet with
`κ = √21/3` and `3κ² = 7`.

Two earlier diagnoses recorded here were wrong and are corrected: the limit is **not** coefficient
magnitude (solutions 1 and 8 close with `8`, and an attempt failed with `18` written in five nodes),
and it is **not** that constants are trees per se — constants that are never distributed, like the
`4` of the centre separation, cost nothing. It is `acLt` on nested constant trees *under
distribution*, and the fix is to keep them out of the distribution.

## What this costs, stated plainly

`sqrt` enters the footprint here, and it did not before. That is not a breach of the firewall the
rest of the development maintains — `tangentExt_iff` and `certified_tangencies` remain sqrt-free,
and a *candidate* is still identified by a root certificate rather than a radical. But naming a
particular point requires writing its radius down, and these radii are irrational. The dependency is
localised to this module deliberately, so that `#print axioms` on anything else still shows the
firewall intact.

Every use of `sqrt` here fires `sqrt_sq_nonneg` on a manifestly nonnegative argument, so the
totalisation branch `sqrt_neg_zero` is unreachable and no junk value can enter a coordinate.
-/

namespace MachLib
namespace Geometry
namespace Apollonius
namespace Coordinates

open Real
open SymmetricTriple
open Examples

/-! ## Two irrationals, and the only facts needed about them -/

/-- `√2`. -/
noncomputable def rt2 : Real := sqrt (1 + 1)

theorem rt2_sq : rt2 * rt2 = 1 + 1 := sqrt_two_sq

theorem rt2_nonneg : 0 ≤ rt2 := sqrt_nonneg _

/-- `1 < √2`. Needed for radius positivity, and proved from the square rather than from any
ordering axiom about `sqrt`: if `√2 ≤ 1` then `2 = √2·√2 ≤ √2 ≤ 1`. -/
theorem one_lt_rt2 : 1 < rt2 := by
  have hlt : (1 : Real) < 1 + 1 := by
    have v := add_lt_add_left zero_lt_one_ax 1
    have l : (1 : Real) + 0 = 1 := by mach_ring
    rw [l] at v; exact v
  have key : ¬ (rt2 ≤ 1) := by
    intro hle
    have h1 : rt2 * rt2 ≤ rt2 * 1 := mul_le_mul_of_nonneg_left hle rt2_nonneg
    have e : rt2 * 1 = rt2 := by mach_ring
    rw [e, rt2_sq] at h1
    exact lt_irrefl_ax _ (lt_of_lt_of_le hlt (le_trans h1 hle))
  rcases lt_total 1 rt2 with h | h | h
  · exact h
  · exact absurd (le_of_eq h.symm) key
  · exact absurd (le_of_lt h) key

/-! ## The flagship, concretely

`d = 4`, `ρ = 1`: unit circles at `(0,0)`, `(4,0)`, `(0,4)`. -/

private theorem h1pos : (0 : Real) < 1 := zero_lt_one_ax

/-- `A = (0,0,1)`. -/ noncomputable def A : Circle := cA flagRho h1pos
/-- `B = (4,0,1)`. -/ noncomputable def B : Circle := cB flagD flagRho h1pos
/-- `C = (0,4,1)`. -/ noncomputable def C : Circle := cC flagD flagRho h1pos

/-! ### Solution 1 — the outer Soddy circle, `(outer, outer, outer)`

Centre `(2, 2)`, radius `2√2 − 1`. Externally tangent to all three. -/

theorem sol_ooo_pos : (0 : Real) < (1 + 1) * rt2 - 1 := by
  have h : (1 : Real) * 1 < (1 + 1) * rt2 := by
    have hstep : (1 : Real) * 1 < (1 + 1) * 1 := by
      have v := add_lt_add_left zero_lt_one_ax 1
      have l : (1 : Real) + 0 = 1 := by mach_ring
      rw [l] at v
      have e1 : (1 : Real) * 1 = 1 := by mach_ring
      have e2 : (1 : Real) + 1 = (1 + 1) * 1 := by mach_ring
      rw [e1, ← e2]; exact v
    refine lt_of_lt_of_le hstep ?_
    refine mul_le_mul_of_nonneg_left (le_of_lt one_lt_rt2) ?_
    exact le_of_lt (add_pos zero_lt_one_ax zero_lt_one_ax)
  have e : (1 : Real) * 1 = 1 := by mach_ring
  rw [e] at h
  have v := add_lt_add_left h (-1)
  have l : (-1 : Real) + 1 = 0 := by mach_ring
  have r : (-1 : Real) + (1 + 1) * rt2 = (1 + 1) * rt2 - 1 := by mach_ring
  rw [l, r] at v; exact v

/-- The outer Soddy circle of the flagship. -/
noncomputable def solOOO : Circle := ⟨1 + 1, 1 + 1, (1 + 1) * rt2 - 1, sol_ooo_pos⟩

/-- The squared sum-of-radii, reduced. `mach_mpoly` treats `rt2` as an opaque atom — which is
correct, it is one — so the square has to be routed through `rt2_sq` explicitly rather than hoped
for. Every tangency below is then the same arithmetic. -/
private theorem ooo_radius_sq :
    ((1 + 1) * rt2 - 1 + 1) * ((1 + 1) * rt2 - 1 + 1) = (1 + 1) * (1 + 1) * (1 + 1) := by
  have e : ((1 + 1) * rt2 - 1 + 1) * ((1 + 1) * rt2 - 1 + 1) = (1 + 1) * (1 + 1) * (rt2 * rt2) := by
    mach_mpoly [rt2]
  rw [e, rt2_sq]

/-- **All three tangencies, checked.** The identity is the same at each of the three circles —
`2² + 2² = 8 = (2√2)²` — which is the right-isosceles symmetry of the configuration showing up as
one algebraic fact rather than three. -/
theorem solOOO_tangent :
    TangentExt solOOO A ∧ TangentExt solOOO B ∧ TangentExt solOOO C := by
  refine ⟨?_, ?_, ?_⟩
  · show (1 + 1 - 0) * (1 + 1 - 0) + (1 + 1 - 0) * (1 + 1 - 0)
        = ((1 + 1) * rt2 - 1 + 1) * ((1 + 1) * rt2 - 1 + 1)
    rw [ooo_radius_sq]; mach_ring
  · show (1 + 1 - (1 + 1) * (1 + 1)) * (1 + 1 - (1 + 1) * (1 + 1)) + (1 + 1 - 0) * (1 + 1 - 0)
        = ((1 + 1) * rt2 - 1 + 1) * ((1 + 1) * rt2 - 1 + 1)
    rw [ooo_radius_sq]; mach_ring
  · show (1 + 1 - 0) * (1 + 1 - 0) + (1 + 1 - (1 + 1) * (1 + 1)) * (1 + 1 - (1 + 1) * (1 + 1))
        = ((1 + 1) * rt2 - 1 + 1) * ((1 + 1) * rt2 - 1 + 1)
    rw [ooo_radius_sq]; mach_ring

/-! ### Solution 8 — the inner Soddy circle, `(inner, inner, inner)`

Centre `(2, 2)`, radius `1 + 2√2`. Internally tangent to all three. Same centre as solution 1 and
the same `8 = (2√2)²`, with the radius on the other side of the antipodal pairing. -/

theorem sol_iii_pos : (0 : Real) < 1 + (1 + 1) * rt2 := by
  refine add_pos zero_lt_one_ax ?_
  refine mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax) ?_
  exact lt_trans_ax zero_lt_one_ax one_lt_rt2

/-- The inner Soddy circle of the flagship. -/
noncomputable def solIII : Circle := ⟨1 + 1, 1 + 1, 1 + (1 + 1) * rt2, sol_iii_pos⟩

private theorem iii_radius_sq :
    (1 + (1 + 1) * rt2 - 1) * (1 + (1 + 1) * rt2 - 1) = (1 + 1) * (1 + 1) * (1 + 1) := by
  have e : (1 + (1 + 1) * rt2 - 1) * (1 + (1 + 1) * rt2 - 1) = (1 + 1) * (1 + 1) * (rt2 * rt2) := by
    mach_mpoly [rt2]
  rw [e, rt2_sq]

/-- **All three tangencies, checked** — internal this time. -/
theorem solIII_tangent :
    TangentInt solIII A ∧ TangentInt solIII B ∧ TangentInt solIII C := by
  refine ⟨?_, ?_, ?_⟩
  · show (1 + 1 - 0) * (1 + 1 - 0) + (1 + 1 - 0) * (1 + 1 - 0)
        = (1 + (1 + 1) * rt2 - 1) * (1 + (1 + 1) * rt2 - 1)
    rw [iii_radius_sq]; mach_ring
  · show (1 + 1 - (1 + 1) * (1 + 1)) * (1 + 1 - (1 + 1) * (1 + 1)) + (1 + 1 - 0) * (1 + 1 - 0)
        = (1 + (1 + 1) * rt2 - 1) * (1 + (1 + 1) * rt2 - 1)
    rw [iii_radius_sq]; mach_ring
  · show (1 + 1 - 0) * (1 + 1 - 0) + (1 + 1 - (1 + 1) * (1 + 1)) * (1 + 1 - (1 + 1) * (1 + 1))
        = (1 + (1 + 1) * rt2 - 1) * (1 + (1 + 1) * rt2 - 1)
    rw [iii_radius_sq]; mach_ring

/-! ## Coordinates with a denominator, via a better parameter

The remaining solutions have centres like `3 + 3√2/2`. The obvious move — clear denominators by
scaling the tangency identity — makes things **worse**: multiplying through by `4` multiplies every
coefficient by `4` too, and `mach_mpoly` walls on the result. The corpus already warned that the
numeral limit is about the constants an identity *generates*, not the ones it starts with, and this
is that warning arriving on schedule.

The fix is to change parameter rather than to clear denominators. Put

    h := √2 / 2       so that   2h² = 1   and   √2 = 2h

Then `3 + 3√2/2 = 3 + 3h` and `2 + 3√2 = 2 + 6h`: every coordinate is a *small integer combination
of `h`*, division occurs once in the definition of `h` and never again, and the largest constant any
identity generates drops from the thousands to under forty.
-/

private theorem two_ne : (1 + 1 : Real) ≠ 0 := ne_of_gt (add_pos zero_lt_one_ax zero_lt_one_ax)

/-- `2 · (a/2) = a`. The only fact about division this file needs. -/
private theorem two_mul_half (a : Real) : (1 + 1) * (a / (1 + 1)) = a := by
  rw [div_def a (1 + 1) two_ne]
  have h := mul_inv (1 + 1 : Real) two_ne
  have e : (1 + 1) * (a * (1 / (1 + 1))) = a * ((1 + 1) * (1 / (1 + 1))) := by
    mach_mpoly [a, (1 : Real) / (1 + 1)]
  rw [e, h]; mach_ring

/-- `h = √2/2`. -/
noncomputable def h : Real := rt2 / (1 + 1)

theorem two_mul_h : (1 + 1) * h = rt2 := two_mul_half rt2

/-- **`2h² = 1`** — the single algebraic fact about `h`, and the only one any identity below needs.
Derived from `√2·√2 = 2` by cancelling one factor of two, so no new axiom is involved. -/
theorem h_sq : (1 + 1) * (h * h) = 1 := by
  refine QuadraticRoots.mul_left_cancel two_ne ?_
  have e : (1 + 1) * ((1 + 1) * (h * h)) = ((1 + 1) * h) * ((1 + 1) * h) := by mach_mpoly [h]
  rw [e, two_mul_h, rt2_sq]
  mach_ring

theorem h_pos : 0 < h := by
  have h2 : (0 : Real) < 1 + 1 := add_pos zero_lt_one_ax zero_lt_one_ax
  rcases lt_total 0 h with hp | hz | hn
  · exact hp
  · exfalso
    have : (1 + 1) * h = 0 := by rw [← hz]; mach_ring
    rw [two_mul_h] at this
    exact lt_irrefl_ax _ (lt_of_lt_of_le (lt_trans_ax zero_lt_one_ax one_lt_rt2) (le_of_eq this))
  · exfalso
    have hle : (1 + 1) * h ≤ (1 + 1) * 0 := mul_le_mul_of_nonneg_left (le_of_lt hn) (le_of_lt h2)
    rw [two_mul_h] at hle
    have e : (1 + 1) * (0 : Real) = 0 := by mach_ring
    rw [e] at hle
    exact lt_irrefl_ax _ (lt_of_lt_of_le (lt_trans_ax zero_lt_one_ax one_lt_rt2) hle)

/-! ### The `√2` pair: `(outer,inner,inner)` and `(inner,outer,outer)`

Centres `3 ± v`, radii `2 + 2v` and `2v − 2`, where **`v := 3h = 3√2/2`** and the only fact needed
is `2v² = 9`.

**The compression to `v` is what makes these close, and the reason is `Lean.Meta.acLt`.** Written in
terms of `h` the identities carry constants like `6` and `18` *inside a distribution*, and `acLt` —
the associative-commutative ordering `simp` uses — blows up on the nested `(1+1)` trees that
produces. Raising `maxHeartbeats` to four million does not rescue it; the growth is in the
normaliser's term ordering, not in arithmetic. Absorbing the `3` into a single variable removes
those constants from the distribution entirely, and every identity becomes a two-term polynomial in
one atom with no constant above `4`.

This corrects the diagnosis recorded here earlier. The limit is not "constants are trees"; it is
`acLt` on nested constant trees *under distribution*. Constants that never get distributed — the `4`
of the centre separation, for instance — cost nothing at all.
-/

/-- Discharge a residual of the shape `9 − 2v²`.

Phrased so the goal is never rewritten. An earlier version used `rw [← z]` to turn the `0` of
`u - v = 0` into the residual, which also rewrote the `0` inside every `(c - 0)` term and blew the
normaliser up — a rewrite hitting more occurrences than intended, misread at the time as a scale
limit. -/
private theorem zero_of_res {v u : Real} (hv : (1 + 1) * (v * v) = ((1 + 1 + 1) * (1 + 1 + 1)))
    (e : u = ((1 + 1 + 1) * (1 + 1 + 1)) - (1 + 1) * (v * v)) : u = 0 := by
  rw [hv] at e; rw [e]; mach_ring

/-- `v = 3√2/2`, the compressed parameter. -/
noncomputable def v2 : Real := (1 + 1 + 1) * h

/-- **`2v² = 9`** — the single fact every identity below consumes. -/
theorem v2_sq : (1 + 1) * (v2 * v2) = ((1 + 1 + 1) * (1 + 1 + 1)) := by
  show (1 + 1) * (((1 + 1 + 1) * h) * ((1 + 1 + 1) * h)) = ((1 + 1 + 1) * (1 + 1 + 1))
  have e : (1 + 1) * (((1 + 1 + 1) * h) * ((1 + 1 + 1) * h)) = ((1 + 1 + 1) * (1 + 1 + 1)) * ((1 + 1) * (h * h)) := by mach_mpoly [h]
  rw [e, h_sq]; mach_ring

theorem v2_pos : 0 < v2 :=
  mul_pos (add_pos (add_pos zero_lt_one_ax zero_lt_one_ax) zero_lt_one_ax) h_pos

set_option maxHeartbeats 1000000 in
/-- The `(outer,inner,inner)` identities, for any `v` with `2v² = 9`. -/
private theorem sq2_oii (v : Real) (hv : (1 + 1) * (v * v) = ((1 + 1 + 1) * (1 + 1 + 1))) :
    (((1 + 1 + 1) + v - 0) * ((1 + 1 + 1) + v - 0) + ((1 + 1 + 1) + v - 0) * ((1 + 1 + 1) + v - 0)
      = ((1 + 1) + (1 + 1) * v + 1) * ((1 + 1) + (1 + 1) * v + 1))
    ∧
    (((1 + 1 + 1) + v - ((1 + 1) * (1 + 1))) * ((1 + 1 + 1) + v - ((1 + 1) * (1 + 1))) + ((1 + 1 + 1) + v - 0) * ((1 + 1 + 1) + v - 0)
      = ((1 + 1) + (1 + 1) * v - 1) * ((1 + 1) + (1 + 1) * v - 1))
    ∧
    (((1 + 1 + 1) + v - 0) * ((1 + 1 + 1) + v - 0) + ((1 + 1 + 1) + v - ((1 + 1) * (1 + 1))) * ((1 + 1 + 1) + v - ((1 + 1) * (1 + 1)))
      = ((1 + 1) + (1 + 1) * v - 1) * ((1 + 1) + (1 + 1) * v - 1)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine QuadraticRoots.eq_of_sub_eq_zero (zero_of_res hv ?_) <;>
    mach_mpoly [v]

set_option maxHeartbeats 1000000 in
/-- The `(inner,outer,outer)` identities, for any `v` with `2v² = 9`. -/
private theorem sq2_ioo (v : Real) (hv : (1 + 1) * (v * v) = ((1 + 1 + 1) * (1 + 1 + 1))) :
    (((1 + 1 + 1) - v - 0) * ((1 + 1 + 1) - v - 0) + ((1 + 1 + 1) - v - 0) * ((1 + 1 + 1) - v - 0)
      = ((1 + 1) * v - (1 + 1) - 1) * ((1 + 1) * v - (1 + 1) - 1))
    ∧
    (((1 + 1 + 1) - v - ((1 + 1) * (1 + 1))) * ((1 + 1 + 1) - v - ((1 + 1) * (1 + 1))) + ((1 + 1 + 1) - v - 0) * ((1 + 1 + 1) - v - 0)
      = ((1 + 1) * v - (1 + 1) + 1) * ((1 + 1) * v - (1 + 1) + 1))
    ∧
    (((1 + 1 + 1) - v - 0) * ((1 + 1 + 1) - v - 0) + ((1 + 1 + 1) - v - ((1 + 1) * (1 + 1))) * ((1 + 1 + 1) - v - ((1 + 1) * (1 + 1)))
      = ((1 + 1) * v - (1 + 1) + 1) * ((1 + 1) * v - (1 + 1) + 1)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine QuadraticRoots.eq_of_sub_eq_zero (zero_of_res hv ?_) <;>
    mach_mpoly [v]

theorem sol_oii_pos : (0 : Real) < (1 + 1) + (1 + 1) * v2 :=
  add_pos (add_pos zero_lt_one_ax zero_lt_one_ax)
    (mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax) v2_pos)

/-- `(outer, inner, inner)`: centre `(3 + 3√2/2, 3 + 3√2/2)`, radius `2 + 3√2`. -/
noncomputable def solOII : Circle := ⟨(1 + 1 + 1) + v2, (1 + 1 + 1) + v2, (1 + 1) + (1 + 1) * v2, sol_oii_pos⟩

/-- **All three tangencies of the `(outer,inner,inner)` circle.** -/
theorem solOII_tangent :
    TangentExt solOII A ∧ TangentInt solOII B ∧ TangentInt solOII C :=
  sq2_oii v2 v2_sq

private theorem two_lt_nine : ((1 + 1) : Real) < ((1 + 1 + 1) * (1 + 1 + 1)) := by
  have pos : (0 : Real) < 1 + 1 + 1 + 1 + 1 + 1 + 1 := by
    repeat' refine add_pos ?_ zero_lt_one_ax
    exact zero_lt_one_ax
  have v := add_lt_add_left pos ((1 + 1) : Real)
  have l : ((1 + 1) : Real) + 0 = (1 + 1) := by mach_ring
  have r : ((1 + 1) : Real) + (1 + 1 + 1 + 1 + 1 + 1 + 1) = ((1 + 1 + 1) * (1 + 1 + 1)) := by mach_ring
  rw [l, r] at v; exact v

/-- `1 < v = 3√2/2`, from `2v² = 9` alone. -/
theorem one_lt_v2 : 1 < v2 := by
  have key : ¬ (v2 ≤ 1) := by
    intro hle
    have h1 : v2 * v2 ≤ v2 * 1 := mul_le_mul_of_nonneg_left hle (le_of_lt v2_pos)
    have e : v2 * 1 = v2 := by mach_ring
    rw [e] at h1
    have h3 : (1 + 1) * (v2 * v2) ≤ (1 + 1) * 1 :=
      mul_le_mul_of_nonneg_left (le_trans h1 hle)
        (le_of_lt (add_pos zero_lt_one_ax zero_lt_one_ax))
    rw [v2_sq] at h3
    have e3 : ((1 + 1) : Real) * 1 = (1 + 1) := by mach_ring
    rw [e3] at h3
    exact lt_irrefl_ax _ (lt_of_lt_of_le two_lt_nine h3)
  rcases lt_total 1 v2 with h | h | h
  · exact h
  · exact absurd (le_of_eq h.symm) key
  · exact absurd (le_of_lt h) key

theorem sol_ioo_pos : (0 : Real) < (1 + 1) * v2 - (1 + 1) := by
  have hd : (0 : Real) < v2 - 1 := by
    have v := add_lt_add_left one_lt_v2 (-1 : Real)
    have l : (-1 : Real) + 1 = 0 := by mach_ring
    have r : (-1 : Real) + v2 = v2 - 1 := by mach_ring
    rw [l, r] at v; exact v
  have hp : (0 : Real) < (1 + 1) * (v2 - 1) :=
    mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax) hd
  have e : ((1 + 1) : Real) * (v2 - 1) = (1 + 1) * v2 - (1 + 1) := by mach_ring
  rw [e] at hp; exact hp

/-- `(inner, outer, outer)`: centre `(3 − 3√2/2, 3 − 3√2/2)`, radius `3√2 − 2`. -/
noncomputable def solIOO : Circle := ⟨(1 + 1 + 1) - v2, (1 + 1 + 1) - v2, (1 + 1) * v2 - (1 + 1), sol_ioo_pos⟩

/-- **All three tangencies of the `(inner,outer,outer)` circle**, the antipodal partner. -/
theorem solIOO_tangent :
    TangentInt solIOO A ∧ TangentExt solIOO B ∧ TangentExt solIOO C :=
  sq2_ioo v2 v2_sq

/-! ### The `√21` quartet: the four mixed modes

Radius `2κ` and centre `(2, 2±κ)` or `(2±κ, 2)`, where **`κ := √21/3`** and the only fact needed is
`3κ² = 7`. Same compression discipline as the `√2` pair: `κ` absorbs the denominator, so the
identities carry no constant above `4` and `acLt` never sees a nested constant under distribution.

All twelve identities share the residual `7 − 3κ²`.
-/

private theorem zero_of_res21 {k u : Real} (hk : (1 + 1 + 1) * (k * k) = (1 + 1 + 1 + 1 + 1 + 1 + 1))
    (e : u = (1 + 1 + 1 + 1 + 1 + 1 + 1) - (1 + 1 + 1) * (k * k)) : u = 0 := by
  rw [hk] at e; rw [e]; mach_ring

private theorem three_ne : (((1 + 1 + 1)) : Real) ≠ 0 :=
  ne_of_gt (add_pos (add_pos zero_lt_one_ax zero_lt_one_ax) zero_lt_one_ax)

private theorem three_mul_third (a : Real) : (1 + 1 + 1) * (a / (1 + 1 + 1)) = a := by
  rw [div_def a (1 + 1 + 1) three_ne]
  have h := mul_inv (((1 + 1 + 1)) : Real) three_ne
  have e : (1 + 1 + 1) * (a * (1 / (1 + 1 + 1))) = a * ((1 + 1 + 1) * (1 / (1 + 1 + 1))) := by
    mach_mpoly [a, (1 : Real) / (1 + 1 + 1)]
  rw [e, h]; mach_ring

/-- `√21`. -/
noncomputable def rt21 : Real := sqrt ((1 + 1 + 1) * (1 + 1 + 1 + 1 + 1 + 1 + 1))

theorem rt21_sq : rt21 * rt21 = (1 + 1 + 1) * (1 + 1 + 1 + 1 + 1 + 1 + 1) := by
  refine sqrt_sq_nonneg _ (le_of_lt (mul_pos ?_ ?_))
  · exact add_pos (add_pos zero_lt_one_ax zero_lt_one_ax) zero_lt_one_ax
  · repeat' refine add_pos ?_ zero_lt_one_ax
    exact zero_lt_one_ax

theorem rt21_pos : 0 < rt21 := by
  rcases lt_total 0 rt21 with h | h | h
  · exact h
  · exfalso
    have := rt21_sq
    rw [← h] at this
    have e : (0 : Real) * 0 = 0 := by mach_ring
    rw [e] at this
    have pos : (0 : Real) < (1 + 1 + 1) * (1 + 1 + 1 + 1 + 1 + 1 + 1) := by
      refine mul_pos (add_pos (add_pos zero_lt_one_ax zero_lt_one_ax) zero_lt_one_ax) ?_
      repeat' refine add_pos ?_ zero_lt_one_ax
      exact zero_lt_one_ax
    rw [← this] at pos; exact lt_irrefl_ax _ pos
  · exact absurd h (fun hc => lt_irrefl_ax _ (lt_of_lt_of_le hc (sqrt_nonneg _)))

/-- `κ = √21/3`, the compressed parameter. -/
noncomputable def kap : Real := rt21 / (1 + 1 + 1)

theorem three_mul_kap : (1 + 1 + 1) * kap = rt21 := three_mul_third rt21

/-- **`3κ² = 7`** — the single fact the quartet consumes. -/
theorem kap_sq : (1 + 1 + 1) * (kap * kap) = (1 + 1 + 1 + 1 + 1 + 1 + 1) := by
  refine QuadraticRoots.mul_left_cancel three_ne ?_
  have e : (1 + 1 + 1) * ((1 + 1 + 1) * (kap * kap)) = ((1 + 1 + 1) * kap) * ((1 + 1 + 1) * kap) := by mach_mpoly [kap]
  rw [e, three_mul_kap, rt21_sq]; mach_ring

theorem kap_pos : 0 < kap := by
  rcases lt_total 0 kap with h | h | h
  · exact h
  · exfalso
    have e : (1 + 1 + 1) * kap = 0 := by rw [← h]; mach_ring
    rw [three_mul_kap] at e
    have hp := rt21_pos
    rw [e] at hp; exact lt_irrefl_ax _ hp
  · exfalso
    have hle : (1 + 1 + 1) * kap ≤ (1 + 1 + 1) * 0 :=
      mul_le_mul_of_nonneg_left (le_of_lt h)
        (le_of_lt (add_pos (add_pos zero_lt_one_ax zero_lt_one_ax) zero_lt_one_ax))
    rw [three_mul_kap] at hle
    have e : ((1 + 1 + 1) : Real) * 0 = 0 := by mach_ring
    rw [e] at hle
    exact lt_irrefl_ax _ (lt_of_lt_of_le rt21_pos hle)

theorem sol_kap_pos : (0 : Real) < (1 + 1) * kap :=
  mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax) kap_pos

set_option maxHeartbeats 1000000 in
/-- `(outer,outer,inner)`: centre `(2, 2+κ)`. -/
private theorem sq21_ooi (k : Real) (hk : (1 + 1 + 1) * (k * k) = (1 + 1 + 1 + 1 + 1 + 1 + 1)) :
    (((1 + 1) - 0) * ((1 + 1) - 0) + ((1 + 1) + k - 0) * ((1 + 1) + k - 0)
      = ((1 + 1) * k + 1) * ((1 + 1) * k + 1))
    ∧
    (((1 + 1) - ((1 + 1) * (1 + 1))) * ((1 + 1) - ((1 + 1) * (1 + 1))) + ((1 + 1) + k - 0) * ((1 + 1) + k - 0)
      = ((1 + 1) * k + 1) * ((1 + 1) * k + 1))
    ∧
    (((1 + 1) - 0) * ((1 + 1) - 0) + ((1 + 1) + k - ((1 + 1) * (1 + 1))) * ((1 + 1) + k - ((1 + 1) * (1 + 1)))
      = ((1 + 1) * k - 1) * ((1 + 1) * k - 1)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine QuadraticRoots.eq_of_sub_eq_zero (zero_of_res21 hk ?_) <;>
    mach_mpoly [k]

set_option maxHeartbeats 1000000 in
/-- `(outer,inner,outer)`: centre `(2+κ, 2)`. -/
private theorem sq21_oio (k : Real) (hk : (1 + 1 + 1) * (k * k) = (1 + 1 + 1 + 1 + 1 + 1 + 1)) :
    (((1 + 1) + k - 0) * ((1 + 1) + k - 0) + ((1 + 1) - 0) * ((1 + 1) - 0)
      = ((1 + 1) * k + 1) * ((1 + 1) * k + 1))
    ∧
    (((1 + 1) + k - ((1 + 1) * (1 + 1))) * ((1 + 1) + k - ((1 + 1) * (1 + 1))) + ((1 + 1) - 0) * ((1 + 1) - 0)
      = ((1 + 1) * k - 1) * ((1 + 1) * k - 1))
    ∧
    (((1 + 1) + k - 0) * ((1 + 1) + k - 0) + ((1 + 1) - ((1 + 1) * (1 + 1))) * ((1 + 1) - ((1 + 1) * (1 + 1)))
      = ((1 + 1) * k + 1) * ((1 + 1) * k + 1)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine QuadraticRoots.eq_of_sub_eq_zero (zero_of_res21 hk ?_) <;>
    mach_mpoly [k]

set_option maxHeartbeats 1000000 in
/-- `(inner,outer,inner)`: centre `(2−κ, 2)`. -/
private theorem sq21_ioi (k : Real) (hk : (1 + 1 + 1) * (k * k) = (1 + 1 + 1 + 1 + 1 + 1 + 1)) :
    (((1 + 1) - k - 0) * ((1 + 1) - k - 0) + ((1 + 1) - 0) * ((1 + 1) - 0)
      = ((1 + 1) * k - 1) * ((1 + 1) * k - 1))
    ∧
    (((1 + 1) - k - ((1 + 1) * (1 + 1))) * ((1 + 1) - k - ((1 + 1) * (1 + 1))) + ((1 + 1) - 0) * ((1 + 1) - 0)
      = ((1 + 1) * k + 1) * ((1 + 1) * k + 1))
    ∧
    (((1 + 1) - k - 0) * ((1 + 1) - k - 0) + ((1 + 1) - ((1 + 1) * (1 + 1))) * ((1 + 1) - ((1 + 1) * (1 + 1)))
      = ((1 + 1) * k - 1) * ((1 + 1) * k - 1)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine QuadraticRoots.eq_of_sub_eq_zero (zero_of_res21 hk ?_) <;>
    mach_mpoly [k]

set_option maxHeartbeats 1000000 in
/-- `(inner,inner,outer)`: centre `(2, 2−κ)`. -/
private theorem sq21_iio (k : Real) (hk : (1 + 1 + 1) * (k * k) = (1 + 1 + 1 + 1 + 1 + 1 + 1)) :
    (((1 + 1) - 0) * ((1 + 1) - 0) + ((1 + 1) - k - 0) * ((1 + 1) - k - 0)
      = ((1 + 1) * k - 1) * ((1 + 1) * k - 1))
    ∧
    (((1 + 1) - ((1 + 1) * (1 + 1))) * ((1 + 1) - ((1 + 1) * (1 + 1))) + ((1 + 1) - k - 0) * ((1 + 1) - k - 0)
      = ((1 + 1) * k - 1) * ((1 + 1) * k - 1))
    ∧
    (((1 + 1) - 0) * ((1 + 1) - 0) + ((1 + 1) - k - ((1 + 1) * (1 + 1))) * ((1 + 1) - k - ((1 + 1) * (1 + 1)))
      = ((1 + 1) * k + 1) * ((1 + 1) * k + 1)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine QuadraticRoots.eq_of_sub_eq_zero (zero_of_res21 hk ?_) <;>
    mach_mpoly [k]

/-- `(outer, outer, inner)`. -/
noncomputable def solOOI : Circle := ⟨(1 + 1), (1 + 1) + kap, (1 + 1) * kap, sol_kap_pos⟩
/-- `(outer, inner, outer)`. -/
noncomputable def solOIO : Circle := ⟨(1 + 1) + kap, (1 + 1), (1 + 1) * kap, sol_kap_pos⟩
/-- `(inner, outer, inner)`. -/
noncomputable def solIOI : Circle := ⟨(1 + 1) - kap, (1 + 1), (1 + 1) * kap, sol_kap_pos⟩
/-- `(inner, inner, outer)`. -/
noncomputable def solIIO : Circle := ⟨(1 + 1), (1 + 1) - kap, (1 + 1) * kap, sol_kap_pos⟩

theorem solOOI_tangent :
    TangentExt solOOI A ∧ TangentExt solOOI B ∧ TangentInt solOOI C := sq21_ooi kap kap_sq
theorem solOIO_tangent :
    TangentExt solOIO A ∧ TangentInt solOIO B ∧ TangentExt solOIO C := sq21_oio kap kap_sq
theorem solIOI_tangent :
    TangentInt solIOI A ∧ TangentExt solIOI B ∧ TangentInt solIOI C := sq21_ioi kap kap_sq
theorem solIIO_tangent :
    TangentInt solIIO A ∧ TangentInt solIIO B ∧ TangentExt solIIO C := sq21_iio kap kap_sq

end Coordinates
end Apollonius
end Geometry
end MachLib
