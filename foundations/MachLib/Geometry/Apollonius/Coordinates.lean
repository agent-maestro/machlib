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

/-! ## The exceptional locus, `d = 2√2`, `ρ = 1`

The exhibit's **default** view: the configuration where one class degenerates from quadratic to
linear and the count drops from eight to seven. Its coordinates involve `√2`, `√3` and `√6 = √2·√3`,
so two irrationals appear — and `√6` is not a third atom, it is the product of the first two, which
is what keeps the identities small.

Same discipline as the flagship: irrationals are **variables** with a defining square, never
definitions, so the normaliser sees atoms.
-/

/-- `√3`. -/
noncomputable def rt3 : Real := sqrt (1 + 1 + 1)

theorem rt3_sq : rt3 * rt3 = (1 + 1 + 1) :=
  sqrt_sq_nonneg _ (le_of_lt (add_pos (add_pos zero_lt_one_ax zero_lt_one_ax) zero_lt_one_ax))

theorem rt3_pos : 0 < rt3 := by
  rcases lt_total 0 rt3 with h | h | h
  · exact h
  · exfalso
    have hq := rt3_sq
    rw [← h] at hq
    have e : (0 : Real) * 0 = 0 := by mach_ring
    rw [e] at hq
    have pos : (0 : Real) < (1 + 1 + 1) :=
      add_pos (add_pos zero_lt_one_ax zero_lt_one_ax) zero_lt_one_ax
    rw [← hq] at pos; exact lt_irrefl_ax _ pos
  · exact absurd h (fun hc => lt_irrefl_ax _ (lt_of_lt_of_le hc (sqrt_nonneg _)))

/-- `A = (0,0,1)` of the locus triple. -/ noncomputable def Alo : Circle := ⟨0, 0, 1, h1pos⟩
/-- `B = (2√2,0,1)`. -/ noncomputable def Blo : Circle := ⟨(1 + 1) * rt2, 0, 1, h1pos⟩
/-- `C = (0,2√2,1)`. -/ noncomputable def Clo : Circle := ⟨0, (1 + 1) * rt2, 1, h1pos⟩

/-- Residual `2s² − 4`, zero when `s² = 2`. Solutions 1 and 7. -/
private theorem zero_of_s2 {s u : Real} (hs : s * s = (1 + 1))
    (e : u = (1 + 1) * (s * s) - (1 + 1) * (1 + 1)) : u = 0 := by
  rw [hs] at e; rw [e]; mach_ring

/-- Residual `2s² + u² − s²u² − 1`, zero when `s² = 2` and `u² = 3`. All four `√6` solutions,
all three tangencies each — twelve identities, one shape. -/
private theorem zero_of_su {s u w : Real} (hs : s * s = (1 + 1)) (hu : u * u = (1 + 1 + 1))
    (e : w = (1 + 1) * (s * s) + u * u - (s * s) * (u * u) - 1) : w = 0 := by
  rw [hs, hu] at e; rw [e]; mach_ring

set_option maxHeartbeats 1000000 in
/-- Solution 1: `r = 1`, centre `(√2, √2)`, externally tangent to all three. -/
private theorem locus_ooo (s : Real) (hs : s * s = (1 + 1)) :
    ((s - 0) * (s - 0) + (s - 0) * (s - 0)
      = (1 + 1) * (1 + 1))
    ∧
    ((s - (1 + 1) * s) * (s - (1 + 1) * s) + (s - 0) * (s - 0)
      = (1 + 1) * (1 + 1))
    ∧
    ((s - 0) * (s - 0) + (s - (1 + 1) * s) * (s - (1 + 1) * s)
      = (1 + 1) * (1 + 1)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine QuadraticRoots.eq_of_sub_eq_zero (zero_of_s2 hs ?_) <;>
    mach_mpoly [s]

set_option maxHeartbeats 1000000 in
/-- Solution 7: `r = 3`, centre `(√2, √2)`, internally tangent to all three. -/
private theorem locus_iii (s : Real) (hs : s * s = (1 + 1)) :
    ((s - 0) * (s - 0) + (s - 0) * (s - 0)
      = ((1 + 1 + 1) - 1) * ((1 + 1 + 1) - 1))
    ∧
    ((s - (1 + 1) * s) * (s - (1 + 1) * s) + (s - 0) * (s - 0)
      = ((1 + 1 + 1) - 1) * ((1 + 1 + 1) - 1))
    ∧
    ((s - 0) * (s - 0) + (s - (1 + 1) * s) * (s - (1 + 1) * s)
      = ((1 + 1 + 1) - 1) * ((1 + 1 + 1) - 1)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine QuadraticRoots.eq_of_sub_eq_zero (zero_of_s2 hs ?_) <;>
    mach_mpoly [s]

set_option maxHeartbeats 1000000 in
/-- Solution 2: `r = √6`, centre `(√2, √2 + √3)`. -/
private theorem locus_ooi (s u : Real) (hs : s * s = (1 + 1)) (hu : u * u = (1 + 1 + 1)) :
    ((s - 0) * (s - 0) + (s + u - 0) * (s + u - 0)
      = (s * u + 1) * (s * u + 1))
    ∧
    ((s - (1 + 1) * s) * (s - (1 + 1) * s) + (s + u - 0) * (s + u - 0)
      = (s * u + 1) * (s * u + 1))
    ∧
    ((s - 0) * (s - 0) + (s + u - (1 + 1) * s) * (s + u - (1 + 1) * s)
      = (s * u - 1) * (s * u - 1)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine QuadraticRoots.eq_of_sub_eq_zero (zero_of_su hs hu ?_) <;>
    mach_mpoly [s, u]

set_option maxHeartbeats 1000000 in
/-- Solution 3: `r = √6`, centre `(√2 + √3, √2)`. -/
private theorem locus_oio (s u : Real) (hs : s * s = (1 + 1)) (hu : u * u = (1 + 1 + 1)) :
    ((s + u - 0) * (s + u - 0) + (s - 0) * (s - 0)
      = (s * u + 1) * (s * u + 1))
    ∧
    ((s + u - (1 + 1) * s) * (s + u - (1 + 1) * s) + (s - 0) * (s - 0)
      = (s * u - 1) * (s * u - 1))
    ∧
    ((s + u - 0) * (s + u - 0) + (s - (1 + 1) * s) * (s - (1 + 1) * s)
      = (s * u + 1) * (s * u + 1)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine QuadraticRoots.eq_of_sub_eq_zero (zero_of_su hs hu ?_) <;>
    mach_mpoly [s, u]

set_option maxHeartbeats 1000000 in
/-- Solution 5: `r = √6`, centre `(√2 − √3, √2)`. -/
private theorem locus_ioi (s u : Real) (hs : s * s = (1 + 1)) (hu : u * u = (1 + 1 + 1)) :
    ((s - u - 0) * (s - u - 0) + (s - 0) * (s - 0)
      = (s * u - 1) * (s * u - 1))
    ∧
    ((s - u - (1 + 1) * s) * (s - u - (1 + 1) * s) + (s - 0) * (s - 0)
      = (s * u + 1) * (s * u + 1))
    ∧
    ((s - u - 0) * (s - u - 0) + (s - (1 + 1) * s) * (s - (1 + 1) * s)
      = (s * u - 1) * (s * u - 1)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine QuadraticRoots.eq_of_sub_eq_zero (zero_of_su hs hu ?_) <;>
    mach_mpoly [s, u]

set_option maxHeartbeats 1000000 in
/-- Solution 6: `r = √6`, centre `(√2, √2 − √3)`. -/
private theorem locus_iio (s u : Real) (hs : s * s = (1 + 1)) (hu : u * u = (1 + 1 + 1)) :
    ((s - 0) * (s - 0) + (s - u - 0) * (s - u - 0)
      = (s * u - 1) * (s * u - 1))
    ∧
    ((s - (1 + 1) * s) * (s - (1 + 1) * s) + (s - u - 0) * (s - u - 0)
      = (s * u - 1) * (s * u - 1))
    ∧
    ((s - 0) * (s - 0) + (s - u - (1 + 1) * s) * (s - u - (1 + 1) * s)
      = (s * u + 1) * (s * u + 1)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine QuadraticRoots.eq_of_sub_eq_zero (zero_of_su hs hu ?_) <;>
    mach_mpoly [s, u]

private theorem four_ne : (((1 + 1) * (1 + 1)) : Real) ≠ 0 :=
  ne_of_gt (mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax)
                    (add_pos zero_lt_one_ax zero_lt_one_ax))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- Solution 4 of the locus: `r = 3/2`, centre `(√2/4, √2/4)` — the single circle of the class that
degenerates to linear.

Both a denominator **and** a rational radius, so both are compressed: `q = √2/4` with `8q² = 1`, and
`g = 3/2` with `2g = 3`. The separation enters as its own variable `dd` with `dd = 8q`, because the
consumer's circle carries it as `2√2` and those are equal without being syntactically equal.

The identity is multiplied by `4` — the smallest factor clearing both denominators — and the
squaring is split into two steps so no single `mach_mpoly` call has to distribute `(q − 8q)²` and
reconcile `200` in one go. -/
private theorem locus_ioo (q g dd : Real)
    (hq : (1 + 1) * (1 + 1) * (1 + 1) * (q * q) = 1) (hg : (1 + 1) * g = (1 + 1 + 1))
    (hd : dd = (1 + 1) * (1 + 1) * (1 + 1) * q) :
    ((q - 0) * (q - 0) + (q - 0) * (q - 0) = (g - 1) * (g - 1))
    ∧
    ((q - dd) * (q - dd) + (q - 0) * (q - 0) = (g + 1) * (g + 1))
    ∧
    ((q - 0) * (q - 0) + (q - dd) * (q - dd) = (g + 1) * (g + 1)) := by
  subst hd
  have rg : ((1 + 1) * (1 + 1)) * ((g + 1) * (g + 1)) = ((1 + 1) * g + (1 + 1)) * ((1 + 1) * g + (1 + 1)) := by mach_mpoly [g]
  refine ⟨?_, ?_, ?_⟩
  · refine QuadraticRoots.mul_left_cancel four_ne ?_
    have l : ((1 + 1) * (1 + 1)) * ((q - 0) * (q - 0) + (q - 0) * (q - 0))
        = (1 + 1) * (1 + 1) * (1 + 1) * (q * q) := by mach_mpoly [q]
    have r : ((1 + 1) * (1 + 1)) * ((g - 1) * (g - 1)) = ((1 + 1) * g - (1 + 1)) * ((1 + 1) * g - (1 + 1)) := by mach_mpoly [g]
    rw [l, r, hq, hg]; mach_ring
  · refine QuadraticRoots.mul_left_cancel four_ne ?_
    have step : (q - ((1 + 1) * (1 + 1) * (1 + 1) * q)) * (q - ((1 + 1) * (1 + 1) * (1 + 1) * q)) + (q - 0) * (q - 0)
        = (((1 + 1) * (1 + 1) + 1) * ((1 + 1) * (1 + 1) + 1)) * (q * q) + (((1 + 1) * (1 + 1) + 1) * ((1 + 1) * (1 + 1) + 1)) * (q * q) := by mach_mpoly [q]
    have l : ((1 + 1) * (1 + 1)) * ((q - ((1 + 1) * (1 + 1) * (1 + 1) * q)) * (q - ((1 + 1) * (1 + 1) * (1 + 1) * q)) + (q - 0) * (q - 0))
        = ((1 + 1) * (1 + 1) + 1) * ((1 + 1) * (1 + 1) + 1) * ((1 + 1) * (1 + 1) * (1 + 1) * (q * q)) := by
      rw [step]; mach_mpoly [q]
    rw [l, rg, hq, hg]; mach_ring
  · refine QuadraticRoots.mul_left_cancel four_ne ?_
    have step : (q - 0) * (q - 0) + (q - ((1 + 1) * (1 + 1) * (1 + 1) * q)) * (q - ((1 + 1) * (1 + 1) * (1 + 1) * q))
        = (((1 + 1) * (1 + 1) + 1) * ((1 + 1) * (1 + 1) + 1)) * (q * q) + (((1 + 1) * (1 + 1) + 1) * ((1 + 1) * (1 + 1) + 1)) * (q * q) := by mach_mpoly [q]
    have l : ((1 + 1) * (1 + 1)) * ((q - 0) * (q - 0) + (q - ((1 + 1) * (1 + 1) * (1 + 1) * q)) * (q - ((1 + 1) * (1 + 1) * (1 + 1) * q)))
        = ((1 + 1) * (1 + 1) + 1) * ((1 + 1) * (1 + 1) + 1) * ((1 + 1) * (1 + 1) * (1 + 1) * (q * q)) := by
      rw [step]; mach_mpoly [q]
    rw [l, rg, hq, hg]; mach_ring

/-! ### The locus solutions, as circles -/

private theorem four_ne' : (((1 + 1) * (1 + 1)) : Real) ≠ 0 := four_ne

/-- `4 · (a/4) = a`. -/
private theorem four_mul_quarter (a : Real) : ((1 + 1) * (1 + 1)) * (a / ((1 + 1) * (1 + 1))) = a := by
  rw [div_def a ((1 + 1) * (1 + 1)) four_ne']
  have hm := mul_inv ((((1 + 1) * (1 + 1))) : Real) four_ne'
  have e : ((1 + 1) * (1 + 1)) * (a * (1 / ((1 + 1) * (1 + 1)))) = a * (((1 + 1) * (1 + 1)) * (1 / ((1 + 1) * (1 + 1)))) := by
    mach_mpoly [a, (1 : Real) / ((1 + 1) * (1 + 1))]
  rw [e, hm]; mach_ring

/-- `√2/4`. -/
noncomputable def qQ : Real := rt2 / ((1 + 1) * (1 + 1))
theorem four_mul_qQ : ((1 + 1) * (1 + 1)) * qQ = rt2 := four_mul_quarter rt2

/-- **`8q² = 1`**. -/
theorem qQ_sq : (1 + 1) * (1 + 1) * (1 + 1) * (qQ * qQ) = 1 := by
  refine QuadraticRoots.mul_left_cancel (two_ne) ?_
  have e : (1 + 1) * ((1 + 1) * (1 + 1) * (1 + 1) * (qQ * qQ)) = ((1 + 1) * (1 + 1) * qQ) * ((1 + 1) * (1 + 1) * qQ) := by mach_mpoly [qQ]
  rw [e, four_mul_qQ, rt2_sq]; mach_ring

/-- The locus separation `d = 2√2` is `8·(√2/4)`. -/
theorem d_eq_eight_qQ : ((1 + 1) * rt2 : Real) = (1 + 1) * (1 + 1) * (1 + 1) * qQ := by
  have e : ((1 + 1) * (1 + 1) * (1 + 1) : Real) * qQ = (1 + 1) * (((1 + 1) * (1 + 1)) * qQ) := by mach_ring
  rw [e, four_mul_qQ]

/-- `3/2`. -/
noncomputable def gH : Real := (1 + 1 + 1) / (1 + 1)
theorem two_mul_gH : (1 + 1) * gH = (1 + 1 + 1) := two_mul_half (1 + 1 + 1)

theorem gH_pos : 0 < gH := by
  rcases lt_total 0 gH with h | h | h
  · exact h
  · exfalso
    have e : (1 + 1) * gH = 0 := by rw [← h]; mach_ring
    rw [two_mul_gH] at e
    have pos : (0 : Real) < (1 + 1 + 1) :=
      add_pos (add_pos zero_lt_one_ax zero_lt_one_ax) zero_lt_one_ax
    rw [e] at pos; exact lt_irrefl_ax _ pos
  · exfalso
    have hle : (1 + 1) * gH ≤ (1 + 1) * 0 :=
      mul_le_mul_of_nonneg_left (le_of_lt h) (le_of_lt (add_pos zero_lt_one_ax zero_lt_one_ax))
    rw [two_mul_gH] at hle
    have e : ((1 + 1) : Real) * 0 = 0 := by mach_ring
    rw [e] at hle
    have pos : (0 : Real) < (1 + 1 + 1) :=
      add_pos (add_pos zero_lt_one_ax zero_lt_one_ax) zero_lt_one_ax
    exact lt_irrefl_ax _ (lt_of_lt_of_le pos hle)

private theorem three_pos : (0 : Real) < (1 + 1 + 1) :=
  add_pos (add_pos zero_lt_one_ax zero_lt_one_ax) zero_lt_one_ax
private theorem rt6_pos : (0 : Real) < rt2 * rt3 :=
  mul_pos (lt_trans_ax zero_lt_one_ax one_lt_rt2) rt3_pos

/-- Solution 1 of the locus: `r = 1`, centre `(√2, √2)`. -/
noncomputable def loOOO : Circle := ⟨rt2, rt2, 1, zero_lt_one_ax⟩
theorem loOOO_tangent : TangentExt loOOO Alo ∧ TangentExt loOOO Blo ∧ TangentExt loOOO Clo :=
  locus_ooo rt2 rt2_sq

/-- Solution 7: `r = 3`, centre `(√2, √2)`. -/
noncomputable def loIII : Circle := ⟨rt2, rt2, (1 + 1 + 1), three_pos⟩
theorem loIII_tangent : TangentInt loIII Alo ∧ TangentInt loIII Blo ∧ TangentInt loIII Clo :=
  locus_iii rt2 rt2_sq

/-- Solution 2: `r = √6`, centre `(√2, √2 + √3)`. -/
noncomputable def loOOI : Circle := ⟨rt2, rt2 + rt3, rt2 * rt3, rt6_pos⟩
theorem loOOI_tangent : TangentExt loOOI Alo ∧ TangentExt loOOI Blo ∧ TangentInt loOOI Clo :=
  locus_ooi rt2 rt3 rt2_sq rt3_sq

/-- Solution 3: `r = √6`, centre `(√2 + √3, √2)`. -/
noncomputable def loOIO : Circle := ⟨rt2 + rt3, rt2, rt2 * rt3, rt6_pos⟩
theorem loOIO_tangent : TangentExt loOIO Alo ∧ TangentInt loOIO Blo ∧ TangentExt loOIO Clo :=
  locus_oio rt2 rt3 rt2_sq rt3_sq

/-- Solution 5: `r = √6`, centre `(√2 − √3, √2)`. -/
noncomputable def loIOI : Circle := ⟨rt2 - rt3, rt2, rt2 * rt3, rt6_pos⟩
theorem loIOI_tangent : TangentInt loIOI Alo ∧ TangentExt loIOI Blo ∧ TangentInt loIOI Clo :=
  locus_ioi rt2 rt3 rt2_sq rt3_sq

/-- Solution 6: `r = √6`, centre `(√2, √2 − √3)`. -/
noncomputable def loIIO : Circle := ⟨rt2, rt2 - rt3, rt2 * rt3, rt6_pos⟩
theorem loIIO_tangent : TangentInt loIIO Alo ∧ TangentInt loIIO Blo ∧ TangentExt loIIO Clo :=
  locus_iio rt2 rt3 rt2_sq rt3_sq

/-- Solution 4: `r = 3/2`, centre `(√2/4, √2/4)`. The degenerate class's single circle. -/
noncomputable def loIOO : Circle := ⟨qQ, qQ, gH, gH_pos⟩
theorem loIOO_tangent : TangentInt loIOO Alo ∧ TangentExt loIOO Blo ∧ TangentExt loIOO Clo :=
  locus_ioo qQ gH ((1 + 1) * rt2) qQ_sq two_mul_gH d_eq_eight_qQ

/-! ## Below the locus, `d = 5/2`, `ρ = 1`

The third configuration. Its centre is `5/4` and the separation is `2 · 5/4`, so the outer and inner
Soddy circles need **no numeric value at all** — their identity is `2c² = c²s²`, true for every `c`
once `s² = 2`. That is worth noticing: two of the eight points here are cheaper than any point in
either earlier configuration.
-/

/-- Residual `2c² − c²s²`, zero when `s² = 2`, **for any `c`**. -/
private theorem zero_of_cs (s c : Real) {w : Real} (hs : s * s = (1 + 1))
    (e : w = (1 + 1) * (c * c) - (c * c) * (s * s)) : w = 0 := by
  rw [hs] at e; rw [e]; mach_ring

set_option maxHeartbeats 1000000 in
/-- Soddy pair below the locus: centre `(c, c)`, separation `2c`, radii `cs ∓ 1`. -/
private theorem below_soddy (c s : Real) (hs : s * s = (1 + 1)) :
    ((c - 0) * (c - 0) + (c - 0) * (c - 0) = (c * s - 1 + 1) * (c * s - 1 + 1))
    ∧
    ((c - (1 + 1) * c) * (c - (1 + 1) * c) + (c - 0) * (c - 0)
      = (c * s - 1 + 1) * (c * s - 1 + 1))
    ∧
    ((c - 0) * (c - 0) + (c - (1 + 1) * c) * (c - (1 + 1) * c)
      = (c * s - 1 + 1) * (c * s - 1 + 1)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine QuadraticRoots.eq_of_sub_eq_zero (zero_of_cs s c hs ?_) <;>
    mach_mpoly [c, s] <;> mach_ring

set_option maxHeartbeats 1000000 in
/-- The inner Soddy circle below the locus: radius `1 + cs`, internally tangent to all three. -/
private theorem below_soddy_inner (c s : Real) (hs : s * s = (1 + 1)) :
    ((c - 0) * (c - 0) + (c - 0) * (c - 0) = (1 + c * s - 1) * (1 + c * s - 1))
    ∧
    ((c - (1 + 1) * c) * (c - (1 + 1) * c) + (c - 0) * (c - 0)
      = (1 + c * s - 1) * (1 + c * s - 1))
    ∧
    ((c - 0) * (c - 0) + (c - (1 + 1) * c) * (c - (1 + 1) * c)
      = (1 + c * s - 1) * (1 + c * s - 1)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine QuadraticRoots.eq_of_sub_eq_zero (zero_of_cs s c hs ?_) <;>
    mach_mpoly [c, s] <;> mach_ring

/-! ### The two Soddy circles below the locus, as circles -/

/-- `5/4`. -/
noncomputable def cQ : Real := ((1 + 1) * (1 + 1) + 1) / ((1 + 1) * (1 + 1))
theorem four_mul_cQ : ((1 + 1) * (1 + 1)) * cQ = ((1 + 1) * (1 + 1) + 1) := four_mul_quarter ((1 + 1) * (1 + 1) + 1)

private theorem five_pos : (0 : Real) < ((1 + 1) * (1 + 1) + 1) :=
  add_pos (mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax)
                   (add_pos zero_lt_one_ax zero_lt_one_ax)) zero_lt_one_ax

theorem cQ_pos : 0 < cQ := by
  rcases lt_total 0 cQ with h | h | h
  · exact h
  · exfalso
    have e : ((1 + 1) * (1 + 1)) * cQ = 0 := by rw [← h]; mach_ring
    rw [four_mul_cQ] at e
    have p := five_pos; rw [e] at p; exact lt_irrefl_ax _ p
  · exfalso
    have hle : ((1 + 1) * (1 + 1)) * cQ ≤ ((1 + 1) * (1 + 1)) * 0 :=
      mul_le_mul_of_nonneg_left (le_of_lt h) (le_of_lt (mul_pos
        (add_pos zero_lt_one_ax zero_lt_one_ax) (add_pos zero_lt_one_ax zero_lt_one_ax)))
    rw [four_mul_cQ] at hle
    have e : (((1 + 1) * (1 + 1)) : Real) * 0 = 0 := by mach_ring
    rw [e] at hle
    exact lt_irrefl_ax _ (lt_of_lt_of_le five_pos hle)

/-- From `0 < a` and `0 < a·x`, conclude `0 < x`. -/
private theorem pos_of_mul_pos {a x : Real} (ha : 0 < a) (h : 0 < a * x) : 0 < x := by
  rcases lt_total 0 x with hx | hx | hx
  · exact hx
  · exfalso; rw [← hx] at h
    have e : a * (0 : Real) = 0 := by mach_ring
    rw [e] at h; exact lt_irrefl_ax _ h
  · exfalso
    have hle : a * x ≤ a * 0 := mul_le_mul_of_nonneg_left (le_of_lt hx) (le_of_lt ha)
    have e : a * (0 : Real) = 0 := by mach_ring
    rw [e] at hle
    exact lt_irrefl_ax _ (lt_of_lt_of_le h hle)

/-- `5√2/4 > 1`. From `4c = 5` and `1 < √2`: `4(c√2 − 1) = 5√2 − 4 = 5(√2 − 1) + 1 > 0`. -/
theorem below_ooo_pos : (0 : Real) < cQ * rt2 - 1 := by
  have hd : (0 : Real) < rt2 - 1 := by
    have v := add_lt_add_left one_lt_rt2 (-1 : Real)
    have l : (-1 : Real) + 1 = 0 := by mach_ring
    have r : (-1 : Real) + rt2 = rt2 - 1 := by mach_ring
    rw [l, r] at v; exact v
  have hs : (0 : Real) < ((1 + 1) * (1 + 1) + 1) * (rt2 - 1) + 1 :=
    add_pos (mul_pos five_pos hd) zero_lt_one_ax
  have hbig : (0 : Real) < ((1 + 1) * (1 + 1)) * (cQ * rt2 - 1) := by
    have e : (((1 + 1) * (1 + 1)) : Real) * (cQ * rt2 - 1) = (((1 + 1) * (1 + 1)) * cQ) * rt2 - ((1 + 1) * (1 + 1)) := by mach_ring
    rw [e, four_mul_cQ]
    have e2 : (((1 + 1) * (1 + 1) + 1) : Real) * rt2 - ((1 + 1) * (1 + 1)) = ((1 + 1) * (1 + 1) + 1) * (rt2 - 1) + 1 := by mach_ring
    rw [e2]; exact hs
  exact pos_of_mul_pos (mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax)
    (add_pos zero_lt_one_ax zero_lt_one_ax)) hbig

theorem one_lt_cQ_rt2 : 1 < cQ * rt2 := by
  have v := add_lt_add_left below_ooo_pos (1 : Real)
  have l : (1 : Real) + 0 = 1 := by mach_ring
  have r : (1 : Real) + (cQ * rt2 - 1) = cQ * rt2 := by mach_ring
  rw [l, r] at v; exact v

theorem below_iii_pos : (0 : Real) < 1 + cQ * rt2 :=
  add_pos zero_lt_one_ax (mul_pos cQ_pos (lt_trans_ax zero_lt_one_ax one_lt_rt2))

/-- `A = (0,0,1)` of the `d = 5/2` triple. -/ noncomputable def Abe : Circle := ⟨0, 0, 1, h1pos⟩
/-- `B = (5/2,0,1)`. -/ noncomputable def Bbe : Circle := ⟨(1 + 1) * cQ, 0, 1, h1pos⟩
/-- `C = (0,5/2,1)`. -/ noncomputable def Cbe : Circle := ⟨0, (1 + 1) * cQ, 1, h1pos⟩

/-- Outer Soddy circle below the locus: `r = 5√2/4 − 1`, centre `(5/4, 5/4)`. -/
noncomputable def beOOO : Circle := ⟨cQ, cQ, cQ * rt2 - 1, below_ooo_pos⟩
theorem beOOO_tangent : TangentExt beOOO Abe ∧ TangentExt beOOO Bbe ∧ TangentExt beOOO Cbe :=
  below_soddy cQ rt2 rt2_sq

/-- Inner Soddy circle below the locus: `r = 1 + 5√2/4`, centre `(5/4, 5/4)`. -/
noncomputable def beIII : Circle := ⟨cQ, cQ, 1 + cQ * rt2, below_iii_pos⟩
theorem beIII_tangent : TangentInt beIII Abe ∧ TangentInt beIII Bbe ∧ TangentInt beIII Cbe :=
  below_soddy_inner cQ rt2 rt2_sq

/-! ### The `√34` quartet, via the factored residual

The direct route — clear both denominators with `144 = 16·9` — puts constants like `288` inside
every identity and the normaliser refuses. But the residual **factors**:

```
    2c² + t² − c²t² − 1  =  1 − (c² − 1)(t² − 2)
```

so the twelve tangency identities need only the constants `1` and `2`, and the entire arithmetic
burden collapses into a single side fact, `(c²−1)(t²−2) = 1`, proved once. With `c = 5/4` and
`t = √34/3` that is `(9/16)(16/9)`, and even *that* is discharged without ever forming `144`
explicitly: scale each factor separately, `16(c²−1) = 9` and `9(t²−2) = 16`, then cancel.

**This is the same lesson as the compression, one level up.** Do not hand the normaliser a big
identity and hope; find the form in which the constants never meet. -/

/-- Residual `1 − (c²−1)(t²−2)`. -/
private theorem zero_of_pq (c t : Real) {w : Real}
    (h : (c * c - 1) * (t * t - (1 + 1)) = 1)
    (e : w = 1 - (c * c - 1) * (t * t - (1 + 1))) : w = 0 := by
  rw [h] at e; rw [e]; mach_ring

/-- `X·Y = 1` from `16X = 9` and `9Y = 16`, without forming `144` in any goal the normaliser
must expand. -/
private theorem prod_one_of_scaled {X Y : Real} (hX : ((1 + 1) * (1 + 1) * (1 + 1) * (1 + 1)) * X = ((1 + 1 + 1) * (1 + 1 + 1))) (hY : ((1 + 1 + 1) * (1 + 1 + 1)) * Y = ((1 + 1) * (1 + 1) * (1 + 1) * (1 + 1))) :
    X * Y = 1 := by
  refine QuadraticRoots.mul_left_cancel (a := (((1 + 1) * (1 + 1) * (1 + 1) * (1 + 1)) * ((1 + 1 + 1) * (1 + 1 + 1)))) ?_ ?_
  · refine ne_of_gt (mul_pos ?_ ?_)
    · exact mul_pos (mul_pos (mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax)
        (add_pos zero_lt_one_ax zero_lt_one_ax)) (add_pos zero_lt_one_ax zero_lt_one_ax))
        (add_pos zero_lt_one_ax zero_lt_one_ax)
    · exact mul_pos (add_pos (add_pos zero_lt_one_ax zero_lt_one_ax) zero_lt_one_ax)
        (add_pos (add_pos zero_lt_one_ax zero_lt_one_ax) zero_lt_one_ax)
  · have e : ((((1 + 1) * (1 + 1) * (1 + 1) * (1 + 1)) * ((1 + 1 + 1) * (1 + 1 + 1))) : Real) * (X * Y) = (((1 + 1) * (1 + 1) * (1 + 1) * (1 + 1)) * X) * (((1 + 1 + 1) * (1 + 1 + 1)) * Y) := by mach_mpoly [X, Y]
    rw [e, hX, hY]; mach_ring

set_option maxHeartbeats 1000000 in
/-- Solution 2: `r = 5√34/12`, centre `(5/4, 5/4 + √34/3)`. -/
private theorem below_ooi (c t : Real) (h : (c * c - 1) * (t * t - (1 + 1)) = 1) :
    ((c - 0) * (c - 0) + (c + t - 0) * (c + t - 0)
      = (c * t + 1) * (c * t + 1))
    ∧
    ((c - (1 + 1) * c) * (c - (1 + 1) * c) + (c + t - 0) * (c + t - 0)
      = (c * t + 1) * (c * t + 1))
    ∧
    ((c - 0) * (c - 0) + (c + t - (1 + 1) * c) * (c + t - (1 + 1) * c)
      = (c * t - 1) * (c * t - 1)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine QuadraticRoots.eq_of_sub_eq_zero (zero_of_pq c t h ?_) <;>
    mach_mpoly [c, t] <;> mach_ring

set_option maxHeartbeats 1000000 in
/-- Solution 3: `r = 5√34/12`, centre `(5/4 + √34/3, 5/4)`. -/
private theorem below_oio (c t : Real) (h : (c * c - 1) * (t * t - (1 + 1)) = 1) :
    ((c + t - 0) * (c + t - 0) + (c - 0) * (c - 0)
      = (c * t + 1) * (c * t + 1))
    ∧
    ((c + t - (1 + 1) * c) * (c + t - (1 + 1) * c) + (c - 0) * (c - 0)
      = (c * t - 1) * (c * t - 1))
    ∧
    ((c + t - 0) * (c + t - 0) + (c - (1 + 1) * c) * (c - (1 + 1) * c)
      = (c * t + 1) * (c * t + 1)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine QuadraticRoots.eq_of_sub_eq_zero (zero_of_pq c t h ?_) <;>
    mach_mpoly [c, t] <;> mach_ring

set_option maxHeartbeats 1000000 in
/-- Solution 6: `r = 5√34/12`, centre `(5/4 − √34/3, 5/4)`. -/
private theorem below_ioi (c t : Real) (h : (c * c - 1) * (t * t - (1 + 1)) = 1) :
    ((c - t - 0) * (c - t - 0) + (c - 0) * (c - 0)
      = (c * t - 1) * (c * t - 1))
    ∧
    ((c - t - (1 + 1) * c) * (c - t - (1 + 1) * c) + (c - 0) * (c - 0)
      = (c * t + 1) * (c * t + 1))
    ∧
    ((c - t - 0) * (c - t - 0) + (c - (1 + 1) * c) * (c - (1 + 1) * c)
      = (c * t - 1) * (c * t - 1)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine QuadraticRoots.eq_of_sub_eq_zero (zero_of_pq c t h ?_) <;>
    mach_mpoly [c, t] <;> mach_ring

set_option maxHeartbeats 1000000 in
/-- Solution 7: `r = 5√34/12`, centre `(5/4, 5/4 − √34/3)`. -/
private theorem below_iio (c t : Real) (h : (c * c - 1) * (t * t - (1 + 1)) = 1) :
    ((c - 0) * (c - 0) + (c - t - 0) * (c - t - 0)
      = (c * t - 1) * (c * t - 1))
    ∧
    ((c - (1 + 1) * c) * (c - (1 + 1) * c) + (c - t - 0) * (c - t - 0)
      = (c * t - 1) * (c * t - 1))
    ∧
    ((c - 0) * (c - 0) + (c - t - (1 + 1) * c) * (c - t - (1 + 1) * c)
      = (c * t + 1) * (c * t + 1)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine QuadraticRoots.eq_of_sub_eq_zero (zero_of_pq c t h ?_) <;>
    mach_mpoly [c, t] <;> mach_ring

/-! ### The quartet, as circles -/

/-- `√34`. -/
noncomputable def rt34 : Real := sqrt ((1 + 1) * ((1 + 1) * (1 + 1) * (1 + 1) * (1 + 1) + 1))

private theorem n34_pos : (0 : Real) < ((1 + 1) * ((1 + 1) * (1 + 1) * (1 + 1) * (1 + 1) + 1)) := by
  refine mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax) (add_pos ?_ zero_lt_one_ax)
  exact mul_pos (mul_pos (mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax)
    (add_pos zero_lt_one_ax zero_lt_one_ax)) (add_pos zero_lt_one_ax zero_lt_one_ax))
    (add_pos zero_lt_one_ax zero_lt_one_ax)

theorem rt34_sq : rt34 * rt34 = ((1 + 1) * ((1 + 1) * (1 + 1) * (1 + 1) * (1 + 1) + 1)) := sqrt_sq_nonneg _ (le_of_lt n34_pos)

theorem rt34_pos : 0 < rt34 := by
  rcases lt_total 0 rt34 with h | h | h
  · exact h
  · exfalso
    have hq := rt34_sq
    rw [← h] at hq
    have e : (0 : Real) * 0 = 0 := by mach_ring
    rw [e] at hq
    have p := n34_pos; rw [← hq] at p; exact lt_irrefl_ax _ p
  · exact absurd h (fun hc => lt_irrefl_ax _ (lt_of_lt_of_le hc (sqrt_nonneg _)))

/-- `√34/3`. -/
noncomputable def tT : Real := rt34 / (1 + 1 + 1)
theorem three_mul_tT : (1 + 1 + 1) * tT = rt34 := three_mul_third rt34

theorem tT_pos : 0 < tT := by
  refine pos_of_mul_pos (add_pos (add_pos zero_lt_one_ax zero_lt_one_ax) zero_lt_one_ax) ?_
  rw [three_mul_tT]; exact rt34_pos

/-- `16(c² − 1) = 9` for `c = 5/4`. -/
theorem cQ_scaled : ((1 + 1) * (1 + 1) * (1 + 1) * (1 + 1)) * (cQ * cQ - 1) = ((1 + 1 + 1) * (1 + 1 + 1)) := by
  have hsq : ((1 + 1) * (1 + 1) * (1 + 1) * (1 + 1)) * (cQ * cQ) = (((1 + 1) * (1 + 1) + 1) * ((1 + 1) * (1 + 1) + 1)) := by
    have e : (((1 + 1) * (1 + 1) * (1 + 1) * (1 + 1)) : Real) * (cQ * cQ) = (((1 + 1) * (1 + 1)) * cQ) * (((1 + 1) * (1 + 1)) * cQ) := by mach_mpoly [cQ]
    rw [e, four_mul_cQ]
  have e2 : (((1 + 1) * (1 + 1) * (1 + 1) * (1 + 1)) : Real) * (cQ * cQ - 1) = ((1 + 1) * (1 + 1) * (1 + 1) * (1 + 1)) * (cQ * cQ) - ((1 + 1) * (1 + 1) * (1 + 1) * (1 + 1)) := by mach_ring
  rw [e2, hsq]; mach_ring

/-- `9(t² − 2) = 16` for `t = √34/3`. -/
theorem tT_scaled : ((1 + 1 + 1) * (1 + 1 + 1)) * (tT * tT - (1 + 1)) = ((1 + 1) * (1 + 1) * (1 + 1) * (1 + 1)) := by
  have hsq : ((1 + 1 + 1) * (1 + 1 + 1)) * (tT * tT) = ((1 + 1) * ((1 + 1) * (1 + 1) * (1 + 1) * (1 + 1) + 1)) := by
    have e : (((1 + 1 + 1) * (1 + 1 + 1)) : Real) * (tT * tT) = ((1 + 1 + 1) * tT) * ((1 + 1 + 1) * tT) := by mach_mpoly [tT]
    rw [e, three_mul_tT, rt34_sq]
  have e2 : (((1 + 1 + 1) * (1 + 1 + 1)) : Real) * (tT * tT - (1 + 1)) = ((1 + 1 + 1) * (1 + 1 + 1)) * (tT * tT) - ((1 + 1 + 1) * (1 + 1 + 1)) * (1 + 1) := by mach_ring
  rw [e2, hsq]; mach_ring

/-- **`(c²−1)(t²−2) = 1`** — the single side fact the whole quartet consumes. -/
theorem cQ_tT_prod : (cQ * cQ - 1) * (tT * tT - (1 + 1)) = 1 :=
  prod_one_of_scaled cQ_scaled tT_scaled

theorem below_quartet_pos : (0 : Real) < cQ * tT := mul_pos cQ_pos tT_pos

/-- Solution 2: `r = 5√34/12`, centre `(5/4, 5/4 + √34/3)`. -/
noncomputable def beOOI : Circle := ⟨cQ, cQ + tT, cQ * tT, below_quartet_pos⟩
theorem beOOI_tangent : TangentExt beOOI Abe ∧ TangentExt beOOI Bbe ∧ TangentInt beOOI Cbe :=
  below_ooi cQ tT cQ_tT_prod

/-- Solution 3: `r = 5√34/12`, centre `(5/4 + √34/3, 5/4)`. -/
noncomputable def beOIO : Circle := ⟨cQ + tT, cQ, cQ * tT, below_quartet_pos⟩
theorem beOIO_tangent : TangentExt beOIO Abe ∧ TangentInt beOIO Bbe ∧ TangentExt beOIO Cbe :=
  below_oio cQ tT cQ_tT_prod

/-- Solution 6: `r = 5√34/12`, centre `(5/4 − √34/3, 5/4)`. -/
noncomputable def beIOI : Circle := ⟨cQ - tT, cQ, cQ * tT, below_quartet_pos⟩
theorem beIOI_tangent : TangentInt beIOI Abe ∧ TangentExt beIOI Bbe ∧ TangentInt beIOI Cbe :=
  below_ioi cQ tT cQ_tT_prod

/-- Solution 7: `r = 5√34/12`, centre `(5/4, 5/4 − √34/3)`. -/
noncomputable def beIIO : Circle := ⟨cQ, cQ - tT, cQ * tT, below_quartet_pos⟩
theorem beIIO_tangent : TangentInt beIIO Abe ∧ TangentInt beIIO Bbe ∧ TangentExt beIIO Cbe :=
  below_iio cQ tT cQ_tT_prod

/-! ### The doubled `(inner,outer,outer)` class — the last two, and the full derivation

`r = 25/7 ± 45√2/28`, centre `−45/28 ∓ 9√2/7`. **Not checked in Lean.** The mathematics below is
complete and verified by hand; what is missing is a presentation the normaliser accepts. Written out
in full so the next attempt starts from the end of five, not from the beginning.

## Setup

Solution 5 is solution 4 under `e ↦ −e`, so one lemma in a parameter `e` with `e² = 2` gives both.
Scaled by `28² = 784` the coordinates are `28x = −9u`, `28(r − 1) = 9w`, with

```
    u = 5 + 4e        w = 8 + 5e
```

and the separation `28d = 70`.

## Everything reduces to one fact

**`w = u · e`**, since `(5 + 4e)e = 5e + 4e² = 8 + 5e` when `e² = 2`. Hence

```
    w² = u²e² = 2u²
```

*The internal tangency is exactly this*: `2u² − w² = u²(2 − e²) = 0`, with no numeral beyond `2`.

*The external tangency is also exactly this*, which is the part that took five attempts to see. As a
difference of squares, `a² − b² = (a−b)(a+b)` with `a = 56 + 9w`, `b = 9u + 70`:

```
    a − b  =  u + w
    a + b  =  9(14 + u + w)  =  9 · 9(w − u)
```

the second equality because **`14 + u + w = 9(w − u)`**, which follows from the single small fact

```
    4w − 5u = 7
```

So `a² − b² = (u + w) · 81(w − u) = 81(w² − u²) = 81(2u² − u²) = 81u² = (9u)²`, which is the external
tangency. No second arithmetic fact is needed anywhere.

## What blocks it, precisely

Not the geometry, not `natCast`, and not the size of `115` or `128` — those never have to be
written. What fails is numeral arithmetic on **tree-encoded constants near `126`**:

| step | identity | status |
| --- | --- | --- |
| `w = u·e` | `(5+4e)e = 4e² + 5e` | closes |
| `w² = 2u²` | `u²(2 − e²)` | closes |
| `4w − 5u = 7` | substitute `u`, `w` | closes |
| `14 + u + w = 9(w − u)` | `−2(4w − 5u − 7)` | closes |
| `a − b = u + w` | `2(4w − 5u − 7)` | closes |
| **`a + b = 9(14 + u + w)`** | needs `56 + 70 = 9 · 14` | **fails** |
| **`(u+w)·9·9·(w−u) = 81(w²−u²)`** | distributes two nines | **fails** |

Both failures are `Lean.Meta.acLt` on constants that are *products of small factors* — `56 = 8·7`,
`70 = 10·7`, `126 = 18·7` — where the normaliser must still evaluate the products. Raising
`maxHeartbeats` to four million does not move either.

**The next thing to try** is giving `7` itself a variable: every constant in the two failing steps is
a multiple of `7`, so a parameter `k` with `k = 7` supplied as a hypothesis would put `56 + 70 = 9·14`
into the form `8k + 10k = 18k`, which is linear and free. That is untried.

## Status

**21 of the 23 exhibit points are Lean-checked.** These two are the remainder. Everything above is
derived and none of it is in Lean.
-/

end Coordinates
end Apollonius
end Geometry
end MachLib
