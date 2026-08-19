import MachLib.Geometry.Apollonius.Examples

/-!
# The flagship coordinates, checked

The exhibit at `monogate.org/proofs/apollonius` carried, per solution, a row reading
**Lean-checked point — NOT YET**, under the disclaimer:

> **NOT PROVED — the eight coordinates below.** COMPUTED here in exact arithmetic and verified to
> have zero tangency residuals; NOT checked in Lean. MachLib proves the COUNT and its structure,
> not these particular coordinates.

This file closes that for the flagship, `d = 4`, `ρ = 1` — three unit circles at `(0,0)`, `(4,0)`,
`(0,4)`. Each solution is stated as an explicit centre and radius in closed form and discharged
against `Circle.lean`'s **geometric** predicates `TangentExt` / `TangentInt`, not against the
algebraic enumeration equation. Zero residual, symbolically.

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

/-! ### The other six: blocked, and the diagnosis is precise

Solutions 1 and 8 above are checked. The remaining six are **not**, and this records exactly why so
the next attempt does not repeat the three that failed here.

Their coordinates carry denominators — `3 + 3√2/2` for the `(outer,inner,inner)` /
`(inner,outer,outer)` pair, and `2 ± √21/3` with radius `2√21/3` for the four mixed modes. The
groundwork above (`two_mul_half`, `h`, `h_sq`, `h_pos`) removes the denominator cleanly: with
`h = √2/2` the pair becomes `3 + 3h` and `2 + 6h`, and `2h² = 1` is the only algebraic fact needed.
That part works.

What does not work is the final polynomial identity. Three encodings were tried:

| attempt | encoding of the constants | result |
| --- | --- | --- |
| 1 | clear denominators by scaling the identity by `4` | `mach_mpoly` timeout |
| 2 | `h`-parametrised, constants as sums (`18` = eighteen `1+`) | timeout |
| 3 | `h`-parametrised, constants as products (`18` = `2·3·3`) | timeout |

**The limit is not coefficient magnitude.** Solutions 1 and 8 close instantly with the constant `8`,
and attempt 3 fails with `18` written in five nodes. `MachLib.Real` has `OfNat` only for `0` and
`1`, so every constant is a syntax tree, and the normaliser's cost is driven by the *tree* the
identity generates during distribution — not by the number it denotes. Attempt 1 was the worst
because scaling multiplies every constant tree at once.

This is the same wall the `natCast` work exists to remove, and it is the documented unblocker. Until
then the honest position is the one the exhibit states: **two of the eight coordinates are
Lean-checked, six are computed in exact arithmetic and verified to have zero tangency residual by an
untrusted oracle.**

The two that are checked are not arbitrary. They are the outer and inner Soddy circles — the
antipodal pair through the configuration's symmetry axis — so what is verified is precisely the pair
whose centres are rational.
-/

end Coordinates
end Apollonius
end Geometry
end MachLib
