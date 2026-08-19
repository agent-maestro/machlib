import MachLib.Ring
import MachLib.MPolyRing

/-!
# Degree-2 root bounds, by subtraction

`ax² + bx + c` has at most two distinct real roots, and `bx + c` with `b ≠ 0` at most one. Both are
proved directly from the field axioms — subtract two root equations, factor out the difference, and
use that a nonzero element has an inverse.

**Why not the polynomial framework.** `PolynomialRootCount` states in its own docstring that it
"does not prove the general degree/root-count theorem": it carries the degree-1 case and *names* the
general one (`RootListDegreeBound`, and `ProductDegreeBoundTarget` in
`NormalizedPolynomialRootCount`) as open targets. Reaching degree 2 through it would mean finishing
it. The direct proof is forty lines and buys a strictly smaller trust base — the footprint here is
the **field axioms only**: no order, no `sqrt`, no `exp`/`log`. A consumer that needs "a quadratic
has at most two roots" should not thereby inherit the analytic hierarchy.

Written for the Apollonius enumeration, where each mode class contributes one quadratic in the
radius, but nothing here mentions geometry.

**Tactic hazard, recorded.** Three of these goals were first attempted with `mach_ring`, which
reported `unsolved goals` *and* left `sorryAx` in the resulting axiom footprint. The error text
alone would not have revealed that; `#print axioms` did. `mach_mpoly` closes all three.
-/

namespace MachLib
namespace QuadraticRoots

open Real

/-- No zero divisors, derived from `mul_inv` alone. -/
private theorem right_of_mul_eq_zero {u v : Real} (hu : u ≠ 0) (h : u * v = 0) : v = 0 := by
  have hone : u * (1 / u) = 1 := mul_inv u hu
  have e : (1 / u) * (u * v) = ((u * (1 / u)) * v) := by mach_ring
  rw [hone] at e
  have e1 : (1 : Real) * v = v := by mach_ring
  rw [e1] at e
  rw [h] at e
  have z : (1 / u) * (0 : Real) = 0 := by mach_ring
  rw [z] at e
  exact e.symm

private theorem eq_of_sub_eq_zero {u v : Real} (h : u - v = 0) : u = v := by
  have e : u = (u - v) + v := by mach_ring
  rw [h] at e
  have z : (0 : Real) + v = v := by mach_ring
  rw [z] at e; exact e

private theorem sub_ne_zero_of_ne {u v : Real} (h : u ≠ v) : u - v ≠ 0 :=
  fun hz => h (eq_of_sub_eq_zero hz)

/-- **Two roots of a genuine quadratic satisfy Vieta's linear relation.** -/
theorem quadratic_two_roots_sum {a b c r s : Real} (hne : r ≠ s)
    (hr : a * r * r + b * r + c = 0) (hs : a * s * s + b * s + c = 0) :
    a * (r + s) + b = 0 := by
  refine right_of_mul_eq_zero (sub_ne_zero_of_ne hne) ?_
  have e : (r - s) * (a * (r + s) + b)
      = (a * r * r + b * r + c) - (a * s * s + b * s + c) := by mach_mpoly [a, b, c, r, s]
  rw [e, hr, hs]; mach_ring

/-- **A genuine quadratic has no three pairwise-distinct roots.** -/
theorem quadratic_no_three_distinct_roots {a b c r s t : Real} (ha : a ≠ 0)
    (hr : a * r * r + b * r + c = 0)
    (hs : a * s * s + b * s + c = 0)
    (ht : a * t * t + b * t + c = 0) :
    r = s ∨ r = t ∨ s = t := by
  rcases Classical.em (r = s) with h | hrs
  · exact Or.inl h
  rcases Classical.em (r = t) with h | hrt
  · exact Or.inr (Or.inl h)
  refine Or.inr (Or.inr ?_)
  have hA : a * (r + s) + b = 0 := quadratic_two_roots_sum hrs hr hs
  have hB : a * (r + t) + b = 0 := quadratic_two_roots_sum hrt hr ht
  refine eq_of_sub_eq_zero (right_of_mul_eq_zero ha ?_)
  have e : a * (s - t) = (a * (r + s) + b) - (a * (r + t) + b) := by mach_mpoly [a, b, r, s, t]
  rw [e, hA, hB]; mach_ring

/-- **The linear degeneration: `a = 0`, `b ≠ 0` gives at most one root.** -/
theorem linear_root_unique {b c r s : Real} (hb : b ≠ 0)
    (hr : b * r + c = 0) (hs : b * s + c = 0) : r = s := by
  refine eq_of_sub_eq_zero (right_of_mul_eq_zero hb ?_)
  have e : b * (r - s) = (b * r + c) - (b * s + c) := by mach_mpoly [b, c, r, s]
  rw [e, hr, hs]; mach_ring

end QuadraticRoots
end MachLib
