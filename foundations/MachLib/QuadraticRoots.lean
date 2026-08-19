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

/-- No zero divisors, derived from `mul_inv` alone. Public because the Apollonius elimination
needs it to cancel the scale factors that clearing denominators introduces. -/
theorem right_of_mul_eq_zero {u v : Real} (hu : u ≠ 0) (h : u * v = 0) : v = 0 := by
  have hone : u * (1 / u) = 1 := mul_inv u hu
  have e : (1 / u) * (u * v) = ((u * (1 / u)) * v) := by mach_ring
  rw [hone] at e
  have e1 : (1 : Real) * v = v := by mach_ring
  rw [e1] at e
  rw [h] at e
  have z : (1 / u) * (0 : Real) = 0 := by mach_ring
  rw [z] at e
  exact e.symm

theorem eq_of_sub_eq_zero {u v : Real} (h : u - v = 0) : u = v := by
  have e : u = (u - v) + v := by mach_ring
  rw [h] at e
  have z : (0 : Real) + v = v := by mach_ring
  rw [z] at e; exact e

theorem sub_ne_zero_of_ne {u v : Real} (h : u ≠ v) : u - v ≠ 0 :=
  fun hz => h (eq_of_sub_eq_zero hz)

/-- **Cancellation.** `a ≠ 0 → a·u = a·v → u = v`. Clearing a denominator by multiplying through
is only reversible because of this, and every elimination step below leans on it. -/
theorem mul_left_cancel {a u v : Real} (ha : a ≠ 0) (h : a * u = a * v) : u = v := by
  refine eq_of_sub_eq_zero (right_of_mul_eq_zero ha ?_)
  have e : a * (u - v) = a * u - a * v := by mach_mpoly [a, u, v]
  rw [e, h]
  have z : a * v - a * v = 0 := by mach_mpoly [a, v]
  exact z

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


/-- **A quadratic vanishing at three distinct points is the zero polynomial.** The strengthening
`quadratic_no_three_distinct_roots` gives by contraposition, chained through the linear case: three
distinct roots force `a = 0`, then `b = 0`, then `c = 0`.

Needed where a reduced equation's coefficients are not known in advance — one cannot assume the
leading coefficient is nonzero, so the honest statement is that three roots collapse the whole
polynomial rather than contradicting a hypothesis. -/
theorem quadratic_zero_of_three_roots {a b c r s t : Real}
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hr : a * r * r + b * r + c = 0)
    (hs : a * s * s + b * s + c = 0)
    (ht : a * t * t + b * t + c = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have ha : a = 0 := by
    rcases Classical.em (a = 0) with h | h
    · exact h
    · rcases quadratic_no_three_distinct_roots h hr hs ht with e | e | e
      · exact absurd e hrs
      · exact absurd e hrt
      · exact absurd e hst
  subst ha
  have hr' : b * r + c = 0 := by
    have e : b * r + c = 0 * r * r + b * r + c := by mach_mpoly [b, c, r]
    rw [e]; exact hr
  have hs' : b * s + c = 0 := by
    have e : b * s + c = 0 * s * s + b * s + c := by mach_mpoly [b, c, s]
    rw [e]; exact hs
  have hb : b = 0 := by
    rcases Classical.em (b = 0) with h | h
    · exact h
    · exact absurd (linear_root_unique h hr' hs') hrs
  subst hb
  have hc : c = 0 := by
    have e : c = 0 * r + c := by mach_mpoly [c, r]
    rw [e]; exact hr'
  exact ⟨rfl, rfl, hc⟩

/-- **Cramer's rule for a 2×2 system, division-free.**

Stated as an equivalence between the system and its determinant-scaled solution, so it can be used
in both directions without ever forming a quotient. The nonsingularity hypothesis is exactly what
the backward direction needs — and in the Apollonius elimination this is the *only* place a
general-position assumption enters, which is how that assumption gets forced rather than chosen. -/
theorem cramer_2x2 {p₁ p₂ q₁ q₂ u v x y : Real} (hdet : p₁ * q₂ - p₂ * q₁ ≠ 0) :
    (p₁ * x + p₂ * y = u ∧ q₁ * x + q₂ * y = v)
      ↔ ((p₁ * q₂ - p₂ * q₁) * x = u * q₂ - p₂ * v
          ∧ (p₁ * q₂ - p₂ * q₁) * y = p₁ * v - u * q₁) := by
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have e : (p₁ * q₂ - p₂ * q₁) * x = q₂ * (p₁ * x + p₂ * y) - p₂ * (q₁ * x + q₂ * y) := by
        mach_mpoly [p₁, p₂, q₁, q₂, x, y]
      rw [e, h1, h2]; mach_mpoly [u, v, p₂, q₂]
    · have e : (p₁ * q₂ - p₂ * q₁) * y = p₁ * (q₁ * x + q₂ * y) - q₁ * (p₁ * x + p₂ * y) := by
        mach_mpoly [p₁, p₂, q₁, q₂, x, y]
      rw [e, h1, h2]; mach_mpoly [u, v, p₁, q₁]
  · rintro ⟨h1, h2⟩
    constructor
    · refine mul_left_cancel hdet ?_
      have e : (p₁ * q₂ - p₂ * q₁) * (p₁ * x + p₂ * y)
          = p₁ * ((p₁ * q₂ - p₂ * q₁) * x) + p₂ * ((p₁ * q₂ - p₂ * q₁) * y) := by
        mach_mpoly [p₁, p₂, q₁, q₂, x, y]
      rw [e, h1, h2]; mach_mpoly [u, v, p₁, p₂, q₁, q₂]
    · refine mul_left_cancel hdet ?_
      have e : (p₁ * q₂ - p₂ * q₁) * (q₁ * x + q₂ * y)
          = q₁ * ((p₁ * q₂ - p₂ * q₁) * x) + q₂ * ((p₁ * q₂ - p₂ * q₁) * y) := by
        mach_mpoly [p₁, p₂, q₁, q₂, x, y]
      rw [e, h1, h2]; mach_mpoly [u, v, p₁, p₂, q₁, q₂]

end QuadraticRoots
end MachLib
