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


/-- **A root from the discriminant, division-free.**

Given `s` with `s² = b² − 4ac`, any `r` with `2a·r = −b + s` is a root. Stated on the scaled root
rather than on `(−b+s)/(2a)` so no quotient is ever formed, and with `s` an arbitrary square root of
the discriminant so that the two branches `±√disc` are the *same* theorem applied twice. -/
theorem quadratic_root_of_disc {a b c s r : Real} (ha : a ≠ 0)
    (hs : s * s = b * b - (1 + 1) * (1 + 1) * a * c)
    (hr : (1 + 1) * a * r = -b + s) :
    a * r * r + b * r + c = 0 := by
  have h4a : (1 + 1) * (1 + 1) * a ≠ 0 := by
    intro hz
    exact ha (right_of_mul_eq_zero
      (ne_of_gt (mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax)
                         (add_pos zero_lt_one_ax zero_lt_one_ax))) hz)
  refine right_of_mul_eq_zero h4a ?_
  have e : (1 + 1) * (1 + 1) * a * (a * r * r + b * r + c)
      = ((1 + 1) * a * r) * ((1 + 1) * a * r)
        + (1 + 1) * b * ((1 + 1) * a * r)
        + (1 + 1) * (1 + 1) * a * c := by
    mach_mpoly [a, b, c, r] <;> mach_ring
  rw [e, hr]
  have e2 : (-b + s) * (-b + s) + (1 + 1) * b * (-b + s) + (1 + 1) * (1 + 1) * a * c
      = (s * s - (b * b - (1 + 1) * (1 + 1) * a * c)) := by
    mach_mpoly [a, b, c, s] <;> mach_ring
  rw [e2, hs]
  mach_mpoly [b, a, c] <;> mach_ring

/-- **The two branches are distinct when the discriminant is nonzero.** Both scalings share the
left-hand side `2a·r`, so equal roots force `−b + s = −b − s`, hence `2s = 0`. -/
theorem quadratic_roots_distinct {a s b r₁ r₂ : Real} (hsne : s ≠ 0)
    (h₁ : (1 + 1) * a * r₁ = -b + s) (h₂ : (1 + 1) * a * r₂ = -b - s) :
    r₁ ≠ r₂ := by
  intro heq
  subst heq
  have hbs : -b + s = -b - s := by rw [← h₁, h₂]
  have e2 : (1 + 1) * s = 0 := by
    refine eq_of_sub_eq_zero ?_
    have e : (1 + 1) * s - 0 = (-b + s) - (-b - s) := by mach_mpoly [b, s] <;> mach_ring
    rw [e, hbs]
    mach_mpoly [b, s] <;> mach_ring
  exact hsne (right_of_mul_eq_zero
    (ne_of_gt (add_pos zero_lt_one_ax zero_lt_one_ax)) e2)


/-- **A scaled solution always exists** when the scale is nonzero. The one place a field inverse is
formed in this development; everything above it consumes the scaled equation `u·r = v` instead. -/
theorem exists_scaled (u v : Real) (hu : u ≠ 0) : ∃ r : Real, u * r = v := by
  refine ⟨v * (1 / u), ?_⟩
  have e : u * (v * (1 / u)) = v * (u * (1 / u)) := by mach_ring
  rw [e, mul_inv u hu]
  mach_ring

/-- **Two distinct roots from a nonzero discriminant.**

Existence, not just verification: `exists_scaled` produces the two scaled roots and
`quadratic_root_of_disc` certifies each. The hypothesis is `s ≠ 0` with `s² = b² − 4ac` — so the
caller supplies a square root rather than this theorem computing one, and the *same* statement
covers both branches because `(−s)² = s²`. -/
theorem two_distinct_roots {a b c s : Real} (ha : a ≠ 0) (hsne : s ≠ 0)
    (hs : s * s = b * b - (1 + 1) * (1 + 1) * a * c) :
    ∃ r₁ r₂ : Real, r₁ ≠ r₂ ∧ a * r₁ * r₁ + b * r₁ + c = 0 ∧ a * r₂ * r₂ + b * r₂ + c = 0 := by
  have hu : (1 + 1) * a ≠ 0 := by
    intro hz
    exact ha (right_of_mul_eq_zero (ne_of_gt (add_pos zero_lt_one_ax zero_lt_one_ax)) hz)
  obtain ⟨r₁, h₁⟩ := exists_scaled ((1 + 1) * a) (-b + s) hu
  obtain ⟨r₂, h₂⟩ := exists_scaled ((1 + 1) * a) (-b - s) hu
  have h₂' : (1 + 1) * a * r₂ = -b + -s := by rw [h₂]; mach_ring
  have hsneg : (-s) * (-s) = b * b - (1 + 1) * (1 + 1) * a * c := by
    have e : (-s) * (-s) = s * s := by mach_ring
    rw [e]; exact hs
  exact ⟨r₁, r₂, quadratic_roots_distinct hsne h₁ h₂,
    quadratic_root_of_disc ha hs h₁, quadratic_root_of_disc ha hsneg h₂'⟩


/-- **A negative leading coefficient makes the discriminant positive for free.**

`b² − 4ac = b² + 4(−a)c`, a nonnegative square plus a positive product. No expansion of `a`, `b` or
`c` is required — which matters when they are large polynomials whose product would be past what a
ring normaliser can handle. -/
theorem disc_pos_of_lead_neg {a b c : Real} (ha : a < 0) (hc : 0 < c) :
    0 < b * b - (1 + 1) * (1 + 1) * a * c := by
  have two_pos : (0 : Real) < 1 + 1 := add_pos zero_lt_one_ax zero_lt_one_ax
  have hna : (0 : Real) < -a := by
    have v := add_lt_add_left ha (-a)
    have l : -a + a = 0 := by mach_ring
    have rr : -a + (0 : Real) = -a := by mach_ring
    rw [l, rr] at v; exact v
  have hpos : (0 : Real) < (1 + 1) * (1 + 1) * (-a) * c :=
    mul_pos (mul_pos (mul_pos two_pos two_pos) hna) hc
  have e : b * b - (1 + 1) * (1 + 1) * a * c = b * b + (1 + 1) * (1 + 1) * (-a) * c := by
    mach_mpoly [a, b, c] <;> mach_ring
  rw [e]
  have v := add_lt_add_left hpos (b * b)
  have l : b * b + (0 : Real) = b * b := by mach_ring
  rw [l] at v
  have hbb : (0 : Real) ≤ b * b := by
    rcases lt_total 0 b with hb | hb | hb
    · exact le_of_lt (mul_pos hb hb)
    · rw [← hb]
      have z : (0 : Real) * 0 = 0 := by mach_ring
      rw [z]; exact le_refl 0
    · have hnb : (0 : Real) < -b := by
        have w := add_lt_add_left hb (-b)
        have l2 : -b + b = 0 := by mach_ring
        have r2 : -b + (0 : Real) = -b := by mach_ring
        rw [l2, r2] at w; exact w
      have e2 : b * b = (-b) * (-b) := by mach_ring
      rw [e2]; exact le_of_lt (mul_pos hnb hnb)
  exact lt_of_le_of_lt hbb v

end QuadraticRoots
end MachLib
