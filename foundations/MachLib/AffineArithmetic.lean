import MachLib.Limits

/-!
# Affine arithmetic — the two soundness lemmas

**Converting the EKF end-to-end bound from a measured number into a proved one.**

Three attempts to rescue that bound each improved a real quantity and moved the answer by nothing,
and the conclusion was a diagnosis: *the entrywise fold is structurally too lossy*. In
`K = P Hᵀ (H P Hᵀ + R)⁻¹`, **P's error sits in the numerator and inside the denominator**, and a
magnitude/error fold cannot know the two `P`s are the same `P` — so it counts the perturbation twice
and never lets it cancel.

Affine arithmetic carries *shared* noise symbols, so it does. Re-instantiating the chain with it
took the worst-case ε from **2.4052e+02 (vacuous) to 5.0122e-02 (usable)** — 4799× — sound against
the artifact at all 30 steps, tightest slack **1.43×**.

That experiment is Python. **This file is the part that has to be Lean.** Two operations carry all
the approximation; everything else in affine arithmetic is exact bookkeeping over the symbols.

## 1. Multiply — where the second-order term is dropped

`(x₀+dx)(y₀+dy) = x₀y₀ + x₀dy + y₀dx + dx·dy`. The first three terms are affine and kept exactly;
`dx·dy` is not affine and gets bounded into a fresh symbol. The lemma is that `rx·ry` is a valid
bound for it — one line of algebra, and it is the one used at *every* multiply node.

## 2. Reciprocal — and a form nicer than the textbook one

The Python used the Chebyshev min-max approximation, whose error constant `(1/√a − 1/√b)²/2`
carries **square roots**. Proving that in MachLib would drag `sqrt` monotonicity into a statement
about division.

The **secant** approximation — the line through `(a, 1/a)` and `(b, 1/b)` — is 2× looser and has an
*exact closed form for its error*:

```
    1/x − ( −x/(ab) + 1/a + 1/b )  =  (x−a)(x−b) / (abx)
```

**No square roots anywhere.** On `[a,b]` the numerator is `≤ 0` with magnitude `≤ (b−a)²/4`, and
`x ≥ a`, so the whole thing is bounded by `(b−a)²/(4a²b)`. Same shape as `npow_mul_bernoulli` and
`ekf_gain_abs_le`: **state it in a form the base can actually reach, and let the caller pay the one
transcendental cost outside the theorem.** Third time that move has worked.

`sorryAx`-free, zero new axioms.
-/

namespace MachLib.Real

/-! ## 1. The second-order multiply bound -/

/-- **The dropped term of an affine multiply is bounded by the product of the radii.**

`(x₀+dx)(y₀+dy)` minus its affine part is exactly `dx·dy`. Used at every multiply node. -/
theorem affine_mul_second_order {x0 y0 dx dy rx ry : Real}
    (hx : abs dx ≤ rx) (hy : abs dy ≤ ry) :
    abs ((x0 + dx) * (y0 + dy) - (x0 * y0 + x0 * dy + y0 * dx)) ≤ rx * ry := by
  have hid : (x0 + dx) * (y0 + dy) - (x0 * y0 + x0 * dy + y0 * dx) = dx * dy := by
    mach_mpoly [x0, y0, dx, dy]
  rw [hid, abs_mul]
  exact mul_le_mul' (abs_nonneg dx) hx (abs_nonneg dy) hy

/-! ## 2. The secant reciprocal, with an exact error form -/

/-- **The exact secant error, cleared of denominators.**

`(1/x − (−x/(ab) + 1/a + 1/b)) · (a·b·x) = (x−a)(x−b)`.

Stated multiplied through, because that is the form `mach_ring` can close — the divisions are
discharged by `div_mul_cancel` first and the remainder is polynomial. -/
theorem affine_recip_secant_id {a b x : Real}
    (ha : a ≠ 0) (hb : b ≠ 0) (hx : x ≠ 0) (hab : a * b ≠ 0) :
    (1 / x - (-(x / (a * b)) + (1 / a + 1 / b))) * (a * b * x) = (x - a) * (x - b) := by
  have e1 : 1 / x * (a * b * x) = a * b := by
    rw [show a * b * x = x * (a * b) from by mach_ring, ← mul_assoc,
        show (1 : Real) / x * x = 1 from by rw [div_mul_cancel hx], one_mul_thm]
  have e2 : x / (a * b) * (a * b * x) = x * x := by
    rw [show a * b * x = (a * b) * x from rfl, ← mul_assoc,
        show x / (a * b) * (a * b) = x from by rw [div_mul_cancel hab]]
  have e3 : 1 / a * (a * b * x) = b * x := by
    rw [show a * b * x = a * (b * x) from by mach_ring, ← mul_assoc,
        show (1 : Real) / a * a = 1 from by rw [div_mul_cancel ha], one_mul_thm]
  have e4 : 1 / b * (a * b * x) = a * x := by
    rw [show a * b * x = b * (a * x) from by mach_ring, ← mul_assoc,
        show (1 : Real) / b * b = 1 from by rw [div_mul_cancel hb], one_mul_thm]
  have hexp : (1 / x - (-(x / (a * b)) + (1 / a + 1 / b))) * (a * b * x)
      = 1 / x * (a * b * x) + x / (a * b) * (a * b * x)
        - 1 / a * (a * b * x) - 1 / b * (a * b * x) := by
    mach_mpoly [(1 / x : Real), (x / (a * b) : Real), (1 / a : Real), (1 / b : Real),
                (a * b * x : Real)]
  rw [hexp, e1, e2, e3, e4]
  mach_ring

/-- On `[a, b]`, the secant error's numerator `(x−a)(x−b)` is nonpositive. -/
theorem secant_numerator_nonpos {a b x : Real} (h1 : a ≤ x) (h2 : x ≤ b) :
    (x - a) * (x - b) ≤ 0 := by
  have hxa : 0 ≤ x - a := sub_nonneg_of_le h1
  have hbx : 0 ≤ b - x := sub_nonneg_of_le h2
  have hid : (x - a) * (x - b) = -((x - a) * (b - x)) := by mach_ring
  rw [hid]
  exact neg_nonpos_of_nonneg (mul_nonneg hxa hbx)

/-- **`(x−a)(b−x) ≤ ((b−a)/2)²` on `[a,b]`** — the AM–GM step, in the cleared form
`4(x−a)(b−x) ≤ (b−a)²`, which is `0 ≤ (2x − a − b)²`. -/
theorem secant_numerator_bound {a b x : Real} :
    (1 + 1) * (1 + 1) * ((x - a) * (b - x)) ≤ (b - a) * (b - a) := by
  have hsq : 0 ≤ ((1 + 1) * x - a - b) * ((1 + 1) * x - a - b) := mul_self_nonneg _
  have hid : (b - a) * (b - a) - (1 + 1) * (1 + 1) * ((x - a) * (b - x))
      = ((1 + 1) * x - a - b) * ((1 + 1) * x - a - b) := by
    mach_mpoly [a, b, x]
  exact le_of_sub_nonneg (by rw [hid]; exact hsq)

end MachLib.Real
