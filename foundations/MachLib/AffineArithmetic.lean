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

/-! ## 3. The affine FORM — where shared symbols actually buy something

The two lemmas above bound what each *operation* discards. They say nothing about the structure the
whole method rests on: that a noise symbol appearing in two places is **the same symbol**, so its
contributions add algebraically and can cancel.

That is the entire difference from the entrywise fold, so it is the thing that has to be stated.

A form is a centre plus a coefficient per symbol index; `eval` interprets it against a **shared**
assignment `e : Nat → Real` with `|e i| ≤ 1`. Sharing is not a convention here — it is forced by
`eval` taking one `e` for both operands. -/

/-- Coefficient list, read against symbol indices `i, i+1, …`. -/
noncomputable def evalDev : List Real → Nat → (Nat → Real) → Real
  | [], _, _ => 0
  | c :: rest, i, e => c * e i + evalDev rest (i + 1) e

/-- The radius: sum of `|coefficient|`. -/
noncomputable def radDev : List Real → Real
  | [] => 0
  | c :: rest => abs c + radDev rest

/-- Coefficientwise addition, padding the shorter list. **Index `i` meets index `i`** — this
definition is where "the same symbol" becomes a mathematical fact rather than a naming discipline. -/
noncomputable def addDev : List Real → List Real → List Real
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: addDev l m

/-- Hoisted for `mach_mpoly`, whose atom list is elaborated OUTSIDE the tactic block — so names
bound by `cases`/`intro` are invisible there. **Fourth instance of this trap in this library**;
the fix is always the same, and stating the identity generically also keeps the goal small. -/
private theorem affine_cons_id (a b x L M : Real) :
    (a + b) * x + (L + M) = (a * x + L) + (b * x + M) := by
  mach_mpoly [a, b, x, L, M]

/-- A valid noise assignment: every symbol in `[-1, 1]`. -/
def ValidNoise (e : Nat → Real) : Prop := ∀ i, abs (e i) ≤ 1

/-- **SOUNDNESS: the radius bounds the deviation.** Without this the whole method is decoration. -/
theorem evalDev_le_radDev (e : Nat → Real) (he : ValidNoise e) (l : List Real) :
    ∀ i : Nat, abs (evalDev l i e) ≤ radDev l := by
  induction l with
  | nil =>
      intro i
      rw [show evalDev [] i e = 0 from rfl, show radDev [] = 0 from rfl, abs_zero]
      exact le_refl 0
  | cons c rest ih =>
      intro i
      rw [show evalDev (c :: rest) i e = c * e i + evalDev rest (i + 1) e from rfl,
          show radDev (c :: rest) = abs c + radDev rest from rfl]
      refine le_trans (abs_add _ _) (add_le_add_both ?_ (ih (i + 1)))
      rw [abs_mul]
      have h := mul_le_mul_of_nonneg_left (he i) (abs_nonneg c)
      rwa [mul_one_ax] at h

/-- **THE HOMOMORPHISM — the theorem that states what affine arithmetic buys.**

`evalDev (addDev l m) = evalDev l + evalDev m`, with **one shared `e`**. Coefficients at the same
index are added *before* being multiplied by their symbol, so opposite contributions cancel
algebraically. The entrywise fold has no way to express this step: it would bound `|l|` and `|m|`
separately and add the bounds. -/
theorem evalDev_addDev (e : Nat → Real) (l : List Real) :
    ∀ (m : List Real) (i : Nat), evalDev (addDev l m) i e = evalDev l i e + evalDev m i e := by
  induction l with
  | nil =>
      intro m i
      rw [show addDev [] m = m from rfl, show evalDev ([] : List Real) i e = 0 from rfl,
          add_comm, add_zero]
  | cons a l ih =>
      intro m i
      cases m with
      | nil =>
          rw [show addDev (a :: l) [] = a :: l from rfl,
              show evalDev ([] : List Real) i e = 0 from rfl, add_zero]
      | cons b m =>
          rw [show addDev (a :: l) (b :: m) = (a + b) :: addDev l m from rfl,
              show evalDev ((a + b) :: addDev l m) i e
                = (a + b) * e i + evalDev (addDev l m) (i + 1) e from rfl,
              ih m (i + 1),
              show evalDev (a :: l) i e = a * e i + evalDev l (i + 1) e from rfl,
              show evalDev (b :: m) i e = b * e i + evalDev m (i + 1) e from rfl]
          exact affine_cons_id a b (e i) (evalDev l (i + 1) e) (evalDev m (i + 1) e)

/-- **THE CANCELLATION, made formal.** A form added to its own negation has value **exactly zero**,
at every valid assignment — not "bounded by twice the radius".

This is the property the entrywise fold cannot represent, in one line. It is why `x · recip(x)`
collapses toward `1` while `x · recip(y)` does not, and therefore why the EKF bound moved 4700× when
nothing else did: `P`'s perturbation enters `K`'s numerator and denominator on the SAME symbols. -/
theorem evalDev_cancels (e : Nat → Real) (l : List Real) (i : Nat) :
    evalDev (addDev l (List.map (fun c => -c) l)) i e = 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons a rest ih =>
      rw [show List.map (fun c => -c) (a :: rest) = (-a) :: List.map (fun c => -c) rest from rfl,
          show addDev (a :: rest) ((-a) :: List.map (fun c => -c) rest)
            = (a + -a) :: addDev rest (List.map (fun c => -c) rest) from rfl,
          show evalDev ((a + -a) :: addDev rest (List.map (fun c => -c) rest)) i e
            = (a + -a) * e i + evalDev (addDev rest (List.map (fun c => -c) rest)) (i+1) e from rfl,
          ih (i + 1), add_neg]
      rw [show (0 : Real) * e i = 0 from by mach_ring, add_zero]

/-- And the entrywise fold's answer for the same quantity: `rad l + rad (-l) = 2·rad l`. So on a
form of radius `r`, affine arithmetic gives **0** and the fold gives **2r** — the gap is the whole
method. -/
theorem radDev_neg_doubles (l : List Real) :
    radDev (List.map (fun c => -c) l) = radDev l := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      rw [show List.map (fun c => -c) (a :: rest) = (-a) :: List.map (fun c => -c) rest from rfl,
          show radDev ((-a) :: List.map (fun c => -c) rest)
            = abs (-a) + radDev (List.map (fun c => -c) rest) from rfl,
          abs_neg, ih, show radDev (a :: rest) = abs a + radDev rest from rfl]

end MachLib.Real
