import MachLib.BipevDescent

/-!
# The quotient rule, cleared

The last ingredient the composition needs. `hasDerivAt_ratFn` (brick three) gives `S'` in the form

```
S' = P'·(1/Q) + P·(−Q'/(Q·Q))
```

and everything downstream wants it in the form the count consumes: `S'·Q² = D` with
`D = P'Q − PQ'`. That is the hypothesis `bipev_dcoeffs_eq_zero_on_tail` takes and the identity
`cleared_relation_impossible` is stated against.

The conversion is one field computation, and the only thing it needs is `Q(x) ≠ 0` — which is
already carried, since brick three needs it to differentiate at all. **No new hypothesis enters
here**, which is worth checking rather than assuming: a composition step that quietly added a side
condition would be the sort of thing that only surfaces at the very end.
-/

namespace MachLib

open Real

/-- `a/b · b = a`, from `div_def` and `mul_inv`. Proved locally: `PolyDivision`'s copy is `private`,
and `DivisionError`'s is a heavier import than one line of field arithmetic. -/
private theorem div_mul_cancel_here {a b : Real} (hb : b ≠ 0) : a / b * b = a := by
  rw [div_def a b hb, mul_assoc, mul_comm (1 / b) b, mul_inv b hb, mul_one_ax]

/-- **`S'·Q² = D`.** Brick three's derivative, multiplied out. -/
theorem ratFn_deriv_cleared (P Q : List Real) (x : Real) (hQ : pev Q x ≠ 0) :
    (pev (pderiv P) x * (1 / pev Q x)
       + pev P x * (-(pev (pderiv Q) x) / (pev Q x * pev Q x))) * pev (pmul Q Q) x
      = pev (psub (pmul (pderiv P) Q) (pmul P (pderiv Q))) x := by
  have hqq : pev Q x * pev Q x ≠ 0 := mul_ne_zero hQ hQ
  -- (1/Q)·Q² = Q
  have h1 : (1 / pev Q x) * (pev Q x * pev Q x) = pev Q x := by
    have hinv : pev Q x * (1 / pev Q x) = 1 := mul_inv (pev Q x) hQ
    have e : (1 / pev Q x) * (pev Q x * pev Q x)
        = (pev Q x * (1 / pev Q x)) * pev Q x := by mach_ring
    rw [e, hinv, one_mul_thm]
  -- (−Q'/Q²)·Q² = −Q'
  have h2 : (-(pev (pderiv Q) x) / (pev Q x * pev Q x)) * (pev Q x * pev Q x)
      = -(pev (pderiv Q) x) := div_mul_cancel_here hqq
  rw [pev_pmul, pev_psub, pev_pmul, pev_pmul]
  have hsplit : (pev (pderiv P) x * (1 / pev Q x)
        + pev P x * (-(pev (pderiv Q) x) / (pev Q x * pev Q x))) * (pev Q x * pev Q x)
      = pev (pderiv P) x * ((1 / pev Q x) * (pev Q x * pev Q x))
        + pev P x * ((-(pev (pderiv Q) x) / (pev Q x * pev Q x)) * (pev Q x * pev Q x)) := by
    mach_mpoly [pev (pderiv P) x, pev P x, pev Q x, 1 / pev Q x,
                -(pev (pderiv Q) x) / (pev Q x * pev Q x)]
  rw [hsplit, h1, h2]
  mach_ring

end MachLib
