import MachLib.PevDeriv

/-!
# Brick two: `y = exp(S)` satisfies `y' = S'·y`

This is the identity the whole differential argument turns on. A polynomial relation in
`y = exp(S(x))` differentiates back into a polynomial relation **in the same `y`** — no new
transcendental appears — and that is what makes a degree-drop against minimality possible. Without
it, differentiating a relation just produces a different, unrelated object.

It costs two lines given the chain rule, which is the point: the expensive part of the differential
route is not this step, it is the bookkeeping around it.

## What is deliberately not done here

**The germ-to-representative transfer.** `RatGerm` says `f = pev P / pev Q` off a finite exceptional
set, and `HasDerivAt` is a *pointwise* notion that `HasDerivAt_congr` transfers only across a
**neighbourhood**. Going from "agrees off a finite set" to "agrees near `x`" needs a
finite-set-avoidance step this corpus does not have yet, so every statement here is about an explicit
function rather than about a germ. That is a real gap and it is named rather than papered over —
`PevRoots` makes the exceptional set finite, so the step is available in principle and is simply not
built.

Consequently the quotient rule below is stated for `pev P · (1 / pev Q)`, the function that is
*literally* differentiated, rather than for `pev P / pev Q`. The two agree wherever `pev Q ≠ 0`; the
difference is only about which function the theorem is *about*, and conflating them is exactly the
kind of quiet step this file is trying not to take.
-/

namespace MachLib

open Real

/-- The chain rule for `exp ∘ S` in the shape the argument uses it: **`y' = S'·y`** for `y = exp(S)`.

`hasDerivAt_exp_comp` (in `EMLTChartKhovanskii`, from the Khovanskii work) already supplies
`exp(S x)·S'`; this is the same fact with the factors in the order that makes the differential
identity readable. Reused rather than redefined — the build caught the duplicate, which is the
second time today that grepping for an existing decoder or lemma would have been cheaper than
writing one. -/
theorem hasDerivAt_exp_comp_swap {S : Real → Real} {S' x : Real} (h : HasDerivAt S S' x) :
    HasDerivAt (fun y => exp (S y)) (S' * exp (S x)) x := by
  have hd := hasDerivAt_exp_comp S S' x h
  have e : exp (S x) * S' = S' * exp (S x) := by mach_mpoly [exp (S x), S']
  rw [e] at hd
  exact hd

/-- **The quotient rule, for the function actually differentiated.** `pev P · (1 / pev Q)` agrees
with `pev P / pev Q` wherever the denominator is nonzero; see the module docstring for why the
distinction is kept explicit. -/
theorem hasDerivAt_ratFn (P Q : List Real) (x : Real) (hQ : pev Q x ≠ 0) :
    HasDerivAt (fun y => pev P y * (1 / pev Q y))
      (pev (pderiv P) x * (1 / pev Q x)
        + pev P x * (-(pev (pderiv Q) x) / (pev Q x * pev Q x))) x :=
  HasDerivAt_mul (fun y => pev P y) (fun y => 1 / pev Q y)
    (pev (pderiv P) x) (-(pev (pderiv Q) x) / (pev Q x * pev Q x)) x
    (hasDerivAt_pev P x)
    (HasDerivAt_inv (fun y => pev Q y) (pev (pderiv Q) x) x hQ (hasDerivAt_pev Q x))

/-- **The composite the differential argument consumes**: `exp` of a rational function, with its
derivative expressed through `pderiv`. Everything needed to differentiate a relation in
`y = exp(P/Q)` is now available as a single term. -/
theorem hasDerivAt_exp_ratFn (P Q : List Real) (x : Real) (hQ : pev Q x ≠ 0) :
    HasDerivAt (fun y => exp (pev P y * (1 / pev Q y)))
      ((pev (pderiv P) x * (1 / pev Q x)
        + pev P x * (-(pev (pderiv Q) x) / (pev Q x * pev Q x)))
        * exp (pev P x * (1 / pev Q x))) x :=
  hasDerivAt_exp_comp_swap (hasDerivAt_ratFn P Q x hQ)

end MachLib
