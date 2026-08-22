import MachLib.BoundedGermEnvelope
import MachLib.Differentiation

/-!
# Differentiating a coefficient list — brick one of the differential route

Today's two envelope theorems proved that **no growth argument can reach the bounded branch** of
`BoundedGermTranscendence`: `F ∘ S` is polynomially enveloped there, so every instrument in this
corpus has a false hypothesis. `BoundedGermTranscendence`'s own docstring anticipated this — *"a
bounded `F ∘ S` is indistinguishable from an algebraic function by any envelope, which is why the
route through differentiation is the one on offer"* — and that prose is now backed by a theorem
rather than asserted.

So: differentiation. This file is the first brick, and it is deliberately only the first.

## The Horner-native derivative

The obvious definition scales each coefficient by its index, which then needs an index-carrying
recursion and a lemma relating it back to Horner form. The Horner-native one needs neither:

```
pderiv []        = []
pderiv (_ :: cs) = padd cs (0 :: pderiv cs)
```

because `pev (padd cs (0 :: pderiv cs)) x = pev cs x + x · pev (pderiv cs) x` **is** the product rule
applied to `c + x·P(x)`, and it follows from `pev_padd` alone. The head is dropped exactly as
differentiation drops a constant, and the `0 ::` is the shift that multiplication by `x` induces.

Sanity: `pderiv [c, a₁, a₂] = [a₁, 2a₂, 0]`, which is `a₁ + 2a₂x` with a harmless trailing zero.

## This is one brick

`HasDerivAt (pev L) (pev (pderiv L) x) x` is what the differential argument needs *first*. It does
not prove `BoundedGermTranscendence`, and nothing here should be read as progress on it beyond
supplying an ingredient. The remaining bricks are named in the file's closing comment so the next
session does not have to re-derive the plan.

**This is also the first result in the arc to import an analytic axiom.** Fifteen results held the
ledger at 242 and declined the analytic route three times where it was available. Spending it here
is deliberate: the bounded branch was *proved* unreachable without it.
-/

namespace MachLib

open Real

/-- The derivative of a coefficient list, in Horner form. -/
noncomputable def pderiv : List Real → List Real
  | []      => []
  | _ :: cs => padd cs (0 :: pderiv cs)

/-- The defining identity, and it is just `pev_padd`. -/
theorem pev_pderiv_cons (c : Real) (cs : List Real) (x : Real) :
    pev (pderiv (c :: cs)) x = pev cs x + x * pev (pderiv cs) x := by
  show pev (padd cs (0 :: pderiv cs)) x = pev cs x + x * pev (pderiv cs) x
  rw [pev_padd]
  have e : pev (0 :: pderiv cs) x = x * pev (pderiv cs) x := by
    show (0 : Real) + x * pev (pderiv cs) x = x * pev (pderiv cs) x
    mach_ring
  rw [e]

/-- **`pev (pderiv L)` is the derivative of `pev L`.** -/
theorem hasDerivAt_pev : ∀ (L : List Real) (x : Real),
    HasDerivAt (fun y => pev L y) (pev (pderiv L) x) x := by
  intro L
  induction L with
  | nil =>
      intro x
      show HasDerivAt (fun _ => (0 : Real)) (pev (pderiv []) x) x
      have e : pev (pderiv ([] : List Real)) x = 0 := rfl
      rw [e]
      exact HasDerivAt_const 0 x
  | cons c cs ih =>
      intro x
      have hprod : HasDerivAt (fun y => y * pev cs y)
          (1 * pev cs x + x * pev (pderiv cs) x) x :=
        HasDerivAt_mul (fun y => y) (fun y => pev cs y) 1 (pev (pderiv cs) x) x
          (HasDerivAt_id x) (ih x)
      have hsum : HasDerivAt (fun y => c + y * pev cs y)
          (0 + (1 * pev cs x + x * pev (pderiv cs) x)) x :=
        HasDerivAt_add (fun _ => c) (fun y => y * pev cs y) 0
          (1 * pev cs x + x * pev (pderiv cs) x) x (HasDerivAt_const c x) hprod
      have e : (0 : Real) + (1 * pev cs x + x * pev (pderiv cs) x)
          = pev (pderiv (c :: cs)) x := by
        rw [pev_pderiv_cons]
        mach_mpoly [pev cs x, x, pev (pderiv cs) x]
      rw [e] at hsum
      exact hsum

/-! ## The remaining bricks, named

What the differential argument still needs, in order, so the next session starts from a plan rather
than a blank file:

1. **`HasDerivAt` for a rational germ** — quotient rule on `pev P / pev Q` where `pev Q x ≠ 0`.
   `HasDerivAt_div` or `HasDerivAt_inv` plus the product rule; the nonvanishing is already available
   off a finite exceptional set from `zero_query_finite_exception_normal_form`.
2. **`HasDerivAt (fun x => exp (S x))`** — chain rule, giving `exp(S x) · S' x`. This is the step the
   whole argument turns on: `y = exp(S)` satisfies `y' = S'·y`, which is what lets a polynomial
   relation in `y` be differentiated back into a polynomial relation in `y`.
3. **Differentiate the relation.** From `Σⱼ pⱼ(x)·yʲ = 0` derive `Σⱼ (pⱼ' + j·S'·pⱼ)·yʲ = 0`, then
   eliminate the top coefficient against the original to drop the degree — contradicting minimality.
4. **The positive branch is NOT this argument.** On `S > 0`, `F(S) = exp(S) + log(S)`, which is not
   `exp` of anything, so step 2 does not apply as stated. That branch needs its own treatment and
   should not be assumed to follow by symmetry — the two sides have already diverged twice today
   (totalisation deletes the log on the negative side; the decay bound needed a different argument
   on the positive one).

Step 4 is the honest reason this file claims one brick and not a route. -/

end MachLib
