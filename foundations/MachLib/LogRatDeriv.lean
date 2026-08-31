import MachLib.DerivQuotientLog
import MachLib.PevEvEq
import MachLib.PevDeriv
import MachLib.GermDerivFbasis

/-!
# Leg 2, derivative half: a rational-log germ identity differentiates

`(fm)` split the route to `¬ RatGerm (log ∘ S)` into three legs. Legs 1 and 3 are theorems
(`deriv_eq_of_eq_on_ray` + the two rules in `DerivQuotientLog`; `peq_of_ev_eq`). Leg 2 — *clear
denominators to `no_rational_logarithm`'s `hident`* — splits again, and this is its first half.

From `log (P/Q) = N/D` on a ray, both sides differentiate and the derivatives agree at every
**interior** point:

```
((P′Q − PQ′)/(Q·Q)) / (P/Q)  =  (N′D − ND′)/(D·D)
```

Nothing here is new mathematics — it is the three lemmas of legs 1 and 3 composing, which is worth
having as a checked theorem rather than as a claim that they compose. That distinction has cost this
arc twice: `(fq)` asserted the chain and quotient rules "compose" before either existed, and `(fk)`
found bricks re-deriving generic machinery because the summit was never checked.

## What remains of leg 2

The **algebra half**: cross-multiplying the display above into

```
(P′Q − PQ′)·(D·D)  =  (N′D − ND′)·(Q·P)
```

which is `hident` at `k = 1`, then `peq_of_ev_eq` to promote it from a ray identity to `PEq`.

That is three nested divisions cleared against each other. It is standard, and it is **long in this
corpus's idiom**: `mach_mpoly` cannot relate distinct reciprocals, so each clearing step needs its
own `div_of_eq_mul` or `mul_left_cancel`. Recorded as open rather than estimated, per this arc's
record on the word "assembly".
-/

namespace MachLib

open Real

/-- **Leg 2, derivative half.** From `log (P/Q) = N/D` on a ray, the two sides' derivatives agree at
every interior point — with both sides written out. This is the step that consumes
`logComp_hasDerivAt`, `div_hasDerivAt` and `deriv_eq_of_eq_on_ray` together. -/
theorem logRat_deriv_eq {P Q N D : List Real} {X : Real}
    (hQ : ∀ x : Real, X ≤ x → pev Q x ≠ 0)
    (hD : ∀ x : Real, X ≤ x → pev D x ≠ 0)
    (hpos : ∀ x : Real, X ≤ x → 0 < pev P x / pev Q x)
    (hlog : ∀ x : Real, X ≤ x → log (pev P x / pev Q x) = pev N x / pev D x) :
    ∀ x : Real, X < x →
      ((pev (pderiv P) x * pev Q x - pev P x * pev (pderiv Q) x) / (pev Q x * pev Q x))
          / (pev P x / pev Q x)
        = (pev (pderiv N) x * pev D x - pev N x * pev (pderiv D) x) / (pev D x * pev D x) := by
  intro x hx
  have hxle : X ≤ x := le_of_lt hx
  -- the inner rational germ and its derivative
  have hSder : HasDerivAt (fun t => pev P t / pev Q t)
      ((pev (pderiv P) x * pev Q x - pev P x * pev (pderiv Q) x) / (pev Q x * pev Q x)) x :=
    div_hasDerivAt (hasDerivAt_pev P x) (hasDerivAt_pev Q x) (hQ x hxle)
  -- the left side: log of it
  have hL : HasDerivAt (fun t => log (pev P t / pev Q t))
      (((pev (pderiv P) x * pev Q x - pev P x * pev (pderiv Q) x) / (pev Q x * pev Q x))
        / (pev P x / pev Q x)) x :=
    logComp_hasDerivAt hSder (hpos x hxle)
  -- the right side
  have hR : HasDerivAt (fun t => pev N t / pev D t)
      ((pev (pderiv N) x * pev D x - pev N x * pev (pderiv D) x) / (pev D x * pev D x)) x :=
    div_hasDerivAt (hasDerivAt_pev N x) (hasDerivAt_pev D x) (hD x hxle)
  exact deriv_eq_of_eq_on_ray hx hlog hL hR

/-! ## Leg 2b — clearing the denominators

The target is `no_rational_logarithm`'s `hident` at `k = 1`.

**Order matters here.** Multiplying through by `Q·Q` does it in one step: that cancels the left
quotient outright *and* turns `Q·Q·(P/Q)` into `Q·P`, leaving nothing over. Clearing the outer
division first — the obvious order — leaves a stray `Q` and needs its own cancellation. Same shape as
`D·(1/(D·D)) = 1/D` in `DerivQuotientLog`: in this corpus the order denominators are cleared in
decides whether the remainder is one `mach_mpoly` call or a chain of them.
-/


/-- **Cross-multiplication, the direction the corpus lacked.** `div_eq_div_of_cross` builds an
equality of quotients from a cross product; this reads one off. -/
theorem cross_of_div_eq_div {a b c d : Real} (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a / b = c / d) : a * d = c * b := by
  have hstep : (b * d) * (a / b) = (b * d) * (c / d) := by rw [h]
  have hl : (b * d) * (a / b) = d * a := by
    rw [show (b * d) * (a / b) = d * (b * (a / b)) from by mach_ring,
        mul_div_cancel_left hb]
  have hr : (b * d) * (c / d) = b * c := by
    rw [show (b * d) * (c / d) = b * (d * (c / d)) from by mach_ring,
        mul_div_cancel_left hd]
  rw [hl, hr] at hstep
  rw [show a * d = d * a from by mach_ring, show c * b = b * c from by mach_ring]
  exact hstep

/-- **Leg 2b: the derivative identity clears to `hident` at `k = 1`.**

Multiplying through by `Q·Q` does it in one step, because that cancels the left quotient outright and
turns `Q·Q·(P/Q)` into `Q·P` — no residual factor to cancel afterwards. Clearing the outer division
first instead leaves a stray `Q` and needs a cancellation the corpus would make you earn. -/
theorem logRat_cross_identity {E1 E2 P Q D : Real}
    (hQ : Q ≠ 0) (hD : D ≠ 0) (hP : P ≠ 0)
    (h : (E1 / (Q * Q)) / (P / Q) = E2 / (D * D)) :
    E1 * (D * D) = E2 * (Q * P) := by
  have hQQ : Q * Q ≠ 0 := mul_ne_zero hQ hQ
  have hDD : D * D ≠ 0 := mul_ne_zero hD hD
  have hPQ : P / Q ≠ 0 := by
    intro hz
    refine hP ?_
    have h1 : Q * (P / Q) = P := mul_div_cancel_left hQ
    rw [hz] at h1
    rw [← h1]; mach_ring
  have hx := cross_of_div_eq_div hPQ hDD h
  have hstep : (Q * Q) * ((E1 / (Q * Q)) * (D * D)) = (Q * Q) * (E2 * (P / Q)) := by rw [hx]
  have hl : (Q * Q) * ((E1 / (Q * Q)) * (D * D)) = E1 * (D * D) := by
    rw [show (Q * Q) * ((E1 / (Q * Q)) * (D * D)) = ((Q * Q) * (E1 / (Q * Q))) * (D * D)
          from by mach_ring,
        mul_div_cancel_left hQQ]
  have hr : (Q * Q) * (E2 * (P / Q)) = E2 * (Q * P) := by
    rw [show (Q * Q) * (E2 * (P / Q)) = E2 * (Q * (Q * (P / Q))) from by mach_ring,
        mul_div_cancel_left hQ]
  rw [hl, hr] at hstep
  exact hstep

end MachLib
