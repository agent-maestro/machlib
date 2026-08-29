import MachLib.EMLQueryGermAntecedent
import MachLib.Bipoly

/-!
# The degenerate-denominator route is FALSE, with a witness

After `(er)` the obligation `OneQueryDichotomy` sits two hypotheses away — `DivDenomsOK` and the
`ctxFrac` non-vanishing — and the plan recorded for closing them was a two-case split:

* denominator germ **not** eventually zero → `bipolyNoOscillation_holds` gives eventually non-zero,
  discharging both hypotheses on a ray;
* denominator germ **eventually zero** → `a / 0 = 0` collapses the node, so `FCtx.eval` is eventually
  zero and the `EvZeroF` branch holds outright.

**The second case is false**, and this module carries the witness rather than a corrected sentence.

## The witness

```
C = hole + (1 / 0)
```

`ctxFrac (div a b) = (num_a · den_b, den_a · num_b)`, so a `div` by something with numerator `0`
gives that node the denominator `0`; `ctxFrac (add a b)` multiplies the denominators, so **the whole
context's denominator is identically zero.** But `FCtx.eval (add a b) = eval a + eval b`, and
`1 / 0 = 0`, so the context evaluates to `y` — the hole, untouched. Take `y = Fbasis 0 = 1` and it is
never zero.

**A degenerate denominator does not make the value degenerate**, because `add` keeps the live part
alive. The `ctxFrac` normal form loses information that `FCtx.eval` retains.

## Where my recorded prediction was wrong

The prediction attached to that plan named `div` and `mul` as the risky cases — *"where a germ can be
eventually zero without either operand being"*. The failure is in **`add`**, and it is not about
germs multiplying to zero at all: it is that the normal form's denominator is a product over the
*whole tree*, so one degenerate leaf zeroes it, while the value only degenerates if that leaf is on a
multiplicative path to the root.

## What the route has to be instead

A **div-clamp**, exactly analogous to `declamp` for EML trees: replace each `div` node whose divisor
is degenerate on the ray by `const 0` — justified by `a / 0 = 0` — and apply
`oneQueryDichotomy_divConditioned` to the clamped context, which now satisfies `DivDenomsOK`.
The uniformity problem `declamp` has does **not** arise: "eventually zero" is a ray property, so the
clamped context is fixed once the ray is far enough out, rather than varying per interval.
-/

namespace MachLib

open Real

/-- `hole + (1 / 0)` — the whole point being that `div` poisons the normal form's denominator while
`add` protects the value. -/
noncomputable def divDegenerateCtx : FCtx :=
  FCtx.add FCtx.hole (FCtx.div (FCtx.const 1) (FCtx.const 0))

/-- **Its normal-form denominator is identically zero.** -/
theorem divDegenerateCtx_denom (x y : Real) :
    bipev (ctxFrac divDegenerateCtx).2 x y = 0 := by
  show bipev (bimul [[(1 : Real)]] (bimul [[(1 : Real)]] [[(0 : Real)]])) x y = 0
  rw [bipev_bimul, bipev_bimul]
  show (pev [(1 : Real)] x + y * bipev [] x y)
      * ((pev [(1 : Real)] x + y * bipev [] x y) * (pev [(0 : Real)] x + y * bipev [] x y)) = 0
  show ((1 : Real) + x * pev [] x + y * 0)
      * (((1 : Real) + x * pev [] x + y * 0) * ((0 : Real) + x * pev [] x + y * 0)) = 0
  show ((1 : Real) + x * 0 + y * 0) * (((1 : Real) + x * 0 + y * 0) * ((0 : Real) + x * 0 + y * 0))
      = 0
  mach_mpoly [x, y]

/-- **But its value is the hole, untouched** — `1 / 0 = 0`, and `add` keeps the live part. -/
theorem divDegenerateCtx_eval (x y : Real) : FCtx.eval divDegenerateCtx x y = y := by
  show y + (1 : Real) / (0 : Real) = y
  rw [div_zero]
  mach_ring

/-- **The route is false.** A context whose normal-form denominator is eventually zero — indeed
identically zero — while its value is eventually **non**-zero.

Witness `P = []`, `Q = [1]`: then `u = 0 / 1 = 0` and `Fbasis 0 = 1`, so the germ is the constant `1`.

Kept as a theorem rather than a remark because a refuted plan that survives only as prose gets
re-attempted; one that survives as a `False`-producing witness does not. -/
theorem denom_evZero_does_not_imply_eval_evZero :
    ∃ (C : FCtx) (P Q : List Real),
      EvZeroF (fun x => bipev (ctxFrac C).2 x (Fbasis (pev P x / pev Q x)))
      ∧ ¬ EvZeroF (fun x => FCtx.eval C x (Fbasis (pev P x / pev Q x))) := by
  refine ⟨divDegenerateCtx, [], [1], ⟨1, le_refl 1, fun x _ => divDegenerateCtx_denom x _⟩, ?_⟩
  rintro ⟨Y, hY1, hY⟩
  have hu : pev ([] : List Real) Y / pev [(1 : Real)] Y = 0 := by
    show (0 : Real) / ((1 : Real) + Y * pev [] Y) = 0
    show (0 : Real) / ((1 : Real) + Y * 0) = 0
    have e : (1 : Real) + Y * 0 = 1 := by mach_ring
    rw [e, div_def 0 1 (fun h => absurd h.symm (ne_of_lt zero_lt_one_ax)), zero_mul]
  -- typed `have`, because `hY Y _` lands as an UNREDUCED `(fun x => …) Y`. Fourth time this
  -- gotcha has cost a build today, and it is in CLAUDE.md.
  have h0 : FCtx.eval divDegenerateCtx Y (Fbasis (pev [] Y / pev [(1 : Real)] Y)) = 0 :=
    hY Y (le_refl Y)
  rw [divDegenerateCtx_eval, hu, Fbasis_zero] at h0
  exact absurd h0.symm (ne_of_lt zero_lt_one_ax)

/-! ## Which hypothesis actually fails — and it is not the one I named

`(es)` said the corrected route is a div-clamp giving `DivDenomsOK`. **`DivDenomsOK` was never the
problem here.** It asks, at each `div` node, that the *divisor's* `ctxFrac` **denominator** be
non-zero. In `hole + (1 / 0)` the divisor is `const 0`, whose `ctxFrac` is `([[0]], [[1]])` — its
denominator is `[[1]]`, which is `1`. So `DivDenomsOK` holds outright.

What fails is the **other** hypothesis: the *whole context's* denominator
`bipev (ctxFrac C).2`, which is the product over the entire tree and is zeroed by the divisor's
**numerator**. The two hypotheses are about different polynomials and fail for different reasons, and
conflating them is what made `(es)`'s one-line route description wrong. -/

/-- **`DivDenomsOK` holds for the witness.** So the failing hypothesis is the whole-context
denominator, not this one. -/
theorem divDegenerateCtx_divDenomsOK (x y : Real) : DivDenomsOK divDegenerateCtx x y := by
  refine ⟨True.intro, True.intro, True.intro, ?_⟩
  show bipev [[(1 : Real)]] x y ≠ 0
  show (pev [(1 : Real)] x + y * bipev [] x y) ≠ 0
  show ((1 : Real) + x * pev [] x + y * 0) ≠ 0
  show ((1 : Real) + x * 0 + y * 0) ≠ 0
  intro h
  have e : (1 : Real) + x * 0 + y * 0 = 1 := by mach_ring
  rw [e] at h
  exact absurd h.symm (ne_of_lt zero_lt_one_ax)

end MachLib
