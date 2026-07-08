import MachLib.AnalyticFiniteZeros
import MachLib.PfaffianGeneralReduce

/-!
# Pfaffian functions over an analytic chain are analytic

Bridges the axiomatized analytic layer (`AnalyticFiniteZeros`) to the Pfaffian
descent's `hAnalytic` requirement. `log_step_multilinear_analytic` needs
`∀ r, IsAnalyticOnReals (pfaffianChainFn c r).eval (Icc a b)` — every polynomial
in `(x, y_1, …, y_n)` over the chain must be analytic. This file reduces that to
a single, reusable obligation: **each chain value `y_i` is analytic on `S`**.
Given that (and the identity `x`), the whole polynomial is analytic by closure
under `+`/`−`/`×` (`analytic_add`/`analytic_sub`/`analytic_mul`).

- `poly_eval_analytic` — the induction on the polynomial's structure.
- `pfaffianChainFn_eval_analytic` — packages it in the `pfaffianChainFn … .eval`
  shape the descent consumes.

The remaining obligation ("each chain value is analytic on the interval") is the
encoder's to discharge, using its per-node positivity side-condition
(`LogArgPos`) for the log/reciprocal analytic domains.

No new axioms here (`analytic_mul` lives in `AnalyticFiniteZeros`).
-/

namespace MachLib

open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
  MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianChain
  MachLib.PfaffianGeneralReduce

/-- A polynomial in `(x, y_1, …, y_n)`, evaluated along an environment whose
`x`-slot is the identity and each `y`-slot (`env · i`) is analytic on `S`, is
itself analytic on `S`. Structural induction on the polynomial. -/
theorem poly_eval_analytic {n : Nat} (S : RealSet) (env : Real → Fin n → Real)
    (henv : ∀ i, IsAnalyticOnReals (fun x => env x i) S)
    (p : MultiPoly n) :
    IsAnalyticOnReals (fun x => MultiPoly.eval p x (env x)) S := by
  induction p with
  | const c => exact analytic_const c S
  | varX => exact analytic_id S
  | varY i => exact henv i
  | add p q ihp ihq => exact analytic_add _ _ S ihp ihq
  | sub p q ihp ihq => exact analytic_sub _ _ S ihp ihq
  | mul p q ihp ihq => exact analytic_mul _ _ S ihp ihq

/-- **Every Pfaffian function over an analytic chain is analytic.** If each chain
value `c.evals i` is analytic on `S`, then for every polynomial `r` the Pfaffian
function `pfaffianChainFn c r` is analytic on `S`. This is exactly the
`hAnalytic` hypothesis of `log_step_multilinear_analytic` (take `S := Icc a b`). -/
theorem pfaffianChainFn_eval_analytic {n : Nat} (c : PfaffianChain n) (S : RealSet)
    (hevals : ∀ i, IsAnalyticOnReals (fun x => c.evals i x) S) (r : MultiPoly n) :
    IsAnalyticOnReals (pfaffianChainFn c r).eval S :=
  poly_eval_analytic S (fun x => c.chainValues x) hevals r

end MachLib
