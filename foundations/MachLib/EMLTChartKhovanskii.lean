import MachLib.Differentiation
import MachLib.Exp
import MachLib.Log
import MachLib.MultiPoly
import MachLib.PfaffianChain
import MachLib.PfaffianGeneralReduce

/-!
# EML → t-chart exp-type chain — foundation (Brick 3d-i, full route)

Retiring `PfaffianFunction.zero_count_bound_classical` from the general
`sin_not_in_eml_any_depth`, via the **log-substitution + denominator-clearing**
route (see the scoping doc
`monogate-research/exploration/eml_exp_rational_khovanskii_extend_scoping_2026_07_07/FINDINGS.md`,
including the 2026-07-07 CORRECTION).

## The route in one paragraph

Re-chart EML from `x` to `t = log x` (`x = eᵗ`, a bijection `ℝ → (0,∞)`). In
the `t`-chart every EML generator except *logs of composite arguments* is
exp-type or the base variable: `x = eᵗ` (`y'=y`), `1/x = e⁻ᵗ` (`y'=−y`),
`exp(u) = e^u` (`y' = u'·y`), `log x = t` (base variable). A `log(b)` with `b`
composite needs `1/b`, degree-2 — the sole residue. **Clear** those `1/bᵢ`
denominators (as `MachLib.clearNum` does for `1/x` in the x-chart): the cleared
`W = V·∏bᵢᵏ` is a pure `IsExpChain` `pfaffianChainFn`, and on the EML domain
(`bᵢ > 0`) `V`'s zeros ⊆ `W`'s zeros. Then the existing, `rolle`-only
`pfaffian_khovanskii_bound_gen_uncond` bounds `W`'s zeros, and
`MachLib.zero_count_transfer` (Brick 3d-ii) pulls the bound back to the x-chart.
No surgery on the descent — the whole new content is this additive encoder.

## Blueprint of the recursive encoder (the multi-session bulk ahead)

For an `EMLTree T`, build (mutually, bottom-up over the tree):
  * `chainOf T : PfaffianChain (arity T)` — generators, in triangular order:
      base var `t`; `eᵗ` (for every `var`); for each `eml t1 t2` node an
      `e^{u1}` (`u1 = value of t1`), an `L2 = log(v2)` (`v2 = value of t2`),
      and a reciprocal `w2 = 1/v2`.
  * `valOf T : MultiPoly (arity T)` with
      `pfaffianChainFn (chainOf T) (valOf T) t = T.eval (eᵗ)` — the value `V`.
  * `denomOf T : MultiPoly (arity T)` — the product `∏ v2ᵏ` of composite-log
      arguments, cleared into the numerator.
  * `numOf T := valOf T * denomOf T` — the cleared `W`, over the *exp-type*
      sub-chain (all `w2` eliminated). Prove `IsExpChain` on that sub-chain.

Proof obligations per node: coherence (`chainOf T` `IsCoherentOn` — the exp
generators via `hasDerivAt_exp_comp` below, `L2` via `HasDerivAt_log_pos`+chain,
`w2` via `HasDerivAt_inv`), `IsExpChain` of the cleared sub-chain, and the
zero-subset `V=0 ∧ domain → W=0` (`W = V·∏v2ᵏ`, `v2 > 0`).

This file currently lands the **coherence atom** every exp generator reuses; the
recursive `chainOf`/`valOf`/`numOf` and their invariants are the subsequent
bricks.
-/

namespace MachLib

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod

/-- **Exp-generator coherence atom.** `d/dt exp(u(t)) = exp(u(t))·u'(t)`. This is
the coherence obligation for every exp-type generator `e^u` in the `t`-chart
chain: its Pfaffian relation is `G·y` with `G` the `MultiPoly` for `u'`, and the
value along the chain is `exp(u)`, so `(e^u)' = u'·e^u` is exactly this. Built
from the chain rule `HasDerivAt_comp` and `HasDerivAt_exp`. -/
theorem hasDerivAt_exp_comp (u : Real → Real) (u' x : Real) (hu : HasDerivAt u u' x) :
    HasDerivAt (fun t => exp (u t)) (exp (u x) * u') x :=
  HasDerivAt_comp Real.exp u u' (Real.exp (u x)) x hu (HasDerivAt_exp (u x))

/-- The `x = eᵗ` generator (`var`'s value): `d/dt eᵗ = eᵗ` — exp-type with
`G = 1` (`y' = 1·y`). Instance of `hasDerivAt_exp_comp` with `u = id`. -/
theorem hasDerivAt_exp_t (x : Real) :
    HasDerivAt (fun t => exp t) (exp x) x := by
  have h := hasDerivAt_exp_comp (fun t => t) 1 x (HasDerivAt_id x)
  rw [mul_one_ax] at h; exact h

/-- The `1/x = e⁻ᵗ` generator: `d/dt e⁻ᵗ = −e⁻ᵗ` — exp-type with `G = −1`
(`y' = −y`), the linchpin that makes the reciprocal linear in the log-chart. -/
theorem hasDerivAt_exp_neg_t (x : Real) :
    HasDerivAt (fun t => exp (-t)) (-(exp (-x))) x := by
  have hu : HasDerivAt (fun t => -t) (-1) x := by
    simpa using HasDerivAt_neg (fun t => t) 1 x (HasDerivAt_id x)
  have h := hasDerivAt_exp_comp (fun t => -t) (-1) x hu
  have he : exp (-x) * (-1) = -(exp (-x)) := by mach_ring
  rw [he] at h; exact h

end MachLib
