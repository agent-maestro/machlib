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

## What the log-chart buys — and what it does NOT (corrected 2026-07-07)

Re-chart EML from `x` to `t = log x` (`x = eᵗ`, a bijection `ℝ → (0,∞)`). The
`t`-chart linearises a lot: `x = eᵗ` (`y'=y`), `1/x = e⁻ᵗ` (`y'=−y`),
`exp(u) = e^u` (`y' = u'·y`), and crucially `log x = t` (the **base variable**,
derivative `1`, *no reciprocal*).

But it does **not** eliminate `log` of a *composite* argument. `log(v)` has
derivative `v'/v`, so any Pfaffian representation carries `1/v` — cf.
`Pfaffian.lean`'s `log_atom.derivative = inv var`. For composite `v` (an EML
subvalue, a difference `exp − log`, not a pure exponential) this `1/v` is a
degree-2 generator (`(1/v)' = −v'·(1/v)²`) that lives in the chain's *coherence
relations*, not as a value in `V`. **Clearing does not remove it** — there is no
reciprocal *value* in `V` to clear; the reciprocal is structural to `log`'s
derivative. (An earlier note here wrongly claimed clearing yields a pure
`IsExpChain`; that holds only when logs have non-composite arguments.)

### Honest consequence
- **Subclass (log of the bare variable only):** every `log` is `log x = t`, no
  reciprocal anywhere; the `t`-chart chain is a genuine `IsExpChain` and the
  existing `rolle`-only `pfaffian_khovanskii_bound_gen_uncond` + Brick 3d-ii
  transfer close it directly. This is the surgery-free, achievable case.
- **General EML (nested composite logs):** the chain has degree-2 reciprocal
  levels interleaved with exp levels. This needs the **extended-class descent**
  (handle reciprocal levels), i.e. the genuine Khovanskii surgery on
  `PfaffianGeneral*`. Bricks 3b/3c (`clearNum`, `reciprocalPfaffian_zero_count`)
  are the *reciprocal base-case tools* for that descent — not a way around it.
  The log-chart still helps (outer `1/x`, `log x`, all exps go linear; the
  `x↔t` bijection is Brick 3d-ii) but the interleaved reciprocals are the core.

## What this file provides

The **exp-generator coherence atom** every exp-type level reuses — in the
subclass chain *and* in the exp levels of the general extended descent. The
recursive encoder itself is scoped by which case is being built (see the
exploration FINDINGS re-correction of 2026-07-07).
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
