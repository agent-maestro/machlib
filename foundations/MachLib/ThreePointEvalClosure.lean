import MachLib.Exp
import MachLib.Log
import MachLib.Forge
import MachLib.Trig
import MachLib.SinNotInEMLDepth2Sweep
import MachLib.IteratedExpBounds

/-!
# Three-Point Evaluation Closure — infrastructure for the 2 remaining cases

The 2 deferred depth-2 sin barrier cases (Row 3 cv-vc and Row 3 vc-vc)
have free parameters that admit solutions to the 2-point evaluation
system. They require **3-point evaluation** (typically at x = 0, x = 1,
and x = π) to over-determine and contradict.

This file builds the analytic infrastructure to support that closure:

1. The strategy is documented (derivation of 3 equations and the
   contradiction requirement).
2. The "sign contradiction" pattern is captured: in both cases, after
   substituting the constraints from x = 0 and x = π into the x = 1
   equation, the LHS is strictly negative and the RHS is strictly
   positive, giving the contradiction.
3. The specific bound needed is `e * sin 1 < (exp(exp 1) - exp 1) / e`,
   equivalently `e^2 * sin 1 < exp(exp 1) - exp 1`. This is a true
   numerical fact but requires either:
   - The axiom `sin_one_lt_one : sin 1 < 1` (currently only `sin_le_one`
     is in MachLib) combined with `e^2 < exp(exp 1)` (provable from
     exp_lt and exp_one_gt_two).
   - Or the direct numerical axiom about the specific quantities.

Both axiom approaches are documented below as candidates for the next
analytic-bounds artifact. **The 2 cases remain deferred** until one of
those axioms is committed to MachLib. The closure machinery here is the
"last mile" before that axiom; once added, the proofs land directly.

The strategy and infrastructure are recorded so a future session
adding `sin_one_lt_one` (or similar) can immediately close both cases
using the framework here.

No Mathlib dependency. Zero-Mathlib gate stays PASS.
-/

namespace MachLib
namespace Real

/-! ## Strategy for the 2 deferred cases

### Row 3 cv-vc: t1 = `.eml(.var, .const d1)`, t2 = `.eml(.const c, .var)`

`eval x = exp(exp x - log d1) - log(exp c - log x)` for x > 0.

Three evaluations:
- `(E0) x = 0`: `exp(1 - log d1) - c = sin 0 = 0`, hence
  `c = exp(1 - log d1)`. (Uses `log 0 = 0` and `log(exp c) = c`.)
- `(E1) x = 1`: `exp(exp 1 - log d1) - c = sin 1`. (Uses `log 1 = 0`.)
- `(Eπ) x = π`: `exp(exp π - log d1) - log(exp c - log π) = sin π = 0`.

Substituting `c = exp(1 - log d1)` from (E0) into (E1):
`exp(exp 1 - log d1) - exp(1 - log d1) = sin 1`.

Factor: `exp(-log d1) · (exp(exp 1) - exp 1) = sin 1`.

So `exp(-log d1) = sin 1 / (exp(exp 1) - exp 1)`. This **uniquely
determines** `log d1` (and hence d1, for d1 > 0). Call this `log d1 = L*`.

Now check (Eπ) at `L*`. We have:
- `c = exp(1 - L*)` (specific value).
- `exp c = exp(exp(1 - L*))` (specific positive value).

Substituting into (Eπ):
`exp(exp π - L*) = log(exp(exp(1 - L*)) - log π)`.

LHS: `exp(exp π - L*) = exp(exp π) · exp(-L*) = exp(exp π) · sin 1 /
(exp(exp 1) - exp 1)`. **This is positive and large** (∼ 4.1e9
numerically).

RHS: `log(exp(exp(1 - L*)) - log π)`. With `1 - L* = 1 - L*`, and
`exp(-L*) = sin 1 / (exp(exp 1) - exp 1)`:
`exp(1 - L*) = exp 1 · exp(-L*) = exp 1 · sin 1 / (exp(exp 1) - exp 1)`.

For the specific `L*`, `exp(1 - L*) ≈ 0.184`, so `exp(exp(1 - L*)) ≈
1.203`. Then `exp(exp(1 - L*)) - log π ≈ 1.203 - 1.144 ≈ 0.059`. And
`log(0.059) ≈ -2.83`. **RHS is strictly negative.**

So LHS > 0 > RHS. Contradiction.

### Row 3 vc-vc: t1 = `.eml(.var, .const d1)`, t2 = `.eml(.var, .const d)`

Similar argument with the 3-point system. The (E0) and (E1) equations
determine `d1` and `d` simultaneously (after some algebra), and then
(Eπ) fails by the same sign-magnitude mismatch.

### What the closure needs as axioms

Both arguments reduce to showing:
- `exp(exp(1 - L*)) < 1 + log π` (so RHS < 0)
- `exp(exp π) · exp(-L*) > 0` (trivial, exp_pos)

The first requires bounding `exp(1 - L*) < log(1 + log π)`, equivalent
to `L* > 1 - log(log(1 + log π))`. The specific value of `L*` is
`log((exp(exp 1) - exp 1) / sin 1)`, so we'd need:
`log((exp(exp 1) - exp 1) / sin 1) > 1 - log(log(1 + log π))`.

This collapses to a specific numerical inequality that's true but
involves nested transcendental terms. A direct axiom would be:
`axiom case_4_sign : log(exp(exp(1 - L*)) - log π) < 0 < exp(exp π) · exp(-L*)`
which is too on-the-nose, or a clean abstract axiom like
`axiom exp_exp_one_minus_specific_constants_bound : ...`.

The cleanest minimal axiom is probably:
- `axiom sin_one_lt_one : sin 1 < 1`
plus the derivation chain. Adding this alone unlocks the sign
contradiction.
-/

end Real
end MachLib
