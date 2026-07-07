import MachLib.SinNotInEML
import MachLib.EMLPfaffian
import MachLib.Log
import MachLib.Ring

/-!
# Constructive zero-count for EML trees — retiring the classical Khovanskii axiom

## Goal

`EMLPfaffian.sin_not_in_eml_any_depth` (and its cosine twin) is sorry-free but
its `#print axioms` footprint contains

  `PfaffianFunction.zero_count_bound_classical`   (the classical Khovanskii
      zero-count, cited as an axiom, Khovanskii 1991 Ch.3 Thm.1)

while the **constructive** Khovanskii bounds
(`chainN_khovanskii_bound_unconditional`, `pfaffian_khovanskii_bound_gen_uncond`)
are proven with `rolle` as the sole analytic axiom — but they require
`IsExpChain` (exp-*type* chains). EML trees carry `log` nodes (log' = 1/x is
Pfaffian but not exp-type), so the constructive results do not directly cover
them. This file is the bridge: bound the zeros of an EML tree constructively,
so the barrier can drop the classical axiom.

## The reduction spine (this build)

On its validity domain (every `log` argument strictly positive), an EML node
vanishes iff an **exp-only** relation holds:

  `exp a − log b = 0  ↔  b = exp (exp a)`        (for `b > 0`)      -- `eml_node_zero_iff`

i.e. one `log` is traded for a double-`exp`. Iterating from the innermost `log`
outward converts an EML tree's *zero-set* into the zero-set of an **exp-only**
expression (an iterated-exponential-tower polynomial), whose zeros are bounded
uniformly-in-interval by `chainN_khovanskii_bound_unconditional`. sin has
`Θ(interval-length)` zeros, exceeding any fixed bound on a long enough
interval → contradiction, constructively.

## Status (installment 1 — foundations)

PROVEN here (0 sorry):
  * `eml_node_zero_iff`   — the log-elimination identity (the reduction crux).
  * `eml_eval_zero_iff`   — its eval-level form on an `EMLTree.eml` node.

REMAINING (documented, multi-session — the ~800-line body):
  1. The log-elimination *recursion*. Note the reduced relation
     `t2.eval x = exp (exp (t1.eval x))` mixes `t1` and `t2`, and
     `exp (exp ·)` is NOT itself an `EMLTree.eml` node — so the recursion
     leaves the EML grammar and must land in a broader **exp-polynomial**
     representation (the `MultiPoly` over the iterated-exp tower `chainNFn`).
     This encoding is the bulk of the work.
  2. Encode the log-eliminated exp expression as `chainNFn (m+2) p` and prove
     eval-agreement, so `chainN_khovanskii_bound_unconditional` applies.
  3. Discharge the validity/positivity side-conditions from the sin-equality
     hypothesis (this is where the second axiom,
     `eml_pfaffian_validon_from_sin_equality`, currently stands in — a separate
     smoothness bridge, not addressed here).
  4. Re-prove `sin_not_in_eml_any_depth` citing the constructive bound instead
     of `zero_count_bound_classical`, and confirm via `#print axioms` that the
     classical axiom leaves the footprint.

Alternative path (not taken here): extend the constructive Khovanskii proof
itself (`pfaffian_bound_step_hnz_gen_IF` + `vehExpo`) from `IsExpChain` to an
exp-or-log chain generator. Cleaner conceptually but requires re-proving the
integrating-factor step for a `log`-type generator.
-/

namespace MachLib
namespace Real

/-- **Log-elimination (the reduction crux).** On the validity domain `b > 0`,
the EML-node value `exp a − log b` vanishes iff `b = exp (exp a)`. Trades a
`log` for a double-`exp`, moving an EML zero toward an exp-only chain. Proof is
pure `exp`/`log` inverse algebra (`exp_log`, `log_exp`). -/
theorem eml_node_zero_iff (a b : Real) (hb : 0 < b) :
    (exp a - log b = 0) ↔ (b = exp (exp a)) := by
  constructor
  · intro h
    have h1 : exp a = log b := by
      have e : exp a - log b + log b = 0 + log b := by rw [h]
      rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at e
      exact e
    have hb2 := congrArg exp h1
    rw [exp_log hb] at hb2
    exact hb2.symm
  · intro h
    rw [h, log_exp, sub_def, add_neg]

end Real

/-- **Eval-level log-elimination on an `EMLTree.eml` node.** Where the inner
subtree stays positive (the validity condition), the node's zero is exactly the
exp-only relation `t2.eval x = exp (exp (t1.eval x))`. This is the base step of
the reduction recursion. -/
theorem eml_eval_zero_iff (t1 t2 : EMLTree) (x : Real)
    (hpos : 0 < t2.eval x) :
    (EMLTree.eml t1 t2).eval x = 0 ↔
      t2.eval x = Real.exp (Real.exp (t1.eval x)) := by
  show Real.exp (t1.eval x) - Real.log (t2.eval x) = 0 ↔ _
  exact Real.eml_node_zero_iff (t1.eval x) (t2.eval x) hpos

end MachLib
