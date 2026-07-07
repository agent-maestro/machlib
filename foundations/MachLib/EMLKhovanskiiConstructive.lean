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

## Status

PROVEN here (0 sorry, footprints free of `sorryAx` and
`zero_count_bound_classical`):

  installment 1 — foundations:
  * `eml_node_zero_iff`   — the log-elimination identity (the reduction crux).
  * `eml_eval_zero_iff`   — its eval-level form on an `EMLTree.eml` node.

  installment 2a — the closed expression type:
  * `ELExpr` (+ `eval`, `logCount`) — the type the recursion runs on.
  * `EMLTree.toELExpr` (+ `toELExpr_eval`) — EML embeds, eval-preserving.

  installment 2b — the recursion STEP:
  * `Real.sub_log_zero_iff` — the general engine `A − log b = 0 ↔ b = exp A`.
  * `ELExpr.elim_top_log`   — one log removed, zeros preserved on `B > 0`.
  * `ELExpr.elim_top_log_logCount` — the step lowers `logCount` by one
                                     (recursion terminates).

REMAINING (documented, multi-session — the rest of the ~800-line body):
  3. The recursion DRIVER: iterate `elim_top_log` under strong induction on
     `logCount`, with re-association lemmas that always surface a subtracted
     `log` into the `A − logE B` shape the step consumes. Terminates at a
     `logCount = 0` (exp-only) `ELExpr`.
  4. Encode an exp-only `ELExpr` as an exp-type Pfaffian chain + `MultiPoly`
     (over `chainNFn` / a tailored `PfaffianChain`) with eval-agreement, so
     `chainN_khovanskii_bound_unconditional` / `pfaffian_khovanskii_bound_gen_uncond`
     applies. This is the bulk of what's left.
  5. Discharge the validity/positivity side-conditions (the second axiom,
     `eml_pfaffian_validon_from_sin_equality`, a separate smoothness bridge).
  6. Re-prove `sin_not_in_eml_any_depth` citing the constructive bound instead
     of `zero_count_bound_classical`; confirm via `#print axioms`.

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

/-! ## installment 2a — the closed expression type for the recursion

The log-elimination recursion leaves the EML grammar (`exp (exp ·)` is not an
`EMLTree.eml` node), so it operates on a broader type `ELExpr` closed under
`+ − × exp log`, into which `EMLTree` embeds. `logCount` is the recursion's
termination measure: each elimination step drops it by one until the expression
is log-free (exp-only), where an exp-type Pfaffian chain applies. -/

/-- Exp/log expression algebra: the closed type the reduction recurses on. -/
inductive ELExpr : Type where
  | const : Real → ELExpr
  | var   : ELExpr
  | add   : ELExpr → ELExpr → ELExpr
  | sub   : ELExpr → ELExpr → ELExpr
  | mul   : ELExpr → ELExpr → ELExpr
  | expE  : ELExpr → ELExpr
  | logE  : ELExpr → ELExpr

namespace ELExpr

/-- Real evaluation. -/
noncomputable def eval : ELExpr → Real → Real
  | const c, _ => c
  | var,     x => x
  | add a b, x => a.eval x + b.eval x
  | sub a b, x => a.eval x - b.eval x
  | mul a b, x => a.eval x * b.eval x
  | expE a,  x => Real.exp (a.eval x)
  | logE a,  x => Real.log (a.eval x)

/-- Number of `log` nodes — the termination measure of the log-elimination
recursion. A `logCount = 0` expression is exp-only. -/
def logCount : ELExpr → Nat
  | const _ => 0
  | var     => 0
  | add a b => a.logCount + b.logCount
  | sub a b => a.logCount + b.logCount
  | mul a b => a.logCount + b.logCount
  | expE a  => a.logCount
  | logE a  => 1 + a.logCount

end ELExpr

/-- Embed an EML tree into `ELExpr`: an `eml` node is `exp(t1) − log(t2)`. -/
def EMLTree.toELExpr : EMLTree → ELExpr
  | .const c   => .const c
  | .var       => .var
  | .eml t1 t2 => .sub (.expE t1.toELExpr) (.logE t2.toELExpr)

/-- The embedding preserves evaluation. -/
theorem EMLTree.toELExpr_eval (t : EMLTree) (x : Real) :
    t.toELExpr.eval x = t.eval x := by
  induction t with
  | const c => rfl
  | var => rfl
  | eml t1 t2 ih1 ih2 =>
    show Real.exp (t1.toELExpr.eval x) - Real.log (t2.toELExpr.eval x)
       = Real.exp (t1.eval x) - Real.log (t2.eval x)
    rw [ih1, ih2]

end MachLib

namespace MachLib
namespace Real

/-- **The general log-elimination engine.** For ANY real `A` (not just an
`exp`): `A − log b = 0 ↔ b = exp A`, on `b > 0`. This is what isolates the
topmost subtracted `log` at each recursion step; `eml_node_zero_iff` is the
special case `A = exp a`. -/
theorem sub_log_zero_iff (A b : Real) (hb : 0 < b) :
    (A - log b = 0) ↔ (b = exp A) := by
  constructor
  · intro h
    have h1 : A = log b := by
      have e : A - log b + log b = 0 + log b := by rw [h]
      rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at e
      exact e
    have hb2 := congrArg exp h1
    rw [exp_log hb] at hb2
    exact hb2.symm
  · intro h
    rw [h, log_exp, sub_def, add_neg]

/-- `a − b = 0 ↔ a = b`. -/
theorem sub_eq_zero_iff (a b : Real) : (a - b = 0) ↔ (a = b) := by
  constructor
  · intro h
    have e : a - b + b = 0 + b := by rw [h]
    rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at e
    exact e
  · intro h; rw [h, sub_self]

end Real

/-! ## installment 2b — the recursion step (one log eliminated, zeros preserved)

The engine of the reduction, at the `ELExpr` level: an isolable-log form
`A − log B` (the shape every EML `log` sits in after re-association) has, on the
validity domain `B > 0`, exactly the same zeros as `B − exp A` — which carries
one fewer `log`. Iterating drives `logCount` to `0` (an exp-only expression),
where an exp-type Pfaffian chain and the constructive Khovanskii bound apply. -/

namespace ELExpr

/-- **Recursion step — zeros preserved, one `log` removed.** For any
`A B : ELExpr`, on the validity domain `0 < B.eval x`,
`A − log B` and `B − exp A` have the same zero at `x`. -/
theorem elim_top_log (A B : ELExpr) (x : Real) (hpos : 0 < B.eval x) :
    (ELExpr.sub A (ELExpr.logE B)).eval x = 0 ↔
    (ELExpr.sub B (ELExpr.expE A)).eval x = 0 := by
  show A.eval x - Real.log (B.eval x) = 0 ↔ B.eval x - Real.exp (A.eval x) = 0
  rw [Real.sub_log_zero_iff (A.eval x) (B.eval x) hpos,
      Real.sub_eq_zero_iff (B.eval x) (Real.exp (A.eval x))]

/-- The step strictly lowers the `log`-count (termination of the recursion):
`sub B (expE A)` has one fewer `log` than `sub A (logE B)`. -/
theorem elim_top_log_logCount (A B : ELExpr) :
    (ELExpr.sub B (ELExpr.expE A)).logCount + 1
      = (ELExpr.sub A (ELExpr.logE B)).logCount := by
  show (B.logCount + A.logCount) + 1 = A.logCount + (1 + B.logCount)
  omega

end ELExpr
end MachLib
