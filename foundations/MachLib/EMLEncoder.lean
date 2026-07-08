import MachLib.PfaffianChainExtend
import MachLib.SinNotInEML

/-!
# EMLTree → Pfaffian chain encoder — foundation

The recursive encoder turns an `EMLTree` (`const | var | eml t1 t2` with
`eml t1 t2 = exp(t1) − log(t2)`) into a Pfaffian chain + barrier polynomial
with eval-agreement, by *state-threading* a single growing chain via
`chainExtend` (no chain-merging).

This file builds the two index-bookkeeping primitives the recursion needs:

- `nVars t` — the number of chain variables `t` contributes: `0` for
  `const`/`var`, and `nVars t2 + nVars t1 + 3` for `eml t1 t2` (each `eml`
  node adds a reciprocal, a log, and an exp variable on top of its
  subtrees'). Ordered `t2` first so the recursion processes the log
  argument's reciprocal before the log itself.

- `liftLastYBy k` — `liftLastY` iterated `k` times, embedding `MultiPoly n`
  into `MultiPoly (n + k)` free of the top `k` variables. This is the ONE
  lift the encoder needs: after `t1` extends the chain above `t2`'s
  variables, `t2`'s barrier rises by `nVars t1` levels. `eval_liftLastYBy`
  says the added top variables are irrelevant to the lifted polynomial's
  value.

No new axioms.
-/

namespace MachLib

open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly

/-- Number of chain variables an EML tree contributes. -/
def nVars : EMLTree → Nat
  | .const _  => 0
  | .var      => 0
  | .eml t1 t2 => nVars t2 + nVars t1 + 3

/-- `liftLastY` iterated `k` times: `MultiPoly n → MultiPoly (n + k)`,
free of the top `k` variables. -/
noncomputable def liftLastYBy {n : Nat} : (k : Nat) → MultiPoly n → MultiPoly (n + k)
  | 0,     p => p
  | k + 1, p => MultiPoly.liftLastY (liftLastYBy k p)

/-- The top `k` variables are irrelevant to a `k`-fold lift's value. -/
theorem eval_liftLastYBy {n : Nat} (k : Nat) (p : MultiPoly n) (x : Real)
    (env : Fin (n + k) → Real) :
    MultiPoly.eval (liftLastYBy k p) x env
      = MultiPoly.eval p x (fun i : Fin n => env ⟨i.val, by omega⟩) := by
  induction k with
  | zero =>
    show MultiPoly.eval p x env
       = MultiPoly.eval p x (fun i : Fin n => env ⟨i.val, by omega⟩)
    congr 1
  | succ k ih =>
    show MultiPoly.eval (MultiPoly.liftLastY (liftLastYBy k p)) x env
       = MultiPoly.eval p x (fun i : Fin n => env ⟨i.val, by omega⟩)
    rw [MultiPoly.eval_liftLastY (liftLastYBy k p) x env,
        ih (fun j : Fin (n + k) => env ⟨j.val, by omega⟩)]

open MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianChain

/-- **The encoder (eval layer).** State-threads a single growing chain over
the EML tree, returning `(chain, barrier)` with the barrier expressing the
tree's value in the chain's variables. The chain's *evaluations* are the
exact sub-expression values (so `barrier` evaluates to `t.eval`); its
*relations* are placeholders (`const 0`) at this layer — the coherent
relations that make it `IsExpLogRecipW`/coherent come from the
`PfaffianChainNodes` steps in the next layer. The recursion:
`eml t1 t2` processes `t2` (log arg), then `t1` (exp arg) on top, lifts
`t2`'s barrier over `t1`'s new variables (`liftLastYBy`), then appends
reciprocal / log / exp variables; the barrier is `exp_var − log_var`. The
one length cast reconciles `((N+a)+b)+3` with `N+(a+b+3)`. -/
noncomputable def enc : (t : EMLTree) → {N : Nat} → PfaffianChain N →
    PfaffianChain (N + nVars t) × MultiPoly (N + nVars t)
  | .const c, _, chain => (chain, MultiPoly.const c)
  | .var,     _, chain => (chain, MultiPoly.varX)
  | .eml t1 t2, N, chain =>
    let r2 := enc t2 chain
    let r1 := enc t1 r2.1
    let cb := r1.1
    let b2b := liftLastYBy (nVars t1) r2.2
    let b1  := r1.2
    let cc := chainExtend cb
      (fun y => 1 / MultiPoly.eval b2b y (cb.chainValues y)) (MultiPoly.const 0)
    let b2c := MultiPoly.liftLastY b2b
    let cd := chainExtend cc
      (fun y => Real.log (MultiPoly.eval b2c y (cc.chainValues y))) (MultiPoly.const 0)
    let b1c := liftLastYBy 2 b1
    let ce := chainExtend cd
      (fun y => Real.exp (MultiPoly.eval b1c y (cd.chainValues y))) (MultiPoly.const 0)
    let barrier : MultiPoly (N + nVars t2 + nVars t1 + 3) := MultiPoly.sub
      (MultiPoly.varY (⟨N + nVars t2 + nVars t1 + 2, by omega⟩ :
        Fin (N + nVars t2 + nVars t1 + 3)))
      (MultiPoly.varY (⟨N + nVars t2 + nVars t1 + 1, by omega⟩ :
        Fin (N + nVars t2 + nVars t1 + 3)))
    let hlen : N + nVars t2 + nVars t1 + 3 = N + nVars (EMLTree.eml t1 t2) := by
      simp only [nVars]; omega
    (hlen ▸ ce, hlen ▸ barrier)

end MachLib
