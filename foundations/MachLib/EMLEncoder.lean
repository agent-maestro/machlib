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

/-- The chain length `enc` actually produces from a context of length `N`.
Defined to MATCH the construction exactly (`len t1 (len t2 N) + 3` for
`eml`), so `enc` needs no length cast. Equals `N + nVars t` (`len_eq`). -/
def len : EMLTree → Nat → Nat
  | .const _, N => N
  | .var,     N => N
  | .eml t1 t2, N => len t1 (len t2 N) + 3

/-- `len t N = N + nVars t`. -/
theorem len_eq (t : EMLTree) (N : Nat) : len t N = N + nVars t := by
  induction t generalizing N with
  | const c => rfl
  | var => rfl
  | eml t1 t2 ih1 ih2 => show len t1 (len t2 N) + 3 = _; rw [ih1, ih2, nVars]; omega

/-- **The encoder (eval layer).** State-threads a single growing chain over
the EML tree, returning `(chain, barrier)` with the barrier expressing the
tree's value in the chain's variables. The chain's *evaluations* are the
exact sub-expression values (so `barrier` evaluates to `t.eval`); its
*relations* are placeholders (`const 0`) at this layer — the coherent
`IsExpLogRecipW` relations come from the `PfaffianChainNodes` steps in the
next layer.

`eml t1 t2` processes `t2` (log arg), then `t1` (exp arg) on top, then
appends reciprocal (`1/t2`), log (`log t2`), exp (`exp t1`) variables; the
barrier is `exp_var − log_var`. Using `len` for the length and referencing
the sub-chains `ca`/`cb` directly in the node eval-functions makes the def
BOTH cast-free and lift-free — the two simplifications that make its
eval-agreement (`enc_eval`) clean. -/
noncomputable def enc : (t : EMLTree) → {N : Nat} → PfaffianChain N →
    PfaffianChain (len t N) × MultiPoly (len t N)
  | .const c, _, chain => (chain, MultiPoly.const c)
  | .var,     _, chain => (chain, MultiPoly.varX)
  | .eml t1 t2, N, chain =>
    let r2 := enc t2 chain
    let r1 := enc t1 r2.1
    let ca := r2.1
    let b2 := r2.2
    let cb := r1.1
    let b1 := r1.2
    let cc := chainExtend cb
      (fun y => 1 / MultiPoly.eval b2 y (ca.chainValues y)) (MultiPoly.const 0)
    let cd := chainExtend cc
      (fun y => Real.log (MultiPoly.eval b2 y (ca.chainValues y))) (MultiPoly.const 0)
    let ce := chainExtend cd
      (fun y => Real.exp (MultiPoly.eval b1 y (cb.chainValues y))) (MultiPoly.const 0)
    let barrier : MultiPoly (len t1 (len t2 N) + 3) := MultiPoly.sub
      (MultiPoly.varY (⟨len t1 (len t2 N) + 2, by omega⟩ :
        Fin (len t1 (len t2 N) + 3)))
      (MultiPoly.varY (⟨len t1 (len t2 N) + 1, by omega⟩ :
        Fin (len t1 (len t2 N) + 3)))
    (ce, barrier)

end MachLib
