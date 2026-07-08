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
  MachLib.PfaffianChainMod.PfaffianFn MachLib.PfaffianGeneralReduce

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

/-- The `eml` step, factored out as a NAMED helper so its structure is
exposed for `enc`'s eval-agreement proof. Given `t2`'s chain/barrier
`(ca, b2)` and `t1`'s `(cb, b1)`, appends the reciprocal / log / exp
variables and returns `(chain, exp_var − log_var)`. Eval-functions read the
sub-values off `ca`/`cb` directly (lift-free). -/
noncomputable def encEmlStep {N : Nat} (ca : PfaffianChain N) (b2 : MultiPoly N)
    {M : Nat} (cb : PfaffianChain M) (b1 : MultiPoly M) :
    PfaffianChain (M + 3) × MultiPoly (M + 3) :=
  let cc := chainExtend cb
    (fun y => 1 / MultiPoly.eval b2 y (ca.chainValues y)) (MultiPoly.const 0)
  let cd := chainExtend cc
    (fun y => Real.log (MultiPoly.eval b2 y (ca.chainValues y))) (MultiPoly.const 0)
  let ce := chainExtend cd
    (fun y => Real.exp (MultiPoly.eval b1 y (cb.chainValues y))) (MultiPoly.const 0)
  (ce, MultiPoly.sub
    (MultiPoly.varY (⟨M + 2, by omega⟩ : Fin (M + 3)))
    (MultiPoly.varY (⟨M + 1, by omega⟩ : Fin (M + 3))))

noncomputable def enc : (t : EMLTree) → {N : Nat} → PfaffianChain N →
    PfaffianChain (len t N) × MultiPoly (len t N)
  | .const c, _, chain => (chain, MultiPoly.const c)
  | .var,     _, chain => (chain, MultiPoly.varX)
  | .eml t1 t2, N, chain =>
    let r2 := enc t2 chain
    let r1 := enc t1 r2.1
    encEmlStep r2.1 r2.2 r1.1 r1.2

/-- `encEmlStep`'s barrier evaluates to `exp v1 − log v2` when the two
sub-barriers evaluate to `v1` (`t1`'s value) and `v2` (`t2`'s value). The
exp variable is `encEmlStep`'s top; the log variable is one below it. -/
theorem encEmlStep_eval {N : Nat} (ca : PfaffianChain N) (b2 : MultiPoly N)
    {M : Nat} (cb : PfaffianChain M) (b1 : MultiPoly M) (x v1 v2 : Real)
    (hb2 : MultiPoly.eval b2 x (ca.chainValues x) = v2)
    (hb1 : MultiPoly.eval b1 x (cb.chainValues x) = v1) :
    MultiPoly.eval (encEmlStep ca b2 cb b1).2 x ((encEmlStep ca b2 cb b1).1.chainValues x)
      = Real.exp v1 - Real.log v2 := by
  simp only [encEmlStep, MultiPoly.eval_sub, MultiPoly.eval_varY]
  congr 1
  · show (chainExtend _ _ _).evals (⟨M + 2, by omega⟩ : Fin (M + 3)) x = Real.exp v1
    rw [chainExtend_evals_last]
    show Real.exp (MultiPoly.eval b1 x (cb.chainValues x)) = Real.exp v1
    rw [hb1]
  · show (chainExtend _ _ _).evals (⟨M + 1, by omega⟩ : Fin (M + 3)) x = Real.log v2
    rw [chainExtend_evals_of_lt _ _ _ _ (by omega : M + 1 < M + 2)]
    show (chainExtend _ _ _).evals (⟨M + 1, by omega⟩ : Fin (M + 2)) x = Real.log v2
    rw [chainExtend_evals_last]
    show Real.log (MultiPoly.eval b2 x (ca.chainValues x)) = Real.log v2
    rw [hb2]

/-- **Eval-agreement.** The encoded barrier evaluates to the tree's value:
`(pfaffianChainFn (enc t chain).1 (enc t chain).2).eval x = t.eval x`, for any
context chain. This is the correctness of the encoder's eval layer. -/
theorem enc_eval : ∀ (t : EMLTree) {N : Nat} (chain : PfaffianChain N) (x : Real),
    (pfaffianChainFn (enc t chain).1 (enc t chain).2).eval x = t.eval x := by
  intro t
  induction t with
  | const c => intro N chain x; rfl
  | var => intro N chain x; rfl
  | eml t1 t2 ih1 ih2 =>
    intro N chain x
    show MultiPoly.eval (enc (EMLTree.eml t1 t2) chain).2 x
          ((enc (EMLTree.eml t1 t2) chain).1.chainValues x)
       = Real.exp (t1.eval x) - Real.log (t2.eval x)
    exact encEmlStep_eval (enc t2 chain).1 (enc t2 chain).2
      (enc t1 (enc t2 chain).1).1 (enc t1 (enc t2 chain).1).2 x (t1.eval x) (t2.eval x)
      (ih2 chain x) (ih1 (enc t2 chain).1 x)

end MachLib
