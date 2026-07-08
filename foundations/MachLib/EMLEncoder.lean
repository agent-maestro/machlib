import MachLib.PfaffianChainExtend
import MachLib.PfaffianChainNodes
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

/-! ## Foundation for the coherent-relations layer

The eval layer above uses placeholder (`const 0`) relations and reads sub-values
off the sub-chains directly, which is lift-free. The coherent layer must instead
carry the *real* Pfaffian relations, which live in the full chain space and
reference `chainTotalDeriv` of the (coherent) sub-chain — so a sub-barrier `b2`
built in `ca`'s space (`MultiPoly N`) must be raised into `cb`'s space
(`MultiPoly (len t1 N)`). `encLift` is that raise, cast-free (target size is
`len`-shaped), and `eval_encLift` + `enc_lower` prove it preserves the value:
the raised barrier, evaluated along the extended chain, agrees with the original
along the sub-chain. -/

/-- Encoding only grows the chain: `N ≤ len t N`. -/
theorem le_len (t : EMLTree) (N : Nat) : N ≤ len t N := by
  induction t generalizing N with
  | const _ => exact Nat.le_refl N
  | var => exact Nat.le_refl N
  | eml t1 t2 ih1 ih2 =>
      have h2 := ih2 N
      have h1 := ih1 (len t2 N)
      show N ≤ len t1 (len t2 N) + 3
      omega

/-- Raise a `MultiPoly N` up to the chain `enc t` produces (`MultiPoly (len t N)`),
threading through exactly the variables `t` adds. Cast-free: the target size is
`len`-shaped, matching `enc`'s output. -/
noncomputable def encLift : (t : EMLTree) → {N : Nat} → MultiPoly N → MultiPoly (len t N)
  | .const _, _, p => p
  | .var,     _, p => p
  | .eml t1 t2, _, p => liftLastYBy 3 (encLift t1 (encLift t2 p))

/-- **`encLift` transports value:** the added variables are irrelevant, so a
raised polynomial evaluates to the original on the shared lower env. -/
theorem eval_encLift : (t : EMLTree) → {N : Nat} → (p : MultiPoly N) → (x : Real) →
    (env : Fin (len t N) → Real) →
    MultiPoly.eval (encLift t p) x env
      = MultiPoly.eval p x
          (fun i : Fin N => env ⟨i.val, Nat.lt_of_lt_of_le i.isLt (le_len t N)⟩)
  | .const _, _, _, _, _ => rfl
  | .var,     _, _, _, _ => rfl
  | .eml t1 t2, _, p, x, env => by
      show MultiPoly.eval (liftLastYBy 3 (encLift t1 (encLift t2 p))) x env = _
      rw [eval_liftLastYBy 3 (encLift t1 (encLift t2 p)) x env,
          eval_encLift t1 (encLift t2 p) x _,
          eval_encLift t2 p x _]

/-- **`enc` preserves lower chain-values.** Because every node is added on
top, the first `N` variables of `enc t ca` are `ca`'s originals. -/
theorem enc_lower (t : EMLTree) : ∀ {N : Nat} (ca : PfaffianChain N) (x : Real) (i : Fin N),
    (enc t ca).1.evals ⟨i.val, Nat.lt_of_lt_of_le i.isLt (le_len t N)⟩ x = ca.evals i x := by
  induction t with
  | const c => intro N ca x i; rfl
  | var => intro N ca x i; rfl
  | eml t1 t2 ih1 ih2 =>
      intro N ca x i
      have hN2 : N ≤ len t2 N := le_len t2 N
      have hM : len t2 N ≤ len t1 (len t2 N) := le_len t1 (len t2 N)
      have hi0 : i.val < len t1 (len t2 N) + 2 := by have := i.isLt; omega
      have hi1 : i.val < len t1 (len t2 N) + 1 := by have := i.isLt; omega
      have hi2 : i.val < len t1 (len t2 N) := by have := i.isLt; omega
      simp only [enc, encEmlStep]
      rw [chainExtend_evals_of_lt _ _ _ _ hi0,
          chainExtend_evals_of_lt _ _ _ _ hi1,
          chainExtend_evals_of_lt _ _ _ _ hi2,
          ih1 (enc t2 ca).1 x ⟨i.val, Nat.lt_of_lt_of_le i.isLt hN2⟩, ih2 ca x i]

/-! ## Coherent-relations layer

The eval layer's `encEmlStep` uses placeholder (`const 0`) relations. Here is the
same eml step built with the *real* recip / log / exp Pfaffian relations, and a
proof it is coherent. `w : MultiPoly M` is `t2`'s value expressed in `cb`'s
space (the caller supplies `encLift t1 b2`, whose value equals `⟦t2⟧` by
`eval_encLift` + `enc_lower`). Eval-functions are written in the node-matching
form so each node lemma applies with `hne := rfl`. Threading this through `enc`
(with a per-`eml`-node log-argument-positivity hypothesis) is the remaining
brick toward `(enc t chain).1.IsCoherentOn`. -/

/-- Reciprocal level: append `r = 1/⟦t2⟧` with the recip-type relation
`r' = −(cTD w)·r²`. -/
noncomputable def stepCC {M : Nat} (cb : PfaffianChain M) (w : MultiPoly M) :
    PfaffianChain (M + 1) :=
  chainExtend cb
    (fun y => 1 / MultiPoly.eval w y (cb.chainValues y))
    (MultiPoly.mul (MultiPoly.neg (MultiPoly.liftLastY (chainTotalDeriv cb w)))
      (MultiPoly.mul (MultiPoly.varY (⟨M, by omega⟩ : Fin (M + 1)))
                     (MultiPoly.varY (⟨M, by omega⟩ : Fin (M + 1)))))

/-- Log level: append `L = log⟦t2⟧` with the log-type relation `L' = (cTD w)·r`,
referencing the reciprocal variable `r` (at index `M`). -/
noncomputable def stepCD {M : Nat} (cb : PfaffianChain M) (w : MultiPoly M) :
    PfaffianChain (M + 2) :=
  chainExtend (stepCC cb w)
    (fun y => Real.log (MultiPoly.eval (MultiPoly.liftLastY w) y ((stepCC cb w).chainValues y)))
    (MultiPoly.mul (MultiPoly.liftLastY (chainTotalDeriv (stepCC cb w) (MultiPoly.liftLastY w)))
      (MultiPoly.varY (⟨M, by omega⟩ : Fin (M + 2))))

/-- Coherent eml step: reciprocal → log → exp, all with real Pfaffian relations
(`b1 = ⟦t1⟧` in `cb`'s space; the exp level's `E' = (cTD b1)·E`). -/
noncomputable def encEmlStepR {M : Nat} (cb : PfaffianChain M) (b1 w : MultiPoly M) :
    PfaffianChain (M + 3) :=
  chainExtend (stepCD cb w)
    (fun y => Real.exp (MultiPoly.eval (liftLastYBy 2 b1) y ((stepCD cb w).chainValues y)))
    (MultiPoly.mul (MultiPoly.liftLastY (chainTotalDeriv (stepCD cb w) (liftLastYBy 2 b1)))
      (MultiPoly.varY (⟨M + 2, by omega⟩ : Fin (M + 3))))

/-- **Per-step coherence.** If `cb` is coherent on `(a,b)` and `⟦t2⟧` (= `eval w`
along `cb`) is positive there, the eml step's chain is coherent on `(a,b)`.
Composes the three node-coherence lemmas (`recip`/`log`/`exp`) via
`chainExtend_isCoherentOn`; the log level's reciprocal-witness and positivity
transfer through `eval_liftLastY_chainExtend`. -/
theorem encEmlStepR_isCoherentOn {M : Nat} (cb : PfaffianChain M) (b1 w : MultiPoly M)
    (a b : Real) (hcb : cb.IsCoherentOn a b)
    (hwpos : ∀ x, a < x → x < b → 0 < MultiPoly.eval w x (cb.chainValues x)) :
    (encEmlStepR cb b1 w).IsCoherentOn a b := by
  have hcc : (stepCC cb w).IsCoherentOn a b := by
    simp only [stepCC]
    exact chainExtend_isCoherentOn cb _ _ a b hcb (fun x hxa hxb =>
      chainExtend_recip_isCoherentAt cb w x (hcb x hxa hxb) (hwpos x hxa hxb) _ rfl _ rfl)
  have hlw : ∀ y, MultiPoly.eval (MultiPoly.liftLastY w) y ((stepCC cb w).chainValues y)
      = MultiPoly.eval w y (cb.chainValues y) := by
    intro y; simp only [stepCC]; exact eval_liftLastY_chainExtend cb _ _ w y
  have hrecipval : ∀ y, (stepCC cb w).evals (⟨M, by omega⟩ : Fin (M + 1)) y
      = 1 / MultiPoly.eval (MultiPoly.liftLastY w) y ((stepCC cb w).chainValues y) := by
    intro y
    rw [hlw y]
    simp only [stepCC]
    rw [chainExtend_evals_last cb _ _]
  have hcd : (stepCD cb w).IsCoherentOn a b := by
    simp only [stepCD]
    exact chainExtend_isCoherentOn (stepCC cb w) _ _ a b hcc (fun x hxa hxb =>
      chainExtend_log_isCoherentAt (stepCC cb w) (MultiPoly.liftLastY w)
        (⟨M, by omega⟩ : Fin (M + 1)) x (hcc x hxa hxb)
        (by rw [hlw x]; exact hwpos x hxa hxb) hrecipval _ rfl _ rfl)
  simp only [encEmlStepR]
  exact chainExtend_isCoherentOn (stepCD cb w) _ _ a b hcd (fun x hxa hxb =>
    chainExtend_exp_isCoherentAt (stepCD cb w) (liftLastYBy 2 b1) x (hcd x hxa hxb) _ rfl _ rfl)

end MachLib
