import MachLib.PfaffianChainExtend
import MachLib.PfaffianChainNodes
import MachLib.SinNotInEML

/-!
# EMLTree → Pfaffian chain encoder

The recursive encoder `enc` turns an `EMLTree` (`const | var | eml t1 t2` with
`eml t1 t2 = exp(t1) − log(t2)`) into a Pfaffian chain + barrier polynomial, by
*state-threading* a single growing chain via `chainExtend` (no chain-merging).
It carries the real recip/log/exp Pfaffian relations, so it ships BOTH:

- `enc_eval` — the barrier evaluates to `t.eval` (eval-agreement); and
- `enc_isCoherentOn` — the produced chain is genuinely coherent on `(a,b)`,
  given the context chain is coherent there and every `eml` node's
  log-argument stays positive (`LogArgPos`).

`enc_isCoherentOn` is the payoff: a coherent chain is analytic, which is what
the log-Khovanskii arc consumes.

Two index-bookkeeping primitives the recursion needs:

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

/-! ## Index-lift foundation

The encoder's real Pfaffian relations live in the full chain space and
reference `chainTotalDeriv` of the (coherent) sub-chain, so a sub-barrier `b2`
built in `t2`'s space (`MultiPoly N`) must be raised into `t1`'s space
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

/-! ## The eml step's Pfaffian relations

The three real relations for one `eml` node, added innermost-first: reciprocal
`r = 1/⟦t2⟧`, log `L = log⟦t2⟧`, exp `E = exp⟦t1⟧`. `w : MultiPoly M` is `t2`'s
value expressed in `cb`'s space (the encoder supplies `encLift t1 b2`, whose
value equals `⟦t2⟧` by `eval_encLift` + `enc_lower`). Eval-functions are written
in the node-matching form so each node coherence lemma applies with `hne := rfl`.
-/

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

/-- Coherent eml step chain: reciprocal → log → exp, all with real Pfaffian
relations (`b1 = ⟦t1⟧` in `cb`'s space; the exp level's `E' = (cTD b1)·E`). -/
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

/-! ## The encoder `enc`

`enc` state-threads the eml steps above. At each `eml` node `t2`'s barrier is
lifted into `t1`'s chain space (`encLift t1`) so the recip/log relations can
reference it; `enc_lower` (chain-value preservation) + `eval_encLift` bridge
that lift's value back to `⟦t2⟧`, which is where the genuine positivity
side-condition `LogArgPos` enters `enc_isCoherentOn`. -/

/-- The eml step as `(chain, barrier)`: the real-relation chain `encEmlStepR`
paired with the `exp_var − log_var` barrier. `w` is `t2`'s value in `cb`'s
space (the encoder supplies `encLift t1 b2`). -/
noncomputable def encEmlStep {M : Nat} (cb : PfaffianChain M) (b1 w : MultiPoly M) :
    PfaffianChain (M + 3) × MultiPoly (M + 3) :=
  (encEmlStepR cb b1 w,
   MultiPoly.sub
     (MultiPoly.varY (⟨M + 2, by omega⟩ : Fin (M + 3)))
     (MultiPoly.varY (⟨M + 1, by omega⟩ : Fin (M + 3))))

/-- The encoder: state-thread one growing chain, innermost-first. Cast-free
(`len`-shaped output). At each `eml` node it lifts `t2`'s barrier into `t1`'s
chain space (`encLift t1`) so the recip/log relations can reference it. -/
noncomputable def enc : (t : EMLTree) → {N : Nat} → PfaffianChain N →
    PfaffianChain (len t N) × MultiPoly (len t N)
  | .const c, _, chain => (chain, MultiPoly.const c)
  | .var,     _, chain => (chain, MultiPoly.varX)
  | .eml t1 t2, _, chain =>
    let r2 := enc t2 chain
    let r1 := enc t1 r2.1
    encEmlStep r1.1 r1.2 (encLift t1 r2.2)

/-- **`enc` preserves lower chain-values.** Because every node is added on top,
the first `N` variables of `enc t ca` are `ca`'s originals. Relations do not
affect `evals`. -/
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
      simp only [enc, encEmlStep, encEmlStepR, stepCD, stepCC]
      rw [chainExtend_evals_of_lt _ _ _ _ hi0,
          chainExtend_evals_of_lt _ _ _ _ hi1,
          chainExtend_evals_of_lt _ _ _ _ hi2,
          ih1 (enc t2 ca).1 x ⟨i.val, Nat.lt_of_lt_of_le i.isLt hN2⟩, ih2 ca x i]

/-- **The `encLift` value bridge.** `t2`'s barrier, lifted into `t1`'s chain
space and evaluated along `enc t1 (enc t2 chain).1`, equals its value along
`t2`'s own chain — because `enc_lower` says the lower chain-values are shared
and `eval_encLift` says the added top variables are irrelevant. Stated with the
sub-value `v` as a hypothesis so it serves both `enc_eval` (via the IH) and
`enc_isCoherentOn` (via `enc_eval`) without mutual recursion. -/
theorem enc_encLift_eval (t1 t2 : EMLTree) {N : Nat} (chain : PfaffianChain N) (x v : Real)
    (h2 : MultiPoly.eval (enc t2 chain).2 x ((enc t2 chain).1.chainValues x) = v) :
    MultiPoly.eval (encLift t1 (enc t2 chain).2) x
        ((enc t1 (enc t2 chain).1).1.chainValues x) = v := by
  rw [eval_encLift t1 (enc t2 chain).2 x ((enc t1 (enc t2 chain).1).1.chainValues x)]
  have henv : (fun i : Fin (len t2 N) =>
      ((enc t1 (enc t2 chain).1).1.chainValues x)
        ⟨i.val, Nat.lt_of_lt_of_le i.isLt (le_len t1 (len t2 N))⟩)
      = (enc t2 chain).1.chainValues x := by
    funext i
    exact enc_lower t1 (enc t2 chain).1 x i
  rw [henv]; exact h2

/-- The two top variables (recip, log) of `stepCD` are irrelevant to a barrier
lifted twice (`liftLastYBy 2`): it evaluates as on the base chain `cb`. -/
theorem stepCD_liftLastYBy2_eval {M : Nat} (cb : PfaffianChain M) (w b1 : MultiPoly M)
    (x : Real) :
    MultiPoly.eval (liftLastYBy 2 b1) x ((stepCD cb w).chainValues x)
      = MultiPoly.eval b1 x (cb.chainValues x) := by
  rw [eval_liftLastYBy 2 b1 x ((stepCD cb w).chainValues x)]
  congr 1
  funext i
  show (stepCD cb w).evals ⟨i.val, by omega⟩ x = cb.evals i x
  simp only [stepCD, stepCC]
  rw [chainExtend_evals_of_lt _ _ _ _ (by omega : i.val < M + 1),
      chainExtend_evals_of_lt _ _ _ _ (by omega : i.val < M)]

/-- The one top variable (recip) of `stepCC` is irrelevant to a once-lifted
barrier: `liftLastY w` evaluates as `w` on the base chain `cb`. -/
theorem stepCC_liftLastY_eval {M : Nat} (cb : PfaffianChain M) (w : MultiPoly M) (x : Real) :
    MultiPoly.eval (MultiPoly.liftLastY w) x ((stepCC cb w).chainValues x)
      = MultiPoly.eval w x (cb.chainValues x) := by
  simp only [stepCC]
  exact eval_liftLastY_chainExtend cb _ _ w x

/-- `encEmlStep`'s barrier evaluates to `exp v1 − log v2` when the sub-barriers
evaluate to `v1` (`⟦t1⟧`) and `v2` (`⟦t2⟧`) along `cb`, bridged through the
recip/log lifts. -/
theorem encEmlStep_eval {M : Nat} (cb : PfaffianChain M) (b1 w : MultiPoly M) (x v1 v2 : Real)
    (hb1 : MultiPoly.eval b1 x (cb.chainValues x) = v1)
    (hw : MultiPoly.eval w x (cb.chainValues x) = v2) :
    MultiPoly.eval (encEmlStep cb b1 w).2 x ((encEmlStep cb b1 w).1.chainValues x)
      = Real.exp v1 - Real.log v2 := by
  simp only [encEmlStep, MultiPoly.eval_sub, MultiPoly.eval_varY]
  congr 1
  · show (encEmlStepR cb b1 w).evals (⟨M + 2, by omega⟩ : Fin (M + 3)) x = Real.exp v1
    simp only [encEmlStepR]
    rw [chainExtend_evals_last (stepCD cb w) _ _]
    show Real.exp (MultiPoly.eval (liftLastYBy 2 b1) x ((stepCD cb w).chainValues x))
       = Real.exp v1
    rw [stepCD_liftLastYBy2_eval cb w b1 x, hb1]
  · show (encEmlStepR cb b1 w).evals (⟨M + 1, by omega⟩ : Fin (M + 3)) x = Real.log v2
    simp only [encEmlStepR]
    rw [chainExtend_evals_of_lt _ _ _ _ (by omega : M + 1 < M + 2)]
    show (stepCD cb w).evals (⟨M + 1, by omega⟩ : Fin (M + 2)) x = Real.log v2
    simp only [stepCD]
    rw [chainExtend_evals_last (stepCC cb w) _ _]
    show Real.log (MultiPoly.eval (MultiPoly.liftLastY w) x ((stepCC cb w).chainValues x))
       = Real.log v2
    rw [stepCC_liftLastY_eval cb w x, hw]

/-- **Eval-agreement.** The encoded barrier evaluates to the tree's value:
`(pfaffianChainFn (enc t chain).1 (enc t chain).2).eval x = t.eval x`, for any
context chain. Bridged through `encLift`/`enc_lower` (relation-independent). -/
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
    exact encEmlStep_eval (enc t1 (enc t2 chain).1).1 (enc t1 (enc t2 chain).1).2
      (encLift t1 (enc t2 chain).2) x (t1.eval x) (t2.eval x) (ih1 (enc t2 chain).1 x)
      (enc_encLift_eval t1 t2 chain x (t2.eval x) (ih2 chain x))

/-- The genuine side-condition for `enc`'s coherence: every `eml` node's log
argument `⟦t2⟧` stays positive on `(a,b)` (MachLib's `log` is only
differentiable on the positives). -/
def LogArgPos : EMLTree → Real → Real → Prop
  | .const _, _, _ => True
  | .var,     _, _ => True
  | .eml t1 t2, a, b =>
      LogArgPos t1 a b ∧ LogArgPos t2 a b ∧ (∀ x, a < x → x < b → 0 < t2.eval x)

/-- **The encoder produces a coherent chain.** If the context chain is coherent
on `(a,b)` and every `eml` node's log-argument stays positive there
(`LogArgPos`), then `enc t chain`'s chain is coherent on `(a,b)`. Leaves are
the context unchanged; each `eml` node is `encEmlStepR_isCoherentOn` with `cb` =
the (inductively coherent) `t1` sub-chain and positivity via `enc_eval`. -/
theorem enc_isCoherentOn (t : EMLTree) :
    ∀ {N : Nat} (chain : PfaffianChain N) (a b : Real),
      chain.IsCoherentOn a b → LogArgPos t a b → (enc t chain).1.IsCoherentOn a b := by
  induction t with
  | const c => intro N chain a b hchain _; exact hchain
  | var => intro N chain a b hchain _; exact hchain
  | eml t1 t2 ih1 ih2 =>
    intro N chain a b hchain hlog
    obtain ⟨hlog1, hlog2, hpos2⟩ := hlog
    have hc2 : (enc t2 chain).1.IsCoherentOn a b := ih2 chain a b hchain hlog2
    have hc1 : (enc t1 (enc t2 chain).1).1.IsCoherentOn a b :=
      ih1 (enc t2 chain).1 a b hc2 hlog1
    have hwpos : ∀ x, a < x → x < b →
        0 < MultiPoly.eval (encLift t1 (enc t2 chain).2) x
              ((enc t1 (enc t2 chain).1).1.chainValues x) := by
      intro x hxa hxb
      rw [enc_encLift_eval t1 t2 chain x (t2.eval x) (enc_eval t2 chain x)]
      exact hpos2 x hxa hxb
    exact encEmlStepR_isCoherentOn (enc t1 (enc t2 chain).1).1
      (enc t1 (enc t2 chain).1).2 (encLift t1 (enc t2 chain).2) a b hc1 hwpos

end MachLib
