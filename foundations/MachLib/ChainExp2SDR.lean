import MachLib.KhovanskiiReduction
import MachLib.IterExpChain
import MachLib.PfaffianFnBound

/-!
# MachLib.ChainExp2SDR — chain-2 Khovanskii via the KhovanskiiReduction SDR

## Why this file exists (2026-06-19, fresh-eyes restart)

The earlier chain-2 effort tried four `InnerKhovanskiiExp`-reduction
frameworks (Measured / WFR / WFRPrecond / ListMeasured). All four are
dead ends for chain-2:

1. **No consumer.** Nothing turns an `InnerKhovanskiiExpListMeasured`
   into a zero-count bound.
2. **Circular base case.** `chain2_to_ListMeasured` is built on
   `chainExp2_innerKhovanskii_full` with `T = MultiPoly 2` and `eval`
   the *full* chain-2 evaluation, so its `length_one_bound` obligation
   IS the whole chain-2 theorem (the `(y₀-1)(y₀-2)·y₁` counterexample).
3. **Descent is false.** The h-extended `scalarMul k g = k·y₀·g`
   multiplies by the chain variable `y₀ = eˣ`, shifting the exponent
   support up by one and ENLARGING it for non-last coefficients, so the
   sum-of-measures GROWS under the reduction.

The CORRECT path is the one that already closed single-exp:
`KhovanskiiReduction.lean`'s lex-measure + `StepwiseDecreaseReducer`.
The reduction there is `scaledReduction c f := chainTotalDeriv f - c·f`
(a **scalar** `c`, applied at the polynomial level), the lex measure is
purely a TERMINATION measure (it uses the y-free projection `mP2PFL`,
NOT an eval-based zero count), and the zero-count transfer is plain
Rolle — valid for ANY triangular coherent chain. `singleExp_khovanskii_bound`
already leaves an `sdr_other` hook for non-SingleExp chains; closing
chain-2 = supplying a chain-2 `StepwiseDecreaseReducer`.

## The key chain-2 insight: c = 0, not c = d

For the lex measure's second component
`polyTrueDegreeStrict (polyCoeffs (mP2PFL (leadingCoeffYₜₒₚ f)))`, the
descent under `scaledReduction c` depends on the leading coefficient of
the top chain variable.

* **SingleExp** (top var `y₀`, relation `y₀' = y₀`):
  `leadingCoeffY₀(f') = cTD(a_d) + d·a_d`. The `d·a_d` term has full
  x-degree, so `c = 0` does NOT descend — you need `c = d` to cancel it.

* **Chain-2** (top var `y₁`, relation `y₁' = y₀·y₁`):
  `leadingCoeffY₁(f') = cTD(a_d) + d·y₀·a_d`. The extra factor `y₀` is
  killed by `mP2PFL` (which maps every `varY → const 0`), so under the
  measure the `d·y₀·a_d` term VANISHES and `c = 0` (the plain
  derivative) already gives strict descent. Using `c = d` would instead
  leave a `-d·a_d` residue at full degree. So chain-2 wants `c = 0` —
  the opposite of single-exp, and a cleaner cancellation.

This asymmetry is why chain-2 needs its own SDR rather than reusing
`singleExp_reduceStep`.

## Cornerstone lemma (this file)

The whole chain-2 second-component descent rests on a *generalized*
bridge that drops the y-free hypothesis of
`multiPolyToPolyForLex_chainTotalDeriv_of_y_free`:

  `Poly.eval (mP2PFL (chainTotalDeriv (IterExpChain n) q)) x
     = Poly.eval (polyDerivative (mP2PFL q)) x`     for ALL q.

It holds because every `IterExpChain` relation is `prodVarYUpTo` (a
product that always contains `varY 0`), so it evaluates to 0 once
`mP2PFL` sets `y₀ = 0`. The structural version is false (the projected
product is not syntactically `0`), but the EVAL version holds, and
eval-equality is exactly what the PIT bridge (`PolynomialCanonical`
Phase E) lifts to `polyCoeffs` equality — the same machinery that closed
single-exp's `h_bridge`.

## Remaining pieces to close chain-2 (next increments)

1. **Chain-2 `leadingCoeffY` identity** (the lemma-1 analog):
   `leadingCoeffY₁ (chainTotalDeriv (IterExpChain 2) f)` eval-equals
   `chainTotalDeriv (leadingCoeffY₁ f) + d · y₀ · (leadingCoeffY₁ f)`,
   `d := degreeY₁ f`. Structural induction on `f.poly`; the `mul` case is
   the Leibniz tricky one (mirror ChainExp2PathC's single-exp version).
2. **Second-component strict descent at c = 0** via this cornerstone +
   the PIT bridge + `polyTrueDegreeStrict_polyDerivativeCoeffs_lt`
   (Phase G, already shipped).
3. **chain-2 `ReduceStep`** (`c = 0`) + **canonicalTrim** (when the
   second component is 0, `dropLeadingY` to drop the first component) +
   **dispatch** — mirror `singleExp_reduceStep_closed` /
   `singleExp_canonicalTrim_step` / `singleExp_dispatch_step`.
4. **`chain2_sdr`** assembled, then a `chainN_to_generic_sdr`-style
   dispatcher (n=1 → singleExp, n=2 → chain2, else fallback), fed to
   `PfaffianFn.khovanskii_bound_via_sdr` with `IterExpChain 2`'s
   triangularity + coherence for the end-to-end chain-2 bound.

Zero new axioms. Zero `sorry`.
-/

namespace MachLib
namespace ChainExp2SDR

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.PolynomialRootCount
open MachLib.PolynomialEvidence (Poly)

/-! ## Helper: the y-free projection of an IterExpChain relation evals to 0

Every relation of `IterExpChain` is `prodVarYUpTo k` — a product of
`varY 0 · … · varY k` that always contains the factor `varY 0`. The
y-free projection `mP2PFL` sends each `varY` to `Poly.const 0`, so the
projected product evaluates to `0` at every point. -/
theorem eval_mP2PFL_prodVarYUpTo_eq_zero {n : Nat} (k : Nat) (hk : k < n)
    (x : Real) :
    Poly.eval (multiPolyToPolyForLex (prodVarYUpTo k hk : MultiPoly n)) x = 0 := by
  induction k with
  | zero =>
    -- prodVarYUpTo 0 hk = varY ⟨0, hk⟩; mP2PFL = Poly.const 0; eval = 0.
    rfl
  | succ m ih =>
    -- prodVarYUpTo (m+1) hk = mul (prodVarYUpTo m _) (varY ⟨m+1, hk⟩).
    -- mP2PFL distributes over mul; the left factor evals to 0 by IH.
    show Poly.eval (multiPolyToPolyForLex (prodVarYUpTo m (Nat.lt_of_succ_lt hk))) x
       * Poly.eval (multiPolyToPolyForLex (MultiPoly.varY ⟨m + 1, hk⟩)) x = 0
    rw [ih (Nat.lt_of_succ_lt hk), zero_mul]

/-! ## Cornerstone: the generalized cTD → polyDerivative eval bridge

`multiPolyToPolyForLex_chainTotalDeriv_of_y_free` (in PfaffianChain.lean)
proves the *structural* identity `mP2PFL (cTD q) = polyDerivative (mP2PFL q)`
for y-free `q`. For chain-2 the y₁-leading coefficient is y₁-free but NOT
y₀-free, so that lemma does not apply. This eval-level version drops the
y-free hypothesis entirely (specialised to `IterExpChain`, whose relations
vanish under `mP2PFL`). -/
theorem multiPolyToPolyForLex_eval_chainTotalDeriv_IterExp {n : Nat}
    (q : MultiPoly n) (x : Real) :
    Poly.eval (multiPolyToPolyForLex
        (chainTotalDeriv (IterExpChain n) q)) x =
    Poly.eval (polyDerivative (multiPolyToPolyForLex q)) x := by
  induction q with
  | const c =>
    -- cTD (const c) = const 0; both sides eval to 0.
    rfl
  | varX =>
    -- cTD varX = const 1; mP2PFL varX = Poly.var; polyDerivative var = const 1.
    rfl
  | varY j =>
    -- cTD (varY j) = relations j = prodVarYUpTo j.val j.isLt (evals to 0);
    -- RHS = eval (polyDerivative (const 0)) = 0.
    show Poly.eval (multiPolyToPolyForLex
          (prodVarYUpTo j.val j.isLt : MultiPoly n)) x = 0
    exact eval_mP2PFL_prodVarYUpTo_eq_zero j.val j.isLt x
  | add p q ihp ihq =>
    show Poly.eval (multiPolyToPolyForLex
            (chainTotalDeriv (IterExpChain n) p)) x
         + Poly.eval (multiPolyToPolyForLex
            (chainTotalDeriv (IterExpChain n) q)) x
       = Poly.eval (polyDerivative (multiPolyToPolyForLex p)) x
         + Poly.eval (polyDerivative (multiPolyToPolyForLex q)) x
    rw [ihp, ihq]
  | sub p q ihp ihq =>
    show Poly.eval (multiPolyToPolyForLex
            (chainTotalDeriv (IterExpChain n) p)) x
         - Poly.eval (multiPolyToPolyForLex
            (chainTotalDeriv (IterExpChain n) q)) x
       = Poly.eval (polyDerivative (multiPolyToPolyForLex p)) x
         - Poly.eval (polyDerivative (multiPolyToPolyForLex q)) x
    rw [ihp, ihq]
  | mul p q ihp ihq =>
    -- Leibniz on both sides; cross terms match via IH (the unchanged
    -- factors mP2PFL p / mP2PFL q carry through identically).
    show Poly.eval (multiPolyToPolyForLex
            (chainTotalDeriv (IterExpChain n) p)) x
           * Poly.eval (multiPolyToPolyForLex q) x
         + Poly.eval (multiPolyToPolyForLex p) x
           * Poly.eval (multiPolyToPolyForLex
              (chainTotalDeriv (IterExpChain n) q)) x
       = Poly.eval (polyDerivative (multiPolyToPolyForLex p)) x
           * Poly.eval (multiPolyToPolyForLex q) x
         + Poly.eval (multiPolyToPolyForLex p) x
           * Poly.eval (polyDerivative (multiPolyToPolyForLex q)) x
    rw [ihp, ihq]

/-! ## Top chain-variable degree is preserved by chainTotalDeriv (chain-2)

Chain-2 analog of `degreeY_chainTotalDeriv_eq_SingleExp`. Needed so that
`leadingCoeffY ⟨1⟩` extracts the coefficient of the SAME y₁-power before and after
the derivative: the y₁-degree doesn't move, because `y₁' = y₀·y₁` keeps the y₁
power and only injects a y₀ factor. Purely structural (syntactic degree), so it
holds as an exact equality. -/
theorem degreeY1_chainTotalDeriv_eq_IterExp2 (p : MultiPoly 2) :
    MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)
      = MultiPoly.degreeY ⟨1, by omega⟩ p := by
  induction p with
  | const c => rfl
  | varX => rfl
  | varY j =>
    rcases j with ⟨v, hv⟩
    match v, hv with
    | 0, _ => rfl
    | 1, _ => rfl
  | add p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p))
                 (MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q))
       = Nat.max (MultiPoly.degreeY ⟨1, by omega⟩ p) (MultiPoly.degreeY ⟨1, by omega⟩ q)
    rw [ihp, ihq]
  | sub p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p))
                 (MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q))
       = Nat.max (MultiPoly.degreeY ⟨1, by omega⟩ p) (MultiPoly.degreeY ⟨1, by omega⟩ q)
    rw [ihp, ihq]
  | mul p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)
                  + MultiPoly.degreeY ⟨1, by omega⟩ q)
                 (MultiPoly.degreeY ⟨1, by omega⟩ p
                  + MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q))
       = MultiPoly.degreeY ⟨1, by omega⟩ p + MultiPoly.degreeY ⟨1, by omega⟩ q
    rw [ihp, ihq]; exact Nat.max_self _

/-! ## mP2PFL is evaluation at y = 0

`multiPolyToPolyForLex` replaces every `varY` with `Poly.const 0`, so evaluating
the projected Poly is the same as evaluating the original MultiPoly with all
chain variables set to 0. (Generalises `multiPolyToPolyForLex_eval_of_y_free`,
which needs y-freeness; here we pin the environment instead.) -/
theorem eval_multiPolyToPolyForLex_eq_eval_zero {n : Nat} (q : MultiPoly n)
    (x : Real) :
    Poly.eval (multiPolyToPolyForLex q) x = MultiPoly.eval q x (fun _ => 0) := by
  induction q with
  | const c => rfl
  | varX => rfl
  | varY j => rfl
  | add p q ihp ihq =>
    show Poly.eval (multiPolyToPolyForLex p) x + Poly.eval (multiPolyToPolyForLex q) x
       = MultiPoly.eval p x (fun _ => 0) + MultiPoly.eval q x (fun _ => 0)
    rw [ihp, ihq]
  | sub p q ihp ihq =>
    show Poly.eval (multiPolyToPolyForLex p) x - Poly.eval (multiPolyToPolyForLex q) x
       = MultiPoly.eval p x (fun _ => 0) - MultiPoly.eval q x (fun _ => 0)
    rw [ihp, ihq]
  | mul p q ihp ihq =>
    show Poly.eval (multiPolyToPolyForLex p) x * Poly.eval (multiPolyToPolyForLex q) x
       = MultiPoly.eval p x (fun _ => 0) * MultiPoly.eval q x (fun _ => 0)
    rw [ihp, ihq]

/-! ## leadingCoeffY ⟨1⟩ commutes with cTD at y₀ = 0 (chain-2)

Chain-2 analog of ChainExp2PathC's leadingCoeffY-under-cTD identity, SPECIALISED
to an environment with y₀ = 0. The general identity carries a `d·y₀·lcY₁` term
(because `y₁' = y₀·y₁`); at y₀ = 0 that term vanishes, collapsing every case to a
plain `rw [ihp, ihq]` — no `natCast`/ring `mul`-case algebra. The add/sub
trichotomy and the equal-degree mul distribution use
`degreeY1_chainTotalDeriv_eq_IterExp2` to align the `leadingCoeffY` if-conditions
across the derivative. -/
theorem lcY1_cTD_eval_zero_IterExp2 (p : MultiPoly 2) (x : Real)
    (env : Fin 2 → Real)
    (henv0 : MultiPoly.eval (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)) x env = 0) :
    MultiPoly.eval (MultiPoly.leadingCoeffY ⟨1, by omega⟩
        (chainTotalDeriv (IterExpChain 2) p)) x env
  = MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
        (MultiPoly.leadingCoeffY ⟨1, by omega⟩ p)) x env := by
  induction p with
  | const c => rfl
  | varX => rfl
  | varY j =>
    rcases j with ⟨v, hv⟩
    match v, hv with
    | 0, _ => rfl
    | 1, _ =>
      show MultiPoly.eval (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)) x env
           * MultiPoly.eval (MultiPoly.const (1 : Real)) x env = 0
      rw [henv0]; mach_ring
  | add p q ihp ihq =>
    have hp_eq := degreeY1_chainTotalDeriv_eq_IterExp2 p
    have hq_eq := degreeY1_chainTotalDeriv_eq_IterExp2 q
    by_cases hpq : MultiPoly.degreeY ⟨1, by omega⟩ p > MultiPoly.degreeY ⟨1, by omega⟩ q
    · have h_lhs : MultiPoly.leadingCoeffY ⟨1, by omega⟩
                    (chainTotalDeriv (IterExpChain 2) (MultiPoly.add p q))
                  = MultiPoly.leadingCoeffY ⟨1, by omega⟩
                      (chainTotalDeriv (IterExpChain 2) p) := by
        show (if MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)
                 > MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)
              then MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)
              else if MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)
                      > MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)
                   then MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)
                   else MultiPoly.add
                          (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p))
                          (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)))
              = MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)
        rw [hp_eq, hq_eq, if_pos hpq]
      have h_rhs : MultiPoly.leadingCoeffY ⟨1, by omega⟩ (MultiPoly.add p q)
                  = MultiPoly.leadingCoeffY ⟨1, by omega⟩ p := by
        show (if MultiPoly.degreeY ⟨1, by omega⟩ p > MultiPoly.degreeY ⟨1, by omega⟩ q
              then MultiPoly.leadingCoeffY ⟨1, by omega⟩ p
              else if MultiPoly.degreeY ⟨1, by omega⟩ q > MultiPoly.degreeY ⟨1, by omega⟩ p
                   then MultiPoly.leadingCoeffY ⟨1, by omega⟩ q
                   else MultiPoly.add (MultiPoly.leadingCoeffY ⟨1, by omega⟩ p)
                                      (MultiPoly.leadingCoeffY ⟨1, by omega⟩ q))
              = MultiPoly.leadingCoeffY ⟨1, by omega⟩ p
        rw [if_pos hpq]
      rw [h_lhs, h_rhs]; exact ihp
    · by_cases hqp : MultiPoly.degreeY ⟨1, by omega⟩ q > MultiPoly.degreeY ⟨1, by omega⟩ p
      · have h_first_neg : ¬ MultiPoly.degreeY ⟨1, by omega⟩ p
                             > MultiPoly.degreeY ⟨1, by omega⟩ q :=
          Nat.not_lt.mpr (Nat.le_of_lt hqp)
        have h_lhs : MultiPoly.leadingCoeffY ⟨1, by omega⟩
                      (chainTotalDeriv (IterExpChain 2) (MultiPoly.add p q))
                    = MultiPoly.leadingCoeffY ⟨1, by omega⟩
                        (chainTotalDeriv (IterExpChain 2) q) := by
          show (if MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)
                   > MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)
                then MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)
                else if MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)
                        > MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)
                     then MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)
                     else MultiPoly.add
                            (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p))
                            (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)))
                = MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)
          rw [hp_eq, hq_eq, if_neg h_first_neg, if_pos hqp]
        have h_rhs : MultiPoly.leadingCoeffY ⟨1, by omega⟩ (MultiPoly.add p q)
                    = MultiPoly.leadingCoeffY ⟨1, by omega⟩ q := by
          show (if MultiPoly.degreeY ⟨1, by omega⟩ p > MultiPoly.degreeY ⟨1, by omega⟩ q
                then MultiPoly.leadingCoeffY ⟨1, by omega⟩ p
                else if MultiPoly.degreeY ⟨1, by omega⟩ q > MultiPoly.degreeY ⟨1, by omega⟩ p
                     then MultiPoly.leadingCoeffY ⟨1, by omega⟩ q
                     else MultiPoly.add (MultiPoly.leadingCoeffY ⟨1, by omega⟩ p)
                                        (MultiPoly.leadingCoeffY ⟨1, by omega⟩ q))
                = MultiPoly.leadingCoeffY ⟨1, by omega⟩ q
          rw [if_neg h_first_neg, if_pos hqp]
        rw [h_lhs, h_rhs]; exact ihq
      · have hp_neg : ¬ MultiPoly.degreeY ⟨1, by omega⟩ p > MultiPoly.degreeY ⟨1, by omega⟩ q := hpq
        have hq_neg : ¬ MultiPoly.degreeY ⟨1, by omega⟩ q > MultiPoly.degreeY ⟨1, by omega⟩ p := hqp
        have h_lhs : MultiPoly.leadingCoeffY ⟨1, by omega⟩
                      (chainTotalDeriv (IterExpChain 2) (MultiPoly.add p q))
                    = MultiPoly.add
                        (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p))
                        (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)) := by
          show (if MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)
                   > MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)
                then MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)
                else if MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)
                        > MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)
                     then MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)
                     else MultiPoly.add
                            (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p))
                            (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)))
                = MultiPoly.add
                    (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p))
                    (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q))
          rw [hp_eq, hq_eq, if_neg hp_neg, if_neg hq_neg]
        have h_rhs : MultiPoly.leadingCoeffY ⟨1, by omega⟩ (MultiPoly.add p q)
                    = MultiPoly.add (MultiPoly.leadingCoeffY ⟨1, by omega⟩ p)
                                    (MultiPoly.leadingCoeffY ⟨1, by omega⟩ q) := by
          show (if MultiPoly.degreeY ⟨1, by omega⟩ p > MultiPoly.degreeY ⟨1, by omega⟩ q
                then MultiPoly.leadingCoeffY ⟨1, by omega⟩ p
                else if MultiPoly.degreeY ⟨1, by omega⟩ q > MultiPoly.degreeY ⟨1, by omega⟩ p
                     then MultiPoly.leadingCoeffY ⟨1, by omega⟩ q
                     else MultiPoly.add (MultiPoly.leadingCoeffY ⟨1, by omega⟩ p)
                                        (MultiPoly.leadingCoeffY ⟨1, by omega⟩ q))
                = MultiPoly.add (MultiPoly.leadingCoeffY ⟨1, by omega⟩ p)
                                (MultiPoly.leadingCoeffY ⟨1, by omega⟩ q)
          rw [if_neg hp_neg, if_neg hq_neg]
        rw [h_lhs, h_rhs]
        show MultiPoly.eval (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)) x env
             + MultiPoly.eval (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)) x env
           = MultiPoly.eval (chainTotalDeriv (IterExpChain 2) (MultiPoly.leadingCoeffY ⟨1, by omega⟩ p)) x env
             + MultiPoly.eval (chainTotalDeriv (IterExpChain 2) (MultiPoly.leadingCoeffY ⟨1, by omega⟩ q)) x env
        rw [ihp, ihq]
  | sub p q ihp ihq =>
    have hp_eq := degreeY1_chainTotalDeriv_eq_IterExp2 p
    have hq_eq := degreeY1_chainTotalDeriv_eq_IterExp2 q
    by_cases hpq : MultiPoly.degreeY ⟨1, by omega⟩ p > MultiPoly.degreeY ⟨1, by omega⟩ q
    · have h_lhs : MultiPoly.leadingCoeffY ⟨1, by omega⟩
                    (chainTotalDeriv (IterExpChain 2) (MultiPoly.sub p q))
                  = MultiPoly.leadingCoeffY ⟨1, by omega⟩
                      (chainTotalDeriv (IterExpChain 2) p) := by
        show (if MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)
                 > MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)
              then MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)
              else if MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)
                      > MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)
                   then MultiPoly.sub (MultiPoly.const 0)
                          (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q))
                   else MultiPoly.sub
                          (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p))
                          (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)))
              = MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)
        rw [hp_eq, hq_eq, if_pos hpq]
      have h_rhs : MultiPoly.leadingCoeffY ⟨1, by omega⟩ (MultiPoly.sub p q)
                  = MultiPoly.leadingCoeffY ⟨1, by omega⟩ p := by
        show (if MultiPoly.degreeY ⟨1, by omega⟩ p > MultiPoly.degreeY ⟨1, by omega⟩ q
              then MultiPoly.leadingCoeffY ⟨1, by omega⟩ p
              else if MultiPoly.degreeY ⟨1, by omega⟩ q > MultiPoly.degreeY ⟨1, by omega⟩ p
                   then MultiPoly.sub (MultiPoly.const 0) (MultiPoly.leadingCoeffY ⟨1, by omega⟩ q)
                   else MultiPoly.sub (MultiPoly.leadingCoeffY ⟨1, by omega⟩ p)
                                      (MultiPoly.leadingCoeffY ⟨1, by omega⟩ q))
              = MultiPoly.leadingCoeffY ⟨1, by omega⟩ p
        rw [if_pos hpq]
      rw [h_lhs, h_rhs]; exact ihp
    · by_cases hqp : MultiPoly.degreeY ⟨1, by omega⟩ q > MultiPoly.degreeY ⟨1, by omega⟩ p
      · have h_first_neg : ¬ MultiPoly.degreeY ⟨1, by omega⟩ p
                             > MultiPoly.degreeY ⟨1, by omega⟩ q :=
          Nat.not_lt.mpr (Nat.le_of_lt hqp)
        have h_lhs : MultiPoly.leadingCoeffY ⟨1, by omega⟩
                      (chainTotalDeriv (IterExpChain 2) (MultiPoly.sub p q))
                    = MultiPoly.sub (MultiPoly.const 0)
                        (MultiPoly.leadingCoeffY ⟨1, by omega⟩
                          (chainTotalDeriv (IterExpChain 2) q)) := by
          show (if MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)
                   > MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)
                then MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)
                else if MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)
                        > MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)
                     then MultiPoly.sub (MultiPoly.const 0)
                            (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q))
                     else MultiPoly.sub
                            (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p))
                            (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)))
                = MultiPoly.sub (MultiPoly.const 0)
                    (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q))
          rw [hp_eq, hq_eq, if_neg h_first_neg, if_pos hqp]
        have h_rhs : MultiPoly.leadingCoeffY ⟨1, by omega⟩ (MultiPoly.sub p q)
                    = MultiPoly.sub (MultiPoly.const 0) (MultiPoly.leadingCoeffY ⟨1, by omega⟩ q) := by
          show (if MultiPoly.degreeY ⟨1, by omega⟩ p > MultiPoly.degreeY ⟨1, by omega⟩ q
                then MultiPoly.leadingCoeffY ⟨1, by omega⟩ p
                else if MultiPoly.degreeY ⟨1, by omega⟩ q > MultiPoly.degreeY ⟨1, by omega⟩ p
                     then MultiPoly.sub (MultiPoly.const 0) (MultiPoly.leadingCoeffY ⟨1, by omega⟩ q)
                     else MultiPoly.sub (MultiPoly.leadingCoeffY ⟨1, by omega⟩ p)
                                        (MultiPoly.leadingCoeffY ⟨1, by omega⟩ q))
                = MultiPoly.sub (MultiPoly.const 0) (MultiPoly.leadingCoeffY ⟨1, by omega⟩ q)
          rw [if_neg h_first_neg, if_pos hqp]
        rw [h_lhs, h_rhs]
        show MultiPoly.eval (MultiPoly.const (0:Real)) x env
             - MultiPoly.eval (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)) x env
           = MultiPoly.eval (MultiPoly.const (0:Real)) x env
             - MultiPoly.eval (chainTotalDeriv (IterExpChain 2) (MultiPoly.leadingCoeffY ⟨1, by omega⟩ q)) x env
        rw [ihq]
      · have hp_neg : ¬ MultiPoly.degreeY ⟨1, by omega⟩ p > MultiPoly.degreeY ⟨1, by omega⟩ q := hpq
        have hq_neg : ¬ MultiPoly.degreeY ⟨1, by omega⟩ q > MultiPoly.degreeY ⟨1, by omega⟩ p := hqp
        have h_lhs : MultiPoly.leadingCoeffY ⟨1, by omega⟩
                      (chainTotalDeriv (IterExpChain 2) (MultiPoly.sub p q))
                    = MultiPoly.sub
                        (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p))
                        (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)) := by
          show (if MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)
                   > MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)
                then MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)
                else if MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)
                        > MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)
                     then MultiPoly.sub (MultiPoly.const 0)
                            (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q))
                     else MultiPoly.sub
                            (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p))
                            (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)))
                = MultiPoly.sub
                    (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p))
                    (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q))
          rw [hp_eq, hq_eq, if_neg hp_neg, if_neg hq_neg]
        have h_rhs : MultiPoly.leadingCoeffY ⟨1, by omega⟩ (MultiPoly.sub p q)
                    = MultiPoly.sub (MultiPoly.leadingCoeffY ⟨1, by omega⟩ p)
                                    (MultiPoly.leadingCoeffY ⟨1, by omega⟩ q) := by
          show (if MultiPoly.degreeY ⟨1, by omega⟩ p > MultiPoly.degreeY ⟨1, by omega⟩ q
                then MultiPoly.leadingCoeffY ⟨1, by omega⟩ p
                else if MultiPoly.degreeY ⟨1, by omega⟩ q > MultiPoly.degreeY ⟨1, by omega⟩ p
                     then MultiPoly.sub (MultiPoly.const 0) (MultiPoly.leadingCoeffY ⟨1, by omega⟩ q)
                     else MultiPoly.sub (MultiPoly.leadingCoeffY ⟨1, by omega⟩ p)
                                        (MultiPoly.leadingCoeffY ⟨1, by omega⟩ q))
                = MultiPoly.sub (MultiPoly.leadingCoeffY ⟨1, by omega⟩ p)
                                (MultiPoly.leadingCoeffY ⟨1, by omega⟩ q)
          rw [if_neg hp_neg, if_neg hq_neg]
        rw [h_lhs, h_rhs]
        show MultiPoly.eval (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)) x env
             - MultiPoly.eval (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)) x env
           = MultiPoly.eval (chainTotalDeriv (IterExpChain 2) (MultiPoly.leadingCoeffY ⟨1, by omega⟩ p)) x env
             - MultiPoly.eval (chainTotalDeriv (IterExpChain 2) (MultiPoly.leadingCoeffY ⟨1, by omega⟩ q)) x env
        rw [ihp, ihq]
  | mul p q ihp ihq =>
    have hp_eq := degreeY1_chainTotalDeriv_eq_IterExp2 p
    have hq_eq := degreeY1_chainTotalDeriv_eq_IterExp2 q
    have h_lhs : MultiPoly.leadingCoeffY ⟨1, by omega⟩
                  (chainTotalDeriv (IterExpChain 2) (MultiPoly.mul p q))
                = MultiPoly.add
                    (MultiPoly.mul (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p))
                                   (MultiPoly.leadingCoeffY ⟨1, by omega⟩ q))
                    (MultiPoly.mul (MultiPoly.leadingCoeffY ⟨1, by omega⟩ p)
                                   (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q))) := by
      show (if MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)
               + MultiPoly.degreeY ⟨1, by omega⟩ q
             > MultiPoly.degreeY ⟨1, by omega⟩ p
               + MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)
            then MultiPoly.mul (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p))
                               (MultiPoly.leadingCoeffY ⟨1, by omega⟩ q)
            else if MultiPoly.degreeY ⟨1, by omega⟩ p
                     + MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)
                   > MultiPoly.degreeY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)
                     + MultiPoly.degreeY ⟨1, by omega⟩ q
                 then MultiPoly.mul (MultiPoly.leadingCoeffY ⟨1, by omega⟩ p)
                                    (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q))
                 else MultiPoly.add
                        (MultiPoly.mul (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p))
                                       (MultiPoly.leadingCoeffY ⟨1, by omega⟩ q))
                        (MultiPoly.mul (MultiPoly.leadingCoeffY ⟨1, by omega⟩ p)
                                       (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q))))
            = MultiPoly.add
                (MultiPoly.mul (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p))
                               (MultiPoly.leadingCoeffY ⟨1, by omega⟩ q))
                (MultiPoly.mul (MultiPoly.leadingCoeffY ⟨1, by omega⟩ p)
                               (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)))
      rw [hp_eq, hq_eq, if_neg (Nat.lt_irrefl _), if_neg (Nat.lt_irrefl _)]
    have h_rhs_leading : MultiPoly.leadingCoeffY ⟨1, by omega⟩ (MultiPoly.mul p q)
                        = MultiPoly.mul (MultiPoly.leadingCoeffY ⟨1, by omega⟩ p)
                                        (MultiPoly.leadingCoeffY ⟨1, by omega⟩ q) := rfl
    rw [h_lhs, h_rhs_leading]
    show MultiPoly.eval (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) p)) x env
         * MultiPoly.eval (MultiPoly.leadingCoeffY ⟨1, by omega⟩ q) x env
       + MultiPoly.eval (MultiPoly.leadingCoeffY ⟨1, by omega⟩ p) x env
         * MultiPoly.eval (MultiPoly.leadingCoeffY ⟨1, by omega⟩ (chainTotalDeriv (IterExpChain 2) q)) x env
     = MultiPoly.eval (chainTotalDeriv (IterExpChain 2) (MultiPoly.leadingCoeffY ⟨1, by omega⟩ p)) x env
         * MultiPoly.eval (MultiPoly.leadingCoeffY ⟨1, by omega⟩ q) x env
       + MultiPoly.eval (MultiPoly.leadingCoeffY ⟨1, by omega⟩ p) x env
         * MultiPoly.eval (chainTotalDeriv (IterExpChain 2) (MultiPoly.leadingCoeffY ⟨1, by omega⟩ q)) x env
    rw [ihp, ihq]

/-! ## The descent eval-identity (chain-2, c = 0)

Combining the three pieces — `eval_multiPolyToPolyForLex_eq_eval_zero` (mP2PFL =
eval@0), `lcY1_cTD_eval_zero_IterExp2` (leadingCoeffY commutes with cTD at y₀=0),
and the cornerstone `multiPolyToPolyForLex_eval_chainTotalDeriv_IterExp` — gives
the identity the lex measure's second component needs:

  `mP2PFL(leadingCoeffY₁(cTD p))  ≡  polyDerivative(mP2PFL(leadingCoeffY₁ p))`  (at eval)

i.e. taking the y₁-leading coefficient of `cTD p`, then projecting y→0, is the
same (as a Poly, pointwise) as projecting the leading coefficient of `p` and then
taking the ordinary x-derivative. This is exactly the input the PolynomialCanonical
PIT bridge needs to lift to `polyCoeffs`/`polyTrueDegreeStrict` equality, after
which `polyTrueDegreeStrict_polyDerivativeCoeffs_lt` (Phase G) gives the strict
second-component descent for the `c = 0` ReduceStep. -/
theorem eval_mP2PFL_lcY1_chainTotalDeriv_IterExp2 (p : MultiPoly 2) (x : Real) :
    Poly.eval (multiPolyToPolyForLex (MultiPoly.leadingCoeffY ⟨1, by omega⟩
        (chainTotalDeriv (IterExpChain 2) p))) x
  = Poly.eval (polyDerivative (multiPolyToPolyForLex
        (MultiPoly.leadingCoeffY ⟨1, by omega⟩ p))) x := by
  rw [eval_multiPolyToPolyForLex_eq_eval_zero]
  rw [lcY1_cTD_eval_zero_IterExp2 p x (fun _ => 0) (by rfl)]
  rw [← eval_multiPolyToPolyForLex_eq_eval_zero]
  exact multiPolyToPolyForLex_eval_chainTotalDeriv_IterExp
    (MultiPoly.leadingCoeffY ⟨1, by omega⟩ p) x

/-! ## Lex second-component strict descent at c = 0 (chain-2)

Chain-2 analog of `singleExp_polyTrueDegreeStrict_scaledReduction_lt`, at the
`c = 0` scaledReduction. The descent eval-identity replaces single-exp's
two-step (lemma-2 + y-free structural) bridge with a single PIT step; the only
extra work is reducing the `sub (cTD p) (mul (const 0) p)` shape (the y₁-leading
coefficient distributes since both summands have equal y₁-degree, and the
`mul (const 0)` summand evaluates to 0). -/
open MachLib.PolynomialCanonical in
theorem chain2_polyTrueDegreeStrict_scaledReduction_zero_lt (p : MultiPoly 2)
    (h_strict_pos :
      polyTrueDegreeStrict
        (polyCoeffs (multiPolyToPolyForLex
          (MultiPoly.leadingCoeffY ⟨1, by omega⟩ p))) > 0) :
    polyTrueDegreeStrict
      (polyCoeffs (multiPolyToPolyForLex
        (MultiPoly.leadingCoeffY ⟨1, by omega⟩
          (MultiPoly.sub
            (chainTotalDeriv (IterExpChain 2) p)
            (MultiPoly.mul (MultiPoly.const (0 : Real)) p))))) <
    polyTrueDegreeStrict
      (polyCoeffs (multiPolyToPolyForLex
        (MultiPoly.leadingCoeffY ⟨1, by omega⟩ p))) := by
  let i : Fin 2 := ⟨1, by omega⟩
  let L_p := polyCoeffs (multiPolyToPolyForLex (MultiPoly.leadingCoeffY i p))
  have h_eq1 :
      polyTrueDegreeStrict
        (polyCoeffs (multiPolyToPolyForLex
          (MultiPoly.leadingCoeffY i
            (MultiPoly.sub
              (chainTotalDeriv (IterExpChain 2) p)
              (MultiPoly.mul (MultiPoly.const (0 : Real)) p))))) =
      polyTrueDegreeStrict
        (polyCoeffs (MachLib.PolynomialRootCount.polyDerivative
          (multiPolyToPolyForLex (MultiPoly.leadingCoeffY i p)))) := by
    apply polyTrueDegreeStrict_eq_of_evalCoeffs_eq
    intro x
    rw [polyCoeffs_eval, polyCoeffs_eval]
    have hA : MultiPoly.degreeY i (chainTotalDeriv (IterExpChain 2) p)
            = MultiPoly.degreeY i p := degreeY1_chainTotalDeriv_eq_IterExp2 p
    have hB : MultiPoly.degreeY i (MultiPoly.mul (MultiPoly.const (0 : Real)) p)
            = MultiPoly.degreeY i p := by
      show 0 + MultiPoly.degreeY i p = MultiPoly.degreeY i p
      omega
    have h_notAB : ¬ MultiPoly.degreeY i (chainTotalDeriv (IterExpChain 2) p)
                     > MultiPoly.degreeY i (MultiPoly.mul (MultiPoly.const (0 : Real)) p) := by
      rw [hA, hB]; exact Nat.lt_irrefl _
    have h_notBA : ¬ MultiPoly.degreeY i (MultiPoly.mul (MultiPoly.const (0 : Real)) p)
                     > MultiPoly.degreeY i (chainTotalDeriv (IterExpChain 2) p) := by
      rw [hA, hB]; exact Nat.lt_irrefl _
    have h_lcY_sub :
        MultiPoly.leadingCoeffY i
          (MultiPoly.sub (chainTotalDeriv (IterExpChain 2) p)
                         (MultiPoly.mul (MultiPoly.const (0 : Real)) p))
        = MultiPoly.sub
            (MultiPoly.leadingCoeffY i (chainTotalDeriv (IterExpChain 2) p))
            (MultiPoly.leadingCoeffY i (MultiPoly.mul (MultiPoly.const (0 : Real)) p)) := by
      show (if MultiPoly.degreeY i (chainTotalDeriv (IterExpChain 2) p)
               > MultiPoly.degreeY i (MultiPoly.mul (MultiPoly.const (0 : Real)) p)
            then MultiPoly.leadingCoeffY i (chainTotalDeriv (IterExpChain 2) p)
            else if MultiPoly.degreeY i (MultiPoly.mul (MultiPoly.const (0 : Real)) p)
                    > MultiPoly.degreeY i (chainTotalDeriv (IterExpChain 2) p)
                 then MultiPoly.sub (MultiPoly.const 0)
                        (MultiPoly.leadingCoeffY i (MultiPoly.mul (MultiPoly.const (0 : Real)) p))
                 else MultiPoly.sub
                        (MultiPoly.leadingCoeffY i (chainTotalDeriv (IterExpChain 2) p))
                        (MultiPoly.leadingCoeffY i (MultiPoly.mul (MultiPoly.const (0 : Real)) p)))
          = MultiPoly.sub
              (MultiPoly.leadingCoeffY i (chainTotalDeriv (IterExpChain 2) p))
              (MultiPoly.leadingCoeffY i (MultiPoly.mul (MultiPoly.const (0 : Real)) p))
      rw [if_neg h_notAB, if_neg h_notBA]
    rw [h_lcY_sub]
    show Poly.eval (multiPolyToPolyForLex
            (MultiPoly.leadingCoeffY i (chainTotalDeriv (IterExpChain 2) p))) x
         - Poly.eval (multiPolyToPolyForLex
            (MultiPoly.leadingCoeffY i (MultiPoly.mul (MultiPoly.const (0 : Real)) p))) x
       = Poly.eval (MachLib.PolynomialRootCount.polyDerivative
            (multiPolyToPolyForLex (MultiPoly.leadingCoeffY i p))) x
    have hzero : Poly.eval (multiPolyToPolyForLex
            (MultiPoly.leadingCoeffY i (MultiPoly.mul (MultiPoly.const (0 : Real)) p))) x = 0 := by
      show (0 : Real)
           * Poly.eval (multiPolyToPolyForLex (MultiPoly.leadingCoeffY i p)) x = 0
      mach_ring
    rw [hzero]
    have hsub0 : Poly.eval (multiPolyToPolyForLex
            (MultiPoly.leadingCoeffY i (chainTotalDeriv (IterExpChain 2) p))) x - 0
       = Poly.eval (multiPolyToPolyForLex
            (MultiPoly.leadingCoeffY i (chainTotalDeriv (IterExpChain 2) p))) x := by mach_ring
    rw [hsub0]
    exact eval_mP2PFL_lcY1_chainTotalDeriv_IterExp2 p x
  have h_eq3 :
      polyTrueDegreeStrict
        (polyCoeffs (MachLib.PolynomialRootCount.polyDerivative
          (multiPolyToPolyForLex (MultiPoly.leadingCoeffY i p)))) =
      polyTrueDegreeStrict (polyDerivativeCoeffs L_p) :=
    polyTrueDegreeStrict_polyDerivative_eq_polyDerivativeCoeffs
      (multiPolyToPolyForLex (MultiPoly.leadingCoeffY i p))
  have h_lt :
      polyTrueDegreeStrict (polyDerivativeCoeffs L_p) <
      polyTrueDegreeStrict L_p :=
    polyTrueDegreeStrict_polyDerivativeCoeffs_lt L_p h_strict_pos
  calc polyTrueDegreeStrict
          (polyCoeffs (multiPolyToPolyForLex
            (MultiPoly.leadingCoeffY i
              (MultiPoly.sub
                (chainTotalDeriv (IterExpChain 2) p)
                (MultiPoly.mul (MultiPoly.const (0 : Real)) p)))))
      = polyTrueDegreeStrict
          (polyCoeffs (MachLib.PolynomialRootCount.polyDerivative
            (multiPolyToPolyForLex (MultiPoly.leadingCoeffY i p)))) := h_eq1
    _ = polyTrueDegreeStrict (polyDerivativeCoeffs L_p) := h_eq3
    _ < polyTrueDegreeStrict L_p := h_lt

end ChainExp2SDR
end MachLib
