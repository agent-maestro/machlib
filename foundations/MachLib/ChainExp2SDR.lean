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

end ChainExp2SDR
end MachLib
