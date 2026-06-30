import MachLib.ChainExp2Reducer
import MachLib.MultiPolyReconstruct

/-!
# Path B — the chain-2 *trim* arm of the reduce dispatch

The chain-2 reducer (like the closed single-exp one, `ChainExp2PathC.singleExp_dispatch_step`) must
**dispatch** between two `Chain2ReduceStep` producers when `degreeY₁ p > 0`:

* the **reduce** arm — when `lcY₁ p` is *not* canonically zero — which must strictly decrease the *inner*
  second component of `chain2Measure`. That arm is the open research seam: the c=0 chain total derivative
  provably *fails* (`ChainExp2Reducer.chain2_reducePoly_not_nestedLT` — it injects a `y₀` factor into
  `lcY₁`, raising `degreeY₀`), so it needs a genuinely new sound reduce operator.
* the **trim** arm — when `lcY₁ p` *is* canonically zero (a phantom `y₁`-leading term that evaluates to 0
  at every chain point) — which drops that dead term, strictly lowering `degreeY₁` (the *first* component
  of `chain2Measure`). This file builds that arm.

The single-exp trim (`singleExp_canonicalTrim_step`) is `MultiPoly 1`-only because its `dropLeadingY` +
two lemmas are pinned to `Fin 1`. But the underlying primitives (`reconstructY`, `yCoeffsAt`,
`degreeY_reconstructY_lt`, `yCoeffsAt_*`, `listEvalAuxN_dropLast_eq_of_last_eval_zero`) are all `{n}`-
generic. So here we (1) lift `dropLeadingY` and its two lemmas to a generic `dropLeadingYAt {n} (i)`
(verbatim ports — only the index changes), then (2) instantiate at `⟨1⟩ : Fin 2` to produce a sound
chain-2 `Chain2ReduceStep` (descent in the first component, witnessed by `IsKhovanskiiReducible.trim`).

This closes one of the two dispatch arms. It does **not** close chain-2 — the reduce arm (the crux) is
still open. The single-exp framework is untouched (new file; Path B).
-/

namespace MachLib.ChainExp2Trim

open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.MultiPolyReconstruct
open MachLib.PfaffianChainMod
open MachLib.ChainExp2Reducer

/-! ## Generic `dropLeadingYAt` — the index-parametrised trim (lifts `dropLeadingY` off `Fin 1`) -/

/-- The trim operation at chain variable `y_i`: round-trip through `yCoeffsAt`, drop the (dead) leading
coefficient, reconstruct. Generic over `n`/`i` — `dropLeadingY` is the `n = 1, i = 0` instance. -/
noncomputable def dropLeadingYAt {n : Nat} (i : Fin n) (p : MultiPoly n) : MultiPoly n :=
  reconstructY i (yCoeffsAt i p).dropLast 0

/-- **Formal `degreeY i` strictly decreases** under `dropLeadingYAt i` when `degreeY i p > 0`. Verbatim
port of `degreeY_dropLeadingY_lt` with the index generic. -/
theorem degreeY_dropLeadingYAt_lt {n : Nat} (i : Fin n) (p : MultiPoly n)
    (h_pos : MultiPoly.degreeY i p > 0) :
    MultiPoly.degreeY i (dropLeadingYAt i p) < MultiPoly.degreeY i p := by
  by_cases h_drop_empty : (yCoeffsAt i p).dropLast = []
  · unfold dropLeadingYAt
    rw [h_drop_empty, reconstructY_nil]
    show (0 : Nat) < MultiPoly.degreeY i p
    exact h_pos
  · have h_yCoeffsAt_free :
        ∀ c ∈ yCoeffsAt i p, MultiPoly.degreeY i c = 0 :=
      yCoeffsAt_entries_degreeY_zero _ p
    have h_dropLast_free :
        ∀ c ∈ (yCoeffsAt i p).dropLast, MultiPoly.degreeY i c = 0 := fun c hc =>
      h_yCoeffsAt_free c (List.dropLast_subset _ hc)
    have h_lt := degreeY_reconstructY_lt i (yCoeffsAt i p).dropLast h_drop_empty h_dropLast_free 0
    rw [Nat.zero_add] at h_lt
    have h_drop_le :
        (yCoeffsAt i p).dropLast.length ≤ MultiPoly.degreeY i p := by
      rw [List.length_dropLast]
      have h_le := yCoeffsAt_length_le i p
      omega
    exact Nat.lt_of_lt_of_le h_lt h_drop_le

open MachLib.PolynomialCanonical in
/-- **Eval preservation** for `dropLeadingYAt i` when the last `yCoeffsAt i` entry is canonically zero at
every point. Verbatim port of `eval_dropLeadingY_of_last_canonically_zero` with the index generic. -/
theorem eval_dropLeadingYAt_of_last_canonically_zero {n : Nat} (i : Fin n) (p : MultiPoly n)
    (h_ne : yCoeffsAt i p ≠ [])
    (h_canonical_zero : ∀ x env,
      MultiPoly.eval ((yCoeffsAt i p).getLast h_ne) x env = 0)
    (x : Real) (env : Fin n → Real) :
    MultiPoly.eval (dropLeadingYAt i p) x env = MultiPoly.eval p x env := by
  unfold dropLeadingYAt
  rw [eval_reconstructY]
  rw [← eval_yCoeffsAt i p x env]
  rw [show listEvalN i (yCoeffsAt i p) x env =
          listEvalAuxN i (yCoeffsAt i p) 0 x env from rfl]
  exact listEvalAuxN_dropLast_eq_of_last_eval_zero
    i (yCoeffsAt i p) h_ne x env (h_canonical_zero x env) 0

/-! ## The chain-2 trim `Chain2ReduceStep` (canonical form `⟨2, chain, p⟩`) -/

/-- **The chain-2 canonical-trim step.** When `degreeY₁ p > 0` and the `y₁`-leading coefficient (last
entry of `yCoeffsAt ⟨1⟩ p`) is canonically zero at every chain point, `dropLeadingYAt ⟨1⟩ p` is
eval-equivalent to `p` with strictly smaller `degreeY₁`. This yields a `Chain2ReduceStep` whose
`lex_decrease` is the *first*-component drop of `chain2Measure` (`Or.inl`), witnessed by the `trim`
constructor of `IsKhovanskiiReducible`. Mirrors `singleExp_canonicalTrim_step`, lifted to chain-2. -/
noncomputable def chain2_canonicalTrim_step (chain : PfaffianChain 2) (p : MultiPoly 2)
    (h_pos : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p > 0)
    (h_canonical_zero :
      ∀ (h_ne : yCoeffsAt (⟨1, by omega⟩ : Fin 2) p ≠ [])
        (x : Real) (env : Fin 2 → Real),
        MultiPoly.eval
          ((yCoeffsAt (⟨1, by omega⟩ : Fin 2) p).getLast h_ne) x env = 0) :
    Chain2ReduceStep (⟨2, chain, p⟩ : PfaffianFn) rfl where
  result := ⟨2, chain, dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p⟩
  result_hn := rfl
  counter := 0
  lex_decrease := by
    -- First lex component (degreeY₁) strictly drops.
    refine Or.inl ?_
    show MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
            (dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p) <
         MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p
    exact degreeY_dropLeadingYAt_lt (⟨1, by omega⟩ : Fin 2) p h_pos
  witness := by
    have h_ne : yCoeffsAt (⟨1, by omega⟩ : Fin 2) p ≠ [] :=
      yCoeffsAt_nonempty _ p
    refine PfaffianFn.IsKhovanskiiReducible.trim
      (⟨2, chain, p⟩ : PfaffianFn)
      (⟨2, chain, dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p⟩ : PfaffianFn)
      (dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p) 0 ?_ ?_
    · -- h_eval: f.eval x = trimmed.eval x for every x.
      intro x
      show MultiPoly.eval p x
            ((⟨2, chain, p⟩ : PfaffianFn).chain.chainValues x) =
           MultiPoly.eval (dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p) x
            ((PfaffianFn.mk (⟨2, chain, p⟩ : PfaffianFn).n
                (⟨2, chain, p⟩ : PfaffianFn).chain
                (dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p)).chain.chainValues x)
      have h_canon := h_canonical_zero h_ne
      rw [eval_dropLeadingYAt_of_last_canonically_zero
            (⟨1, by omega⟩ : Fin 2) p h_ne h_canon x _]
    · exact PfaffianFn.IsKhovanskiiReducible.refl _

end MachLib.ChainExp2Trim
