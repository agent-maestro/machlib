import MachLib.IterExpDepthNEstablishHnz
import MachLib.ChainExp2ExplicitTrim
import MachLib.MultiPolyLiftLastY

/-!
# Depth-N `degreeX` non-increase tower (the B-bound side of the chain-N explicit bound)

Step 2 of the chain-N explicit-bound build (`monogate-research/roadmap/chainN-explicit-bound-design.md`),
B-bound half. The explicit bound needs `degreeX` to be non-increasing along the M5⁺ recursion so that a
single global `B := degreeX p₀ + 2` bounds the innermost measure component at every level (exactly as
chain-2's `B` did). Depth-N had **no** `degreeX` lemma for any of its operations; this file supplies them.

The crux — does the depth-N chain total derivative raise `degreeX`? — is already answered: the
chain-generic `PfaffianFn.degreeX_chainTotalDeriv_le` proves `chainTotalDeriv` never raises `degreeX`
for any chain whose relations are x-free, and `IterExpChain (M+2)`'s relations are x-free products of
`y`-variables (`degreeX_prodVarYUpTo_zero`). So `degreeX_chainNReduce_le` is a verbatim mirror of the
proven `degreeX_chain2Reduce_le`, once the multiplier `fullMult` is shown x-free.

  * `degreeX_liftLastY`  (= degreeX)   — AST-preserving lift.
  * `degreeX_dropLastY`  (= degreeX)   — variable-drop preserves degreeX.
  * `degreeX_gradedTop`  (= 0)         — graded multiplier is x-free (`Ffac` is a y-product).
  * `degreeX_fullMult`   (= 0)         — the reduce multiplier is x-free (induction on depth).
  * `degreeX_chainNReduce_le` / `_fullMult_le` — reduce is degreeX-non-increasing.
  * `degreeX_liftInner_le` (≤ max)     — inner-lift is degreeX-non-increasing (given the inner is).
  * trim: `degreeX_dropLeadingYAt_le` is already chain-generic — reused at the top index, no new proof.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.IterExpTopIdentity
open MachLib.IterExpDepthNReduce
open MachLib.ChainExp2Explicit
open MachLib.ChainExp2Trim
open MachLib.ChainExp2CanonMeasure
open MachLib.MultiPolyReconstruct

/-- `liftLastY` preserves `degreeX` — it maps each AST node to a same-`degreeX` node. -/
theorem degreeX_liftLastY {n : Nat} : ∀ (p : MultiPoly n),
    MultiPoly.degreeX (MultiPoly.liftLastY p) = MultiPoly.degreeX p
  | .const _ => rfl
  | .varX => rfl
  | .varY _ => rfl
  | .add p q => by
      show Nat.max (MultiPoly.degreeX (MultiPoly.liftLastY p)) (MultiPoly.degreeX (MultiPoly.liftLastY q))
          = Nat.max (MultiPoly.degreeX p) (MultiPoly.degreeX q)
      rw [degreeX_liftLastY p, degreeX_liftLastY q]
  | .sub p q => by
      show Nat.max (MultiPoly.degreeX (MultiPoly.liftLastY p)) (MultiPoly.degreeX (MultiPoly.liftLastY q))
          = Nat.max (MultiPoly.degreeX p) (MultiPoly.degreeX q)
      rw [degreeX_liftLastY p, degreeX_liftLastY q]
  | .mul p q => by
      show MultiPoly.degreeX (MultiPoly.liftLastY p) + MultiPoly.degreeX (MultiPoly.liftLastY q)
          = MultiPoly.degreeX p + MultiPoly.degreeX q
      rw [degreeX_liftLastY p, degreeX_liftLastY q]

/-- `dropLastY` preserves `degreeX` — dropping the last y-variable maps `varY` to `varY` or `const 0`,
both `degreeX 0`, and is homomorphic elsewhere. -/
theorem degreeX_dropLastY {n : Nat} : ∀ (p : MultiPoly (n + 1)),
    MultiPoly.degreeX (MultiPoly.dropLastY p) = MultiPoly.degreeX p
  | .const _ => rfl
  | .varX => rfl
  | .varY i => by
      show MultiPoly.degreeX (if h : i.val < n then MultiPoly.varY ⟨i.val, h⟩ else MultiPoly.const 0)
          = MultiPoly.degreeX (MultiPoly.varY i)
      by_cases h : i.val < n
      · rw [dif_pos h]; rfl
      · rw [dif_neg h]; rfl
  | .add p q => by
      show Nat.max (MultiPoly.degreeX (MultiPoly.dropLastY p)) (MultiPoly.degreeX (MultiPoly.dropLastY q))
          = Nat.max (MultiPoly.degreeX p) (MultiPoly.degreeX q)
      rw [degreeX_dropLastY p, degreeX_dropLastY q]
  | .sub p q => by
      show Nat.max (MultiPoly.degreeX (MultiPoly.dropLastY p)) (MultiPoly.degreeX (MultiPoly.dropLastY q))
          = Nat.max (MultiPoly.degreeX p) (MultiPoly.degreeX q)
      rw [degreeX_dropLastY p, degreeX_dropLastY q]
  | .mul p q => by
      show MultiPoly.degreeX (MultiPoly.dropLastY p) + MultiPoly.degreeX (MultiPoly.dropLastY q)
          = MultiPoly.degreeX p + MultiPoly.degreeX q
      rw [degreeX_dropLastY p, degreeX_dropLastY q]

/-- `Ffac M` is x-free (it is the y-product `prodVarYUpTo M`). -/
theorem degreeX_Ffac (M : Nat) : MultiPoly.degreeX (Ffac M) = 0 :=
  degreeX_prodVarYUpTo_zero M (by omega)

/-- The graded multiplier `gradedTop M i p = const(·) · Ffac M` is x-free. -/
theorem degreeX_gradedTop (M : Nat) (i : Fin (M + 2)) (p : MultiPoly (M + 2)) :
    MultiPoly.degreeX (gradedTop M i p) = 0 := by
  show MultiPoly.degreeX (MultiPoly.const (MachLib.Real.natCast (MultiPoly.degreeY i p)))
      + MultiPoly.degreeX (Ffac M) = 0
  rw [degreeX_const, degreeX_Ffac]

/-- **The reduce multiplier is x-free.** `degreeX (fullMult k q) = 0` for every depth `k`: at each level
`fullMult` adds a graded top term (x-free) to the `liftLastY` of the lower-level multiplier (x-free by
induction). This is what chain-2 got for free from its literal `(degreeY₁ p)·y₀ + c` multiplier. -/
theorem degreeX_fullMult : ∀ (k : Nat) (q : MultiPoly (k + 2)),
    MultiPoly.degreeX (fullMult k q) = 0
  | 0, q => by
      show Nat.max (MultiPoly.degreeX (gradedTop 0 (⟨1, by omega⟩ : Fin 2) q))
          (MultiPoly.degreeX (MultiPoly.const (MachLib.Real.natCast
            (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q))))) = 0
      rw [degreeX_gradedTop, degreeX_const]; decide
  | k + 1, q => by
      show Nat.max (MultiPoly.degreeX (gradedTop (k + 1) (⟨k + 2, by omega⟩ : Fin (k + 3)) q))
          (MultiPoly.degreeX (MultiPoly.liftLastY (fullMult k (MultiPoly.dropLastY
            (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))))) = 0
      rw [degreeX_gradedTop, degreeX_liftLastY,
        degreeX_fullMult k (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))]
      decide

/-- **Reduce is `degreeX`-non-increasing** (verbatim mirror of `degreeX_chain2Reduce_le`). Given an
x-free multiplier `m`, `chainNReduce M m p = cTD(p) − m·p` cannot raise `degreeX`: the cTD term by the
chain-generic `degreeX_chainTotalDeriv_le` (relations are x-free), the product term because `degreeX m = 0`. -/
theorem degreeX_chainNReduce_le (M : Nat) (m p : MultiPoly (M + 2)) (hm : MultiPoly.degreeX m = 0) :
    MultiPoly.degreeX (chainNReduce M m p) ≤ MultiPoly.degreeX p := by
  have h_rel_x : ∀ j : Fin (M + 2), MultiPoly.degreeX ((IterExpChain (M + 2)).relations j) = 0 :=
    fun j => degreeX_prodVarYUpTo_zero j.val j.isLt
  unfold chainNReduce
  refine Nat.max_le.mpr ⟨degreeX_chainTotalDeriv_le (IterExpChain (M + 2)) h_rel_x p, ?_⟩
  show MultiPoly.degreeX m + MultiPoly.degreeX p ≤ MultiPoly.degreeX p
  rw [hm]; omega

/-- The actual reduce used in the M5⁺ recursion (multiplier `fullMult M p`) is `degreeX`-non-increasing. -/
theorem degreeX_chainNReduce_fullMult_le (M : Nat) (p : MultiPoly (M + 2)) :
    MultiPoly.degreeX (chainNReduce M (fullMult M p) p) ≤ MultiPoly.degreeX p :=
  degreeX_chainNReduce_le M (fullMult M p) p (degreeX_fullMult M p)

/-- **Inner-lift is `degreeX`-non-increasing** (given the inner is). `liftInner k c inner'` reconstructs
from `(yCoeffsAt c).dropLast` (each entry `≤ degreeX c`) plus `liftLastY inner'` (`degreeX inner'`), so
its `degreeX ≤ max (degreeX c) (degreeX inner')`. -/
theorem degreeX_liftInner_le (k : Nat) (c : MultiPoly (k + 3)) (inner' : MultiPoly (k + 2)) :
    MultiPoly.degreeX (liftInner k c inner')
      ≤ Nat.max (MultiPoly.degreeX c) (MultiPoly.degreeX inner') := by
  unfold liftInner
  apply degreeX_reconstructY_le
  intro c' hc'
  rw [List.mem_append] at hc'
  rcases hc' with h | h
  · exact Nat.le_trans
      (yCoeffsAt_entries_degreeX_le _ c c' (List.dropLast_subset _ h))
      (Nat.le_max_left _ _)
  · rw [List.mem_singleton] at h
    rw [h, degreeX_liftLastY]
    exact Nat.le_max_right _ _

end MachLib.IterExpDepthN
