import MachLib.IterExpDepth3Bridge
import MachLib.ChainExp2Bound

/-!
# Depth-3 → depth-2: the recursion closes through the bridge

Combines everything: the depth-3 reduce's leading coefficient, projected via `dropLastY`, is
eval-equal to an honest DEPTH-2 reduce of the projected leading coefficient — on `IterExpChain 2`.

  `eval (dropLastY (lcY₂ (chain3Reduce c p))) [IterExpChain 2]
     = eval (chain2Reduce c (dropLastY (lcY₂ p))) [IterExpChain 2]`.

Chains: `chain3Reduce_lcY2_eval` (cancellation, lemma 1) → the bridge eval-preservation → the `cTD`
commutation → `degreeY₁` preservation → the depth-2 reduce eval-identity. This is the concrete
realization of "the depth-3 recursion closes to depth 2," fully wired through the `MP3→MP2` bridge.

REMAINING for the WF descent (the next phase): `chain2MeasureCanon` is NOT eval-invariant (its first
component is *syntactic* `degreeY₁`), so this eval-equality does not yet yield
`chain2MeasureCanon`-descent. That needs a fully eval-invariant depth-2 measure — a canonical
`y₁`-degree `cdegY1` (the `y₁`-analog of the depth-2 `cdegY0`), which is a fresh sub-arc. Path B; no `sorry`.
-/

namespace MachLib.IterExpDepth3MeasureDescent

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.IterExpTopIdentity
open MachLib.IterExpDepth3Descent
open MachLib.IterExpDepth3Bridge
open MachLib.ChainExp2Reducer
open MachLib.ChainExp2Bound

/-- **First component preserved.** `degreeY₂` (the top, syntactic, trim-handled component of the
depth-3 measure) is unchanged by `chain3Reduce`: `cTD` preserves it and the multiplier is `y₂`-free. -/
theorem chain3Reduce_fst_preserved (c : Real) (p : MultiPoly 3) :
    MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (chain3Reduce c p)
      = MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p := by
  show Nat.max (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (chainTotalDeriv (IterExpChain 3) p))
               (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (mult3 c p)
                + MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)
     = MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p
  rw [degreeY2_cTD_eq_IterExp3, degreeY2_mult3 c p, Nat.zero_add]
  exact Nat.max_self _

/-- **The recursion closes through the bridge.** `dropLastY (lcY₂ (chain3Reduce c p))` is eval-equal
to `chain2Reduce c (dropLastY (lcY₂ p))` on `IterExpChain 2`. The depth-3 reduce's dropped leading
coefficient IS a depth-2 reduce. -/
theorem chain3Reduce_dropLastY_lcY2_eval_eq (c : Real) (p : MultiPoly 3) (z : Real) :
    MultiPoly.eval (MultiPoly.dropLastY
        (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) (chain3Reduce c p))) z
        ((IterExpChain 2).chainValues z)
    = MultiPoly.eval (chain2Reduce c (MultiPoly.dropLastY
        (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p))) z ((IterExpChain 2).chainValues z) := by
  have hf_red : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3)
      (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) (chain3Reduce c p)) = 0 :=
    MultiPoly.degreeY_leadingCoeffY _ _
  have hf_p : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3)
      (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p) = 0 :=
    MultiPoly.degreeY_leadingCoeffY _ _
  have hf_cTD : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3)
      (chainTotalDeriv (IterExpChain 3) (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)) = 0 := by
    rw [degreeY2_cTD_eq_IterExp3]; exact hf_p
  have hY0 : MultiPoly.eval (MultiPoly.varY (⟨0, by omega⟩ : Fin 3)) z ((IterExpChain 3).chainValues z)
      = Real.exp z := rfl
  -- RHS via the depth-2 reduce eval-identity (chain2Fn wrapper is defeq to eval on the chain).
  have hRHS : MultiPoly.eval (chain2Reduce c (MultiPoly.dropLastY
        (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p))) z ((IterExpChain 2).chainValues z)
      = MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
          (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p))) z
          ((IterExpChain 2).chainValues z)
        - (MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
            (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p))) * Real.exp z + c)
          * MultiPoly.eval (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)) z
              ((IterExpChain 2).chainValues z) :=
    chain2Fn_chain2Reduce_eval c
      (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)) z
  rw [← dropLastY_eval_IterExp3 _ hf_red z,
      chain3Reduce_lcY2_eval c p z ((IterExpChain 3).chainValues z),
      hY0,
      dropLastY_eval_IterExp3 _ hf_cTD z,
      dropLastY_cTD_commute _ hf_p,
      dropLastY_eval_IterExp3 _ hf_p z,
      hRHS,
      degreeY1_dropLastY]

/-- **Full-env eval-equality** (the version the measure descent needs — the chain-values version above is
insufficient because `chain2MeasureCanonEvalInv`'s eval-invariance quantifies over ALL environments).
Proven via the framework `MultiPoly.eval_dropLastY` (full-env, env-restricted) rather than the
chain-specific `dropLastY_eval_IterExp3`. -/
theorem chain3Reduce_dropLastY_lcY2_eval_eq_full (c : Real) (p : MultiPoly 3)
    (z : Real) (env : Fin 2 → Real) :
    MultiPoly.eval (MultiPoly.dropLastY
        (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) (chain3Reduce c p))) z env
    = MultiPoly.eval (chain2Reduce c (MultiPoly.dropLastY
        (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p))) z env := by
  have hf_red : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3)
      (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) (chain3Reduce c p)) = 0 :=
    MultiPoly.degreeY_leadingCoeffY _ _
  have hf_p : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3)
      (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p) = 0 :=
    MultiPoly.degreeY_leadingCoeffY _ _
  have hf_cTD : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3)
      (chainTotalDeriv (IterExpChain 3) (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)) = 0 := by
    rw [degreeY2_cTD_eq_IterExp3]; exact hf_p
  have hrestrict : (fun i : Fin 2 =>
      (fun j : Fin 3 => if h : j.val < 2 then env ⟨j.val, h⟩ else 0) ⟨i.val, by omega⟩) = env := by
    funext i
    show (if h : i.val < 2 then env ⟨i.val, h⟩ else 0) = env i
    rw [dif_pos i.isLt]
  have hbridge : ∀ (X : MultiPoly 3), MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) X = 0 →
      MultiPoly.eval (MultiPoly.dropLastY X) z env
        = MultiPoly.eval X z (fun j : Fin 3 => if h : j.val < 2 then env ⟨j.val, h⟩ else 0) := by
    intro X hX
    have hev := MultiPoly.eval_dropLastY X hX z
      (fun j : Fin 3 => if h : j.val < 2 then env ⟨j.val, h⟩ else 0)
    rwa [hrestrict] at hev
  have hcTD_conn : MultiPoly.eval (chainTotalDeriv (IterExpChain 3)
        (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)) z
        (fun j : Fin 3 => if h : j.val < 2 then env ⟨j.val, h⟩ else 0)
      = MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
          (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p))) z env := by
    rw [← hbridge _ hf_cTD, dropLastY_cTD_commute _ hf_p]
  have hY0_conn : MultiPoly.eval (MultiPoly.varY (⟨0, by omega⟩ : Fin 3)) z
        (fun j : Fin 3 => if h : j.val < 2 then env ⟨j.val, h⟩ else 0)
      = MultiPoly.eval (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)) z env := by
    show (if h : (0 : Nat) < 2 then env ⟨0, h⟩ else 0) = env (⟨0, by omega⟩ : Fin 2)
    rw [dif_pos (by omega)]
  rw [hbridge _ hf_red,
      chain3Reduce_lcY2_eval c p z (fun j : Fin 3 => if h : j.val < 2 then env ⟨j.val, h⟩ else 0),
      hcTD_conn, hY0_conn, (hbridge _ hf_p).symm, ← degreeY1_dropLastY,
      show MultiPoly.eval (chain2Reduce c (MultiPoly.dropLastY
            (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p))) z env
         = MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
             (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p))) z env
           - (MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
               (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)))
              * MultiPoly.eval (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)) z env + c)
             * MultiPoly.eval (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)) z env
         from by
           show MultiPoly.eval (MultiPoly.sub _ _) z env = _
           rw [MultiPoly.eval_sub, MultiPoly.eval_mul, MultiPoly.eval_add, MultiPoly.eval_mul,
               MultiPoly.eval_const, MultiPoly.eval_const]]

end MachLib.IterExpDepth3MeasureDescent
