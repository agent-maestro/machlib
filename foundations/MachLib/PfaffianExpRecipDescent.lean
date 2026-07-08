import MachLib.PfaffianRecipStep
import MachLib.PfaffianExpRecipClassW

/-!
# Combined extended descent — Brick A-4b (reciprocal half)

The depth descent for `IsExpOrRecipW` chains (`sin_not_in_eml_any_depth`
retirement, full route). It strips the top level and dispatches on
`IsExpOrRecipW_top`:
- **reciprocal top** → `recip_top_combined` (this file) — clears to the
  restricted chain via `recip_top_step`, consuming the combined IH. No
  integrating factor.
- **exp top** → the generalised exp step (the `vehExpo`-tower machinery over
  mixed chains), which is the remaining A-4a machinery core.

This file lands the **reciprocal half**: fully proven, hole-free, exercising the
witness-enriched class end-to-end with `recip_top_step` and `clearTop`. It shows
the reciprocal levels are completely handled in the combined descent (matching
that reciprocal levels are the "easy", integrating-factor-free part). The exp
half + base case + final assembly are the remaining bricks.
-/

namespace MachLib
namespace PfaffianExpRecipW

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianGeneralReduce
open MachLib.PfaffianExpRecip

variable {N : Nat}

/-- **Reciprocal-top case of the combined descent.** Given the top reciprocal
level's witness `v` (from `IsExpOrRecipW_top`'s reciprocal disjunct) and the
combined induction hypothesis `hM` bounding the cleared function
`clearTop (dropLastY v) p` over `chainRestrict c`, bound `pfaffianChainFn c p`.

Plugs the enriched class's witness into `recip_top_step`: `dropLastY v` is the
restricted-chain denominator; its coherence (`y_top = 1/dropLastY v`) and
positivity come from the witness `hvcoh`/`hvpos` via `eval_dropLastY` (`v` is
top-free at the dropped top). The witness identity `a·w = 1 ⟹ a = 1/w` closes
the `hwitness` obligation. -/
theorem recip_top_combined (c : PfaffianChain (N + 1)) (a b : Real)
    (v : MultiPoly (N + 1))
    (hvtf : ∀ j : Fin (N + 1), N ≤ j.val → MultiPoly.degreeY j v = 0)
    (hvcoh : ∀ x : Real, a < x → x < b →
        c.evals ⟨N, Nat.lt_succ_self N⟩ x * MultiPoly.eval v x (c.chainValues x) = 1)
    (hvpos : ∀ x : Real, a < x → x < b → 0 < MultiPoly.eval v x (c.chainValues x))
    (p : MultiPoly (N + 1)) (M : Nat)
    (hM : ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b
          ∧ (pfaffianChainFn (chainRestrict c) (clearTop (MultiPoly.dropLastY v) p)).eval z = 0) →
        zeros.length ≤ M) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z = 0) →
      zeros.length ≤ M := by
  have hvN : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) v = 0 :=
    hvtf ⟨N, Nat.lt_succ_self N⟩ (Nat.le_refl N)
  have heval : ∀ x : Real, MultiPoly.eval (MultiPoly.dropLastY v) x
        ((chainRestrict c).chainValues x) = MultiPoly.eval v x (c.chainValues x) :=
    fun x => MultiPoly.eval_dropLastY v hvN x (c.chainValues x)
  apply recip_top_step c (MultiPoly.dropLastY v) a b M ?_ ?_ p hM
  · intro x hxa hxb
    have hw : MultiPoly.eval (MultiPoly.dropLastY v) x ((chainRestrict c).chainValues x) ≠ 0 := by
      rw [heval x]; exact ne_of_gt (hvpos x hxa hxb)
    have hcoh1 : c.evals ⟨N, Nat.lt_succ_self N⟩ x
        * MultiPoly.eval (MultiPoly.dropLastY v) x ((chainRestrict c).chainValues x) = 1 := by
      rw [heval x]; exact hvcoh x hxa hxb
    show c.evals ⟨N, Nat.lt_succ_self N⟩ x
        = 1 / MultiPoly.eval (MultiPoly.dropLastY v) x ((chainRestrict c).chainValues x)
    rw [← hcoh1, mul_comm, mul_div_cancel_left' hw]
  · intro x hxa hxb
    rw [heval x]; exact ne_of_gt (hvpos x hxa hxb)

/-- **`clearTop` preserves non-vanishing** on the domain (`v > 0`). If `p` is
non-vanishing at some `z ∈ (a,b)`, so is `clearTop v p` — the cleared numerator
`= v^d · p` and `v^d > 0`. This is what lets the reciprocal-top case feed the
combined induction hypothesis (which requires a non-vanishing target). -/
theorem clearTop_nonvanishing (c : PfaffianChain (N + 1)) (v : MultiPoly N) (a b : Real)
    (hwitness : ∀ x : Real, a < x → x < b →
        c.chainValues x ⟨N, Nat.lt_succ_self N⟩
          = 1 / MultiPoly.eval v x ((chainRestrict c).chainValues x))
    (hvpos : ∀ x : Real, a < x → x < b →
        0 < MultiPoly.eval v x ((chainRestrict c).chainValues x))
    (p : MultiPoly (N + 1))
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) :
    ∃ z, a < z ∧ z < b
      ∧ (pfaffianChainFn (chainRestrict c) (clearTop v p)).eval z ≠ 0 := by
  obtain ⟨z, hza, hzb, hzne⟩ := hne
  refine ⟨z, hza, hzb, ?_⟩
  have hvne : MultiPoly.eval v z ((chainRestrict c).chainValues z) ≠ 0 :=
    ne_of_gt (hvpos z hza hzb)
  show MultiPoly.eval (clearTop v p) z ((chainRestrict c).chainValues z) ≠ 0
  rw [clearTop_chain_bridge c v z (hwitness z hza hzb) hvne p]
  exact mul_ne_zero (ne_of_gt (mpolyPow_eval_pos v (hvpos z hza hzb) _)) hzne

end PfaffianExpRecipW
end MachLib
