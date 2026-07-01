import MachLib.ChainExp2CanonMeasure
import MachLib.ChainExp2YPIT
import MachLib.ChainExp2SDR

/-!
# Route A, brick 3 — `cdegY0` eval-invariance

The canonical `y₀`-degree `cdegY0` (from `ChainExp2CanonMeasure`) is an eval-invariant: eval-equal
`MultiPoly 2`s have equal `cdegY0`. This is what lets the cancellation (`lcY₁(chain2Reduce c p)` is
eval-equal to the single-exp reduce of `lcY₁ p`) transfer the descent to the single-exp side.

Foundation: `coeffCanonZeroB` (the "this `y₀`-coefficient is canonically zero" test) is eval-invariant,
because `CanonicallyZero (polyCoeffs (mP2PFL c))` unfolds — via `polyCoeffs_eval` and
`eval_multiPolyToPolyForLex_eq_eval_zero` — to the eval condition `∀ x, eval c x (0-env) = 0`. Combined
with the `y`-PIT (`ChainExp2YPIT`) applied to `q1 − q2` and the definitional
`yCoeffsAt(sub) = listSubN(yCoeffsAt)(yCoeffsAt)`, eval-equal polys have entry-wise canonically-equal
`yCoeffsAt`, so the `reverse.dropWhile` trimming — hence `cdegY0` — agrees.

`ChainExp2SDR` + single-exp untouched (Path B).
-/

namespace MachLib.ChainExp2CdegInv

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.PolynomialCanonical
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.ChainExp2SDR
open MachLib.ChainExp2CanonMeasure
open MachLib.ChainExp2YPIT

/-- `CanonicallyZero (polyCoeffs (mP2PFL c))` is exactly "the `y→0` projection of `c` evaluates to `0` at
every `x`" — an eval condition. (Chains `polyCoeffs_eval` with `eval_multiPolyToPolyForLex_eq_eval_zero`.) -/
theorem canonZero_iff_eval_zero_at_0 (c : MultiPoly 2) :
    CanonicallyZero (polyCoeffs (multiPolyToPolyForLex c))
      ↔ ∀ x : Real, MultiPoly.eval c x (fun _ => 0) = 0 := by
  unfold CanonicallyZero
  constructor
  · intro h x
    rw [← eval_multiPolyToPolyForLex_eq_eval_zero c x, ← polyCoeffs_eval]
    exact h x
  · intro h x
    rw [polyCoeffs_eval, eval_multiPolyToPolyForLex_eq_eval_zero c x]
    exact h x

/-- **`coeffCanonZeroB` is eval-invariant.** If `c1`, `c2` evaluate identically everywhere, the canonical-
zero test agrees on them. -/
theorem coeffCanonZeroB_eq_of_eval_eq (c1 c2 : MultiPoly 2)
    (h : ∀ (x : Real) (env : Fin 2 → Real), MultiPoly.eval c1 x env = MultiPoly.eval c2 x env) :
    coeffCanonZeroB c1 = coeffCanonZeroB c2 := by
  unfold coeffCanonZeroB
  have hiff : CanonicallyZero (polyCoeffs (multiPolyToPolyForLex c1))
            ↔ CanonicallyZero (polyCoeffs (multiPolyToPolyForLex c2)) := by
    rw [canonZero_iff_eval_zero_at_0, canonZero_iff_eval_zero_at_0]
    constructor
    · intro hc x; rw [← h x (fun _ => 0)]; exact hc x
    · intro hc x; rw [h x (fun _ => 0)]; exact hc x
  exact decide_eq_decide.mpr hiff

end MachLib.ChainExp2CdegInv
