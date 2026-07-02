import MachLib.IterExpDepthNMeasureCanon
import MachLib.IterExpDepthNChainFn
import MachLib.IterExpDepth3InnerTrim

/-!
# Phase D (D3 step ii) — the ∀N inner-trim: drop a phantom leading `y_{top-1}` term of `lcY_top`

The WF induction's fourth arm. When the leading `y_{top-1}`-term of `p`'s leading top-coefficient is
phantom, `innerTrimN` replaces `leadingCoeffY_top p` by its `dropLeadingYAt ⟨top-1⟩` — preserving the
evaluation everywhere (`eval_innerTrimN`) while strictly lowering the *syntactic* `degreeY_{top-1}` of the
projected leading coefficient. Faithful ∀N port of `innerTrim3`/`eval_innerTrim3` (all primitives —
`reconstructY`, `dropLeadingYAt`, `eval_reconstructY_last_swap` — are index-generic). No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.MultiPolyReconstruct
open MachLib.ChainExp2Trim
open MachLib.IterExpDepth3InnerTrim

/-- The ∀N inner-trim: replace the leading top-coefficient by its `dropLeadingYAt ⟨top-1⟩`. -/
noncomputable def innerTrimN (m : Nat) (p : MultiPoly (m + 3)) : MultiPoly (m + 3) :=
  reconstructY (⟨m + 2, by omega⟩ : Fin (m + 3))
    ((MultiPoly.yCoeffsAt (⟨m + 2, by omega⟩ : Fin (m + 3)) p).dropLast ++
      [dropLeadingYAt (⟨m + 1, by omega⟩ : Fin (m + 3))
        (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)]) 0

/-- **Eval-preservation.** When the leading `y_{top-1}`-term of `lcY_top p` vanishes everywhere,
`innerTrimN p` evaluates identically to `p`. -/
theorem eval_innerTrimN (m : Nat) (p : MultiPoly (m + 3))
    (h_phantom : ∀ (x : Real) (env : Fin (m + 3) → Real),
      MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨m + 1, by omega⟩ : Fin (m + 3))
        (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)).getLast
        (MultiPoly.yCoeffsAt_nonempty (⟨m + 1, by omega⟩ : Fin (m + 3))
          (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p))) x env = 0)
    (x : Real) (env : Fin (m + 3) → Real) :
    MultiPoly.eval (innerTrimN m p) x env = MultiPoly.eval p x env := by
  have hswap_eval : MultiPoly.eval (dropLeadingYAt (⟨m + 1, by omega⟩ : Fin (m + 3))
        (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)) x env
      = MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨m + 2, by omega⟩ : Fin (m + 3)) p).getLast
          (MultiPoly.yCoeffsAt_nonempty (⟨m + 2, by omega⟩ : Fin (m + 3)) p)) x env := by
    rw [eval_dropLeadingYAt_of_last_canonically_zero (⟨m + 1, by omega⟩ : Fin (m + 3))
        (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)
        (MultiPoly.yCoeffsAt_nonempty (⟨m + 1, by omega⟩ : Fin (m + 3))
          (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p))
        h_phantom x env]
    exact eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general (⟨m + 2, by omega⟩ : Fin (m + 3)) p
      (MultiPoly.yCoeffsAt_nonempty (⟨m + 2, by omega⟩ : Fin (m + 3)) p) x env
  unfold innerTrimN
  rw [eval_reconstructY_last_swap (⟨m + 2, by omega⟩ : Fin (m + 3))
        (dropLeadingYAt (⟨m + 1, by omega⟩ : Fin (m + 3))
        (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p))
        ((MultiPoly.yCoeffsAt (⟨m + 2, by omega⟩ : Fin (m + 3)) p).getLast
          (MultiPoly.yCoeffsAt_nonempty (⟨m + 2, by omega⟩ : Fin (m + 3)) p))
        x env hswap_eval (MultiPoly.yCoeffsAt (⟨m + 2, by omega⟩ : Fin (m + 3)) p).dropLast 0,
      List.dropLast_concat_getLast (MultiPoly.yCoeffsAt_nonempty (⟨m + 2, by omega⟩ : Fin (m + 3)) p)]
  exact eval_reconstructY_yCoeffsAt (⟨m + 2, by omega⟩ : Fin (m + 3)) p x env

end MachLib.IterExpDepthN
