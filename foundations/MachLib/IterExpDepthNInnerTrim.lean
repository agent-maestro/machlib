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

/-! ### Inner-trim degree lemmas (the M5 tiebreaker facts)

The three facts the M5 augmented measure needs about `innerTrimN`:
* `degreeYtop_innerTrimN_eq` — the syntactic top degree `degreeY_{top}` is *exactly preserved*;
* `leadingCoeffYtop_innerTrimN_eval` — the projected leading top-coefficient evaluates like
  `dropLeadingYAt ⟨top-1⟩ (lcY_top p)` (so the eval-invariant inner measure is unchanged);
* `leadingCoeffYtop_innerTrimN_degreeYprev` — its syntactic `degreeY_{top-1}` equals that of
  `dropLeadingYAt ⟨top-1⟩ (lcY_top p)` — which strictly drops (the M5 tiebreaker).

Faithful ∀N ports of `degreeY2_innerTrim3_eq` / `leadingCoeffY2_innerTrim3{,_eval,_degreeY1}`. -/

/-- `dropLeadingYAt ⟨top-1⟩` preserves `y_top`-freeness (∀N analog of `degreeY2_dropLeadingYAt1_zero`). -/
theorem degreeYtop_dropLeadingYAt_prev_zero (m : Nat) (X : MultiPoly (m + 3))
    (hy : MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) X = 0) :
    MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3))
      (dropLeadingYAt (⟨m + 1, by omega⟩ : Fin (m + 3)) X) = 0 := by
  show MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3))
        (reconstructY (⟨m + 1, by omega⟩ : Fin (m + 3))
          (MultiPoly.yCoeffsAt (⟨m + 1, by omega⟩ : Fin (m + 3)) X).dropLast 0) = 0
  apply degreeY_reconstructY_other_zero (⟨m + 1, by omega⟩ : Fin (m + 3))
    (⟨m + 2, by omega⟩ : Fin (m + 3))
    (by intro h; have h2 : m + 2 = m + 1 := congrArg Fin.val h; omega)
  intro c hc
  exact yCoeffsAt_entries_other_degreeY_zero (⟨m + 1, by omega⟩ : Fin (m + 3))
    (⟨m + 2, by omega⟩ : Fin (m + 3)) X hy c (List.dropLast_subset _ hc)

/-- The rebuilt `y_top`-coefficient list of `innerTrimN` (all entries `y_top`-free, length `degreeY_top p + 1`). -/
private theorem innerTrimN_list_free (m : Nat) (p : MultiPoly (m + 3)) :
    ∀ c ∈ ((MultiPoly.yCoeffsAt (⟨m + 2, by omega⟩ : Fin (m + 3)) p).dropLast ++
      [dropLeadingYAt (⟨m + 1, by omega⟩ : Fin (m + 3))
        (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)]),
      MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) c = 0 := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact MultiPoly.yCoeffsAt_entries_degreeY_zero (⟨m + 2, by omega⟩ : Fin (m + 3)) p c
      (List.dropLast_subset _ h)
  · rw [List.mem_singleton.mp h]
    exact degreeYtop_dropLeadingYAt_prev_zero m _
      (MultiPoly.degreeY_leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)

private theorem innerTrimN_list_len (m : Nat) (p : MultiPoly (m + 3)) :
    ((MultiPoly.yCoeffsAt (⟨m + 2, by omega⟩ : Fin (m + 3)) p).dropLast ++
      [dropLeadingYAt (⟨m + 1, by omega⟩ : Fin (m + 3))
        (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)]).length
      = MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p + 1 := by
  rw [List.length_append, List.length_dropLast, List.length_singleton, yCoeffsAt_length_eq]
  omega

/-- **`degreeY_top` is exactly preserved by `innerTrimN`.** -/
theorem degreeYtop_innerTrimN_eq (m : Nat) (p : MultiPoly (m + 3)) :
    MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) (innerTrimN m p)
      = MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p := by
  unfold innerTrimN
  rw [degreeY_reconstructY_exact (⟨m + 2, by omega⟩ : Fin (m + 3)) _ (by simp)
        (innerTrimN_list_free m p) 0, innerTrimN_list_len m p]
  omega

/-- **`leadingCoeffY_top (innerTrimN p)`** (positive `degreeY_top`): the last coefficient
`dropLeadingYAt ⟨top-1⟩ (lcY_top p)` times the (eval-`1`, `y`-free) leading coeff of `y_top^{degreeY_top p}`. -/
theorem leadingCoeffYtop_innerTrimN (m : Nat) (p : MultiPoly (m + 3))
    (hpos : 0 < MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p) :
    MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) (innerTrimN m p)
      = MultiPoly.mul
          (dropLeadingYAt (⟨m + 1, by omega⟩ : Fin (m + 3))
        (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p))
          (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3))
            (MultiPoly.pow (MultiPoly.varY (⟨m + 2, by omega⟩ : Fin (m + 3)))
              (MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p))) := by
  have hexp : (0 : Nat) + ((MultiPoly.yCoeffsAt (⟨m + 2, by omega⟩ : Fin (m + 3)) p).dropLast ++
      [dropLeadingYAt (⟨m + 1, by omega⟩ : Fin (m + 3))
        (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)]).length - 1
      = MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p := by
    rw [innerTrimN_list_len m p]; omega
  unfold innerTrimN
  rw [leadingCoeffY_reconstructY (⟨m + 2, by omega⟩ : Fin (m + 3)) _ (by simp)
        (innerTrimN_list_free m p) 0 (by rw [innerTrimN_list_len m p]; omega),
      List.getLast_concat, hexp]

/-- Eval version: `leadingCoeffY_top (innerTrimN p)` evaluates like `dropLeadingYAt ⟨top-1⟩ (lcY_top p)`. -/
theorem leadingCoeffYtop_innerTrimN_eval (m : Nat) (p : MultiPoly (m + 3))
    (hpos : 0 < MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p) (x : Real)
    (env : Fin (m + 3) → Real) :
    MultiPoly.eval (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) (innerTrimN m p)) x env
      = MultiPoly.eval (dropLeadingYAt (⟨m + 1, by omega⟩ : Fin (m + 3))
        (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)) x env := by
  rw [leadingCoeffYtop_innerTrimN m p hpos, MultiPoly.eval_mul, leadingCoeffY_pow_self_eval,
      MachLib.Real.mul_one_ax]

/-- `degreeY_{top-1}` version: `leadingCoeffY_top (innerTrimN p)` has the same `y_{top-1}`-degree as
`dropLeadingYAt ⟨top-1⟩ (lcY_top p)` (the `y_top^D` leading factor is `y`-free). -/
theorem leadingCoeffYtop_innerTrimN_degreeYprev (m : Nat) (p : MultiPoly (m + 3))
    (hpos : 0 < MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p) :
    MultiPoly.degreeY (⟨m + 1, by omega⟩ : Fin (m + 3))
        (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) (innerTrimN m p))
      = MultiPoly.degreeY (⟨m + 1, by omega⟩ : Fin (m + 3))
          (dropLeadingYAt (⟨m + 1, by omega⟩ : Fin (m + 3))
        (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)) := by
  rw [leadingCoeffYtop_innerTrimN m p hpos]
  show MultiPoly.degreeY (⟨m + 1, by omega⟩ : Fin (m + 3))
        (dropLeadingYAt (⟨m + 1, by omega⟩ : Fin (m + 3))
        (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p))
      + MultiPoly.degreeY (⟨m + 1, by omega⟩ : Fin (m + 3))
          (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3))
            (MultiPoly.pow (MultiPoly.varY (⟨m + 2, by omega⟩ : Fin (m + 3)))
              (MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p))) = _
  rw [degreeY_leadingCoeffY_pow_self, Nat.add_zero]

end MachLib.IterExpDepthN
