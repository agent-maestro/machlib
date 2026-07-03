import MachLib.IterExpDepthNSynMeasure
import MachLib.IterExpDepthNAssembly
import MachLib.IterExpDepthNInnerTrim
import MachLib.IterExpDepthNDescentInduction

/-!
# Phase C→D absorption — `synMeasure` invariant under a `y`-free factor (helper for the deep trim)

`synMeasure_mul_yfree` — multiplying by a polynomial with all `degreeY_j = 0` leaves `synMeasure` unchanged.
This is what lets the deep-trim's `reconstructY`-based lift descend cleanly: the reconstructed leading
coefficient carries a `y`-free power-unit factor (`leadingCoeffY (yᵢ^D)`), which `synMeasure` (a tuple of raw
`degreeY`s) ignores. No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.ChainExp2NoZeros
open MachLib.MultiPolyReconstruct
open MachLib.ChainExp2Trim
open MachLib.IterExpDepth3InnerTrim

/-- **`synMeasure` ignores a `y`-free factor.** If `c` has `degreeY_j = 0` for every `j`, then
`synMeasure k (q * c) = synMeasure k q`. Induction on depth: raw `degreeY` is additive and `c` contributes
`0` at each level; the leading coefficient of `q * c` is `lcY q * c` (as `c` is its own leading coefficient),
and `dropLastY c` stays `y`-free, so the tail recurses. -/
theorem synMeasure_mul_yfree : ∀ (k : Nat) (q c : MultiPoly (k + 2)),
    (∀ (j : Fin (k + 2)), MultiPoly.degreeY j c = 0) →
    synMeasure k (MultiPoly.mul q c) = synMeasure k q := by
  intro k
  induction k with
  | zero =>
    intro q c hc
    show (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.mul q c), ((0 : Nat), (0 : Nat)))
        = (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q, (0, 0))
    have : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.mul q c)
        = MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q := by
      show MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q + MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) c
        = MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q
      rw [hc (⟨1, by omega⟩ : Fin 2), Nat.add_zero]
    rw [this]
  | succ k ih =>
    intro q c hc
    show (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) (MultiPoly.mul q c),
          synMeasure k (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3))
            (MultiPoly.mul q c))))
        = (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q,
           synMeasure k (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)))
    have hdeg : MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) (MultiPoly.mul q c)
        = MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q := by
      show MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q
          + MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) c
        = MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q
      rw [hc (⟨k + 2, by omega⟩ : Fin (k + 3)), Nat.add_zero]
    have hlceq : MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) (MultiPoly.mul q c)
        = MultiPoly.mul (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q) c := by
      show MultiPoly.mul (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)
            (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) c)
        = MultiPoly.mul (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q) c
      rw [leadingCoeffY_eq_self_of_degreeY_zero (⟨k + 2, by omega⟩ : Fin (k + 3)) c
            (hc (⟨k + 2, by omega⟩ : Fin (k + 3)))]
    have hdc : ∀ (j : Fin (k + 2)), MultiPoly.degreeY j (MultiPoly.dropLastY c) = 0 := by
      intro j
      rw [degreeY_dropLastY_eq_prev (k + 2) (⟨j.val, by omega⟩ : Fin (k + 3)) j rfl c]
      exact hc (⟨j.val, by omega⟩ : Fin (k + 3))
    rw [hdeg, hlceq]
    show (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q,
          synMeasure k (MultiPoly.mul (MultiPoly.dropLastY
            (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)) (MultiPoly.dropLastY c)))
        = (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q,
           synMeasure k (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)))
    rw [ih _ (MultiPoly.dropLastY c) hdc]

/-! ### The deep-trim lift — replace the leading coefficient by `liftLastY inner'` -/

/-- The lift: rebuild `c` with its leading `y_top`-coefficient replaced by `liftLastY inner'`. -/
noncomputable def liftInner (k : Nat) (c : MultiPoly (k + 3)) (inner' : MultiPoly (k + 2)) :
    MultiPoly (k + 3) :=
  reconstructY (⟨k + 2, by omega⟩ : Fin (k + 3))
    ((MultiPoly.yCoeffsAt (⟨k + 2, by omega⟩ : Fin (k + 3)) c).dropLast ++ [liftLastY inner']) 0

/-- **Eval-preservation of the lift.** If `liftLastY inner'` evaluates like the leading `y_top`-coefficient
(the `getLast`), rebuilding with it changes no value. Faithful copy of `eval_innerTrimN`'s swap. -/
theorem eval_liftInner (k : Nat) (c : MultiPoly (k + 3)) (inner' : MultiPoly (k + 2))
    (hswap : ∀ (x : Real) (env : Fin (k + 3) → Real),
      MultiPoly.eval (liftLastY inner') x env
        = MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨k + 2, by omega⟩ : Fin (k + 3)) c).getLast
          (MultiPoly.yCoeffsAt_nonempty (⟨k + 2, by omega⟩ : Fin (k + 3)) c)) x env)
    (x : Real) (env : Fin (k + 3) → Real) :
    MultiPoly.eval (liftInner k c inner') x env = MultiPoly.eval c x env := by
  unfold liftInner
  rw [eval_reconstructY_last_swap (⟨k + 2, by omega⟩ : Fin (k + 3)) (liftLastY inner')
        ((MultiPoly.yCoeffsAt (⟨k + 2, by omega⟩ : Fin (k + 3)) c).getLast
          (MultiPoly.yCoeffsAt_nonempty (⟨k + 2, by omega⟩ : Fin (k + 3)) c))
        x env (hswap x env) (MultiPoly.yCoeffsAt (⟨k + 2, by omega⟩ : Fin (k + 3)) c).dropLast 0,
      List.dropLast_concat_getLast (MultiPoly.yCoeffsAt_nonempty (⟨k + 2, by omega⟩ : Fin (k + 3)) c)]
  exact eval_reconstructY_yCoeffsAt (⟨k + 2, by omega⟩ : Fin (k + 3)) c x env

/-- The rebuilt list of `liftInner` is `y_top`-free and length `degreeY_top c + 1`. -/
private theorem liftInner_list_free (k : Nat) (c : MultiPoly (k + 3)) (inner' : MultiPoly (k + 2)) :
    ∀ e ∈ ((MultiPoly.yCoeffsAt (⟨k + 2, by omega⟩ : Fin (k + 3)) c).dropLast ++ [liftLastY inner']),
      MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) e = 0 := by
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact MultiPoly.yCoeffsAt_entries_degreeY_zero (⟨k + 2, by omega⟩ : Fin (k + 3)) c e
      (List.dropLast_subset _ h)
  · rw [List.mem_singleton.mp h]; exact degreeY_top_liftLastY _

private theorem liftInner_list_len (k : Nat) (c : MultiPoly (k + 3)) (inner' : MultiPoly (k + 2)) :
    ((MultiPoly.yCoeffsAt (⟨k + 2, by omega⟩ : Fin (k + 3)) c).dropLast ++ [liftLastY inner']).length
      = MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) c + 1 := by
  rw [List.length_append, List.length_dropLast, List.length_singleton, yCoeffsAt_length_eq]; omega

/-- **`liftInner` preserves the syntactic top degree.** -/
theorem degreeYtop_liftInner (k : Nat) (c : MultiPoly (k + 3)) (inner' : MultiPoly (k + 2)) :
    MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) (liftInner k c inner')
      = MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) c := by
  unfold liftInner
  rw [degreeY_reconstructY_exact (⟨k + 2, by omega⟩ : Fin (k + 3)) _ (by simp)
        (liftInner_list_free k c inner') 0, liftInner_list_len k c inner']
  omega

/-- **`liftInner`'s leading `y_top`-coefficient** (positive `degreeY_top`): `liftLastY inner'` times the
`y`-free power-unit `leadingCoeffY (y_top^{degreeY_top c})`. -/
theorem leadingCoeffYtop_liftInner (k : Nat) (c : MultiPoly (k + 3)) (inner' : MultiPoly (k + 2))
    (hpos : 0 < MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) c) :
    MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) (liftInner k c inner')
      = MultiPoly.mul (liftLastY inner')
          (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3))
            (MultiPoly.pow (MultiPoly.varY (⟨k + 2, by omega⟩ : Fin (k + 3)))
              (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) c))) := by
  have hexp : (0 : Nat) + ((MultiPoly.yCoeffsAt (⟨k + 2, by omega⟩ : Fin (k + 3)) c).dropLast
      ++ [liftLastY inner']).length - 1 = MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) c := by
    rw [liftInner_list_len k c inner']; omega
  unfold liftInner
  rw [leadingCoeffY_reconstructY (⟨k + 2, by omega⟩ : Fin (k + 3)) _ (by simp)
        (liftInner_list_free k c inner') 0 (by rw [liftInner_list_len k c inner']; omega),
      List.getLast_concat, hexp]

/-- **`synMeasure` of the lift** (positive `degreeY_top c`): `(degreeY_top c, synMeasure k inner')`. Combines
the two lemmas above with `synMeasure_mul_yfree` stripping the `y`-free power-unit. -/
theorem synMeasure_liftInner (k : Nat) (c : MultiPoly (k + 3)) (inner' : MultiPoly (k + 2))
    (hpos : 0 < MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) c) :
    synMeasure (k + 1) (liftInner k c inner')
      = (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) c, synMeasure k inner') := by
  have hyfree : ∀ (j : Fin (k + 2)), MultiPoly.degreeY j
      (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3))
        (MultiPoly.pow (MultiPoly.varY (⟨k + 2, by omega⟩ : Fin (k + 3)))
          (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) c)))) = 0 := by
    intro j
    rw [degreeY_dropLastY_eq_prev (k + 2) (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 3)) j rfl _]
    exact degreeY_leadingCoeffY_pow_self (⟨k + 2, Nat.lt_succ_self (k + 2)⟩ : Fin (k + 3))
      (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 3)) _
  simp only [synMeasure]
  rw [degreeYtop_liftInner k c inner', leadingCoeffYtop_liftInner k c inner' hpos]
  show (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) c,
        synMeasure k (MultiPoly.mul (MultiPoly.dropLastY (liftLastY inner'))
          (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3))
            (MultiPoly.pow (MultiPoly.varY (⟨k + 2, by omega⟩ : Fin (k + 3)))
              (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) c))))))
      = (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) c, synMeasure k inner')
  rw [dropLastY_liftLastY, synMeasure_mul_yfree k inner' _ hyfree]

/-- **`synMeasure` of a bare `liftLastY`** (the `degreeY_top c = 0` trim): `(0, synMeasure k inner')`. -/
theorem synMeasure_liftLastY (k : Nat) (inner' : MultiPoly (k + 2)) :
    synMeasure (k + 1) (liftLastY inner') = (0, synMeasure k inner') := by
  simp only [synMeasure]
  rw [degreeY_top_liftLastY,
      leadingCoeffY_eq_self_of_degreeY_zero (⟨k + 2, by omega⟩ : Fin (k + 3)) (liftLastY inner')
        (degreeY_top_liftLastY _),
      dropLastY_liftLastY]

end MachLib.IterExpDepthN
