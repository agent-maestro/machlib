import MachLib.MultiPolyReconstruct

/-!
# Fixed-degree coefficient foundations — for the LOG leading-coefficient identity

`log_hard` needs the coefficient of `cTD c p` at the FIXED original top degree
`D = degreeY_top p` (NOT `leadingCoeffY (cTD c p)`, which — because a log-type
`cTD` can DROP the top degree — may be extracted at a lower degree; see the
exploration PIVOT note 2026-07-08). Contrast the exp descent
(`PfaffianGeneralReduce.IdNGen`), which uses `leadingCoeffY` throughout because
exp PRESERVES the top degree (`degreeYtop_cTD_eq_gen`).

Two `getD`-at-fixed-index facts, both grounded in `yCoeffsAt_length_eq`
(`(yCoeffsAt i p).length = degreeY i p + 1`):

  * `getD_beyond_degreeY_eval` — index past the top degree ⇒ default `const 0` ⇒ eval `0`.
  * `getD_at_degreeY_eq_lcY_eval` — index AT the top degree (`= length − 1`) is the
    `getLast`, which evals to `leadingCoeffY`.

Plus the two generic `List.getD` facts they rest on.
-/
namespace MachLib
namespace MultiPolyMod
namespace MultiPoly
open MachLib.Real MachLib.MultiPolyReconstruct

/-- `List.getD` past the end returns the default. -/
theorem list_getD_beyond {α : Type _} : ∀ (l : List α) (d : Nat) (dflt : α),
    l.length ≤ d → l.getD d dflt = dflt
  | [], _, _, _ => rfl
  | _ :: as, 0, _, h => absurd h (Nat.not_succ_le_zero as.length)
  | _ :: as, d + 1, dflt, h => list_getD_beyond as d dflt (Nat.le_of_succ_le_succ h)

/-- `List.getD` at `length − 1` is the last element. -/
theorem list_getD_pred_eq_getLast {α : Type _} : ∀ (l : List α) (dflt : α) (h : l ≠ []),
    l.getD (l.length - 1) dflt = l.getLast h
  | [_], _, _ => rfl
  | a :: b :: as, dflt, _ => by
      show (b :: as).getD ((b :: as).length - 1) dflt = (b :: as).getLast (List.cons_ne_nil b as)
      exact list_getD_pred_eq_getLast (b :: as) dflt (List.cons_ne_nil b as)

/-- **`getD` beyond `degreeY` vanishes (eval).** For `d > degreeY i r`, the `d`-th
`yCoeffsAt` entry is past the length-`(degreeY+1)` list, i.e. the default `const 0`.
The "degree dropped" branch of the log leading-coefficient identity's `add`/`mul`
cases lands here. -/
theorem getD_beyond_degreeY_eval {n : Nat} (i : Fin n) (r : MultiPoly n) (d : Nat)
    (hd : MultiPoly.degreeY i r < d) (x : Real) (env : Fin n → Real) :
    MultiPoly.eval ((yCoeffsAt i r).getD d (MultiPoly.const 0)) x env = 0 := by
  have hlen : (yCoeffsAt i r).length ≤ d := by rw [yCoeffsAt_length_eq]; omega
  rw [list_getD_beyond (yCoeffsAt i r) d (MultiPoly.const 0) hlen]; rfl

/-- **`getD` at `degreeY` is the leading coefficient (eval).** The top `yCoeffsAt`
entry (index `degreeY i r = length − 1`) is `getLast`, which evals to
`leadingCoeffY i r` (`eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general`). The
"degree preserved" branch of the log identity uses this to identify the fixed-`D`
coefficient with the leading coefficient. -/
theorem getD_at_degreeY_eq_lcY_eval {n : Nat} (i : Fin n) (r : MultiPoly n)
    (x : Real) (env : Fin n → Real) :
    MultiPoly.eval ((yCoeffsAt i r).getD (MultiPoly.degreeY i r) (MultiPoly.const 0)) x env
      = MultiPoly.eval (MultiPoly.leadingCoeffY i r) x env := by
  have hne : yCoeffsAt i r ≠ [] := by
    intro h; have := yCoeffsAt_length_eq i r; rw [h] at this; simp at this
  have hidx : MultiPoly.degreeY i r = (yCoeffsAt i r).length - 1 := by
    rw [yCoeffsAt_length_eq]; omega
  rw [hidx, list_getD_pred_eq_getLast (yCoeffsAt i r) (MultiPoly.const 0) hne]
  exact (eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general i r hne x env).symm

end MultiPoly
end MultiPolyMod
end MachLib
