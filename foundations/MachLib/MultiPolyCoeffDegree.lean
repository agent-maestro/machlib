import MachLib.MultiPolyReconstruct
import MachLib.MultiPolyCoeffEntry

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

/-- **Product top-coefficient is a SINGLE term (eval).** For coefficient lists
`A`, `B` with `|A| ≤ m+1` and `|B| ≤ nn+1`, the `(m+nn)`-th convolution entry of
`listMulN A B` collapses to `A_m · B_nn` — every other convolution term has a
factor past one list's end (`getD_beyond`), so it vanishes. This is why the LOG
leading-coefficient identity's `mul` case is single-term (like the exp descent's
`lcY_mul`), not a full convolution: applied at `m = degreeY_top p`,
`nn = degreeY_top q` (with `degreeY_top(cTD p) ≤ m` via `degreeYtop_cTD_le_log`),
`getD_{Dp+Dq}(yCoeffs(mul (cTD p) q)) = getD_{Dp}(yCoeffs(cTD p)) · lcY(q)`.
Induction on `A`: `m = 0` forces `A = [a]` (the `a·B_nn` term); `m = m'+1` kills
the `a·getD_{m+nn} B` term (`getD` past `B`) and recurses on the tail. -/
theorem getD_mul_split_eval {n : Nat} : ∀ (A B : List (MultiPoly n)) (m nn : Nat),
    A.length ≤ m + 1 → B.length ≤ nn + 1 → ∀ (x : Real) (env : Fin n → Real),
    MultiPoly.eval ((listMulN A B).getD (m + nn) (MultiPoly.const 0)) x env
      = MultiPoly.eval (A.getD m (MultiPoly.const 0)) x env
        * MultiPoly.eval (B.getD nn (MultiPoly.const 0)) x env
  | [], B, m, nn, _, _, x, env => by
      have h1 : (([] : List (MultiPoly n)).getD (m + nn) (MultiPoly.const 0)) = MultiPoly.const 0 := by
        cases (m + nn) <;> rfl
      have h2 : (([] : List (MultiPoly n)).getD m (MultiPoly.const 0)) = MultiPoly.const 0 := by
        cases m <;> rfl
      show MultiPoly.eval ((listMulN ([] : List (MultiPoly n)) B).getD (m + nn) (MultiPoly.const 0)) x env = _
      rw [show listMulN ([] : List (MultiPoly n)) B = [] from rfl, h1, h2]
      show (0 : Real) = (0 : Real) * _
      rw [Real.zero_mul]
  | a :: as, B, m, nn, hA, hB, x, env => by
      cases m with
      | zero =>
        have has : as = [] := List.length_eq_zero.mp (Nat.le_zero.mp (Nat.le_of_succ_le_succ hA))
        subst has
        rw [getD_listMulN_cons_eval a [] B (0 + nn) x env, Nat.zero_add]
        have hz : MultiPoly.eval ((MultiPoly.const 0 :: listMulN ([] : List (MultiPoly n)) B).getD nn (MultiPoly.const 0)) x env = 0 := by
          rw [show listMulN ([] : List (MultiPoly n)) B = [] from rfl]
          cases nn <;> rfl
        rw [hz]
        show MultiPoly.eval a x env * MultiPoly.eval (B.getD nn (MultiPoly.const 0)) x env + (0 : Real)
           = MultiPoly.eval a x env * MultiPoly.eval (B.getD nn (MultiPoly.const 0)) x env
        rw [Real.add_zero]
      | succ m' =>
        have hAs : as.length ≤ m' + 1 := Nat.le_of_succ_le_succ hA
        rw [getD_listMulN_cons_eval a as B (m' + 1 + nn) x env]
        have hBz : MultiPoly.eval (B.getD (m' + 1 + nn) (MultiPoly.const 0)) x env = 0 := by
          rw [list_getD_beyond B (m' + 1 + nn) (MultiPoly.const 0) (by omega)]; rfl
        have hshift : MultiPoly.eval ((MultiPoly.const 0 :: listMulN as B).getD (m' + 1 + nn) (MultiPoly.const 0)) x env
            = MultiPoly.eval ((listMulN as B).getD (m' + nn) (MultiPoly.const 0)) x env := by
          rw [show m' + 1 + nn = (m' + nn) + 1 by omega]; rfl
        rw [hBz, hshift, getD_mul_split_eval as B m' nn hAs hB x env]
        show MultiPoly.eval a x env * (0 : Real)
             + MultiPoly.eval (as.getD m' (MultiPoly.const 0)) x env * MultiPoly.eval (B.getD nn (MultiPoly.const 0)) x env
           = MultiPoly.eval ((a :: as).getD (m' + 1) (MultiPoly.const 0)) x env
             * MultiPoly.eval (B.getD nn (MultiPoly.const 0)) x env
        rw [show ((a :: as).getD (m' + 1) (MultiPoly.const 0)) = as.getD m' (MultiPoly.const 0) from rfl]
        mach_ring

end MultiPoly
end MultiPolyMod
end MachLib
