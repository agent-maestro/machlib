import MachLib.MultiVarElimPRS

/-!
# The polymorphic `MultiVar k` resultant — CAPSTONE of M.0 (Gate 2d)

Eliminates **any chosen index `i`** from two `MultiVar k` polynomials `p, q` and reads off the resultant
`Res_{x_i}(p, q)` — a `MultiVar k` that is **`i`-free** (`degVar i = 0`, a polynomial in the other `k−1`
variables) and **vanishes at every common zero**, UNCONDITIONALLY (`resultantElim_vanish_uncond`, via the
structural `prsLoopK_terminates`). This is the arity/index-polymorphic generalization of `prsResultant`
(hardwired to `MultiVar 2`, index 1) and `prsResultant3`, and the engine for the mixed-exponential
reduction: eliminate `x`, then `y`, from `{P, Q, w−g}` to reach a relation in `(w, u)`. Pure polynomial
algebra — axioms `propext`/`Classical`/`Quot.sound`/`MachLib.Real`, no analysis.
-/

namespace MachLib
namespace MultiVarMod
namespace ElimK

open MachLib.MultiVarMod.MultiVar

/-- On a length-`≤1` list, the single coefficient (`getLastD`) evaluates to the whole Horner sum. -/
theorem evalC_getLastD_of_length_le_one {k : Nat} (i : Fin k) (env : Fin k → Real) :
    ∀ (l : List (MultiVar k)), l.length ≤ 1 →
      MultiVar.eval (l.getLastD (MultiVar.const 0)) env = evalC i l env
  | [], _ => rfl
  | [c], _ => by
      show MultiVar.eval c env = evalC i [c] env
      simp only [evalC_cons, evalC_nil]; mach_ring
  | _ :: _ :: _, h => by simp only [List.length_cons] at h; omega

/-- The resultant `Res_{x_i}(p, q)` — the `MultiVar k` remainder the PRS reads off. -/
noncomputable def resultantElim {k : Nat} (i : Fin k) (p q : MultiVar k) (fuel : Nat) : MultiVar k :=
  (prsLoopK fuel (coeffsElim i p) (coeffsElim i q)).getLastD (MultiVar.const 0)

/-- The resultant is `i`-free (a polynomial in the other `k−1` variables). -/
theorem resultantElim_ifree {k : Nat} (i : Fin k) (p q : MultiVar k) (fuel : Nat) :
    MultiVar.degVar i (resultantElim i p q fuel) = 0 :=
  getLastD_ifree (prsLoopK fuel (coeffsElim i p) (coeffsElim i q))
    (prsLoopK_ifree fuel (coeffsElim i p) (coeffsElim i q)
      (coeffsElim_ifree i p) (coeffsElim_ifree i q))

/-- **The resultant vanishes at every common zero** (when the PRS eliminated `x_i`). -/
theorem resultantElim_vanish {k : Nat} (i : Fin k) (p q : MultiVar k) (fuel : Nat)
    (hterm : (prsLoopK fuel (coeffsElim i p) (coeffsElim i q)).length ≤ 1)
    (env : Fin k → Real) (hp : MultiVar.eval p env = 0) (hq : MultiVar.eval q env = 0) :
    MultiVar.eval (resultantElim i p q fuel) env = 0 := by
  show MultiVar.eval ((prsLoopK fuel (coeffsElim i p) (coeffsElim i q)).getLastD (MultiVar.const 0)) env
      = 0
  rw [evalC_getLastD_of_length_le_one i env _ hterm]
  exact prsLoopK_vanish i env fuel (coeffsElim i p) (coeffsElim i q)
    (by rw [← eval_coeffsElim i env p]; exact hp)
    (by rw [← eval_coeffsElim i env q]; exact hq)

/-- Canonical fuel — provably enough for the PRS to eliminate `x_i`. -/
noncomputable def prsFuelElim {k : Nat} (i : Fin k) (p q : MultiVar k) : Nat :=
  (coeffsElim i p).length + (coeffsElim i q).length

theorem prsFuelElim_hterm {k : Nat} (i : Fin k) (p q : MultiVar k) :
    (prsLoopK (prsFuelElim i p q) (coeffsElim i p) (coeffsElim i q)).length ≤ 1 :=
  prsLoopK_terminates (prsFuelElim i p q) (coeffsElim i p) (coeffsElim i q) (Nat.le_refl _)

/-- **The resultant vanishes at every common zero, UNCONDITIONALLY** (no `hterm`). The engine for iterated
elimination in the mixed-exponential reduction. -/
theorem resultantElim_vanish_uncond {k : Nat} (i : Fin k) (p q : MultiVar k)
    (env : Fin k → Real) (hp : MultiVar.eval p env = 0) (hq : MultiVar.eval q env = 0) :
    MultiVar.eval (resultantElim i p q (prsFuelElim i p q)) env = 0 :=
  resultantElim_vanish i p q (prsFuelElim i p q) (prsFuelElim_hterm i p q) env hp hq

end ElimK
end MultiVarMod
end MachLib
