import MachLib.MultiVarPRSAt
import MachLib.MultiVarCoeffY3

/-!
# The `(x,u)`-resultant of a `MultiVar 3` system (Gate 2d, Rung 1 brick 1.0 — CAPSTONE)

Eliminates `y` from a system `{P, Q}` in `MultiVar 3` `(x, y, u)` and reads off the resultant `R(x, u)` — a
`MultiVar 2` in `(x, u)` — which **vanishes at every common zero**. The PRS runs on the `(x,u)`-coefficient
lists (`coeffsY3`) via the *generic* `prsLoop`/`reduceStep` (reused verbatim from the polynomial layer),
and its vanishing invariant is the external-Horner `prsLoop_vanish_at`. Because the coefficients already
drop `y`, the remainder is automatically a polynomial in `(x, u)` — no `y`-freeness obligation.

Termination is discharged unconditionally by the *same* `prsLoop_terminates` (structural, evaluation-
independent): at fuel `prsFuel3 = |coeffsY3 P| + |coeffsY3 Q|` the loop has driven the pair to length ≤ 1,
so `prsResultant3_vanish_uncond` needs no `hterm`. This is the elimination half of Rung 1; the remaining
`u = eˣ` substitution (brick 1.1) turns `R(x, u)` into an `ExpPoly` counted by the single-variable bound.
-/

namespace MachLib
namespace MultiVarMod

open MachLib.MultiVarMod.MultiVar

/-- On a length-`≤1` list, the single coefficient (`getLastD`) evaluates to the whole external-Horner
sum. -/
theorem evalCoeffsAt_getLastD_of_length_le_one (env : Fin 2 → Real) (yv : Real) :
    ∀ (l : List (MultiVar 2)), l.length ≤ 1 →
      MultiVar.eval (l.getLastD (MultiVar.const 0)) env = evalCoeffsAt l env yv
  | [], _ => rfl
  | [c], _ => by
      show MultiVar.eval c env = evalCoeffsAt [c] env yv
      simp only [evalCoeffsAt_cons, evalCoeffsAt_nil]
      mach_ring
  | _ :: _ :: _, h => by simp only [List.length_cons] at h; omega

/-- The resultant `R(x, u) = Res_y(P, Q)` (eliminating `y`): the `MultiVar 2` remainder the PRS reads off. -/
noncomputable def prsResultant3 (P Q : MultiVar 3) (fuel : Nat) : MultiVar 2 :=
  (prsLoop fuel (coeffsY3 P) (coeffsY3 Q)).getLastD (MultiVar.const 0)

/-- **The resultant vanishes at every common zero** of `{P, Q}` (when the PRS eliminated `y`). Evaluated in
`(x, u)` with `env2 0 = env3 0` (x), `env2 1 = env3 2` (u); the eliminated `y = env3 1` is supplied as the
external Horner value. -/
theorem prsResultant3_vanish (P Q : MultiVar 3) (fuel : Nat)
    (hterm : (prsLoop fuel (coeffsY3 P) (coeffsY3 Q)).length ≤ 1)
    (env3 : Fin 3 → Real) (env2 : Fin 2 → Real)
    (h0 : env2 0 = env3 0) (h2 : env2 1 = env3 2)
    (hP : MultiVar.eval P env3 = 0) (hQ : MultiVar.eval Q env3 = 0) :
    MultiVar.eval (prsResultant3 P Q fuel) env2 = 0 := by
  show MultiVar.eval ((prsLoop fuel (coeffsY3 P) (coeffsY3 Q)).getLastD (MultiVar.const 0)) env2 = 0
  rw [evalCoeffsAt_getLastD_of_length_le_one env2 (env3 1) _ hterm]
  exact prsLoop_vanish_at env2 (env3 1) fuel (coeffsY3 P) (coeffsY3 Q)
    (by rw [← eval_coeffsY3 env3 env2 (env3 1) h0 h2 rfl]; exact hP)
    (by rw [← eval_coeffsY3 env3 env2 (env3 1) h0 h2 rfl]; exact hQ)

/-- Canonical fuel: `|coeffsY3 P| + |coeffsY3 Q|` — provably enough for the PRS to eliminate `y`. -/
noncomputable def prsFuel3 (P Q : MultiVar 3) : Nat := (coeffsY3 P).length + (coeffsY3 Q).length

theorem prsFuel3_hterm (P Q : MultiVar 3) :
    (prsLoop (prsFuel3 P Q) (coeffsY3 P) (coeffsY3 Q)).length ≤ 1 :=
  prsLoop_terminates (prsFuel3 P Q) (coeffsY3 P) (coeffsY3 Q) (Nat.le_refl _)

/-- **The resultant vanishes at every common zero, UNCONDITIONALLY** (no `hterm`): at the canonical fuel
`prsFuel3` the PRS provably eliminates `y`, so `R(x, u)` vanishes wherever `P` and `Q` do. The elimination
half of Rung 1 — `rolle_ct` + Classical, ZERO new axiom. -/
theorem prsResultant3_vanish_uncond (P Q : MultiVar 3)
    (env3 : Fin 3 → Real) (env2 : Fin 2 → Real)
    (h0 : env2 0 = env3 0) (h2 : env2 1 = env3 2)
    (hP : MultiVar.eval P env3 = 0) (hQ : MultiVar.eval Q env3 = 0) :
    MultiVar.eval (prsResultant3 P Q (prsFuel3 P Q)) env2 = 0 :=
  prsResultant3_vanish P Q (prsFuel3 P Q) (prsFuel3_hterm P Q) env3 env2 h0 h2 hP hQ

end MultiVarMod
end MachLib
