import MachLib.MultiVarPRSYFree
import MachLib.MultiVarCoeffY
import MachLib.MultiVarEliminate

/-!
# The general-q resultant → Bezout obligation A (Gate 2d, resultant brick 3c-4c-3, CAPSTONE)

Assembles the polynomial-remainder sequence into the resultant and the multivariate Bezout bound for an
**arbitrary** system `{p, q}` in `MultiVar 2`. `prsResultant p q fuel` runs `prsLoop` on the
`y`-coefficient lists and reads off the eliminated remainder (`getLastD`). When the loop has driven the
system to a `y`-free remainder (`hterm : length ≤ 1` — the loop eliminated `y`), that remainder is:
* `y`-free (`prsResultant_yfree`, from `prsLoop_yfree` + `coeffsY_yfree`), and
* vanishing at every common zero (`prsResultant_vanish`, from `prsLoop_vanish` + `eval_coeffsY`).

Fed to `xcoords_bound_of_vanishing`, this gives `prsResultant_xbound`: **Bezout obligation A for a general
`p, q`** — the distinct `x`-coordinates of common zeros number `≤ deg_x (resultant)`. Modulo `hterm` (the
PRS terminates — a standard fact not formalized here) and the caller's non-degeneracy `hRne` (the
resultant is not identically zero, i.e. `p, q` share no vertical component). `rolle_ct` + Classical only,
no new axiom.
-/

namespace MachLib
namespace MultiVarMod

open MachLib.MultiVarMod.MultiVar

/-- On a `y`-free-representing list (`length ≤ 1`), the single coefficient (`getLastD`) evaluates to the
whole Horner sum. -/
theorem evalCoeffs_getLastD_of_length_le_one (env : Fin 2 → Real) :
    ∀ (l : List (MultiVar 2)), l.length ≤ 1 →
      MultiVar.eval (l.getLastD (MultiVar.const 0)) env = evalCoeffs l env
  | [], _ => rfl
  | [c], _ => by
      show MultiVar.eval c env = evalCoeffs [c] env
      simp only [evalCoeffs_cons, evalCoeffs_nil]
      mach_ring
  | _ :: _ :: _, h => by simp only [List.length_cons] at h; omega

/-- The resultant of `p, q` (eliminating `y`): the remainder the PRS loop reads off. -/
noncomputable def prsResultant (p q : MultiVar 2) (fuel : Nat) : MultiVar 2 :=
  (prsLoop fuel (coeffsY p) (coeffsY q)).getLastD (MultiVar.const 0)

/-- The resultant is `y`-free (a polynomial in `x`). -/
theorem prsResultant_yfree (p q : MultiVar 2) (fuel : Nat) :
    MultiVar.degVar (1 : Fin 2) (prsResultant p q fuel) = 0 :=
  getLastD_yfree (prsLoop fuel (coeffsY p) (coeffsY q))
    (prsLoop_yfree fuel (coeffsY p) (coeffsY q) (coeffsY_yfree p) (coeffsY_yfree q))

/-- **The resultant vanishes at every common zero** of `{p, q}` (when the PRS eliminated `y`). -/
theorem prsResultant_vanish (p q : MultiVar 2) (fuel : Nat)
    (hterm : (prsLoop fuel (coeffsY p) (coeffsY q)).length ≤ 1)
    (env : Fin 2 → Real) (hp : MultiVar.eval p env = 0) (hq : MultiVar.eval q env = 0) :
    MultiVar.eval (prsResultant p q fuel) env = 0 := by
  show MultiVar.eval ((prsLoop fuel (coeffsY p) (coeffsY q)).getLastD (MultiVar.const 0)) env = 0
  rw [evalCoeffs_getLastD_of_length_le_one env _ hterm]
  exact prsLoop_vanish env fuel (coeffsY p) (coeffsY q)
    (by rw [← eval_coeffsY]; exact hp) (by rw [← eval_coeffsY]; exact hq)

/-- **Bezout obligation A for a general system `{p, q}`.** With the PRS having eliminated `y`
(`hterm`) and the resultant not identically zero (`hRne`), the distinct `x`-coordinates of common zeros
number `≤ deg_x (prsResultant p q fuel)`. The general-q multivariate Bezout bound — closing the resultant
arc. -/
theorem prsResultant_xbound (p q : MultiVar 2) (fuel : Nat)
    (hterm : (prsLoop fuel (coeffsY p) (coeffsY q)).length ≤ 1)
    (a b : Real) (hab : a < b) (env0 : Fin 2 → Real)
    (hRne : ∃ x, MultiVar.eval (prsResultant p q fuel)
      (fun j => if j = (0 : Fin 2) then x else env0 j) ≠ 0)
    (xs : List Real) (hnd : xs.Nodup)
    (hxs : ∀ x₀ ∈ xs, a < x₀ ∧ x₀ < b ∧
      ∃ envc : Fin 2 → Real, envc 0 = x₀ ∧ MultiVar.eval p envc = 0 ∧ MultiVar.eval q envc = 0) :
    xs.length ≤ MultiVar.degVar (0 : Fin 2) (prsResultant p q fuel) :=
  xcoords_bound_of_vanishing p q (prsResultant p q fuel)
    (fun env hp hq => prsResultant_vanish p q fuel hterm env hp hq)
    (prsResultant_yfree p q fuel) a b hab env0 hRne xs hnd hxs

/-- Canonical fuel: `|coeffsY p| + |coeffsY q|` — provably enough for the PRS to eliminate `y`
(`prsLoop_terminates`). -/
noncomputable def prsFuel (p q : MultiVar 2) : Nat := (coeffsY p).length + (coeffsY q).length

theorem prsFuel_hterm (p q : MultiVar 2) :
    (prsLoop (prsFuel p q) (coeffsY p) (coeffsY q)).length ≤ 1 :=
  prsLoop_terminates (prsFuel p q) (coeffsY p) (coeffsY q) (Nat.le_refl _)

/-- **Bezout obligation A, UNCONDITIONAL** (no `hterm`): at the canonical fuel `prsFuel`, the PRS
provably eliminates `y` (`prsFuel_hterm`), so the distinct x-coordinates of common zeros number `≤ deg_x`
of the resultant — modulo only the non-degeneracy `hRne`. -/
theorem prsResultant_xbound_uncond (p q : MultiVar 2)
    (a b : Real) (hab : a < b) (env0 : Fin 2 → Real)
    (hRne : ∃ x, MultiVar.eval (prsResultant p q (prsFuel p q))
      (fun j => if j = (0 : Fin 2) then x else env0 j) ≠ 0)
    (xs : List Real) (hnd : xs.Nodup)
    (hxs : ∀ x₀ ∈ xs, a < x₀ ∧ x₀ < b ∧
      ∃ envc : Fin 2 → Real, envc 0 = x₀ ∧ MultiVar.eval p envc = 0 ∧ MultiVar.eval q envc = 0) :
    xs.length ≤ MultiVar.degVar (0 : Fin 2) (prsResultant p q (prsFuel p q)) :=
  prsResultant_xbound p q (prsFuel p q) (prsFuel_hterm p q) a b hab env0 hRne xs hnd hxs

end MultiVarMod
end MachLib
