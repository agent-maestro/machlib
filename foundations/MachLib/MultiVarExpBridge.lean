import MachLib.MultiVarResultant3
import MachLib.MultiVarToPoly
import MachLib.MultiVarEliminate
import MachLib.MultiVarCoeffYFree
import MachLib.SingleExpKhovanskii
import MachLib.Decimal

/-!
# The `u = eˣ` substitution bridge: `MultiVar 2 (x,u)` → `ExpPoly` (Gate 2d, Rung 1 brick 1.1)

The transcendental step of Rung 1. The `(x,u)`-resultant `R(x, u)` (a `MultiVar 2`, `x = 0`, `u = 1`) is
turned into an `ExpPoly` in `x` by substituting `u = eˣ`: `toExpPoly R` has coefficient list
`(coeffsY R).map mvToPoly` — the `u`-coefficients of `R` (polynomials in `x`) as `Poly`s. Then
`ExpPoly.eval (toExpPoly R) x = Σₖ pₖ(x)·(eˣ)ᵏ = R(x, eˣ)` (`eval_toExpPoly`), so the zeros of the
single-variable ExpPoly `x ↦ R(x, eˣ)` are exactly the `x`-coordinates where `R(x, eˣ) = 0`.

The crux is `evalAux_map_mvToPoly`: the offset-indexed `ExpPoly.evalAux` (which weighs the `k`-th mode by
`exp((o+k)x)`) matches the external-Horner `evalCoeffs` at `y = eˣ`, via `exp((o+1)x) = exp(ox)·exp x`
(`exp_add`) and `mvToPoly` correctness on `u`-free coefficients (`eval_yfree` + `toPoly1`). This is the
step that connects the multivariate elimination to the proven single-variable Khovanskii count — and it
uses only `rolle_ct`'s downstream (via ExpPoly), no new axiom.
-/

namespace MachLib
namespace MultiVarMod

open MachLib.MultiVarMod.MultiVar
open MachLib.PolynomialEvidence (Poly)
open MachLib.SingleExpKhovanskii (ExpPoly)
open MachLib.Real

/-- Convert a `u`-free coefficient (a `MultiVar 2` polynomial in `x = 0`) to a univariate `Poly` in `x`.
The frozen value of the (absent) `u` variable is irrelevant — pinned to `0`. -/
noncomputable def mvToPoly (c : MultiVar 2) : Poly := toPoly1 (0 : Fin 2) (fun _ => 0) c

/-- Substitute `u = eˣ` into a `MultiVar 2 (x,u)`, producing an `ExpPoly` in `x`: its coefficient list is
the `u`-coefficients of `R` (`coeffsY R`), each a `Poly` in `x`. -/
noncomputable def toExpPoly (R : MultiVar 2) : ExpPoly := ⟨(coeffsY R).map mvToPoly⟩

/-- `mvToPoly` is correct on a `u`-free coefficient: evaluating the `Poly` at `x` equals evaluating the
coefficient at `(x, eˣ)` (the frozen `u = 0` doesn't matter, `eval_yfree`). -/
theorem eval_mvToPoly (c : MultiVar 2) (hc : MultiVar.degVar (1 : Fin 2) c = 0) (x : Real) :
    Poly.eval (mvToPoly c) x
      = MultiVar.eval c (fun j => if j = (0 : Fin 2) then x else exp x) := by
  show Poly.eval (toPoly1 (0 : Fin 2) (fun _ => 0) c) x = _
  rw [eval_toPoly1 (0 : Fin 2) (fun _ => 0) x c]
  exact eval_yfree c hc _ _ rfl

/-- **The evalAux ↔ external-Horner match.** The offset-indexed `ExpPoly.evalAux` of the substituted
coefficients equals `exp(o·x)` times the external-Horner sum at `y = eˣ`. Induction on the coefficient
list, using `exp((o+1)x) = exp(ox)·exp x`. Requires the coefficients `u`-free (they are: `coeffsY_yfree`). -/
theorem evalAux_map_mvToPoly (x : Real) :
    ∀ (cs : List (MultiVar 2)) (o : Nat), (∀ c ∈ cs, MultiVar.degVar (1 : Fin 2) c = 0) →
      ExpPoly.evalAux (cs.map mvToPoly) o x
        = exp (natCast o * x)
          * evalCoeffs cs (fun j => if j = (0 : Fin 2) then x else exp x)
  | [], o, _ => by
      show (0 : Real)
          = exp (natCast o * x) * evalCoeffs ([] : List (MultiVar 2))
              (fun j => if j = (0 : Fin 2) then x else exp x)
      rw [evalCoeffs_nil]; mach_ring
  | c :: cs, o, hc => by
      have hc0 : MultiVar.degVar (1 : Fin 2) c = 0 := hc c (List.mem_cons_self c cs)
      have hcs : ∀ d ∈ cs, MultiVar.degVar (1 : Fin 2) d = 0 :=
        fun d hd => hc d (List.mem_cons_of_mem c hd)
      show Poly.eval (mvToPoly c) x * exp (natCast o * x)
          + ExpPoly.evalAux (cs.map mvToPoly) (o + 1) x
          = exp (natCast o * x)
            * evalCoeffs (c :: cs) (fun j => if j = (0 : Fin 2) then x else exp x)
      rw [eval_mvToPoly c hc0 x, evalAux_map_mvToPoly x cs (o + 1) hcs, evalCoeffs_cons]
      have henvE1 : (if (1 : Fin 2) = 0 then x else exp x) = exp x := if_neg (by decide)
      have hexp : exp (natCast (o + 1) * x) = exp (natCast o * x) * exp x := by
        rw [natCast_succ, show (natCast o + 1) * x = natCast o * x + x from by mach_ring, exp_add]
      rw [henvE1, hexp]
      mach_ring

/-- **The substitution bridge is faithful.** `ExpPoly.eval (toExpPoly R) x = R(x, eˣ)` — evaluating the
substituted ExpPoly at `x` equals evaluating `R` at `(x, eˣ)`. -/
theorem eval_toExpPoly (R : MultiVar 2) (x : Real) :
    (toExpPoly R).eval x
      = MultiVar.eval R (fun j => if j = (0 : Fin 2) then x else exp x) := by
  show ExpPoly.evalAux ((coeffsY R).map mvToPoly) 0 x = _
  rw [evalAux_map_mvToPoly x (coeffsY R) 0 (coeffsY_yfree R),
    ← eval_coeffsY (fun j => if j = (0 : Fin 2) then x else exp x) R]
  have h1 : exp (natCast 0 * x) = 1 := by
    rw [show (natCast 0 : Real) = 0 from natCast_zero, show (0 : Real) * x = 0 from by mach_ring,
      exp_zero]
  rw [h1]; mach_ring

end MultiVarMod
end MachLib
