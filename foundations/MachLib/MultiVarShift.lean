import MachLib.MultiVarCoeffY
import MachLib.MultiVarResultantGen

/-!
# Coefficient-list shift `shiftCoeffs` — the pseudo-division primitive (Gate 2d, resultant brick 3c-1)

The polynomial-remainder sequence for a **general** `q` (`deg_y q ≥ 2`) reduces `p` by `q` via
`q_lead·p − p_lead·yᵏ·q`. The `yᵏ·q` is `shiftCoeffs k` — prepend `k` zero coefficients (multiply the
`y`-polynomial by `yᵏ`). This file builds it and its eval law `evalCoeffs (shiftCoeffs k as) = yᵏ ·
evalCoeffs as` (with `yᵏ = eval (pow (var 1) k)`, kept opaque via `eval_pow_succ`).

**Key point (why brick 3c does NOT need canonicalization):** one reduction step produces a list whose
top coefficient cancels to something eval-zero but *formally* present (`X−X`). Applying `dropLast` removes
exactly that coefficient — so the formal length drops by one (termination) AND eval is preserved (the
dropped term is `0·yᵈ`). No identically-zero detection is needed. `shiftCoeffs` (here) and that dropLast
identity are the two atoms of the reduction step (brick 3c-2).
-/

namespace MachLib
namespace MultiVarMod

open MachLib.MultiVarMod.MultiVar

/-- Multiply a `y`-coefficient list by `yᵏ`: prepend `k` zero coefficients. -/
noncomputable def shiftCoeffs (k : Nat) (as : List (MultiVar 2)) : List (MultiVar 2) :=
  List.replicate k (MultiVar.const 0) ++ as

/-- **Shift eval law.** `evalCoeffs (shiftCoeffs k as) = yᵏ · evalCoeffs as`, with `yᵏ = eval(pow (var 1)
k)`. -/
theorem evalCoeffs_shiftCoeffs (as : List (MultiVar 2)) (env : Fin 2 → Real) :
    ∀ k : Nat,
      evalCoeffs (shiftCoeffs k as) env
        = MultiVar.eval (MultiVar.pow (MultiVar.var (1 : Fin 2)) k) env * evalCoeffs as env
  | 0 => by
      show evalCoeffs (List.replicate 0 (MultiVar.const 0) ++ as) env
          = MultiVar.eval (MultiVar.pow (MultiVar.var (1 : Fin 2)) 0) env * evalCoeffs as env
      rw [eval_pow_zero]
      simp only [List.replicate, List.nil_append]
      mach_ring
  | k + 1 => by
      show evalCoeffs (List.replicate (k + 1) (MultiVar.const 0) ++ as) env
          = MultiVar.eval (MultiVar.pow (MultiVar.var (1 : Fin 2)) (k + 1)) env * evalCoeffs as env
      rw [eval_pow_succ,
        show List.replicate (k + 1) (MultiVar.const 0) ++ as
            = MultiVar.const 0 :: (List.replicate k (MultiVar.const 0) ++ as) from rfl,
        evalCoeffs_cons, MultiVar.eval_var, MultiVar.eval_const,
        show List.replicate k (MultiVar.const 0) ++ as = shiftCoeffs k as from rfl,
        evalCoeffs_shiftCoeffs as env k]
      mach_ring

end MultiVarMod
end MachLib
