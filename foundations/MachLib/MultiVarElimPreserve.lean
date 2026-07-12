import MachLib.MultiVarElimResultant

/-!
# Elimination preserves freeness in the OTHER variables (Gate 2d, M.0-f)

For iterated elimination (the mixed-exponential reduction eliminates `x` then `y`), the resultant must stay
free in the *already-eliminated* variables: after eliminating `x`, the intermediate is `x`-free; eliminating
`y` from it must keep it `x`-free so the final `R(w,u)` is a genuine polynomial in `(w,u)` only.

`coeffsElim_pres_free`: if `p` is `i'`-free then every coefficient of `coeffsElim i p` is `i'`-free (any
`i'`, including `i' ≠ i`). `resultantElim_pres_free`: eliminating `i` from `i'`-free `p, q` gives an
`i'`-free resultant. Mathlib-free.
-/

namespace MachLib
namespace MultiVarMod
namespace ElimK

open MachLib.MultiVarMod.MultiVar

/-- **`coeffsElim` preserves `i'`-freeness of the input** (for any `i'`, in particular `i' ≠ i`). -/
theorem coeffsElim_pres_free {k : Nat} (i i' : Fin k) :
    ∀ p : MultiVar k, MultiVar.degVar i' p = 0 → ∀ c ∈ coeffsElim i p, MultiVar.degVar i' c = 0
  | .const _, _ => by
      intro c hc
      simp only [coeffsElim, List.mem_singleton] at hc
      subst hc; rfl
  | .var j, hp => by
      intro c hc
      by_cases h : j = i
      · rw [coeffsElim, if_pos h] at hc
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> rfl
      · rw [coeffsElim, if_neg h] at hc
        simp only [List.mem_singleton] at hc
        subst hc; exact hp
  | .add p q, hp => by
      intro c hc
      have hp0 : MultiVar.degVar i' p = 0 := Nat.le_zero.mp (by rw [← hp]; exact Nat.le_max_left _ _)
      have hq0 : MultiVar.degVar i' q = 0 := Nat.le_zero.mp (by rw [← hp]; exact Nat.le_max_right _ _)
      exact addC_ifree (coeffsElim i p) (coeffsElim i q)
        (coeffsElim_pres_free i i' p hp0) (coeffsElim_pres_free i i' q hq0) c hc
  | .sub p q, hp => by
      intro c hc
      have hp0 : MultiVar.degVar i' p = 0 := Nat.le_zero.mp (by rw [← hp]; exact Nat.le_max_left _ _)
      have hq0 : MultiVar.degVar i' q = 0 := Nat.le_zero.mp (by rw [← hp]; exact Nat.le_max_right _ _)
      exact subC_ifree (coeffsElim i p) (coeffsElim i q)
        (coeffsElim_pres_free i i' p hp0) (coeffsElim_pres_free i i' q hq0) c hc
  | .mul p q, hp => by
      intro c hc
      have hp0 : MultiVar.degVar i' p = 0 :=
        Nat.le_zero.mp (by rw [← hp]; exact Nat.le_add_right _ _)
      have hq0 : MultiVar.degVar i' q = 0 :=
        Nat.le_zero.mp (by rw [← hp]; exact Nat.le_add_left _ _)
      exact mulC_ifree (coeffsElim i p) (coeffsElim i q)
        (coeffsElim_pres_free i i' p hp0) (coeffsElim_pres_free i i' q hq0) c hc

/-- **Eliminating `i` preserves `i'`-freeness of the system.** -/
theorem resultantElim_pres_free {k : Nat} (i i' : Fin k) (p q : MultiVar k) (fuel : Nat)
    (hp : MultiVar.degVar i' p = 0) (hq : MultiVar.degVar i' q = 0) :
    MultiVar.degVar i' (resultantElim i p q fuel) = 0 :=
  getLastD_ifree (prsLoopK fuel (coeffsElim i p) (coeffsElim i q))
    (prsLoopK_ifree fuel (coeffsElim i p) (coeffsElim i q)
      (coeffsElim_pres_free i i' p hp) (coeffsElim_pres_free i i' q hq))

end ElimK
end MultiVarMod
end MachLib
