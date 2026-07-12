import MachLib.MultiVarEliminate

/-!
# The 2×2 (linear-in-y) resultant certificate for `MultiVar 2` (Gate 2d, resultant Rung, brick 3a)

The general resultant construction (pseudo-remainder sequence, brick 3) needs a canonicalization layer to
detect zero leading coefficients — a genuine subsystem. This file discharges the certificate for the
first nontrivial case that needs **no** iteration and **no** canonicalization: `p, q` both **linear in
y**, `p = p₁·y + p₀`, `q = q₁·y + q₀` (coefficients `y`-free). Their resultant is the 2×2
cross-determinant

    R = p₁·q₀ − p₀·q₁,

which is `y`-free and vanishes at every common zero (Cramer: `p₁y+p₀ = q₁y+q₀ = 0 ⟹ p₁q₀ − p₀q₁ = 0`).
Fed to `xcoords_bound_of_vanishing`, this closes Bezout obligation A for a genuine multivariate system —
demonstrating the whole certificate pipeline end-to-end. General `p` (linear `q`) needs the homogenizing
powers `q₁^k`; general `q` needs the PRS + canonicalization (brick 3, a fresh subsystem).
-/

namespace MachLib
namespace MultiVarMod

open MachLib.MultiVarMod.MultiVar

/-- The 2×2 resultant of `p = p₁·y + p₀` and `q = q₁·y + q₀`: the cross-determinant `p₁·q₀ − p₀·q₁`. -/
noncomputable def resLinLin (p0 p1 q0 q1 : MultiVar 2) : MultiVar 2 :=
  MultiVar.sub (MultiVar.mul p1 q0) (MultiVar.mul p0 q1)

/-- The 2×2 resultant is `y`-free when the four coefficients are. -/
theorem resLinLin_yfree (p0 p1 q0 q1 : MultiVar 2)
    (h0 : MultiVar.degVar (1 : Fin 2) p0 = 0) (h1 : MultiVar.degVar (1 : Fin 2) p1 = 0)
    (h2 : MultiVar.degVar (1 : Fin 2) q0 = 0) (h3 : MultiVar.degVar (1 : Fin 2) q1 = 0) :
    MultiVar.degVar (1 : Fin 2) (resLinLin p0 p1 q0 q1) = 0 := by
  show Nat.max (MultiVar.degVar (1 : Fin 2) p1 + MultiVar.degVar (1 : Fin 2) q0)
        (MultiVar.degVar (1 : Fin 2) p0 + MultiVar.degVar (1 : Fin 2) q1) = 0
  rw [h0, h1, h2, h3]; decide

/-- **The 2×2 resultant vanishes at a common zero.** If `p₁·y + p₀ = 0` and `q₁·y + q₀ = 0` at `env`
(i.e. `p` and `q` both vanish there, with `y = env 1`), then `R = p₁q₀ − p₀q₁ = 0`. Cramer, via the
identity `p₁q₀ − p₀q₁ = p₁·(q₁y+q₀) − q₁·(p₁y+p₀)`. -/
theorem resLinLin_vanish (p0 p1 q0 q1 : MultiVar 2) (env : Fin 2 → Real)
    (hp : MultiVar.eval p1 env * env 1 + MultiVar.eval p0 env = 0)
    (hq : MultiVar.eval q1 env * env 1 + MultiVar.eval q0 env = 0) :
    MultiVar.eval (resLinLin p0 p1 q0 q1) env = 0 := by
  show MultiVar.eval p1 env * MultiVar.eval q0 env
      - MultiVar.eval p0 env * MultiVar.eval q1 env = 0
  have key : MultiVar.eval p1 env * MultiVar.eval q0 env
        - MultiVar.eval p0 env * MultiVar.eval q1 env
      = MultiVar.eval p1 env * (MultiVar.eval q1 env * env 1 + MultiVar.eval q0 env)
        - MultiVar.eval q1 env * (MultiVar.eval p1 env * env 1 + MultiVar.eval p0 env) := by
        mach_mpoly [MultiVar.eval p1 env, MultiVar.eval q0 env, MultiVar.eval p0 env,
          MultiVar.eval q1 env, env 1]
  rw [key, hp, hq]
  mach_ring

/-- **Bezout obligation A for a linear×linear system.** With `p = p₁y+p₀`, `q = q₁y+q₀` (coefficients
`y`-free) presented by their evaluation laws, and the 2×2 resultant `R = p₁q₀−p₀q₁` not identically zero,
the distinct `x`-coordinates of common zeros number `≤ deg_x R`. The certificate pipeline
(`resLinLin_vanish` → `xcoords_bound_of_vanishing`) closing end-to-end on a genuine multivariate system. -/
theorem xbound_linlin (p q p0 p1 q0 q1 : MultiVar 2)
    (hp0 : MultiVar.degVar (1 : Fin 2) p0 = 0) (hp1 : MultiVar.degVar (1 : Fin 2) p1 = 0)
    (hq0 : MultiVar.degVar (1 : Fin 2) q0 = 0) (hq1 : MultiVar.degVar (1 : Fin 2) q1 = 0)
    (hpeval : ∀ env : Fin 2 → Real,
      MultiVar.eval p env = MultiVar.eval p1 env * env 1 + MultiVar.eval p0 env)
    (hqeval : ∀ env : Fin 2 → Real,
      MultiVar.eval q env = MultiVar.eval q1 env * env 1 + MultiVar.eval q0 env)
    (a b : Real) (hab : a < b) (env0 : Fin 2 → Real)
    (hRne : ∃ x, MultiVar.eval (resLinLin p0 p1 q0 q1)
      (fun j => if j = (0 : Fin 2) then x else env0 j) ≠ 0)
    (xs : List Real) (hnd : xs.Nodup)
    (hxs : ∀ x₀ ∈ xs, a < x₀ ∧ x₀ < b ∧
      ∃ envc : Fin 2 → Real, envc 0 = x₀ ∧ MultiVar.eval p envc = 0 ∧ MultiVar.eval q envc = 0) :
    xs.length ≤ MultiVar.degVar (0 : Fin 2) (resLinLin p0 p1 q0 q1) := by
  refine xcoords_bound_of_vanishing p q (resLinLin p0 p1 q0 q1)
    (fun env hpz hqz => resLinLin_vanish p0 p1 q0 q1 env ?_ ?_)
    (resLinLin_yfree p0 p1 q0 q1 hp0 hp1 hq0 hq1) a b hab env0 hRne xs hnd hxs
  · rw [← hpeval env]; exact hpz
  · rw [← hqeval env]; exact hqz

end MultiVarMod
end MachLib
