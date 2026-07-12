import MachLib.MultiVarToPoly

/-!
# Elimination / resultant certificate for `MultiVar 2` (Gate 2d, resultant Rung, brick 2)

The resultant's *purpose* is elimination: a nonzero univariate `R(x)` whose roots contain the
`x`-coordinates of the common zeros of `{p, q}`. The cleanest interface to that fact — decoupling it from
*how* `R` is constructed (pseudo-division / Sylvester, brick 3+) — is a **resultant certificate**: a
Bezout identity `u·p + v·q = R` with `R` `y`-free (a polynomial in `x` alone). At a common zero `p = q =
0`, the identity forces `R = 0`; and since `R` is `y`-free its value depends only on `x`, so the
`x`-coordinate is a root of the univariate `R`.

This file proves that reduction:
- `eval_yfree` — a `y`-free `MultiVar 2` (`degVar 1 = 0`) has value depending only on the `x`-coordinate.
- `certificate_xbound` — **Bezout obligation A, modulo the certificate**: given a certificate with a
  non-vanishing `R`, the distinct `x`-coordinates of common zeros number `≤ deg_x R`. Reuses
  `fiber_count` in the `x`-direction (`live = 0`).

What remains is discharging the certificate (constructing `u, v, R` with `deg_x R ≤ deg·deg`) — the
pseudo-division / resultant construction on `coeffsY` (`MultiVarCoeffY.lean`), brick 3.
-/

namespace MachLib
namespace MultiVarMod

open MachLib.MultiVarMod.MultiVar

/-- **A `y`-free polynomial's value depends only on `x`.** If `degVar 1 p = 0`, then `eval p` agrees on
any two environments sharing the `x`-coordinate (`env 0 = env' 0`). The `MultiVar` analogue of
`eval_dropLastY`. -/
theorem eval_yfree :
    ∀ (p : MultiVar 2), MultiVar.degVar (1 : Fin 2) p = 0 →
      ∀ (env env' : Fin 2 → Real), env 0 = env' 0 → MultiVar.eval p env = MultiVar.eval p env'
  | .const _, _, _, _, _ => rfl
  | .var j, hy, env, env', h0 => by
      have hj0 : j = (0 : Fin 2) := by
        by_cases h1 : j = (1 : Fin 2)
        · rw [h1] at hy; exact absurd hy (by decide)
        · apply Fin.ext
          show j.val = 0
          have hv : j.val ≠ 1 := fun hvv => h1 (Fin.ext hvv)
          have := j.isLt
          omega
      subst hj0
      show MultiVar.eval (MultiVar.var (0 : Fin 2)) env = MultiVar.eval (MultiVar.var (0 : Fin 2)) env'
      simp only [MultiVar.eval_var]
      exact h0
  | .add p q, hy, env, env', h0 => by
      have hmax : Nat.max (MultiVar.degVar (1 : Fin 2) p) (MultiVar.degVar (1 : Fin 2) q) = 0 := hy
      have hp : MultiVar.degVar (1 : Fin 2) p = 0 :=
        Nat.le_zero.mp (hmax ▸ Nat.le_max_left (MultiVar.degVar (1 : Fin 2) p)
          (MultiVar.degVar (1 : Fin 2) q))
      have hq : MultiVar.degVar (1 : Fin 2) q = 0 :=
        Nat.le_zero.mp (hmax ▸ Nat.le_max_right (MultiVar.degVar (1 : Fin 2) p)
          (MultiVar.degVar (1 : Fin 2) q))
      show MultiVar.eval p env + MultiVar.eval q env = MultiVar.eval p env' + MultiVar.eval q env'
      rw [eval_yfree p hp env env' h0, eval_yfree q hq env env' h0]
  | .sub p q, hy, env, env', h0 => by
      have hmax : Nat.max (MultiVar.degVar (1 : Fin 2) p) (MultiVar.degVar (1 : Fin 2) q) = 0 := hy
      have hp : MultiVar.degVar (1 : Fin 2) p = 0 :=
        Nat.le_zero.mp (hmax ▸ Nat.le_max_left (MultiVar.degVar (1 : Fin 2) p)
          (MultiVar.degVar (1 : Fin 2) q))
      have hq : MultiVar.degVar (1 : Fin 2) q = 0 :=
        Nat.le_zero.mp (hmax ▸ Nat.le_max_right (MultiVar.degVar (1 : Fin 2) p)
          (MultiVar.degVar (1 : Fin 2) q))
      show MultiVar.eval p env - MultiVar.eval q env = MultiVar.eval p env' - MultiVar.eval q env'
      rw [eval_yfree p hp env env' h0, eval_yfree q hq env env' h0]
  | .mul p q, hy, env, env', h0 => by
      have hp : MultiVar.degVar (1 : Fin 2) p = 0 := by
        have h : MultiVar.degVar (1 : Fin 2) p + MultiVar.degVar (1 : Fin 2) q = 0 := hy
        omega
      have hq : MultiVar.degVar (1 : Fin 2) q = 0 := by
        have h : MultiVar.degVar (1 : Fin 2) p + MultiVar.degVar (1 : Fin 2) q = 0 := hy
        omega
      show MultiVar.eval p env * MultiVar.eval q env = MultiVar.eval p env' * MultiVar.eval q env'
      rw [eval_yfree p hp env env' h0, eval_yfree q hq env env' h0]

/-- **Bezout obligation A, modulo a resultant certificate.** Given a certificate `u·p + v·q = R` with `R`
`y`-free and not identically zero on the `x`-line through `env0`, the distinct `x`-coordinates of common
zeros of `{p, q}` (each carrying a witnessing common-zero environment) number `≤ deg_x R`. A common zero
forces `R = 0` (the identity), and `R` being `y`-free makes that a root of the univariate `R(x)` — so
`fiber_count` in the `x`-direction bounds them. -/
theorem certificate_xbound (p q u v R : MultiVar 2)
    (hcert : ∀ env : Fin 2 → Real,
      MultiVar.eval u env * MultiVar.eval p env + MultiVar.eval v env * MultiVar.eval q env
        = MultiVar.eval R env)
    (hRy : MultiVar.degVar (1 : Fin 2) R = 0)
    (a b : Real) (hab : a < b) (env0 : Fin 2 → Real)
    (hRne : ∃ x, MultiVar.eval R (fun j => if j = (0 : Fin 2) then x else env0 j) ≠ 0)
    (xs : List Real) (hnd : xs.Nodup)
    (hxs : ∀ x₀ ∈ xs, a < x₀ ∧ x₀ < b ∧
      ∃ envc : Fin 2 → Real, envc 0 = x₀ ∧ MultiVar.eval p envc = 0 ∧ MultiVar.eval q envc = 0) :
    xs.length ≤ MultiVar.degVar (0 : Fin 2) R := by
  refine fiber_count (0 : Fin 2) env0 R a b hab hRne xs hnd (fun x hx => ?_)
  obtain ⟨hxa, hxb, envc, henv0, hpc, hqc⟩ := hxs x hx
  refine ⟨hxa, hxb, ?_⟩
  have hxline0 : (fun j => if j = (0 : Fin 2) then x else env0 j) (0 : Fin 2) = envc 0 := by
    simp [henv0]
  rw [eval_yfree R hRy (fun j => if j = (0 : Fin 2) then x else env0 j) envc hxline0]
  rw [← hcert envc, hpc, hqc]
  mach_ring

end MultiVarMod
end MachLib
