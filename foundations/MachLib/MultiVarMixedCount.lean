import MachLib.MultiVarMixedElim
import MachLib.MultiVarRung1
import MachLib.ExpPolyEffectiveBound

/-!
# Mixed-exponential w-coordinate count (Gate 2d, M.2)

The transcendental step of the mixed-exponential reduction. The relation `R(w,u) = mixedResultant P Q wg`
(M.1) is `x`-free and `y`-free, so it restricts to a `MultiVar 2` in `(w,u)` (`restrict24`); substituting
`u = e^w` (the Rung 1.1 bridge `toExpPoly`, now in the variable `w`) gives the single-variable ExpPoly
`w ↦ R(w, e^w)`. Its zeros are counted by `expPoly_effective_bound`.

`mixed_wcoord_bound`: the distinct `w`-coordinates (`= g(x,y)` values) of solutions of `{P, Q, w−g}` along
`u = e^w` number `≤ |coeffs| + Σ simplified-deg` of `R(w, e^w)`. No multivariate Rolle — the transcendence
is confined to the single-variable `w`-step. (`eval_free`: a `MultiVar k` polynomial free in variable `i`
has `i`-independent evaluation — used to drop `R`'s frozen `x, y`.)
-/

namespace MachLib
namespace MultiVarMod
namespace ElimK

open MachLib.MultiVarMod.MultiVar
open MachLib.SingleExpKhovanskii (ExpPoly)
open MachLib.SingleExpKhovanskii.ExpPoly
open MachLib.Real

/-- **Evaluation is independent of a variable the polynomial is free in.** -/
theorem eval_free {k : Nat} (i : Fin k) :
    ∀ (p : MultiVar k), MultiVar.degVar i p = 0 →
      ∀ (env env' : Fin k → Real), (∀ j, j ≠ i → env j = env' j) →
        MultiVar.eval p env = MultiVar.eval p env'
  | .const c, _, _, _, _ => rfl
  | .var j, hp, env, env', h => by
      have hji : j ≠ i := fun he => by
        rw [he, show MultiVar.degVar i (MultiVar.var i) = 1 from by
          show (if i = i then 1 else 0) = 1; rw [if_pos rfl]] at hp
        exact absurd hp (by decide)
      show env j = env' j
      exact h j hji
  | .add p q, hp, env, env', h => by
      have hp0 : MultiVar.degVar i p = 0 := Nat.le_zero.mp (by rw [← hp]; exact Nat.le_max_left _ _)
      have hq0 : MultiVar.degVar i q = 0 := Nat.le_zero.mp (by rw [← hp]; exact Nat.le_max_right _ _)
      show MultiVar.eval p env + MultiVar.eval q env = MultiVar.eval p env' + MultiVar.eval q env'
      rw [eval_free i p hp0 env env' h, eval_free i q hq0 env env' h]
  | .sub p q, hp, env, env', h => by
      have hp0 : MultiVar.degVar i p = 0 := Nat.le_zero.mp (by rw [← hp]; exact Nat.le_max_left _ _)
      have hq0 : MultiVar.degVar i q = 0 := Nat.le_zero.mp (by rw [← hp]; exact Nat.le_max_right _ _)
      show MultiVar.eval p env - MultiVar.eval q env = MultiVar.eval p env' - MultiVar.eval q env'
      rw [eval_free i p hp0 env env' h, eval_free i q hq0 env env' h]
  | .mul p q, hp, env, env', h => by
      have hp0 : MultiVar.degVar i p = 0 := Nat.le_zero.mp (by rw [← hp]; exact Nat.le_add_right _ _)
      have hq0 : MultiVar.degVar i q = 0 := Nat.le_zero.mp (by rw [← hp]; exact Nat.le_add_left _ _)
      show MultiVar.eval p env * MultiVar.eval q env = MultiVar.eval p env' * MultiVar.eval q env'
      rw [eval_free i p hp0 env env' h, eval_free i q hq0 env env' h]

/-- Restrict a `MultiVar 4` `(x,y,w,u)` to `MultiVar 2` `(w,u)`: `w:2↦0`, `u:3↦1`, and `x,y` frozen to `0`
(sound when the input is `x`- and `y`-free). -/
noncomputable def restrict24 : MultiVar 4 → MultiVar 2
  | .const c => MultiVar.const c
  | .var j   => if j = 2 then MultiVar.var 0 else if j = 3 then MultiVar.var 1 else MultiVar.const 0
  | .add p q => MultiVar.add (restrict24 p) (restrict24 q)
  | .sub p q => MultiVar.sub (restrict24 p) (restrict24 q)
  | .mul p q => MultiVar.mul (restrict24 p) (restrict24 q)

theorem eval_restrict24 (env2 : Fin 2 → Real) :
    ∀ R : MultiVar 4, MultiVar.eval (restrict24 R) env2
      = MultiVar.eval R (fun j => if j = 2 then env2 0 else if j = 3 then env2 1 else 0)
  | .const c => rfl
  | .var j => by
      show MultiVar.eval (if j = 2 then MultiVar.var 0 else if j = 3 then MultiVar.var 1
            else MultiVar.const 0) env2
          = (if j = 2 then env2 0 else if j = 3 then env2 1 else (0 : Real))
      by_cases h2 : j = 2
      · rw [if_pos h2, if_pos h2]; rfl
      · by_cases h3 : j = 3
        · rw [if_neg h2, if_pos h3, if_neg h2, if_pos h3]; rfl
        · rw [if_neg h2, if_neg h3, if_neg h2, if_neg h3]; rfl
  | .add p q => by
      show MultiVar.eval (restrict24 p) env2 + MultiVar.eval (restrict24 q) env2
          = MultiVar.eval p _ + MultiVar.eval q _
      rw [eval_restrict24 env2 p, eval_restrict24 env2 q]
  | .sub p q => by
      show MultiVar.eval (restrict24 p) env2 - MultiVar.eval (restrict24 q) env2
          = MultiVar.eval p _ - MultiVar.eval q _
      rw [eval_restrict24 env2 p, eval_restrict24 env2 q]
  | .mul p q => by
      show MultiVar.eval (restrict24 p) env2 * MultiVar.eval (restrict24 q) env2
          = MultiVar.eval p _ * MultiVar.eval q _
      rw [eval_restrict24 env2 p, eval_restrict24 env2 q]

/-- Evaluation is independent of TWO variables the polynomial is free in. -/
theorem eval_free2 {k : Nat} (i0 i1 : Fin k) (R : MultiVar k)
    (h0 : MultiVar.degVar i0 R = 0) (h1 : MultiVar.degVar i1 R = 0)
    (env env' : Fin k → Real) (h : ∀ j, j ≠ i0 → j ≠ i1 → env j = env' j) :
    MultiVar.eval R env = MultiVar.eval R env' := by
  have e1 : MultiVar.eval R env
      = MultiVar.eval R (fun j => if j = i0 then env' i0 else env j) :=
    eval_free i0 R h0 env _ (fun j hj => by rw [if_neg hj])
  have e2 : MultiVar.eval R (fun j => if j = i0 then env' i0 else env j) = MultiVar.eval R env' :=
    eval_free i1 R h1 _ env' (fun j hj => by
      by_cases h0j : j = i0
      · rw [if_pos h0j, h0j]
      · rw [if_neg h0j]; exact h j h0j hj)
  rw [e1, e2]

/-- **The substituted ExpPoly evaluated at `w` equals `R` at any `(x,y,w,e^w)`** (for `x,y`-free `R`). -/
theorem eval_toExpPoly_restrict24 (R : MultiVar 4)
    (hx : MultiVar.degVar (0 : Fin 4) R = 0) (hy : MultiVar.degVar (1 : Fin 4) R = 0)
    (w : Real) (env4 : Fin 4 → Real) (h2 : env4 2 = w) (h3 : env4 3 = exp w) :
    (toExpPoly (restrict24 R)).eval w = MultiVar.eval R env4 := by
  rw [eval_toExpPoly (restrict24 R) w,
    eval_restrict24 (fun j => if j = (0 : Fin 2) then w else exp w) R]
  refine eval_free2 (0 : Fin 4) (1 : Fin 4) R hx hy _ env4 ?_
  intro j hj0 hj1
  by_cases h2j : j = 2
  · subst h2j; simp [h2]
  · by_cases h3j : j = 3
    · subst h3j; simp [h3]
    · exfalso
      have e0 : j.val ≠ 0 := fun hv => hj0 (Fin.ext hv)
      have e1 : j.val ≠ 1 := fun hv => hj1 (Fin.ext hv)
      have e2 : j.val ≠ 2 := fun hv => h2j (Fin.ext hv)
      have e3 : j.val ≠ 3 := fun hv => h3j (Fin.ext hv)
      have := j.isLt; omega

/-- **Mixed-exponential w-coordinate count.** The distinct `w`-coordinates of solutions of `{P, Q, w−g}`
along `u = e^w` (each witnessed by an `env4` with `w = env4 2`, `u = e^w = env4 3`, and `P = Q = wg = 0`)
number `≤ |coeffs| + Σ simplified-deg` of the ExpPoly `w ↦ R(w, e^w)`, `R = mixedResultant P Q wg`. Reduces
to the single-variable Khovanskii bound; no multivariate Rolle. -/
theorem mixed_wcoord_bound (P Q wg : MultiVar 4) (a b : Real) (hab : a < b)
    (hne : ∃ w : Real, a < w ∧ w < b
      ∧ (toExpPoly (restrict24 (mixedResultant P Q wg))).eval w ≠ 0)
    (ws : List Real) (hnd : ws.Nodup)
    (hws : ∀ w₀ ∈ ws, a < w₀ ∧ w₀ < b ∧
      ∃ env4 : Fin 4 → Real, env4 2 = w₀ ∧ env4 3 = exp w₀ ∧
        MultiVar.eval P env4 = 0 ∧ MultiVar.eval Q env4 = 0 ∧ MultiVar.eval wg env4 = 0) :
    ws.length
      ≤ (toExpPoly (restrict24 (mixedResultant P Q wg))).coeffs.length
        + sumSimplifiedDegrees (toExpPoly (restrict24 (mixedResultant P Q wg))).coeffs := by
  apply expPoly_effective_bound (toExpPoly (restrict24 (mixedResultant P Q wg))) a b hab hne ws hnd
  intro w₀ hw₀
  obtain ⟨ha, hb, env4, h2, h3, hP, hQ, hwg⟩ := hws w₀ hw₀
  refine ⟨ha, hb, ?_⟩
  rw [eval_toExpPoly_restrict24 (mixedResultant P Q wg)
    (mixedResultant_xfree P Q wg) (mixedResultant_yfree P Q wg) w₀ env4 h2 h3]
  exact mixedResultant_vanish P Q wg env4 hP hQ hwg

end ElimK
end MultiVarMod
end MachLib
