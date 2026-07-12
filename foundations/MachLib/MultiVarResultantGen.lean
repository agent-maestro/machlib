import MachLib.MultiVarCoeffY
import MachLib.MultiVarEliminate

/-!
# The resultant of general `p` with linear `q` (Gate 2d, resultant Rung, brick 3b)

Extends the linear×linear cross-determinant (brick 3a) to **arbitrary `p`**, still with `q` linear in
`y` (`q = q₁·y + q₀`). Their resultant is the homogenized substitution `y := −q₀/q₁` cleared by `q₁^d`:

    resLin [p₀,…,p_d] q₀ q₁ = Σᵢ pᵢ·(−q₀)ⁱ·q₁^{d−i}    (d = deg_y p),

built by the recursion `resLin (p₀::ps') = q₁^{|ps'|}·p₀ + (−q₀)·resLin ps'`. The load-bearing fact is
`resLin_identity`: under the linear-`q` vanishing condition `q₀ = −q₁·y`, `eval (resLin ps q₀ q₁) =
q₁^{|ps|−1} · evalCoeffs ps` — so when `evalCoeffs ps = eval p = 0` at a common zero, the resultant
vanishes. No canonicalization is needed (only `q`'s single leading coefficient `q₁` enters, via powers).
-/

namespace MachLib
namespace MultiVarMod

open MachLib.MultiVarMod.MultiVar

theorem eval_pow_zero (p : MultiVar 2) (env : Fin 2 → Real) :
    MultiVar.eval (MultiVar.pow p 0) env = 1 := rfl
theorem eval_pow_succ (p : MultiVar 2) (k : Nat) (env : Fin 2 → Real) :
    MultiVar.eval (MultiVar.pow p (k + 1)) env
      = MultiVar.eval (MultiVar.pow p k) env * MultiVar.eval p env := rfl

/-- A power of a `y`-free base is `y`-free. -/
theorem degVar_pow_of_zero (i : Fin 2) (q : MultiVar 2) (hq : MultiVar.degVar i q = 0) :
    ∀ k : Nat, MultiVar.degVar i (MultiVar.pow q k) = 0
  | 0 => rfl
  | k + 1 => by
      show MultiVar.degVar i (MultiVar.pow q k) + MultiVar.degVar i q = 0
      rw [degVar_pow_of_zero i q hq k, hq]

/-- The resultant of `p = Σ pᵢ yⁱ` (coefficient list `ps`) with the linear `q = q₁y + q₀`. -/
noncomputable def resLin : List (MultiVar 2) → MultiVar 2 → MultiVar 2 → MultiVar 2
  | [], _, _ => MultiVar.const 0
  | p0 :: ps', q0, q1 =>
      MultiVar.add (MultiVar.mul (MultiVar.pow q1 ps'.length) p0)
        (MultiVar.mul (MultiVar.sub (MultiVar.const 0) q0) (resLin ps' q0 q1))

/-- Power-shift under a coefficient tail: `q₁ · q₁^{pred|ps'|} · evalCoeffs ps' = q₁^{|ps'|} ·
evalCoeffs ps'`. Holds for empty `ps'` (both sides `·0`) and nonempty (`eval_pow_succ`). -/
theorem pow_pred_mul (q1 : MultiVar 2) (env : Fin 2 → Real) :
    ∀ ps' : List (MultiVar 2),
      MultiVar.eval q1 env * MultiVar.eval (MultiVar.pow q1 ps'.length.pred) env
          * evalCoeffs ps' env
        = MultiVar.eval (MultiVar.pow q1 ps'.length) env * evalCoeffs ps' env
  | [] => by simp only [evalCoeffs_nil]; mach_ring
  | d :: ds => by
      show MultiVar.eval q1 env * MultiVar.eval (MultiVar.pow q1 ds.length) env * evalCoeffs (d :: ds) env
          = MultiVar.eval (MultiVar.pow q1 (ds.length + 1)) env * evalCoeffs (d :: ds) env
      rw [eval_pow_succ]
      mach_mpoly [MultiVar.eval q1 env, MultiVar.eval (MultiVar.pow q1 ds.length) env,
        evalCoeffs (d :: ds) env]

/-- **The closed-form identity.** Under the linear-`q` vanishing condition `q₀ = −q₁·y`,
`eval (resLin ps q₀ q₁) = q₁^{|ps|−1} · evalCoeffs ps`. -/
theorem resLin_identity (q0 q1 : MultiVar 2) (env : Fin 2 → Real)
    (hqc : MultiVar.eval q0 env = 0 - MultiVar.eval q1 env * env 1) :
    ∀ ps : List (MultiVar 2),
      MultiVar.eval (resLin ps q0 q1) env
        = MultiVar.eval (MultiVar.pow q1 ps.length.pred) env * evalCoeffs ps env
  | [] => by
      show MultiVar.eval (MultiVar.const 0) env
          = MultiVar.eval (MultiVar.pow q1 (List.length ([] : List (MultiVar 2))).pred) env
            * evalCoeffs [] env
      simp only [evalCoeffs_nil, MultiVar.eval_const]
      mach_ring
  | p0 :: ps' => by
      have IH := resLin_identity q0 q1 env hqc ps'
      have hpp := pow_pred_mul q1 env ps'
      show MultiVar.eval (MultiVar.add (MultiVar.mul (MultiVar.pow q1 ps'.length) p0)
              (MultiVar.mul (MultiVar.sub (MultiVar.const 0) q0) (resLin ps' q0 q1))) env
          = MultiVar.eval (MultiVar.pow q1 (p0 :: ps').length.pred) env * evalCoeffs (p0 :: ps') env
      rw [eval_add, eval_mul, eval_mul, eval_sub, eval_const, IH,
        show (p0 :: ps').length.pred = ps'.length from rfl, evalCoeffs_cons, hqc]
      have step : MultiVar.eval q1 env * env 1
            * (MultiVar.eval (MultiVar.pow q1 ps'.length.pred) env * evalCoeffs ps' env)
          = env 1 * (MultiVar.eval (MultiVar.pow q1 ps'.length) env * evalCoeffs ps' env) := by
        rw [← hpp]
        mach_mpoly [MultiVar.eval q1 env, env 1,
          MultiVar.eval (MultiVar.pow q1 ps'.length.pred) env, evalCoeffs ps' env]
      rw [show (0 : Real) - (0 - MultiVar.eval q1 env * env 1) = MultiVar.eval q1 env * env 1 from by
          mach_ring, step]
      mach_ring

/-- **The resultant vanishes at a common zero (linear `q`).** With `q₀ = −q₁·y` (i.e. `q = 0`) and
`evalCoeffs ps = eval p = 0`, `eval (resLin ps q₀ q₁) = 0`. -/
theorem resLin_vanish (ps : List (MultiVar 2)) (q0 q1 : MultiVar 2) (env : Fin 2 → Real)
    (hqc : MultiVar.eval q0 env = 0 - MultiVar.eval q1 env * env 1)
    (hp0 : evalCoeffs ps env = 0) :
    MultiVar.eval (resLin ps q0 q1) env = 0 := by
  rw [resLin_identity q0 q1 env hqc ps, hp0]; mach_ring

/-- The resultant is `y`-free when the coefficients of `p` and of the linear `q` are. -/
theorem resLin_yfree (q0 q1 : MultiVar 2)
    (hq0 : MultiVar.degVar (1 : Fin 2) q0 = 0) (hq1 : MultiVar.degVar (1 : Fin 2) q1 = 0) :
    ∀ ps : List (MultiVar 2), (∀ c ∈ ps, MultiVar.degVar (1 : Fin 2) c = 0) →
      MultiVar.degVar (1 : Fin 2) (resLin ps q0 q1) = 0
  | [], _ => rfl
  | p0 :: ps', hps => by
      have hp0 : MultiVar.degVar (1 : Fin 2) p0 = 0 := hps p0 (List.mem_cons_self _ _)
      have hrest := resLin_yfree q0 q1 hq0 hq1 ps' (fun c hc => hps c (List.mem_cons_of_mem _ hc))
      have h1 : MultiVar.degVar (1 : Fin 2) (MultiVar.mul (MultiVar.pow q1 ps'.length) p0) = 0 := by
        show MultiVar.degVar (1 : Fin 2) (MultiVar.pow q1 ps'.length)
            + MultiVar.degVar (1 : Fin 2) p0 = 0
        rw [degVar_pow_of_zero (1 : Fin 2) q1 hq1, hp0]
      have h2 : MultiVar.degVar (1 : Fin 2)
          (MultiVar.mul (MultiVar.sub (MultiVar.const 0) q0) (resLin ps' q0 q1)) = 0 := by
        show Nat.max (MultiVar.degVar (1 : Fin 2) (MultiVar.const 0)) (MultiVar.degVar (1 : Fin 2) q0)
            + MultiVar.degVar (1 : Fin 2) (resLin ps' q0 q1) = 0
        rw [hrest, hq0]; decide
      show Nat.max (MultiVar.degVar (1 : Fin 2) (MultiVar.mul (MultiVar.pow q1 ps'.length) p0))
          (MultiVar.degVar (1 : Fin 2)
            (MultiVar.mul (MultiVar.sub (MultiVar.const 0) q0) (resLin ps' q0 q1))) = 0
      rw [h1, h2]; decide

/-- **Bezout obligation A for a general `p` with a linear `q`.** With `p` given by its `y`-coefficient
list `ps` (`y`-free coefficients, `eval p = evalCoeffs ps`), `q = q₁y+q₀` (`y`-free coefficients), and the
resultant `resLin ps q₀ q₁` not identically zero, the distinct `x`-coordinates of common zeros number
`≤ deg_x (resLin ps q₀ q₁)`. The pipeline `resLin_vanish` → `xcoords_bound_of_vanishing`. -/
theorem xbound_lin (p q q0 q1 : MultiVar 2) (ps : List (MultiVar 2))
    (hps_eval : ∀ env : Fin 2 → Real, MultiVar.eval p env = evalCoeffs ps env)
    (hps_yfree : ∀ c ∈ ps, MultiVar.degVar (1 : Fin 2) c = 0)
    (hq0 : MultiVar.degVar (1 : Fin 2) q0 = 0) (hq1 : MultiVar.degVar (1 : Fin 2) q1 = 0)
    (hqeval : ∀ env : Fin 2 → Real,
      MultiVar.eval q env = MultiVar.eval q1 env * env 1 + MultiVar.eval q0 env)
    (a b : Real) (hab : a < b) (env0 : Fin 2 → Real)
    (hRne : ∃ x, MultiVar.eval (resLin ps q0 q1)
      (fun j => if j = (0 : Fin 2) then x else env0 j) ≠ 0)
    (xs : List Real) (hnd : xs.Nodup)
    (hxs : ∀ x₀ ∈ xs, a < x₀ ∧ x₀ < b ∧
      ∃ envc : Fin 2 → Real, envc 0 = x₀ ∧ MultiVar.eval p envc = 0 ∧ MultiVar.eval q envc = 0) :
    xs.length ≤ MultiVar.degVar (0 : Fin 2) (resLin ps q0 q1) := by
  refine xcoords_bound_of_vanishing p q (resLin ps q0 q1)
    (fun env hpz hqz => resLin_vanish ps q0 q1 env ?_ ?_)
    (resLin_yfree q0 q1 hq0 hq1 ps hps_yfree) a b hab env0 hRne xs hnd hxs
  · have : MultiVar.eval q1 env * env 1 + MultiVar.eval q0 env = 0 := by rw [← hqeval env]; exact hqz
    have hq0v : MultiVar.eval q0 env = 0 - MultiVar.eval q1 env * env 1 := by
      rw [← this]; mach_ring
    exact hq0v
  · rw [← hps_eval env]; exact hpz

end MultiVarMod
end MachLib
