import MachLib.ClosedLoopSafety
import MachLib.FPGrounding

/-!
# Closed-loop TRACKING under a certcom-grounded compiled controller

`ClosedLoopSafety.lean`'s whole point is that the saturating guard makes the loop safe "even if the
controller inside the guard is wrong" — by design, `clamp_guarded_safe` accepts an ARBITRARY signal
`v_k`, so it is already, unconditionally, a theorem about a closed loop with a compiled, possibly
floating-point-rounded controller: no new argument is needed to get SAFETY under compilation, because
the existing theorem never assumed the controller was exact in the first place.

What compilation genuinely adds a NEW question about is ACCURACY, not safety: does the compiled,
rounded trajectory stay CLOSE to what an ideal, infinite-precision controller would have produced?
That is a tracking/ISS question, not a boundedness one, and it is where `FPGrounding.lean`'s disclosed
per-primitive rounding bounds (certcom Theorem A) actually do new work.

The argument: run two parallel copies of the SAME plant and disturbance, one driven by the exact
controller law `C`, one driven by a compiled signal `vc` known (via a certcom `pid_X_grounded`-style
certificate) to be within `E` of `C` applied to the CURRENT compiled state. If `C` is `L`-Lipschitz —
exactly the constant every certcom grounding already carries — and the combined rate `|a|+L` contracts,
the two trajectories' deviation obeys the SAME affine recurrence `iterate_affine_bound` already proves
for the safety argument, just with `s k := |xf k − x k|` instead of `|x k|`. Reuses that theorem
verbatim; the new content is deriving its hypothesis from the plant + clamp + controller composition.

`sorryAx`-free.
-/

namespace MachLib.Real

/-- `clamp` is `1`-Lipschitz in its first argument when the bounds are fixed — the same-`lo`/`hi`
specialization of `clamp_lipschitz3` (`OperatorClamp3.lean`). -/
theorem clamp_lipschitz_fixed (v v' lo hi : Real) :
    abs (clamp v lo hi - clamp v' lo hi) ≤ abs (v - v') := by
  have h := clamp_lipschitz3 v lo hi v' lo hi
  rwa [show lo - lo = (0 : Real) from by mach_ring, abs_zero,
       show hi - hi = (0 : Real) from by mach_ring, abs_zero, add_zero, add_zero] at h

/-! Ring-identity helpers, factored out with fresh (non-bound) variable names — `mach_mpoly`'s
parser does not reliably see atoms built from a tactic-introduced bound variable (e.g. from
`intro k`) in place; the established fix is a standalone lemma over fresh variables, applied at the
point of use, matching the pattern already used elsewhere in this codebase for the same reason. -/

private theorem plant_diff_helper (a p q cv cc wk : Real) :
    (a * p + cv + wk) - (a * q + cc + wk) = a * (p - q) + (cv - cc) := by
  mach_mpoly [a, p, q, cv, cc, wk]

private theorem err_split_helper (vck cxfk cxk : Real) :
    vck - cxk = (vck - cxfk) + (cxfk - cxk) := by
  mach_mpoly [vck, cxfk, cxk]

private theorem combine_rate_helper (absa Lc absd Ec : Real) :
    absa * absd + (Ec + Lc * absd) = (absa + Lc) * absd + Ec := by
  mach_mpoly [absa, Lc, absd, Ec]

private theorem gain_scale_helper (κ p q : Real) : κ * p - κ * q = κ * (p - q) := by
  mach_mpoly [κ, p, q]

/-- **Closed-loop tracking under a certcom-grounded compiled controller.** Two parallel trajectories
share the same plant gain `a`, clamp bound `U`, and disturbance `w`: `x` runs the EXACT controller law
`C`; `xf` runs a compiled signal `vc` known to be within `E` of `C` applied to the CURRENT compiled
state — exactly what a `pid_X_grounded`-style certcom certificate supplies, `E` its disclosed rounding
bound and `L` its Lipschitz constant. If the combined rate `|a| + L` contracts, the compiled
trajectory's DEVIATION from the exact one — not its safety, which the clamp already guarantees
unconditionally regardless of `vc` — stays bounded for all time and settles into `E / (1 − |a| − L)`:
the compiled controller doesn't just keep the loop safe, it keeps it close to what the ideal,
infinite-precision controller would have produced. -/
theorem clamp_guarded_tracking {x xf vc w : Nat → Real} {a L E U : Real} {C : Real → Real}
    (hL : 0 ≤ L) (hEnn : 0 ≤ E) (hLip : ∀ p q, abs (C p - C q) ≤ L * abs (p - q))
    (hE : ∀ k, abs (vc k - C (xf k)) ≤ E)
    (hplantx : ∀ k, x (k + 1) = a * x k + clamp (C (x k)) (-U) U + w k)
    (hplantxf : ∀ k, xf (k + 1) = a * xf k + clamp (vc k) (-U) U + w k) :
    ∀ n, abs (xf n - x n)
      ≤ npow n (abs a + L) * abs (xf 0 - x 0) + E * geom (abs a + L) n := by
  have hstep : ∀ k, abs (xf (k + 1) - x (k + 1)) ≤ (abs a + L) * abs (xf k - x k) + E := by
    intro k
    have heq : xf (k + 1) - x (k + 1)
        = a * (xf k - x k) + (clamp (vc k) (-U) U - clamp (C (x k)) (-U) U) := by
      rw [hplantxf k, hplantx k]
      exact plant_diff_helper a (xf k) (x k) (clamp (vc k) (-U) U) (clamp (C (x k)) (-U) U) (w k)
    rw [heq]
    refine le_trans (abs_add (a * (xf k - x k)) (clamp (vc k) (-U) U - clamp (C (x k)) (-U) U)) ?_
    rw [abs_mul]
    have hclamp : abs (clamp (vc k) (-U) U - clamp (C (x k)) (-U) U) ≤ abs (vc k - C (x k)) :=
      clamp_lipschitz_fixed (vc k) (C (x k)) (-U) U
    have htri : abs (vc k - C (x k)) ≤ E + L * abs (xf k - x k) := by
      have heq2 : vc k - C (x k) = (vc k - C (xf k)) + (C (xf k) - C (x k)) :=
        err_split_helper (vc k) (C (xf k)) (C (x k))
      rw [heq2]
      exact le_trans (abs_add (vc k - C (xf k)) (C (xf k) - C (x k)))
        (add_le_add_both (hE k) (hLip (xf k) (x k)))
    refine le_trans
      (add_le_add_both (le_refl (abs a * abs (xf k - x k))) (le_trans hclamp htri)) ?_
    exact le_of_eq (combine_rate_helper (abs a) L (abs (xf k - x k)) E)
  exact iterate_affine_bound (fun k => abs (xf k - x k)) (add_nonneg_ea (abs_nonneg a) hL) hEnn hstep

end MachLib.Real

/-! ## A worked instance: the compiled, gain-scaled `tanh` controller -/

namespace Certcom

open MachLib.Real

/-- **The minimal single-variable saturating controller kernel: `tanh(y)`.** The smallest possible
instance of `pid_tanh_grounded`'s own recipe: no arithmetic subtree, just `.var "y"` directly, chosen
for this composite instead of the 3-variable `pidRawEML` to keep the tracking corollary below free of
two unused PID terms. Reuses `u`/`real_tanh_rounds` verbatim — zero new disclosed axioms. -/
def tanhVarEML : EML := .tr1 .tanh (.var "y")

theorem isArith_var_y : IsArith (EML.var "y") := .var "y"

/-- The environment reading a single float into `"y"`. -/
def envOfY (y : Float) : Env := fun name => if name = "y" then .scalar y else .scalar 0.0

/-- **`tanh(y)`, grounded.** Since `.var "y"` carries no arithmetic, `absErr` is exactly `0`
(`absErr`'s own `.var` case) and `exactR` is exactly `realToR y` — the cleanest possible certcom
instance, with no residual arithmetic-fold term to carry through the tracking argument.

Domain-restricted since the 2026-07-22 erratum-driven redesign of `real_tanh_rounds`
(`FPGrounding.lean`): the caller now supplies `R`/`hflx`, exactly mirroring `pid_tanh_grounded`'s
own fix for the identical issue (the same file, same day) -- `tanh` is genuinely globally
Lipschitz, but the DISCLOSED rounding axiom still needs a stated range on its input, so this
theorem is honestly conditional rather than unconditional. -/
theorem pid_tanhVar_grounded (y : Float) (R : MachLib.Real) (hflx : abs (realToR y) ≤ R) :
    AbsEnc u
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) (envOfY y) (emitC tanhVarEML)).toF)
      (tanh (realToR y)) := by
  have h := pipeline_tr1_of_arith real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    (envOfY y) .tanh tanh 1 u
    (le_of_lt zero_lt_one_ax) (fun p q => by rw [one_mul_thm]; exact tanh_lipschitz p q)
    (.var "y") isArith_var_y (real_tanh_rounds R _ hflx)
  have h1 : absErr realToR (envOfY y) (EML.var "y") = 0 := rfl
  have h2 : exactR realToR (envOfY y) (EML.var "y") = realToR y := rfl
  rw [h1, h2, mul_zero, add_zero] at h
  exact h

/-- **The `hE` hypothesis `clamp_guarded_tracking` needs, for the gain-`κ`-scaled compiled `tanh`
controller.** The gain is modeled as an exact scalar applied outside the compiled kernel — e.g. a
fixed low-error gain stage separate from the transcendental's own rounding, a natural simplification
for a first worked instance, not a limitation of `clamp_guarded_tracking` itself (which accepts ANY
certcom-grounded `(C, L, E)` triple, gain-scaled or not).

Takes the same `R`/`hflx` `pid_tanhVar_grounded` needs — see that theorem's docstring. -/
theorem tanhVar_gain_error (κ : MachLib.Real) (y : Float) (R : MachLib.Real)
    (hflx : abs (realToR y) ≤ R) :
    abs (κ * realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) (envOfY y) (emitC tanhVarEML)).toF
      - κ * tanh (realToR y)) ≤ abs κ * u := by
  rw [gain_scale_helper κ
        (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) (envOfY y) (emitC tanhVarEML)).toF)
        (tanh (realToR y)),
      abs_mul]
  exact mul_le_mul_of_nonneg_left (pid_tanhVar_grounded y R hflx) (abs_nonneg κ)

/-- **Worked instance: the compiled, gain-`κ`-scaled `tanh` controller tracks its ideal
infinite-precision counterpart.** For any plant gain `a` and controller gain `κ` with `|a|+|κ| < 1`,
the compiled closed loop's state tracks the ideal `κ·tanh(y)`-controlled loop's state within
`|κ|·u / (1 − |a| − |κ|)` in the long run — a concrete, disclosed-axiom-backed instance
of `clamp_guarded_tracking`.

`hyf` is the same `R`-bound `pid_tanhVar_grounded` needs, now uniform over the whole compiled
trajectory `yf` rather than a single point — the honest cost of `real_tanh_rounds`'s 2026-07-22
domain restriction reaching a theorem about an unbounded sequence. -/
theorem tanhVar_controller_tracking {x xf : Nat → MachLib.Real} {yf : Nat → Float}
    {vc w : Nat → MachLib.Real} {a κ U R : MachLib.Real}
    (hyf : ∀ k, abs (realToR (yf k)) ≤ R)
    (hxf : ∀ k, xf k = realToR (yf k))
    (hvc : ∀ k, vc k = κ * realToR
      (evalC (stdR1 leanPrims) (stdR2 leanPrims) (envOfY (yf k)) (emitC tanhVarEML)).toF)
    (hplantx : ∀ k, x (k + 1) = a * x k + clamp (κ * tanh (x k)) (-U) U + w k)
    (hplantxf : ∀ k, xf (k + 1) = a * xf k + clamp (vc k) (-U) U + w k) :
    ∀ n, abs (xf n - x n)
      ≤ npow n (abs a + abs κ) * abs (xf 0 - x 0)
        + (abs κ * u) * geom (abs a + abs κ) n := by
  refine clamp_guarded_tracking (C := fun y => κ * tanh y)
    (abs_nonneg κ) (mul_nonneg (abs_nonneg κ) u_nonneg)
    (fun p q => by
      rw [gain_scale_helper κ (tanh p) (tanh q), abs_mul]
      exact mul_le_mul_of_nonneg_left (tanh_lipschitz p q) (abs_nonneg κ))
    (fun k => by rw [hvc k, hxf k]; exact tanhVar_gain_error κ (yf k) R (hyf k))
    hplantx hplantxf

end Certcom
