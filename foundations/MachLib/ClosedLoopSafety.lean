import MachLib.OperatorClamp3
import MachLib.Iteration

/-!
# Closed-loop safety — the guard keeps the plant in a safe envelope, for all time

Everything else in the certifier bounds error *per step*. This is the property a control engineer
actually cares about: a **closed-loop invariant** — the plant STATE stays inside a safe set for
ALL time, under ALL bounded disturbances. It is the "guard" thesis taken to its real conclusion.

The argument is a discrete-time barrier / Lyapunov (input-to-state-stability) one:

* `safe_envelope_invariant` — abstract core: if the trajectory contracts as `|x_{k+1}| ≤ ρ·|x_k| +
  δ` (`ρ < 1` hidden inside the invariance condition) and the envelope `X` is large enough
  (`ρ·X + δ ≤ X`, i.e. `X ≥ δ/(1−ρ)`), then `|x_k| ≤ X` for all `k`. The safe set is
  forward-invariant.
* `guarded_closed_loop_safe` — for a first-order plant `x_{k+1} = a·x_k + u_k + w_k` with a
  BOUNDED control `|u_k| ≤ U` and bounded disturbance `|w_k| ≤ W`, the state stays in the envelope
  whenever `|a|·X + (U+W) ≤ X` (a stable plant, `|a| < 1`, makes such an `X` exist).
* `clamp_guarded_safe` — the punchline. The bound `|u_k| ≤ U` is exactly what a **saturating guard**
  `u_k = clamp(v_k, −U, U)` provides (`clamp_abs_le`), for ANY signal `v_k` the controller computes.
  So the guarded loop is safe *even if the controller inside the guard is wrong* — the saturation,
  not the control law, is what carries the safety proof.

`sorryAx`-free (rests only on the model's `abs`/`max` primitives, as the clamp lemmas do).
-/

namespace MachLib.Real

/-- **Forward invariance of a safe envelope.** A trajectory that contracts (`|x_{k+1}| ≤ ρ·|x_k| +
δ`) starting inside an envelope wide enough to absorb the offset (`ρ·X + δ ≤ X`) never leaves it.
The discrete Lyapunov/ISS core: `|x_k| ≤ X` for all `k`. -/
theorem safe_envelope_invariant {x : Nat → Real} {ρ δ X : Real}
    (hρ : 0 ≤ ρ) (hinv : ρ * X + δ ≤ X) (h0 : abs (x 0) ≤ X)
    (hstep : ∀ k, abs (x (k + 1)) ≤ ρ * abs (x k) + δ) :
    ∀ k, abs (x k) ≤ X := by
  intro k
  induction k with
  | zero => exact h0
  | succ n ih =>
      exact le_trans (hstep n)
        (le_trans (add_le_add_both (mul_le_mul_of_nonneg_left ih hρ) (le_refl δ)) hinv)

/-- **A bounded-control first-order loop stays safe.** Plant `x_{k+1} = a·x_k + u_k + w_k`, control
bounded `|u_k| ≤ U`, disturbance bounded `|w_k| ≤ W`. If the envelope satisfies `|a|·X + (U+W) ≤ X`
(true for some finite `X` exactly when the plant is stable, `|a| < 1`) and the loop starts inside
it, the state stays inside it forever. -/
theorem guarded_closed_loop_safe {x u w : Nat → Real} {a U W X : Real}
    (hplant : ∀ k, x (k + 1) = a * x k + u k + w k)
    (hguard : ∀ k, abs (u k) ≤ U)
    (hdist : ∀ k, abs (w k) ≤ W)
    (hinv : abs a * X + (U + W) ≤ X)
    (h0 : abs (x 0) ≤ X) :
    ∀ k, abs (x k) ≤ X := by
  refine safe_envelope_invariant (abs_nonneg a) hinv h0 (fun k => ?_)
  rw [hplant k]
  have step : abs (a * x k + u k + w k) ≤ (abs a * abs (x k) + U) + W := by
    refine le_trans (abs_add (a * x k + u k) (w k)) ?_
    refine le_trans (add_le_add_both (abs_add (a * x k) (u k)) (le_refl (abs (w k)))) ?_
    rw [abs_mul]
    exact add_le_add_both (add_le_add_both (le_refl _) (hguard k)) (hdist k)
  exact le_trans step (le_of_eq (by mach_mpoly [abs a, abs (x k), U, W]))

/-- **The guard thesis, closed-loop.** A SATURATING guard `u_k = clamp(v_k, −U, U)` makes the loop
safe for ANY controller signal `v_k`: the clamp alone bounds `|u_k| ≤ U` (`clamp_abs_le`), and the
previous theorem does the rest. The safety property does not depend on what the controller inside
the guard computes — only that the guard saturates it. This is what lets a provably-safe envelope
survive a wrong (or faulty) controller. -/
theorem clamp_guarded_safe {x v w : Nat → Real} {a U W X : Real}
    (hplant : ∀ k, x (k + 1) = a * x k + clamp (v k) (-U) U + w k)
    (hU : 0 ≤ U)
    (hdist : ∀ k, abs (w k) ≤ W)
    (hinv : abs a * X + (U + W) ≤ X)
    (h0 : abs (x 0) ≤ X) :
    ∀ k, abs (x k) ≤ X := by
  refine guarded_closed_loop_safe hplant (fun k => ?_) hdist hinv h0
  have h := clamp_abs_le (v k) (-U) U
  rwa [abs_neg, abs_of_nonneg hU, max_self] at h

/-! ## ISS ultimate bound — the state CONVERGES into the safe envelope, from anywhere -/

/-- Clean-named ring identities (mach_mpoly's parser can't take atoms built from the induction
variable `m`, e.g. `npow m L` / `geom L m` — same limit as obtain'd primed vars). -/
theorem affine_step_eq (L s0 ε P G : Real) :
    L * (P * s0 + ε * G) + ε = (L * P) * s0 + ε * (1 + L * G) := by
  mach_mpoly [L, s0, ε, P, G]

theorem geom_reassoc (A UW G : Real) :
    (1 - A) * (UW * G) = UW * ((1 - A) * G) := by mach_mpoly [A, UW, G]

/-- Solution of the affine recurrence `s_{k+1} ≤ L·s_k + ε`: `s_n ≤ Lⁿ·s₀ + ε·(1+L+…+Lⁿ⁻¹)`.
Unlike `contraction_certificate` (which assumes `s₀ ≤ 0`, two orbits starting together), this keeps
the `Lⁿ·s₀` transient, so it bounds the ABSOLUTE state from an arbitrary start. -/
theorem iterate_affine_bound {L ε : Real} (s : Nat → Real) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hstep : ∀ k, s (k + 1) ≤ L * s k + ε) :
    ∀ n, s n ≤ npow n L * s 0 + ε * geom L n := by
  intro n
  induction n with
  | zero =>
      show s 0 ≤ npow 0 L * s 0 + ε * geom L 0
      rw [show npow 0 L = 1 from rfl, show geom L 0 = 0 from rfl]
      exact le_of_eq (by mach_ring)
  | succ m ih =>
      refine le_trans (hstep m)
        (le_trans (add_le_add_both (mul_le_mul_of_nonneg_left ih hL) (le_refl ε)) (le_of_eq ?_))
      rw [geom_succ, npow_succ]
      exact affine_step_eq L (s 0) ε (npow m L) (geom L m)

/-- **The guarded loop is input-to-state stable: the state converges into the safe envelope from
ANY initial state.** `|x_n| ≤ |a|ⁿ·|x₀| + (U+W)·geom |a| n`: the transient `|a|ⁿ·|x₀|` decays
(`|a| < 1`), and the disturbance term is bounded by the ultimate envelope —
`(1−|a|)·((U+W)·geom |a| n) ≤ U+W`, i.e. `(U+W)·geom |a| n ≤ (U+W)/(1−|a|)`. So the trajectory
settles into `‖x‖ ≤ (U+W)/(1−|a|)` no matter where it starts. The clamp guard supplies the `|u|≤U`
(`clamp_abs_le`), for ANY controller signal `v_k`. -/
theorem clamp_guarded_ultimately_bounded {x v w : Nat → Real} {a U W : Real}
    (hplant : ∀ k, x (k + 1) = a * x k + clamp (v k) (-U) U + w k)
    (hU : 0 ≤ U) (hW : 0 ≤ W)
    (hdist : ∀ k, abs (w k) ≤ W) :
    ∀ n, abs (x n) ≤ npow n (abs a) * abs (x 0) + (U + W) * geom (abs a) n
      ∧ (1 - abs a) * ((U + W) * geom (abs a) n) ≤ U + W := by
  have hUW : 0 ≤ U + W := add_nonneg_ea hU hW
  have hstep : ∀ k, abs (x (k + 1)) ≤ abs a * abs (x k) + (U + W) := by
    intro k
    rw [hplant k]
    have hg : abs (clamp (v k) (-U) U) ≤ U := by
      have h := clamp_abs_le (v k) (-U) U; rwa [abs_neg, abs_of_nonneg hU, max_self] at h
    have step : abs (a * x k + clamp (v k) (-U) U + w k) ≤ (abs a * abs (x k) + U) + W := by
      refine le_trans (abs_add (a * x k + clamp (v k) (-U) U) (w k)) ?_
      refine le_trans
        (add_le_add_both (abs_add (a * x k) (clamp (v k) (-U) U)) (le_refl (abs (w k)))) ?_
      rw [abs_mul]
      exact add_le_add_both (add_le_add_both (le_refl _) hg) (hdist k)
    exact le_trans step (le_of_eq (by mach_mpoly [abs a, abs (x k), U, W]))
  intro n
  refine ⟨iterate_affine_bound (fun k => abs (x k)) (abs_nonneg a) hUW hstep n, ?_⟩
  have hsc := geom_scaled_le_one (abs_nonneg a) n
  rw [geom_reassoc (abs a) (U + W) (geom (abs a) n)]
  exact le_trans (mul_le_mul_of_nonneg_left hsc hUW) (le_of_eq (by mach_ring))

/-! ## The envelope as a number — the value a bench measures against -/

/-- **The safe envelope, pinned to its ultimate value, division-free.** For a first-order plant
`x_{k+1} = a·x_k + clamp(v_k, −U, U) + w_k` with `0 ≤ a` and bounded disturbance `|w_k| ≤ W`: if the
candidate envelope `X` satisfies the ultimate-bound relation `(1 − a)·X = U + W` — i.e.
`X = (U+W)/(1−a)`, stated multiplicatively so no division/inverse is needed — and the trajectory
starts inside it, then `|x_k| ≤ X` for ALL `k`.

This is the bench's check made into a theorem: discharge `(1−a)·X = U+W` for a concrete plant (one
multiplication of the plant's own constants) and `X` is the line the captured state may not cross.
It is the division-free specialisation of `clamp_guarded_safe` — `abs a · X + (U+W) = a·X + (1−a)·X
= X`, so the invariance condition holds with equality exactly at the ultimate bound. -/
theorem first_order_clamp_envelope {x v w : Nat → Real} {a U W X : Real}
    (hplant : ∀ k, x (k + 1) = a * x k + clamp (v k) (-U) U + w k)
    (ha : 0 ≤ a) (hU : 0 ≤ U) (hdist : ∀ k, abs (w k) ≤ W)
    (henv : (1 - a) * X = U + W) (h0 : abs (x 0) ≤ X) :
    ∀ k, abs (x k) ≤ X := by
  refine clamp_guarded_safe hplant hU hdist ?_ h0
  rw [abs_of_nonneg ha, ← henv]
  exact le_of_eq (by mach_ring)

/-! ## Nonlinear plants — the guard keeps a NONLINEAR drift safe too -/

/-- **Closed-loop safety for a NONLINEAR plant.** The plant drift `f` is an arbitrary function; all
that matters is a sub-unity growth bound `|f(y)| ≤ L·|y| + c` (Lipschitz-at-origin / linear-growth,
`L < 1` via the invariance condition). Under the saturating guard, the state stays in `|x[k]| ≤ X`
for all `k` and ANY controller signal, whenever `L·X + (c+U+W) ≤ X`. The clamp again carries the
proof — the drift never has to be linear. This SUBSUMES `first_order_clamp_envelope`: a linear
`f(x)=a·x` gives `|f(x)| = |a|·|x|`, i.e. `L = |a|`, `c = 0`. -/
theorem nonlinear_drift_clamp_safe {x v w : Nat → Real} {f : Real → Real} {L c U W X : Real}
    (hplant : ∀ k, x (k + 1) = f (x k) + clamp (v k) (-U) U + w k)
    (hf : ∀ y, abs (f y) ≤ L * abs y + c)
    (hL : 0 ≤ L) (hU : 0 ≤ U) (hdist : ∀ k, abs (w k) ≤ W)
    (hinv : L * X + (c + U + W) ≤ X) (h0 : abs (x 0) ≤ X) :
    ∀ k, abs (x k) ≤ X := by
  refine safe_envelope_invariant hL hinv h0 (fun k => ?_)
  rw [hplant k]
  have hclamp : abs (clamp (v k) (-U) U) ≤ U := by
    have h := clamp_abs_le (v k) (-U) U; rwa [abs_neg, abs_of_nonneg hU, max_self] at h
  refine le_trans (abs_add (f (x k) + clamp (v k) (-U) U) (w k)) ?_
  refine le_trans
    (add_le_add_both (abs_add (f (x k)) (clamp (v k) (-U) U)) (le_refl (abs (w k)))) ?_
  refine le_trans (add_le_add_both (add_le_add_both (hf (x k)) hclamp) (hdist k)) ?_
  exact le_of_eq (by mach_ring)

/-- **Worked nonlinear instance.** A genuinely non-affine (V-shaped) drift `f(x) = a·|x|` is safe
under the guard: `|a·|y|| = |a|·|y|`, so `L = |a|`, `c = 0`, and the envelope is `X ≥ (U+W)/(1−|a|)`
exactly as in the linear case — but the plant is not linear. Shows `nonlinear_drift_clamp_safe` is
instantiable on a non-smooth drift, not just a relabelled linear one. -/
theorem nonlinear_abs_drift_safe {x v w : Nat → Real} {a U W X : Real}
    (hplant : ∀ k, x (k + 1) = a * abs (x k) + clamp (v k) (-U) U + w k)
    (hU : 0 ≤ U) (hdist : ∀ k, abs (w k) ≤ W)
    (hinv : abs a * X + (0 + U + W) ≤ X) (h0 : abs (x 0) ≤ X) :
    ∀ k, abs (x k) ≤ X := by
  refine nonlinear_drift_clamp_safe (f := fun y => a * abs y) hplant (fun y => ?_)
    (abs_nonneg a) hU hdist hinv h0
  rw [abs_mul, abs_of_nonneg (abs_nonneg y)]
  exact le_of_eq (by mach_ring)

end MachLib.Real
