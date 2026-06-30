import MachLib.OperatorClamp3

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

end MachLib.Real
