import MachLib.Basic
import MachLib.Lemmas
import MachLib.Forge
import MachLib.Ring
import MachLib.MPolyRing
import MachLib.FPModel

/-!
# Backward error — the dual lens

Forward error asks *how far is the computed value from `f(exact)`?* **Backward**
error asks the dual: *the computed value is `f(exact)` for slightly-perturbed
inputs.* For ill-conditioned problems the backward view is often the honest one —
the algorithm is "good" if it solves a nearby problem exactly, even when the
forward error is large (because the problem itself is sensitive).

In the standard model `fl(a∘b) = (a∘b)(1+δ)`, every rounded op is *exactly* the
operation on relatively-perturbed inputs:

* `mul_backward` — `fl(a·b) = a'·b` with `|a'−a| ≤ w·|a|` (perturb one factor);
* `add_backward` — `fl(a+b) = a'+b'` with each input perturbed by `≤ w·|·|`.

This is the seed of the backward-stability theory (Higham): a rounded inner
product is the *exact* inner product of inputs each perturbed by `≤ γ_n`. The
condition number then maps backward error to forward error (`fwd ≲ κ·bwd`) —
joining this lens to the κ-analysis. `sorryAx`-free.
-/

namespace MachLib.Real

/-! fresh-var ring identities (obtain'd `δ` can't go through mach_mpoly's parser). -/
theorem bw_mulcomm (a b d : Real) : (a * b) * (1 + d) = (a * (1 + d)) * b := by
  mach_mpoly [a, b, d]
theorem bw_distrib (a b d : Real) : (a + b) * (1 + d) = a * (1 + d) + b * (1 + d) := by
  mach_mpoly [a, b, d]
theorem bw_pert_eq (a d : Real) : a * (1 + d) - a = a * d := by mach_mpoly [a, d]

/-- `|δ| ≤ w` from a `RoundsW` witness. -/
theorem roundsW_delta_abs {w δ : Real}
    (hδl : -w ≤ δ) (hδu : δ ≤ w) : abs δ ≤ w := by
  apply abs_le_of hδu
  have h := neg_le_neg hδl
  rwa [show -(-w) = w from by mach_ring] at h

/-- The perturbation a single relative `δ` induces: `|a·δ| ≤ w·|a|`. -/
theorem pert_bound {a δ w : Real} (h : abs δ ≤ w) : abs (a * δ) ≤ w * abs a := by
  rw [abs_mul]
  exact le_trans (mul_le_mul_of_nonneg_left h (abs_nonneg a))
                 (le_of_eq (mul_comm (abs a) w))

/-- **Backward error of a rounded product.** The computed product is the *exact*
product of a perturbed first factor. -/
theorem mul_backward {w a b p : Real} (hp : RoundsW w p (a * b)) :
    ∃ a', p = a' * b ∧ abs (a' - a) ≤ w * abs a := by
  obtain ⟨δ, hδl, hδu, hpeq⟩ := hp
  refine ⟨a * (1 + δ), ?_, ?_⟩
  · rw [hpeq]; exact bw_mulcomm a b δ
  · rw [bw_pert_eq a δ]; exact pert_bound (roundsW_delta_abs hδl hδu)

/-- **Backward error of a rounded sum.** The computed sum is the *exact* sum of
both inputs, each relatively perturbed by `≤ w`. -/
theorem add_backward {w a b p : Real} (hp : RoundsW w p (a + b)) :
    ∃ a' b', p = a' + b' ∧ abs (a' - a) ≤ w * abs a ∧ abs (b' - b) ≤ w * abs b := by
  obtain ⟨δ, hδl, hδu, hpeq⟩ := hp
  have hδabs := roundsW_delta_abs hδl hδu
  refine ⟨a * (1 + δ), b * (1 + δ), ?_, ?_, ?_⟩
  · rw [hpeq]; exact bw_distrib a b δ
  · rw [bw_pert_eq a δ]; exact pert_bound hδabs
  · rw [bw_pert_eq b δ]; exact pert_bound hδabs

end MachLib.Real
